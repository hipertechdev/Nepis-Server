using System;
using System.IO;
using System.Linq;
using System.Windows.Forms;
using WMPLib;
using System.Collections.Generic;
using System.Threading.Tasks;
using System.Threading;
using System.Diagnostics;
using System.Security.Principal;
using System.Text;
using Newtonsoft.Json.Linq;
using System.Net.Sockets;
using System.Drawing;
using System.Runtime.InteropServices;
using Newtonsoft.Json;
using System.Text.RegularExpressions;
using System.IO.Compression;
using System.Net;
using System.Net.NetworkInformation;
using System.Collections.Concurrent;
using System.Security.Cryptography;
using Renci.SshNet;
using NAudio.Wave;
using SIPSorcery.SIP;
using SIPSorcery.SIP.App;
using NAudio.CoreAudioApi;

namespace Nepis_Server
{
    public partial class FormMain : Form
    {
        // 메시지 도배 방지 & 재진입 방지
        private bool _tabDeniedNotified = false;
        private bool _handlingSelecting = false;
        private readonly List<TabPage> _lockedTabs = new List<TabPage>();
        private readonly Dictionary<string, int> _origTabIndexes = new Dictionary<string, int>(StringComparer.OrdinalIgnoreCase);
        private ToolStripStatusLabel toolStripStatusLabelLicense;
        private readonly List<TabPage> _allTabsSnapshot = new List<TabPage>();

        // 만료 상태에서 허용할 탭 Name 화이트리스트
        private readonly HashSet<string> _expiredAllowedTabNames =
            new HashSet<string>(StringComparer.OrdinalIgnoreCase)
            {
        "tabSystem" // 설정 탭만 허용
            };
        private Process ffmpegProcess;
        private string musicFolder;
        private string mentFolder;
        private WindowsMediaPlayer player = new WindowsMediaPlayer();
        private Queue<string> playQueue = new Queue<string>();
        private bool isSequentialPlaying = false;
        private string speakerFile = Path.Combine(Application.StartupPath, "speakers.txt");
        private List<(string ip, string location)> statusSpeakers = new List<(string, string)>();
        private readonly object speakerLock = new object();
        private bool isHandlingTabChange = false;
        private bool isCheckingStatus = false;
        private bool hasLoadedVolumeSpeakers = false;
        private bool isHandlingCheckAll = false;
        private List<string> knownDrives = new List<string>();
        private bool isStreamGridReady = false;
        private Dictionary<string, string> youtubeChannelMap = new Dictionary<string, string>();
        private readonly string streamPortFilePath = Path.Combine(Application.StartupPath, "stream_port.txt");
        private string ffmpegPath = Path.Combine(Application.StartupPath, "lib", "ffmpeg.exe");
        private string lastYoutubeUrl = null;
        private bool isYoutubeRepeating = false;
        private string multicastAddress = "239.255.0.1";
        private int port = 5004;
        private string sdpPath = Path.Combine(Application.StartupPath, "stream.sdp");
        private readonly object ffmpegLock = new object();
        private Dictionary<string, string> youtubeChannels = new Dictionary<string, string>();
        private Process micStreamProcess;
        private bool bgmStartedByAuto = false;
        private bool scheduleTabInitialized = false;
        private bool isApplyingGroupSelection = false;
        private readonly string excludeDateFilePath = Path.Combine(Application.StartupPath, "exclude_dates.txt");
        private readonly string configPath = Path.Combine(Application.StartupPath, "streaming_config.txt");
        private readonly string logFilePath = Path.Combine(Application.StartupPath, "log.txt");
        private bool isLoadingStartConfig = false;
        private Process vlcMonitorProcess = null;
        private readonly SemaphoreSlim semaphore = new SemaphoreSlim(10); // 최대 동시 연결 수 제한
        private Dictionary<string, string> speakerStatusMap = new Dictionary<string, string>();
        private HashSet<string> selectedVolumeIPs = new HashSet<string>();
        private bool hasBgmStoppedToday = false;
        private readonly object debugFileLock = new object();
        private StreamWriter ffmpegLogWriter;
        private bool isBgmAutoOnChecked = false;
        private bool isBgmAutoOffChecked = false;
        private bool speakersLoaded = false;
        private List<(string ip, string sip, string location, string group, string model)> allSpeakers
            = new List<(string ip, string sip, string location, string group, string model)>();
        private List<(string ip, string group)> streamSpeakers = new List<(string ip, string group)>();
        private List<(string ip, string location, string group)> scheduleSpeakers = new List<(string ip, string location, string group)>();
        private readonly HashSet<string> _logOnce = new HashSet<string>();
        private readonly object _logOnceLock = new object();
        private CancellationTokenSource _autoBgmCts;
        private enum DebugMode { Off, ErrorsOnly, Full }
        private DebugMode _ffmpegDebugMode = DebugMode.Off;
        //private DebugMode _ffmpegDebugMode = DebugMode.ErrorsOnly; // 기본: 에러 라인만 기록
        private const string FfmpegDebugPath = "ffmpeg_debug.txt";
        private const long FfmpegDebugMaxBytes = 5 * 1024 * 1024; // 5MB
        private EventHandler ffmpegExitedHandler;
        private int _autoRestartGate = 0;
        // BGM 제어 전송을 순차화(충돌 방지)
        private readonly SemaphoreSlim _bgmSendLock = new SemaphoreSlim(1, 1);

        // 재시작 중복 방지 플래그
        private volatile bool isRestartInProgress = false;

        // 스트림 준비 신호(없어도 동작, 있으면 더 안정)
        private volatile bool _streamReady = false;

        // 재시작 시 사용할 대상 IP 스냅샷
        private List<string> lastOnlineIPs = new List<string>();
        private DateTime lastStatusCheckTime = DateTime.MinValue;
        private readonly TimeSpan statusCacheDuration = TimeSpan.FromSeconds(10);

        // 스피커등록 탭: 레벨미터 폴링용
        private const int SP_STATUS_INTERVAL_MS = 100;  // 300 → 100
        private const int SP_STATUS_TIMEOUT_MS = 400;  // 1000 → 400
        private CancellationTokenSource spStatusStreamCts;
        private TcpClient spStatusTcpClient;
        private StreamReader spStatusReader;
        private NetworkStream spStatusNs;
        private bool _suppressSpCheckEvent = false;

        // === Auto-Stop 스케줄링 상태 ===
        private CancellationTokenSource _autoStopCts;
        private DateTime _armedAutoStopAt = DateTime.MinValue;   // 다음 자동 종료 예약시각
        private DateTime _lastAutoStopFired = DateTime.MinValue; // 마지막으로 실제 발화한 시각
        private System.Windows.Forms.Timer timerDailyRearm;      // 자정 재무장용

        // CGI
        private const string CGI_ID = "admin";
        private const string CGI_PW = "aepel1234";

        //=========
        /// </summary>
        private bool _scheduleComboInitDone = false;

        [DllImport("user32.dll")]
        static extern IntPtr SetParent(IntPtr hWndChild, IntPtr hWndNewParent);

        [DllImport("user32.dll")]
        static extern bool MoveWindow(IntPtr hWnd, int X, int Y, int nWidth, int nHeight, bool bRepaint);

        [DllImport("user32.dll", SetLastError = true)]
        static extern int GetWindowText(IntPtr hWnd, StringBuilder lpString, int nMaxCount);

        [DllImport("user32.dll")]
        static extern bool EnumThreadWindows(int dwThreadId, EnumThreadDelegate lpfn, IntPtr lParam);

        delegate bool EnumThreadDelegate(IntPtr hWnd, IntPtr lParam);

        private Process microSIPProcess = null;
        private IntPtr extraWindowHandle = IntPtr.Zero;
        private System.Threading.CancellationTokenSource _logCts;

        private readonly string LastChannelPath = Path.Combine(Application.StartupPath, "last_youtube_channel.txt");
        private readonly string YoutubeListPath = Path.Combine(Application.StartupPath, "youtube_channels.txt");

        // === Stream Watchdog Timer ===
        private volatile bool _streamingExpected = false;
        private volatile bool _isRecovering = false;
        private DateTime _lastRecoveryUtc = DateTime.MinValue;
        private static readonly TimeSpan RecoveryCooldown = TimeSpan.FromSeconds(20);

        // =========================
        // TTS 탭: 오프라인 자동 체크해제
        // =========================
        private System.Windows.Forms.Timer _ttsSpkOnlineTimer;
        private readonly SemaphoreSlim _ttsSpkOnlineGate = new SemaphoreSlim(1, 1);

        private const int TTS_SPK_CHECK_INTERVAL_MS = 8000; // 8초마다
        private const int TTS_SPK_CHECK_TIMEOUT_MS = 400;  // 포트 체크 타임아웃(ms)

        // 자동 종료 이후, 다음 ON 전까지 모든 자동 재시작/복구를 막기 위한 플래그
        private volatile bool _bgmHardStopped = false;

        // === 스피커 ffmpeg 재시작 이벤트 수신용 ===
        private HttpListener _speakerEventListener;
        private CancellationTokenSource _speakerEventCts;
        private DateTime _lastSpeakerResyncUtc = DateTime.MinValue;
        private static readonly TimeSpan SpeakerResyncCooldown = TimeSpan.FromMinutes(30);

        // =========================
        // TTS 상태/설정
        // =========================
        private string _ttsLastRemoteFile = "";
        private string _ttsLastLocalFile = "";

        // ✅ Nepis Server 내 저장 폴더 (원하시는 경로로 변경)
        private readonly string _ttsLocalSaveDir;

        // 로컬 재생
        private IWavePlayer _ttsWaveOut;
        private AudioFileReader _ttsAudioReader;
        private readonly object _ttsPlayLock = new object();
        private float _ttsLocalVolume = 1.0f; // 0.0~1.0

        // 중복 실행 방지
        private bool _ttsBusy = false;

        // =========================
        // (필수) 서버 설정 값 (Nepis Server 설정/ini/db에서 읽어오도록 나중에 연결)
        // =========================
        private string TTS_HOST => "192.168.0.15";  // TODO: 실제 TTS 서버 IP로 교체/설정 연동
        private int TTS_PORT => 22;              // SSH 포트
        private string TTS_USER => "aepel";         // 계정
        private string TTS_PASS => "aepel";      // 비밀번호
        private string TTS_SCRIPT => "/usr/local/bin/rs_tts_makemp3.sh";

        //===============================================================

        // =====================
        // TTS Server Status
        // =====================
        private System.Windows.Forms.Timer _ttsStatusTimer;
        private volatile bool _ttsStatusChecking = false;

        private enum TtsServerState { Checking, Online, Offline }
        private int _ttsServerCheckSeq = 0;

        // ====================================
        // 마지막 원격/로컬 파일
        private string _lastRemoteFileTTS = "";
        private string _lastLocalFileTTS = "";

        // 로컬 저장 폴더 (원하시면 Nepis 음원폴더로 변경)
        private readonly string _localSaveDirTTS = Path.Combine(Application.StartupPath, "Ment");

        // 로컬 재생(NAudio)
        private IWavePlayer _waveOutTTS;
        private AudioFileReader _audioReaderTTS;
        private readonly object _playLockTTS = new object();
        private float _localVolumeTTS = 1.0f; // 0.0~1.0
        private EventHandler<StoppedEventArgs> _ttsStoppedHandler;

        private readonly HashSet<string> _lastCgiTargets = new HashSet<string>();

        // SIP Client
        private SIPTransport _sipTransport;
        private SIPRegistrationUserAgent _regUa;

        // 등록유지(자동 재등록) 관련
        private readonly System.Windows.Forms.Timer _regKeepTimer
            = new System.Windows.Forms.Timer();
        private bool _registered = false;
        private DateTime _lastRegOkUtc = DateTime.MinValue;

        private MMDevice _micDevice;
        private MMDevice _spkDevice;
        private System.Windows.Forms.Timer _vuTimer;

        private NAudio.Wave.WaveInEvent _micCapture;
        private bool _uiUpdating = false;   // 트랙바↔시스템볼륨 이벤트 루프 방지
        private float _micGain = 1.0f;      // SIP 송출 gain (trackBarMic로 조절할 값)
        private float _spkGain = 1.0f;      // 수신 재생 gain (나중에)

        private string GetConfigPath()
        {
            return System.IO.Path.Combine(Application.StartupPath, "config.txt");
        }
        private void SaveTtsServerInfo()
        {
            try
            {
                var path = GetTtsServerConfigPath();

                var lines = new List<string>
        {
            "# Nepis Server - TTS Server Config",
            $"TTS_ServerIp={(txtTTSServerIp.Text ?? "").Trim()}",
            $"TTS_ServerUser={(txtTTSServerUser.Text ?? "").Trim()}",
            $"TTS_ServerPort={((int)numTTSServerPort.Value)}",

            // ✅ 비밀번호는 우선 저장 안 함(권장)
            // $"TTS_ServerPass={txtTTSServerPass.Text ?? ""}",
        };

                System.IO.File.WriteAllLines(path, lines, System.Text.Encoding.UTF8);

                // 상태/로그 표시(원하시면)
                // WriteLog("[TTS] 서버정보 저장 완료");
            }
            catch (Exception ex)
            {
                // WriteLog("[TTS] 서버정보 저장 실패: " + ex.Message);
                MessageBox.Show("TTS 서버정보 저장 실패: " + ex.Message);
            }
        }

        private void InitAudioMeters()
        {
            try
            {
                var enumerator = new MMDeviceEnumerator();

                // ✅ 마이크: Communications → Multimedia → Console 순 fallback
                _micDevice = enumerator.GetDefaultAudioEndpoint(DataFlow.Capture, Role.Communications);
                if (_micDevice == null)
                    _micDevice = enumerator.GetDefaultAudioEndpoint(DataFlow.Capture, Role.Multimedia);
                if (_micDevice == null)
                    _micDevice = enumerator.GetDefaultAudioEndpoint(DataFlow.Capture, Role.Console);

                // ✅ 스피커
                _spkDevice = enumerator.GetDefaultAudioEndpoint(DataFlow.Render, Role.Multimedia);

                // TrackBar 범위
                trackBarMic.Minimum = 0;
                trackBarMic.Maximum = 100;
                trackBarSpk.Minimum = 0;
                trackBarSpk.Maximum = 100;

                _uiUpdating = true;

                if (_micDevice != null)
                    trackBarMic.Value = Clamp0_100((int)(_micDevice.AudioEndpointVolume.MasterVolumeLevelScalar * 100));
                else
                    trackBarMic.Value = 50;

                if (_spkDevice != null)
                    trackBarSpk.Value = Clamp0_100((int)(_spkDevice.AudioEndpointVolume.MasterVolumeLevelScalar * 100));
                else
                    trackBarSpk.Value = 50;

                _uiUpdating = false;

                // 이벤트 연결(중복 방지)
                trackBarMic.Scroll -= trackBarMic_Scroll;
                trackBarMic.Scroll += trackBarMic_Scroll;

                trackBarSpk.Scroll -= trackBarSpk_Scroll;
                trackBarSpk.Scroll += trackBarSpk_Scroll;

                // VU 타이머
                if (_vuTimer == null)
                {
                    _vuTimer = new System.Windows.Forms.Timer();
                    _vuTimer.Interval = 50;
                    _vuTimer.Tick += VuTimer_Tick;
                }
                _vuTimer.Start();

                // 초기 상태 컬러(선택)
                lblSIPStatus.ForeColor = Color.Gray;

                // ✅ 디버깅: 실제 잡힌 장치 이름 확인
               //essageBox.Show(
               //   $"Mic: {(_micDevice?.FriendlyName ?? "NULL")}\n" +
               //   $"Spk: {(_spkDevice?.FriendlyName ?? "NULL")}"
               //;
            }
            catch (Exception ex)
            {
                MessageBox.Show("InitAudioMeters 예외: " + ex.Message);
            }
        }

        private void StartMicMonitor()
        {
            StopMicMonitor(); // 중복 방지

            _micCapture = new WaveInEvent();
            _micCapture.DeviceNumber = FindMicWaveInDeviceIndex();
            //_micCapture.DeviceNumber = 0; // 필요하면 콤보박스로 선택하도록 확장
            _micCapture.WaveFormat = new WaveFormat(8000, 16, 1);
            _micCapture.BufferMilliseconds = 20;

            _micCapture.DataAvailable += MicCapture_DataAvailable;
            _micCapture.RecordingStopped += (s, e) => { /* 필요시 로그 */ };

            _micCapture.StartRecording();
        }

        private void StopMicMonitor()
        {
            if (_micCapture == null) return;
            try { _micCapture.StopRecording(); } catch { }
            try { _micCapture.Dispose(); } catch { }
            _micCapture = null;
        }

        private int Clamp0_100(int v) => Math.Max(0, Math.Min(100, v));


        private void LoadTtsServerInfo()
        {
            try
            {
                var path = GetTtsServerConfigPath();
                if (!System.IO.File.Exists(path)) return;

                var dict = new Dictionary<string, string>(StringComparer.OrdinalIgnoreCase);

                foreach (var raw in System.IO.File.ReadAllLines(path, System.Text.Encoding.UTF8))
                {
                    var line = (raw ?? "").Trim();
                    if (line.Length == 0) continue;
                    if (line.StartsWith("#")) continue;

                    int idx = line.IndexOf('=');
                    if (idx <= 0) continue;

                    var key = line.Substring(0, idx).Trim();
                    var val = line.Substring(idx + 1).Trim();
                    dict[key] = val;
                }

                if (dict.TryGetValue("TTS_ServerIp", out var ip)) txtTTSServerIp.Text = ip;
                if (dict.TryGetValue("TTS_ServerUser", out var user)) txtTTSServerUser.Text = user;

                if (dict.TryGetValue("TTS_ServerPort", out var portStr) && int.TryParse(portStr, out var port))
                {
                    if (port < (int)numTTSServerPort.Minimum) port = (int)numTTSServerPort.Minimum;
                    if (port > (int)numTTSServerPort.Maximum) port = (int)numTTSServerPort.Maximum;
                    numTTSServerPort.Value = port;
                }

                // 비밀번호 저장 안 하면 로드도 생략
                // if (dict.TryGetValue("TTS_ServerPass", out var pass)) txtTTSServerPass.Text = pass;
            }
            catch (Exception ex)
            {
                // WriteLog("[TTS] 서버정보 로드 실패: " + ex.Message);
            }
        }
        private void btnTtsSaveServerInfo_Click(object sender, EventArgs e)
        {
            SaveTtsServerInfo();
        }
        private sealed class TtsPhraseItem
        {
            public int Id { get; set; }
            public string Title { get; set; }       // 사용자 표시명
            public string FileName { get; set; }    // 폴더 내 파일명 (예: 0001_화재대피.txt)
            public string Display => $"{Id:0000} | {Title}";
        }

        private TtsPhraseItem _selectedTtsPhrase = null;
        private bool _ttsPhraseLoading = false;

        private string GetTtsPhraseDir()
        {
            var dir = System.IO.Path.Combine(Application.StartupPath, "TTS", "phrases");
            System.IO.Directory.CreateDirectory(dir);
            return dir;
        }

        private string GetTtsIndexPath()
        {
            return System.IO.Path.Combine(GetTtsPhraseDir(), "index.cfg");
        }

        private string GetTtsPhrasePath(string fileName)
        {
            return System.IO.Path.Combine(GetTtsPhraseDir(), fileName);
        }
        private void InitTtsPhraseUi()
        {
            lstTTSFileList.DisplayMember = "Display";
            lstTTSFileList.SelectedIndexChanged -= lstTTSFileList_SelectedIndexChanged;
            lstTTSFileList.SelectedIndexChanged += lstTTSFileList_SelectedIndexChanged;

            // ✅ 파일명 박스를 클릭/포커스하면 신규 모드로 전환
            txtTTSFileName.Enter -= txtTTSFileName_EnterNewMode;
            txtTTSFileName.Enter += txtTTSFileName_EnterNewMode;

            ReloadTtsPhraseList();
        }
        private void txtTTSFileName_EnterNewMode(object sender, EventArgs e)
        {
            // 리스트 선택으로 로드 중이면 신규모드 전환 금지
            if (_ttsPhraseLoading) return;

            // 이미 선택이 없으면 할 일 없음
            if (_selectedTtsPhrase == null && lstTTSFileList.SelectedIndex < 0) return;

            // ✅ 선택 해제 + 신규 모드 전환
            lstTTSFileList.ClearSelected();
            _selectedTtsPhrase = null;

            // (선택) 신규 작성 UX: 텍스트를 비울지 유지할지 결정
            // - 파일명만 새로 쓰게 하고 문장은 유지: 아래 2줄 중 txtTTSText는 주석 유지
            txtTTSFileName.Text = "";
            // txtTTSText.Text = "";

            // 커서를 끝/처음 등 취향대로
            txtTTSFileName.SelectAll();
        }
        private void ReloadTtsPhraseList()
        {
            _ttsPhraseLoading = true;
            try
            {
                lstTTSFileList.Items.Clear();
                _selectedTtsPhrase = null;

                var indexPath = GetTtsIndexPath();
                if (!System.IO.File.Exists(indexPath))
                    return;

                var lines = System.IO.File.ReadAllLines(indexPath, System.Text.Encoding.UTF8);

                foreach (var raw in lines)
                {
                    var line = (raw ?? "").Trim();
                    if (line.Length == 0) continue;
                    if (line.StartsWith("#")) continue;

                    // id|title|file
                    var parts = line.Split('|');
                    if (parts.Length < 3) continue;

                    if (!int.TryParse(parts[0].Trim(), out int id)) continue;

                    var title = parts[1].Trim();
                    var file = parts[2].Trim();

                    if (string.IsNullOrWhiteSpace(title) || string.IsNullOrWhiteSpace(file))
                        continue;

                    lstTTSFileList.Items.Add(new TtsPhraseItem
                    {
                        Id = id,
                        Title = title,
                        FileName = file
                    });
                }

                // 정렬(번호순)
                var sorted = lstTTSFileList.Items.Cast<TtsPhraseItem>()
                    .OrderBy(x => x.Id)
                    .ToList();

                lstTTSFileList.Items.Clear();
                foreach (var it in sorted)
                    lstTTSFileList.Items.Add(it);
            }
            finally
            {
                _ttsPhraseLoading = false;
            }
        }
        private void lstTTSFileList_SelectedIndexChanged(object sender, EventArgs e)
        {
            if (_ttsPhraseLoading) return;

            var item = lstTTSFileList.SelectedItem as TtsPhraseItem;
            if (item == null) return;

            _ttsPhraseLoading = true;
            try
            {
                _selectedTtsPhrase = item;
                txtTTSFileName.Text = item.Title;
                txtTTSText.Text = File.ReadAllText(GetTtsPhrasePath(item.FileName), Encoding.UTF8);
            }
            finally
            {
                _ttsPhraseLoading = false;
            }
        }
        private void btnTtsFileSave_Click(object sender, EventArgs e)
        {
            SaveOrUpdateTtsPhrase();
        }
        private void SaveOrUpdateTtsPhrase()
        {
            var title = (txtTTSFileName.Text ?? "").Trim();
            var text = (txtTTSText.Text ?? "").Trim();

            if (string.IsNullOrWhiteSpace(text))
            {
                MessageBox.Show("문장을 입력해 주세요.");
                return;
            }

            // 제목이 비어있으면 문장 앞부분으로 자동 생성(12자)
            if (string.IsNullOrWhiteSpace(title))
            {
                title = MakeTitleFromText(text, 12);
                txtTTSFileName.Text = title;
            }

            var safeTitle = SanitizeFileName(title);

            try
            {
                // ✅ 수정 저장(현재 선택된 항목이 있으면 그 파일에 덮어쓰기)
                if (_selectedTtsPhrase != null)
                {
                    var path = GetTtsPhrasePath(_selectedTtsPhrase.FileName);
                    System.IO.File.WriteAllText(path, text, System.Text.Encoding.UTF8);

                    // 제목이 바뀌었으면 index도 갱신(파일명은 유지)
                    _selectedTtsPhrase.Title = title;
                    UpsertIndexItem(_selectedTtsPhrase.Id, _selectedTtsPhrase.Title, _selectedTtsPhrase.FileName);

                    MessageBox.Show("수정 저장되었습니다.");
                    int keepIdSelected = _selectedTtsPhrase.Id;
                    ReloadTtsPhraseList();
                    ReselectById(keepIdSelected);
                    return;
                }

                // ✅ 신규 저장
                int nextId = GetNextIdFromIndex();
                var fileName = $"{nextId:0000}_{safeTitle}.txt";
                fileName = MakeNonConflictFileName(fileName);

                var filePath = GetTtsPhrasePath(fileName);
                System.IO.File.WriteAllText(filePath, text, System.Text.Encoding.UTF8);

                UpsertIndexItem(nextId, title, fileName);

                MessageBox.Show("새 문장이 저장되었습니다.");
                int keepIdNew = nextId;
                ReloadTtsPhraseList();
                ReselectById(keepIdNew);
            }
            catch (Exception ex)
            {
                MessageBox.Show("저장 실패: " + ex.Message);
            }
        }
        private void btnTtsNew_Click(object sender, EventArgs e)
        {
            // 선택 해제 → 신규 저장 모드로 전환
            lstTTSFileList.ClearSelected();
            _selectedTtsPhrase = null;

            txtTTSFileName.Text = "";
            txtTTSText.Text = "";
            txtTTSText.Focus();
        }
        private void InitTtsNewAutoMode()
        {
            txtTTSFileName.TextChanged -= txtTTSFileName_TextChangedForNewMode;
            txtTTSFileName.TextChanged += txtTTSFileName_TextChangedForNewMode;
        }
        private void txtTTSFileName_TextChangedForNewMode(object sender, EventArgs e)
        {
            if (_ttsPhraseLoading) return;                 // 리스트 선택으로 로드 중이면 무시
            if (_selectedTtsPhrase == null) return;

            // 제목을 바꾸기 시작하면(= 신규 작성 가능성 높음) 자동 신규모드
            // 단, "수정 중 제목 변경(리네임)"을 허용하고 싶다면 이 자동 전환은 끄세요.
            if (!string.Equals((txtTTSFileName.Text ?? "").Trim(),
                               (_selectedTtsPhrase.Title ?? "").Trim(),
                               StringComparison.CurrentCulture))
            {
                lstTTSFileList.ClearSelected();
                _selectedTtsPhrase = null;
            }
        }
        private void btnTtsFileDel_Click(object sender, EventArgs e)
        {
            DeleteSelectedTtsPhrase();
        }
        private void DeleteSelectedTtsPhrase()
        {
            var item = lstTTSFileList.SelectedItem as TtsPhraseItem;

            // 선택이 없으면 _selectedTtsPhrase도 확인(혹시 SelectedItem을 안 쓰는 구조일 경우 대비)
            if (item == null) item = _selectedTtsPhrase;

            if (item == null)
            {
                MessageBox.Show("삭제할 항목을 선택해 주세요.");
                return;
            }

            // 삭제 확인(권장)
            var confirm = MessageBox.Show(
                $"선택한 문장을 삭제할까요?\r\n\r\n[{item.Id:0000} | {item.Title}]",
                "삭제 확인",
                MessageBoxButtons.YesNo,
                MessageBoxIcon.Warning);

            if (confirm != DialogResult.Yes)
                return;

            try
            {
                // 1) txt 파일 삭제
                string phrasePath = GetTtsPhrasePath(item.FileName);
                if (System.IO.File.Exists(phrasePath))
                    System.IO.File.Delete(phrasePath);

                // 2) index.cfg에서 해당 id 제거
                RemoveIndexItem(item.Id);

                // 3) UI 정리
                lstTTSFileList.ClearSelected();
                _selectedTtsPhrase = null;

                txtTTSFileName.Text = "";
                txtTTSText.Text = "";

                // 4) 리스트 갱신
                ReloadTtsPhraseList();

                MessageBox.Show("삭제되었습니다.");
            }
            catch (Exception ex)
            {
                MessageBox.Show("삭제 실패: " + ex.Message);
            }
        }
        private void RemoveIndexItem(int id)
        {
            var indexPath = GetTtsIndexPath();
            if (!System.IO.File.Exists(indexPath)) return;

            var lines = System.IO.File.ReadAllLines(indexPath, System.Text.Encoding.UTF8).ToList();
            if (lines.Count == 0) return;

            var outLines = new List<string>(lines.Count);

            foreach (var raw in lines)
            {
                var line = (raw ?? "").Trim();

                // 주석/빈줄 유지
                if (line.Length == 0 || line.StartsWith("#"))
                {
                    outLines.Add(raw);
                    continue;
                }

                var parts = line.Split('|');
                if (parts.Length < 3)
                {
                    // 포맷 이상 라인은 그대로 유지(안전)
                    outLines.Add(raw);
                    continue;
                }

                if (int.TryParse(parts[0].Trim(), out int curId) && curId == id)
                {
                    // ✅ 해당 항목 제거 (건너뜀)
                    continue;
                }

                outLines.Add(raw);
            }

            System.IO.File.WriteAllLines(indexPath, outLines, System.Text.Encoding.UTF8);
        }

        private int GetNextIdFromIndex()
        {
            var indexPath = GetTtsIndexPath();
            if (!System.IO.File.Exists(indexPath))
                return 1;

            int maxId = 0;
            var lines = System.IO.File.ReadAllLines(indexPath, System.Text.Encoding.UTF8);
            foreach (var raw in lines)
            {
                var line = (raw ?? "").Trim();
                if (line.Length == 0) continue;
                if (line.StartsWith("#")) continue;

                var parts = line.Split('|');
                if (parts.Length < 3) continue;

                if (int.TryParse(parts[0].Trim(), out int id))
                    if (id > maxId) maxId = id;
            }
            return maxId + 1;
        }

        private void UpsertIndexItem(int id, string title, string fileName)
        {
            var indexPath = GetTtsIndexPath();
            var list = new List<string>();

            if (System.IO.File.Exists(indexPath))
                list.AddRange(System.IO.File.ReadAllLines(indexPath, System.Text.Encoding.UTF8));
            else
                list.Add("# TTS phrases index: id|title|file");

            string newLine = $"{id:0000}|{title}|{fileName}";
            bool updated = false;

            for (int i = 0; i < list.Count; i++)
            {
                var line = (list[i] ?? "").Trim();
                if (line.Length == 0) continue;
                if (line.StartsWith("#")) continue;

                var parts = line.Split('|');
                if (parts.Length < 3) continue;

                if (int.TryParse(parts[0].Trim(), out int curId) && curId == id)
                {
                    list[i] = newLine;
                    updated = true;
                    break;
                }
            }

            if (!updated)
                list.Add(newLine);

            // id 기준 정렬(주석은 맨 위 유지)
            var header = list.Where(x => (x ?? "").Trim().StartsWith("#")).ToList();
            var body = list.Where(x => !(x ?? "").Trim().StartsWith("#"))
                           .Where(x => !string.IsNullOrWhiteSpace(x))
                           .ToList();

            body = body.OrderBy(x =>
            {
                var parts = x.Split('|');
                return (parts.Length > 0 && int.TryParse(parts[0].Trim(), out int id2)) ? id2 : int.MaxValue;
            }).ToList();

            var outLines = new List<string>();
            if (header.Count == 0) outLines.Add("# TTS phrases index: id|title|file");
            else outLines.AddRange(header.Distinct());

            outLines.AddRange(body);

            System.IO.File.WriteAllLines(indexPath, outLines, System.Text.Encoding.UTF8);
        }
        private string MakeTitleFromText(string text, int maxLen)
        {
            var t = (text ?? "").Trim().Replace("\r", " ").Replace("\n", " ");
            while (t.Contains("  ")) t = t.Replace("  ", " ");
            if (t.Length <= maxLen) return t;
            return t.Substring(0, maxLen);
        }

        private string SanitizeFileName(string s)
        {
            var invalid = System.IO.Path.GetInvalidFileNameChars();
            var sb = new System.Text.StringBuilder(s.Length);

            foreach (var ch in s)
            {
                if (invalid.Contains(ch)) continue;
                if (ch == '/' || ch == '\\' || ch == ':' || ch == '*' || ch == '?' || ch == '"' || ch == '<' || ch == '>' || ch == '|')
                    continue;
                sb.Append(ch);
            }

            var outp = sb.ToString().Trim();
            if (string.IsNullOrWhiteSpace(outp)) return "TTS";
            return outp;
        }

        private string MakeNonConflictFileName(string fileName)
        {
            var path = GetTtsPhrasePath(fileName);
            if (!System.IO.File.Exists(path)) return fileName;

            var name = System.IO.Path.GetFileNameWithoutExtension(fileName);
            var ext = System.IO.Path.GetExtension(fileName);

            for (int i = 1; i <= 999; i++)
            {
                var fn = $"{name}_{i}{ext}";
                if (!System.IO.File.Exists(GetTtsPhrasePath(fn))) return fn;
            }

            return $"{name}_{Guid.NewGuid():N}{ext}";
        }
        private void ReselectById(int id)
        {
            for (int i = 0; i < lstTTSFileList.Items.Count; i++)
            {
                if (lstTTSFileList.Items[i] is TtsPhraseItem it && it.Id == id)
                {
                    lstTTSFileList.SelectedIndex = i;
                    return;
                }
            }
        }

        private string GetTtsServerConfigPath()
        {
            return System.IO.Path.Combine(Application.StartupPath, "tts_server.cfg");
        }
        private Dictionary<string, string> LoadKeyValueFile(string path)
        {
            var dict = new Dictionary<string, string>(StringComparer.OrdinalIgnoreCase);

            if (!System.IO.File.Exists(path))
                return dict;

            foreach (var raw in System.IO.File.ReadAllLines(path))
            {
                var line = (raw ?? "").Trim();
                if (line.Length == 0) continue;
                if (line.StartsWith("#")) continue; // 주석 허용

                int idx = line.IndexOf('=');
                if (idx <= 0) continue;

                var key = line.Substring(0, idx).Trim();
                var val = line.Substring(idx + 1).Trim();

                dict[key] = val;
            }
            return dict;
        }

        private void WriteKeyValueFile(string path, Dictionary<string, string> dict)
        {
            var sb = new System.Text.StringBuilder();

            // 정렬해서 저장(가독성)
            foreach (var kv in dict.OrderBy(k => k.Key, StringComparer.OrdinalIgnoreCase))
                sb.AppendLine($"{kv.Key}={kv.Value}");

            System.IO.File.WriteAllText(path, sb.ToString(), System.Text.Encoding.UTF8);
        }
        // ===============
        private sealed class ComboItem
        {
            public string Text { get; }
            public string Value { get; }
            public ComboItem(string text, string value) { Text = text; Value = value; }
            public override string ToString() => Text;
        }
        // ✅ TTS 스피커 목록 로드 (app 폴더의 speakers.txt)
        private void LoadSpeakersTTSFromFile()
        {
            try
            {
                string path = Path.Combine(AppDomain.CurrentDomain.BaseDirectory, "speakers.txt");
                if (!File.Exists(path))
                {
                    MessageBox.Show("speakers.txt 파일이 없습니다:\r\n" + path);
                    return;
                }

                EnsureSelectTtsIsCheckbox();

                dgvSpeakersTTS.Rows.Clear();

                var groups = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
                var rowByIp = new Dictionary<string, DataGridViewRow>(StringComparer.OrdinalIgnoreCase);

                foreach (string raw0 in File.ReadAllLines(path))
                {
                    string line = (raw0 ?? "").Trim().Trim('\uFEFF');
                    if (line.Length == 0) continue;
                    if (line.StartsWith("#")) continue;

                    string[] parts = line.Split(new[] { '|' }, StringSplitOptions.None);
                    if (parts.Length < 3) continue;

                    string ip = (parts[0] ?? "").Trim().Trim('\uFEFF');
                    string sip = (parts.Length >= 2 ? parts[1] : "").Trim().Trim('\uFEFF');

                    // ✅ 오른쪽부터 해석: (끝=Model), (끝-1=Group), 나머지=Location
                    string model = "";
                    string group = "";
                    string location = "";

                    if (parts.Length == 3)
                    {
                        // IP|SIP|Location
                        location = (parts[2] ?? "").Trim().Trim('\uFEFF');
                    }
                    else if (parts.Length == 4)
                    {
                        // IP|SIP|Location|Group
                        group = (parts[3] ?? "").Trim().Trim('\uFEFF');
                        location = string.Join("|", parts.Skip(2).Take(parts.Length - 3)).Trim().Trim('\uFEFF');
                    }
                    else // parts.Length >= 5
                    {
                        // IP|SIP|Location|Group|Model  (Location은 | 포함 가능)
                        model = (parts[parts.Length - 1] ?? "").Trim().Trim('\uFEFF');
                        group = (parts[parts.Length - 2] ?? "").Trim().Trim('\uFEFF');
                        location = string.Join("|", parts.Skip(2).Take(parts.Length - 4)).Trim().Trim('\uFEFF');
                    }

                    // ✅ IP당 1행만 유지
                    if (!rowByIp.TryGetValue(ip, out var row))
                    {
                        int idx = dgvSpeakersTTS.Rows.Add();
                        row = dgvSpeakersTTS.Rows[idx];

                        row.Cells["SelectTTS"].Value = false;
                        row.Cells["IPTTS"].Value = ip;
                        row.Cells["SIPTTS"].Value = sip;
                        row.Cells["LocationTTS"].Value = location;
                        row.Cells["GroupColumnTTS"].Value = ""; // 아래에서 set 기반으로 채움
                        row.Cells["ModelColumnTTS"].Value = model; // ✅ 추가

                        // ✅ 그룹은 HashSet으로 누적 저장
                        row.Tag = new HashSet<string>(StringComparer.OrdinalIgnoreCase);

                        rowByIp[ip] = row;
                    }
                    else
                    {
                        // 빈 값이면 보강 정도만
                        if (string.IsNullOrWhiteSpace(row.Cells["SIPTTS"].Value?.ToString()) && !string.IsNullOrWhiteSpace(sip))
                            row.Cells["SIPTTS"].Value = sip;

                        if (string.IsNullOrWhiteSpace(row.Cells["LocationTTS"].Value?.ToString()) && !string.IsNullOrWhiteSpace(location))
                            row.Cells["LocationTTS"].Value = location;
                    }
                    // ✅ 모델도 빈 값이면 보강
                    if (dgvSpeakersTTS.Columns.Contains("ModelColumnTTS"))
                    {
                        if (string.IsNullOrWhiteSpace(row.Cells["ModelColumnTTS"].Value?.ToString()) && !string.IsNullOrWhiteSpace(model))
                            row.Cells["ModelColumnTTS"].Value = model;
                    }

                    // ✅ 그룹 누적 + 콤보 수집 (Tag(HashSet) 항상 보장 + 표시값 항상 갱신)
                    var set = row.Tag as HashSet<string>;
                    if (set == null)
                    {
                        set = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
                        row.Tag = set;
                    }

                    if (!string.IsNullOrWhiteSpace(group))
                    {
                        set.Add(group);
                        groups.Add(group);
                    }

                    // ✅ 화면 표시용 컬럼은 "항상" 갱신 (그룹 없으면 빈 문자열)
                    row.Cells["GroupColumnTTS"].Value = (set.Count > 0)
                        ? string.Join(",", set.OrderBy(x => x))
                        : "";

                }

                // ✅ 그룹 콤보 채우기
                const string ALL_GROUPS = "(전체선택)";   // ✅ '모든 그룹 선택'용 특수 옵션 (그룹명 '전체'와 분리)

                cmbGroupSelectTTS.BeginUpdate();
                try
                {
                    cmbGroupSelectTTS.Items.Clear();
                    cmbGroupSelectTTS.Items.Add(ALL_GROUPS);

                    foreach (var g in groups.OrderBy(x => x))
                        cmbGroupSelectTTS.Items.Add(g);

                    cmbGroupSelectTTS.SelectedIndex = 0;
                }
                finally
                {
                    cmbGroupSelectTTS.EndUpdate();
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("TTS 스피커 목록 로드 오류:\r\n" + ex.Message);
                WriteLog("[TTS] LoadSpeakersTTSFromFile 오류: " + ex);
            }
        }
        private void InitTtsSpeakerOfflineAutoUncheck()
        {
            try
            {
                if (_ttsSpkOnlineTimer != null) return;

                _ttsSpkOnlineTimer = new System.Windows.Forms.Timer();
                _ttsSpkOnlineTimer.Interval = TTS_SPK_CHECK_INTERVAL_MS;

                _ttsSpkOnlineTimer.Tick += async (s, e) =>
                {
                    // TTS 탭이 아닐 때는 불필요하게 돌지 않도록
                    if (tabControl1?.SelectedTab == null) return;
                    if (!string.Equals(tabControl1.SelectedTab.Name, "tabTtsBroadcast", StringComparison.OrdinalIgnoreCase))
                        return;

                    await UpdateTtsSpeakerOnlineStatusAsync();
                };

                _ttsSpkOnlineTimer.Start();

                // ✅ 시작하자마자 1회 즉시 반영
                _ = Task.Run(async () => await UpdateTtsSpeakerOnlineStatusAsync());
            }
            catch (Exception ex)
            {
                WriteLog("[TTS] InitTtsSpeakerOfflineAutoUncheck 오류: " + ex.Message);
            }
        }

        private async Task UpdateTtsSpeakerOnlineStatusAsync()
        {
            // 중복 실행 방지
            if (!await _ttsSpkOnlineGate.WaitAsync(0)) return;

            try
            {
                // 현재 모드에 따라 체크할 포트 결정
                bool useCgi = false;
                SafeUI(() =>
                {
                    try { useCgi = (chkUseCgi?.Checked ?? false); } catch { useCgi = false; }
                });

                int checkPort = useCgi ? 80 : 8787; // CGI면 80, 아니면(파일업/내장) 8787 기준

                // UI에서 IP 목록 스냅샷
                var rows = new List<DataGridViewRow>();
                SafeUI(() =>
                {
                    foreach (DataGridViewRow r in dgvSpeakersTTS.Rows)
                    {
                        if (r.IsNewRow) continue;
                        rows.Add(r);
                    }
                });

                // 병렬 체크 (과도한 동시접속 방지)
                var sem = new SemaphoreSlim(20);
                var results = new ConcurrentDictionary<string, bool>(StringComparer.OrdinalIgnoreCase);

                var tasks = rows.Select(async r =>
                {
                    string ip = "";
                    string model = "";

                    SafeUI(() =>
                    {
                        ip = (r.Cells["IPTTS"]?.Value?.ToString() ?? "").Trim();
                        if (dgvSpeakersTTS.Columns.Contains("ModelColumnTTS"))
                            model = (r.Cells["ModelColumnTTS"]?.Value?.ToString() ?? "").Trim().ToUpperInvariant();
                    });

                    if (string.IsNullOrWhiteSpace(ip))
                        return;

                    // 모델이 NONE(미사용)이면 오프라인 처리(선택 해제)
                    if (model == "NONE")
                    {
                        results[ip] = false;
                        return;
                    }

                    await sem.WaitAsync();
                    try
                    {
                        bool ok = await Task.Run(() => TryConnectWithTimeout(ip, checkPort, TTS_SPK_CHECK_TIMEOUT_MS));
                        results[ip] = ok;
                    }
                    finally
                    {
                        sem.Release();
                    }
                }).ToArray();

                await Task.WhenAll(tasks);

                // UI 반영: 오프라인이면 자동 체크해제 + 회색 처리(가벼운 표시)
                SafeUI(() =>
                {
                    foreach (DataGridViewRow r in dgvSpeakersTTS.Rows)
                    {
                        if (r.IsNewRow) continue;

                        string ip = (r.Cells["IPTTS"]?.Value?.ToString() ?? "").Trim();
                        if (string.IsNullOrWhiteSpace(ip)) continue;

                        if (results.TryGetValue(ip, out bool online))
                        {
                            if (!online)
                            {
                                // ✅ 오프라인이면 선택 해제
                                r.Cells["SelectTTS"].Value = false;

                                // ✅ 표시(선택): 오프라인 시 회색
                                r.DefaultCellStyle.ForeColor = Color.Gray;
                                r.Cells["IPTTS"].ToolTipText = "OFFLINE";
                            }
                            else
                            {
                                // 온라인이면 원복
                                r.DefaultCellStyle.ForeColor = dgvSpeakersTTS.DefaultCellStyle.ForeColor;
                                r.Cells["IPTTS"].ToolTipText = "";
                            }
                        }
                    }

                    // 전체선택 체크박스 상태도 정리
                    bool allChecked = true;
                    foreach (DataGridViewRow r in dgvSpeakersTTS.Rows)
                    {
                        if (r.IsNewRow) continue;
                        bool sel = r.Cells["SelectTTS"].Value as bool? ?? false;
                        if (!sel) { allChecked = false; break; }
                    }

                    _ttsSyncSelectAll = true;
                    try { chkSelectAllTTS.Checked = allChecked; }
                    finally { _ttsSyncSelectAll = false; }
                });
            }
            catch (Exception ex)
            {
                WriteLog("[TTS] UpdateTtsSpeakerOnlineStatusAsync 오류: " + ex);
            }
            finally
            {
                _ttsSpkOnlineGate.Release();
            }
        }

        private bool _ttsSyncSelectAll = false;
        private void chkSelectAllTTS_CheckedChanged(object sender, EventArgs e)
        {
            if (_ttsSyncSelectAll) return;

            bool check = chkSelectAllTTS.Checked;

            foreach (DataGridViewRow row in dgvSpeakersTTS.Rows)
            {
                if (row.IsNewRow) continue;
                row.Cells["SelectTTS"].Value = check;
            }
        }
        private void cmbGroupSelectTTS_SelectedIndexChanged(object sender, EventArgs e)
        {
            const string ALL_GROUPS = "(전체선택)"; // ✅ 위에서 넣은 특수 옵션과 동일해야 함

            string selectedGroup = (cmbGroupSelectTTS.SelectedItem ?? "").ToString().Trim();
            if (string.IsNullOrWhiteSpace(selectedGroup)) return;

            bool isAllGroups = selectedGroup.Equals(ALL_GROUPS, StringComparison.OrdinalIgnoreCase);

            if (isAllGroups)
            {
                foreach (DataGridViewRow row in dgvSpeakersTTS.Rows)
                {
                    if (row.IsNewRow) continue;
                    row.Cells["SelectTTS"].Value = true;
                }

                _ttsSyncSelectAll = true;
                try { chkSelectAllTTS.Checked = true; }
                finally { _ttsSyncSelectAll = false; }
                return;
            }

            // ✅ 여기부터는 '그룹명 그대로' 필터링 (예: "전체" 그룹만 선택 가능)
            foreach (DataGridViewRow row in dgvSpeakersTTS.Rows)
            {
                if (row.IsNewRow) continue;

                var set = row.Tag as HashSet<string>;
                bool inGroup = (set != null && set.Contains(selectedGroup));

                row.Cells["SelectTTS"].Value = inGroup;
            }

            _ttsSyncSelectAll = true;
            try { chkSelectAllTTS.Checked = false; }
            finally { _ttsSyncSelectAll = false; }
        }

        private List<string> GetSelectedSpeakerIPsTTS()
        {
            var ips = new List<string>();

            foreach (DataGridViewRow row in dgvSpeakersTTS.Rows)
            {
                if (row.IsNewRow) continue;

                bool selected = row.Cells["SelectTTS"].Value as bool? ?? false;
                if (!selected) continue;

                string ip = row.Cells["IPTTS"].Value?.ToString();
                if (!string.IsNullOrWhiteSpace(ip))
                    ips.Add(ip.Trim());
            }

            return ips;
        }

        private bool _ttsSelectingInternal = false;
        private void dgvSpeakersTTS_CellValueChanged(object sender, DataGridViewCellEventArgs e)
        {
            if (_ttsSelectingInternal) return;
            if (e.RowIndex < 0) return;
            if (dgvSpeakersTTS.Columns[e.ColumnIndex].Name != "SelectTTS") return;

            bool isChecked = dgvSpeakersTTS.Rows[e.RowIndex].Cells["SelectTTS"].Value as bool? ?? false;
            if (!isChecked) return;

            _ttsSelectingInternal = true;
            try
            {
                foreach (DataGridViewRow row in dgvSpeakersTTS.Rows)
                {
                    if (row.IsNewRow) continue;
                    if (row.Index == e.RowIndex) continue;
                    row.Cells["SelectTTS"].Value = false;
                }

                chkSelectAllTTS.Checked = false;
            }
            finally { _ttsSelectingInternal = false; }
        }
        // CGI
        private void InitSpeakerModelCombo()
        {
            // 표시(Text) / 저장값(Value) 분리
            var items = new[]
            {
        new { Text = "Aepel", Value = "AEPEL" },
        new { Text = "Axis",  Value = "AXIS"  },
        // 필요하면:
        new { Text = "미사용", Value = "NONE" },
    };

            cmbSpeakerModel.DisplayMember = "Text";
            cmbSpeakerModel.ValueMember = "Value";
            cmbSpeakerModel.DataSource = items.ToList();

            // 기본값
            cmbSpeakerModel.SelectedValue = "AEPEL";
        }
        public FormMain()
        {
            InitializeComponent();
            InitSpeakerModelCombo();
            LoadSpeakers();
            EnsureTtsTabAdded();
            InitializeTtsServerInfoUi(); //TTS 관련
            LoadTtsServerInfo();
            InitializeTtsServerInfoUi();
            InitTtsPhraseUi();
            InitTtsGenerateUi();
            InitTtsOptionCombos();
            InitAudioMeters();
            StartMicMonitor();

            this.Load += FormMain_Load;
            WireLicenseUi();

            // 현재 선택된 스트리밍 종류를 상태로 반영
            StreamTypeChanged(null, null);
            this.StartPosition = FormStartPosition.CenterScreen;

            // 리스트 먼저 로드 → 설정값 반영
            LoadYoutubeChannels();
            LoadStartConfig();

            // 타이머/이벤트들
            timerClock.Tick += timerClock_Tick;
            cmbGroupSelectStream.SelectedIndexChanged += cmbGroupSelectStream_SelectedIndexChanged;

            //SIP Client
            // 비밀번호 보기 체크
            chkSIPPasswordView.CheckedChanged += chkSIPPasswordView_CheckedChanged;

            // 등록유지 체크
            chkSIPReRegister.CheckedChanged += chkSIPReRegister_CheckedChanged;

            // 등록 버튼
            btnSIPRegister.Click += btnSIPRegister_Click;

            // 타이머: “등록 유지” 켜졌을 때 주기적으로 상태 점검(필요시 재시작)
            _regKeepTimer.Interval = 10_000; // 10초마다 점검
            _regKeepTimer.Tick += (s, e) => KeepRegistrationIfNeeded();

            // 초기 상태
            SetStatus("현재상태");
            txtSIPPassword.UseSystemPasswordChar = true;

            tabControl1.DrawMode = TabDrawMode.OwnerDrawFixed;
            tabControl1.DrawItem += tabControl1_DrawItem;

            tabInnerControl.DrawMode = TabDrawMode.OwnerDrawFixed;
            tabInnerControl.DrawItem += tabInnerControl_DrawItem;

            rbStreamYoutube.CheckedChanged += RadioMode_CheckedChanged;
            rbStreamMusic.CheckedChanged += RadioMode_CheckedChanged;
            rbStreamMic.CheckedChanged += RadioMode_CheckedChanged;

            musicFolder = Path.Combine(Application.StartupPath, "Music");
            mentFolder = Path.Combine(Application.StartupPath, "Ment");

            this.FormClosing += FormMain_FormClosing;
            player.PlayStateChange += Player_PlayStateChange;

            trackBarVolume.Value = 50;
            player.settings.volume = 50;
            lblVolume.Text = "볼륨: 50%";

            timerBgmAuto.Interval = 1000; // 1초

            Directory.CreateDirectory(musicFolder);
            Directory.CreateDirectory(mentFolder);
            isLoadingStartConfig = false;
            ArmAutoStop();


            LoadFiles();

            // ============================================================
            // 스피커등록 탭: 레벨미터(ProgressBar) & 체크박스 초기화/연결
            // ------------------------------------------------------------
            try
            {
                // 중복 구독 방지 후 초기 상태 OFF
                check_SP_Status.CheckedChanged -= check_SP_Status_CheckedChanged;
                check_SP_Status.Checked = false;
            }
            catch { /* ignore */ }
            finally
            {
                check_SP_Status.CheckedChanged += check_SP_Status_CheckedChanged;
            }

            try
            {
                progressBar_SP_Status.Minimum = 0;
                progressBar_SP_Status.Maximum = 100;
                progressBar_SP_Status.Value = 0;
            }
            catch { /* ignore */ }

            // (선택) 스피커등록 탭이 아닐 때 폴링 자동 중지
            // 탭 이름 또는 인덱스에 맞춰 조건을 조정하세요.
            tabControl1.SelectedIndexChanged += (s, e) =>
            {
                //bool isSpeakerRegTab = (tabControl1.SelectedTab?.Name == "tabSpeakerRegister");
                bool isSpeakerRegTab = (tabControl1.SelectedTab?.Name == "tabSpeakerAdd");

                if (!isSpeakerRegTab)
                {
                    // 스트리밍 정지
                    StopSPStatusStream();

                    // 프로그레스바 0으로
                    try { progressBar_SP_Status.Value = 0; } catch { /* ignore */ }

                    // 체크박스 OFF (이때 이벤트 재귀 방지)
                    _suppressSpCheckEvent = true;
                    try { check_SP_Status.Checked = false; }
                    catch { /* ignore */ }
                    finally { _suppressSpCheckEvent = false; }
                }
                else
                {
                    // 스피커등록 탭으로 다시 돌아왔고, 체크되어 있으면 스트림 재개
                    if (check_SP_Status.Checked)
                        StartSPStatusStream();
                }
            };
        }
        //============
        // TTS 매서드
        private void SafeUI(Action a)
        {
            if (a == null) return;

            // 폼이 닫히는 중이면 UI 업데이트 생략
            if (IsDisposed || !IsHandleCreated) return;

            try
            {
                if (InvokeRequired) BeginInvoke(a);
                else a();
            }
            catch
            {
                // closing 중 BeginInvoke 예외 등 무시
            }
        }

        private void InitializeTtsServerInfoUi()
        {
            // 1) 비밀번호 마스킹 기본값
            try
            {
                txtTTSServerPass.UseSystemPasswordChar = true;
                chkShowPassword.CheckedChanged -= chkShowPassword_CheckedChanged;
                chkShowPassword.CheckedChanged += chkShowPassword_CheckedChanged;
            }
            catch { /* ignore */ }

            // 2) SSH Port 기본값 22
            try
            {
                if (numTTSServerPort.Value <= 0) numTTSServerPort.Value = 22;
                if (numTTSServerPort.Minimum <= 0) numTTSServerPort.Minimum = 1;
                if (numTTSServerPort.Maximum < 65535) numTTSServerPort.Maximum = 65535;

                numTTSServerPort.ValueChanged -= numTTSServerPort_ValueChanged;
                numTTSServerPort.ValueChanged += numTTSServerPort_ValueChanged;
            }
            catch { /* ignore */ }

            // 3) 서버 상태 초기 표시
            SetTtsServerLamp(TtsServerState.Checking, "서버: 확인 중…");

            // 4) 서버 상태 주기 점검 타이머 (15초 권장)
            if (_ttsStatusTimer == null)
            {
                _ttsStatusTimer = new System.Windows.Forms.Timer();
                _ttsStatusTimer.Interval = 15000;
                _ttsStatusTimer.Tick += async (s, e) => await CheckTtsServerAsync();
            }
            _ttsStatusTimer.Start();

            // 5) 값 바뀌면 즉시 재점검(선택: UX 좋음)
            txtTTSServerIp.TextChanged -= TtsServerFields_Changed;
            txtTTSServerUser.TextChanged -= TtsServerFields_Changed;
            txtTTSServerPass.TextChanged -= TtsServerFields_Changed;

            txtTTSServerIp.TextChanged += TtsServerFields_Changed;
            txtTTSServerUser.TextChanged += TtsServerFields_Changed;
            txtTTSServerPass.TextChanged += TtsServerFields_Changed;

            // 첫 점검 1회
            _ = CheckTtsServerAsync();
        }
        // ====================
        private void InitTtsGenerateUi()
        {
            // 폴더 준비
            Directory.CreateDirectory(_localSaveDirTTS);

            // 상태 초기화
            if (lblStatusTTS != null) lblStatusTTS.Text = "대기중..";
            if (prgTTS != null)
            {
                InitTtsProgressBar();   // 항상 보이게 + 빈바
            }

            // 볼륨 슬라이더 초기화
            if (trackLocalVolTTS != null)
            {
                trackLocalVolTTS.Minimum = 0;
                trackLocalVolTTS.Maximum = 100;
                trackLocalVolTTS.Value = 100;

                // 디자이너 연결 누락 대비 강제 연결
                trackLocalVolTTS.Scroll += trackLocalVolTTS_Scroll;
                trackLocalVolTTS.ValueChanged += trackLocalVolTTS_ValueChanged;
            }
            LoadMentSoundListToListBox();
            _localVolumeTTS = 1.0f;
            UpdateLocalVolLabelTTS();

            // 버튼 이벤트 강제 연결
            if (btnMakeTTS != null) btnMakeTTS.Click += btnMakeTTS_Click;
            if (btnLocalPlayTTS != null) btnLocalPlayTTS.Click += btnLocalPlayTTS_Click;
            if (btnStopLocalTTS != null) btnStopLocalTTS.Click += btnStopLocalTTS_Click;
            if (btnOpenFolderTTS != null) btnOpenFolderTTS.Click += btnOpenFolderTTS_Click;

            UpdateButtonsTTS();
            LogTTS("TTS 생성/재생 UI 초기화 완료");
        }
        private void InitTtsProgressBar()
        {
            if (prgTTS == null) return;

            prgTTS.Visible = true;
            prgTTS.Style = ProgressBarStyle.Continuous;
            prgTTS.Minimum = 0;
            prgTTS.Maximum = 100;
            prgTTS.Value = 0;
            prgTTS.MarqueeAnimationSpeed = 0;

            if (prgTTS.Height < 8) prgTTS.Height = 8;
        }

        private void LogTTS(string msg)
        {
            SafeUI(() =>
            {
                if (txtLogTTS == null) return;
                txtLogTTS.AppendText($"[{DateTime.Now:HH:mm:ss}] {msg}{Environment.NewLine}");
            });
        }

        private void SetBusyTTS(bool busy, string status = null)
        {
            _ttsBusy = busy;
            SafeUI(() =>
            {
                if (btnMakeTTS != null) btnMakeTTS.Enabled = !busy;
                if (btnLocalPlayTTS != null) btnLocalPlayTTS.Enabled = !busy && File.Exists(_lastLocalFileTTS);
                if (btnStopLocalTTS != null) btnStopLocalTTS.Enabled = !busy;
                if (btnOpenFolderTTS != null) btnOpenFolderTTS.Enabled = !busy;

                if (prgTTS != null)
                {
                    prgTTS.Visible = true; // 항상 표시
                    if (!busy)
                    {
                        // 작업이 끝나면 "빈 바"로 복귀
                        prgTTS.Style = ProgressBarStyle.Continuous;
                        prgTTS.MarqueeAnimationSpeed = 0;
                        prgTTS.Minimum = 0;
                        prgTTS.Maximum = 100;
                        prgTTS.Value = 0;
                    }
                }
                if (!string.IsNullOrEmpty(status) && lblStatusTTS != null) lblStatusTTS.Text = status;
            });
        }
        private void ShowTtsLoginRequired(string detail = null)
        {
            SafeUI(() =>
            {
                // 상태 표시
                if (lblStatusTTS != null) lblStatusTTS.Text = "서버 로그인 필요";

                // 사용자 안내 메시지
                string msg =
                    "TTS 서버 로그인에 실패했습니다.\r\n\r\n" +
                    "서버 IP/포트/계정/비밀번호를 확인 후\r\n" +
                    "TTS 서버 정보 저장/로그인을 먼저 진행하세요.";

                if (!string.IsNullOrWhiteSpace(detail))
                    msg += "\r\n\r\n[상세]\r\n" + detail;

                MessageBox.Show(msg, "TTS 서버 로그인 필요", MessageBoxButtons.OK, MessageBoxIcon.Warning);
            });

            LogTTS("서버 로그인 필요" + (string.IsNullOrWhiteSpace(detail) ? "" : (": " + detail)));
        }

        // SSH/SFTP 인증 실패 판단 (Renci.SshNet 예외들)
        private bool IsAuthFailure(Exception ex)
        {
            if (ex == null) return false;

            // 비밀번호/권한/인증 실패
            if (ex is Renci.SshNet.Common.SshAuthenticationException) return true;

            // 간혹 inner로 감싸져 올라오는 경우
            if (ex.InnerException is Renci.SshNet.Common.SshAuthenticationException) return true;

            // 텍스트 기반 보강(환경별 메시지 차이 대비)
            string m = (ex.Message ?? "");
            if (m.IndexOf("Permission denied", StringComparison.OrdinalIgnoreCase) >= 0) return true;
            if (m.IndexOf("Authentication", StringComparison.OrdinalIgnoreCase) >= 0) return true;

            return false;
        }

        private void UpdateButtonsTTS()
        {
            SafeUI(() =>
            {
                if (btnLocalPlayTTS != null) btnLocalPlayTTS.Enabled = File.Exists(_lastLocalFileTTS) && !_ttsBusy;
                if (btnOpenFolderTTS != null) btnOpenFolderTTS.Enabled = Directory.Exists(_localSaveDirTTS) && !_ttsBusy;
            });
        }

        private void btnOpenFolderTTS_Click(object sender, EventArgs e)
        {
            try
            {
                Directory.CreateDirectory(_localSaveDirTTS);

                string dir = Path.GetFullPath(_localSaveDirTTS);
                LogTTS("폴더 열기: " + dir);

                // 1) Explorer가 죽어있거나 정책으로 shell open이 안 먹는 경우 대비
                //    explorer.exe를 직접 호출하는 방식이 제일 확실합니다.
                string explorer = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.Windows), "explorer.exe");

                if (!File.Exists(explorer))
                    explorer = "explorer.exe"; // fallback

                // ✅ 폴더 열기
                var psi = new ProcessStartInfo
                {
                    FileName = explorer,
                    Arguments = $"\"{dir}\"",     // 폴더 경로는 반드시 따옴표
                    UseShellExecute = false
                };

                Process.Start(psi);
            }
            catch (Exception ex)
            {
                MessageBox.Show("폴더 열기 실패: " + ex.Message);
                LogTTS("폴더 열기 실패: " + ex);
            }
        }


        // -----------------------
        // 볼륨
        // -----------------------
        private void trackLocalVolTTS_Scroll(object sender, EventArgs e) => ApplyLocalVolumeFromTrackbarTTS();
        private void trackLocalVolTTS_ValueChanged(object sender, EventArgs e) => ApplyLocalVolumeFromTrackbarTTS();

        private void ApplyLocalVolumeFromTrackbarTTS()
        {
            if (trackLocalVolTTS == null) return;

            int v = trackLocalVolTTS.Value;
            _localVolumeTTS = v / 100f;

            UpdateLocalVolLabelTTS();

            lock (_playLockTTS)
            {
                if (_audioReaderTTS != null)
                    _audioReaderTTS.Volume = _localVolumeTTS;
            }
        }

        private void UpdateLocalVolLabelTTS()
        {
            SafeUI(() =>
            {
                if (lblLocalVolTTS == null || trackLocalVolTTS == null) return;
                lblLocalVolTTS.Text = $"볼륨: {trackLocalVolTTS.Value}%";
            });
        }

        // -----------------------
        // 로컬 재생/정지
        // -----------------------
        private void btnLocalPlayTTS_Click(object sender, EventArgs e) => PlayLocalTtsIfExists();

        private void btnStopLocalTTS_Click(object sender, EventArgs e)
        {
            // 1) 로컬 정지
            lock (_playLockTTS)
            {
                StopLocalPlayback_NoThrowTTS();
            }

            // 2) CGI 정지(구현되어 있든 없든 호출해도 OK)
            //StopCgiBroadcast_NoThrowTTS();

            // 3) 스피커 stop_play
            var ips = GetCheckedSpeakerIPs_TTS();
            WriteLog($"[STOP] 선택된 스피커 수: {ips.Count} / {string.Join(",", ips)}");

            if (ips.Count > 0)
            {
                Task.Run(() => SendStopPlayToSpeakers_TTS(ips));
            }

            LogTTS("정지 버튼 실행: 로컬 + CGI + 스피커(stop_play)");
        }
        private List<string> GetCheckedSpeakerIPs_TTS()
        {
            // ✅ 체크박스 값 커밋 (아주 중요)
            try
            {
                dgvSpeakersTTS.CommitEdit(DataGridViewDataErrorContexts.Commit);
                dgvSpeakersTTS.EndEdit();
            }
            catch { }

            var list = new List<string>();

            // TODO: 실제 dgvSpeakersTTS의 컬럼 Name으로 변경
            const string COL_CHECK = "SelectTTS";   // 예: 체크박스 컬럼 Name
            const string COL_IP = "IPTTS";       // 예: IP 컬럼 Name

            foreach (DataGridViewRow row in dgvSpeakersTTS.Rows)
            {
                if (row.IsNewRow) continue;

                bool isChecked = false;
                try { isChecked = Convert.ToBoolean(row.Cells[COL_CHECK].Value); } catch { }

                if (!isChecked) continue;

                string ip = null;
                try { ip = row.Cells[COL_IP].Value?.ToString(); } catch { }

                if (!string.IsNullOrWhiteSpace(ip))
                    list.Add(ip.Trim());
            }

            return list;
        }
        private void SendStopPlayToSpeakers_TTS(List<string> ips)
        {
            foreach (var ip in ips)
            {
                try
                {
                    using (var client = new TcpClient())
                    {
                        client.Connect(ip, 39999);

                        byte[] data = Encoding.UTF8.GetBytes("stop_play");
                        using (var stream = client.GetStream())
                        {
                            stream.Write(data, 0, data.Length);
                            stream.Flush();
                        }
                    }

                    WriteLog($"[STOP OK] {ip}");
                }
                catch (Exception ex)
                {
                    WriteLog($"[STOP FAIL] {ip} : {ex.Message}");
                }
            }
        }

        private void PlayLocalTtsIfExists()
        {
            if (string.IsNullOrWhiteSpace(_lastLocalFileTTS) || !File.Exists(_lastLocalFileTTS))
            {
                LogTTS("로컬 재생 실패: 파일 없음");
                return;
            }

            try
            {
                lock (_playLockTTS)
                {
                    StopLocalPlayback_NoThrowTTS(); // 기존 재생 정리

                    _audioReaderTTS = new AudioFileReader(_lastLocalFileTTS);
                    _audioReaderTTS.Volume = _localVolumeTTS;

                    _waveOutTTS = new WaveOutEvent();

                    // ✅ 중요: PlaybackStopped에서 직접 Dispose하지 말고 UI로 보낸다
                    _ttsStoppedHandler = (s, e) =>
                    {
                        SafeUI(() =>
                        {
                            lock (_playLockTTS)
                            {
                                DisposePlayback_NoThrowTTS(); // 여기서만 Dispose
                            }
                        });
                    };
                    _waveOutTTS.PlaybackStopped += _ttsStoppedHandler;

                    _waveOutTTS.Init(_audioReaderTTS);
                    _waveOutTTS.Play();

                    LogTTS("로컬 재생: " + _lastLocalFileTTS);
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("로컬 재생 실패:\r\n" + ex.Message);
                LogTTS("로컬 재생 실패: " + ex.Message);
                lock (_playLockTTS) StopLocalPlayback_NoThrowTTS();
            }
        }

        private void StopLocalPlayback_NoThrowTTS()
        {
            try
            {
                // ✅ 이벤트 해제 먼저
                if (_waveOutTTS != null && _ttsStoppedHandler != null)
                {
                    try { _waveOutTTS.PlaybackStopped -= _ttsStoppedHandler; } catch { }
                    _ttsStoppedHandler = null;
                }

                try { _waveOutTTS?.Stop(); } catch { }

                // ✅ waveOut 먼저 Dispose
                try { _waveOutTTS?.Dispose(); } catch { }
                _waveOutTTS = null;
            }
            catch { }

            // ✅ 마지막에 reader Dispose
            DisposePlayback_NoThrowTTS();
        }

        private void DisposePlayback_NoThrowTTS()
        {
            try { _audioReaderTTS?.Dispose(); } catch { }
            _audioReaderTTS = null;
        }

        // -----------------------
        // TTS 생성 버튼
        // -----------------------
        private async void btnMakeTTS_Click(object sender, EventArgs e)
        {
            if (_ttsBusy) return;

            // ✅ 문장
            string text = (txtTTSText?.Text ?? "").Trim();
            if (string.IsNullOrWhiteSpace(text))
            {
                MessageBox.Show("TTS 문장이 없습니다. 문장관리에서 문장을 선택/입력하세요.");
                return;
            }

            // ✅ 서버 접속 정보
            string host = (txtTTSServerIp?.Text ?? "").Trim();
            int port = (int)(numTTSServerPort?.Value ?? 22);
            string user = (txtTTSServerUser?.Text ?? "").Trim();
            string pass = (txtTTSServerPass?.Text ?? "");

            if (string.IsNullOrWhiteSpace(host) || string.IsNullOrWhiteSpace(user))
            {
                MessageBox.Show("TTS 서버 정보를 확인하세요.");
                return;
            }

            string scriptPath = "/usr/local/bin/rs_tts_makemp3.sh";

            // ✅ 옵션 읽기 (콤보박스)
            string voice = "hyeryun";
            var vItem = cboTTSVoice?.SelectedItem as ComboItem;
            if (vItem != null && !string.IsNullOrWhiteSpace(vItem.Value))
                voice = vItem.Value;

            string speed = "1.0";
            var sItem = cboTTSSpeed?.SelectedItem as ComboItem;
            if (sItem != null && !string.IsNullOrWhiteSpace(sItem.Value))
                speed = sItem.Value;

            string format = "mp3";
            var fItem = cboTTSFormat?.SelectedItem as ComboItem;
            if (fItem != null && !string.IsNullOrWhiteSpace(fItem.Value))
                format = fItem.Value.ToLowerInvariant();

            if (format != "mp3" && format != "wav") format = "mp3";

            // 현재 서버 스크립트가 voice 인자를 안 받을 수 있으니 일단 로그만 남김
            LogTTS($"옵션: voice={voice}, speed={speed}, format={format}");

            SetBusyTTS(true, "TTS 생성 중...");
            SafeUI(() =>
            {
                if (prgTTS != null)
                {
                    prgTTS.Visible = true;
                    prgTTS.Style = ProgressBarStyle.Continuous;
                }
                if (lblStatusTTS != null) lblStatusTTS.Text = "TTS 생성 중...";
            });

            LogTTS($"TTS 생성 시작: {host}:{port}, user={user}");
            LogTTS($"옵션: speed={speed}, format={format}");

            try
            {
                // 1) SSH로 생성 → 원격 파일 경로 얻기
                string remotePath = await Task.Run(() =>
                    RunRemoteTtsMake(host, port, user, pass, scriptPath, text, speed, format));

                // ✅ 중요: RunRemoteTtsMake가 로그인 실패 시 null 반환하도록 구성한 경우도 대응
                if (string.IsNullOrWhiteSpace(remotePath))
                {
                    // (ShowTtsLoginRequired는 RunRemoteTtsMake 내부에서 이미 띄웠을 수 있음)
                    LogTTS("TTS 생성 중단: 원격 경로 없음(로그인 실패 또는 생성 실패)");
                    SafeUI(() =>
                    {
                        if (lblStatusTTS != null) lblStatusTTS.Text = "서버 로그인 필요";
                    });
                    return;
                }

                _lastRemoteFileTTS = remotePath;
                LogTTS("원격 생성 완료: " + _lastRemoteFileTTS);

                // 2) SFTP 다운로드
                SafeUI(() =>
                {
                    if (lblStatusTTS != null) lblStatusTTS.Text = "다운로드 중...";
                });

                bool downloadOk = await DownloadRemoteTtsFileAsync(host, port, user, pass, _lastRemoteFileTTS);

                if (!downloadOk)
                {
                    SafeUI(() => { if (lblStatusTTS != null) lblStatusTTS.Text = "생성 완료 (다운로드 실패)"; });
                    LogTTS("다운로드 실패");
                    return;
                }

                SafeUI(() => { if (lblStatusTTS != null) lblStatusTTS.Text = "완료"; });
                LogTTS("TTS 생성 + 다운로드 완료");

                // 3) 자동 로컬재생
                if (chkLocalPlayTTS != null && chkLocalPlayTTS.Checked)
                    PlayLocalTtsIfExists();

                // 4) 자동 스피커 전송 (다음 단계)
                // if (chkSP_TXTTS != null && chkSP_TXTTS.Checked) { ... }
            }
            catch (Exception ex)
            {
                // ✅ 로그인 실패(인증 실패)
                if (IsAuthFailure(ex) || (ex.InnerException != null && IsAuthFailure(ex.InnerException)))
                {
                    ShowTtsLoginRequired(ex.Message);
                    LogTTS("TTS 생성 중단: 로그인 필요");
                    SafeUI(() =>
                    {
                        if (lblStatusTTS != null) lblStatusTTS.Text = "서버 로그인 필요";
                    });
                    return;
                }

                // 기타 오류
                SafeUI(() =>
                {
                    if (lblStatusTTS != null) lblStatusTTS.Text = "실패";
                });
                MessageBox.Show("TTS 생성 실패:\r\n" + ex.Message);
                LogTTS("TTS 생성 실패: " + ex.Message);
            }
            finally
            {
                // ✅ 어떤 경우에도 UI 복귀 보장
                SafeUI(() =>
                {
                    if (prgTTS != null)
                    {
                        prgTTS.Visible = true;     // 숨기지 않음
                        prgTTS.Value = 0;          // 완료 후 빈 바로 유지
                        prgTTS.Style = ProgressBarStyle.Continuous;
                        prgTTS.MarqueeAnimationSpeed = 0;
                    }
                    if (lblStatusTTS != null && lblStatusTTS.Text != "완료")
                        lblStatusTTS.Text = "대기중..";
                });

                SetBusyTTS(false);
                UpdateButtonsTTS();
            }
            // ✅ 자동 스피커 전송/방송
            if (chkSP_TXTTS != null && chkSP_TXTTS.Checked)
            {
                await AutoSendTtsToSpeakersAsync(_lastLocalFileTTS);
            }
        }
        private void InitTtsOptionCombos()
        {
            // 1) 화자
            if (cboTTSVoice != null)
            {
                cboTTSVoice.Items.Clear();
                cboTTSVoice.DropDownStyle = ComboBoxStyle.DropDownList;

                // 현재 ReadSpeaker Hyeryun만 사용 (향후 확장 대비)
                cboTTSVoice.Items.Add(new ComboItem("혜련 (기본)", "hyeryun"));

                cboTTSVoice.SelectedIndex = 0;
            }

            // 2) 속도
            if (cboTTSSpeed != null)
            {
                cboTTSSpeed.Items.Clear();
                cboTTSSpeed.DropDownStyle = ComboBoxStyle.DropDownList;

                cboTTSSpeed.Items.Add(new ComboItem("느리게 (-2) 0.8x", "0.8"));
                cboTTSSpeed.Items.Add(new ComboItem("조금 느리게 (-1) 0.9x", "0.9"));
                cboTTSSpeed.Items.Add(new ComboItem("기본 (0) 1.0x", "1.0"));
                cboTTSSpeed.Items.Add(new ComboItem("조금 빠르게 (+1) 1.1x", "1.1"));
                cboTTSSpeed.Items.Add(new ComboItem("빠르게 (+2) 1.2x", "1.2"));

                cboTTSSpeed.SelectedIndex = 2; // 기본 1.0
            }

            // 3) 포맷
            if (cboTTSFormat != null)
            {
                cboTTSFormat.Items.Clear();
                cboTTSFormat.DropDownStyle = ComboBoxStyle.DropDownList;

                cboTTSFormat.Items.Add(new ComboItem("mp3", "mp3"));
                cboTTSFormat.Items.Add(new ComboItem("wav", "wav"));

                cboTTSFormat.SelectedIndex = 0; // 기본 mp3
            }
        }


        private string RunRemoteTtsMake(
           string host, int port, string user, string pass,
           string scriptPath, string text, string speed, string format)
        {
            try
            {
                using (var ssh = new SshClient(host, port, user, pass))
                {
                    ssh.ConnectionInfo.Timeout = TimeSpan.FromSeconds(10);

                    try
                    {
                        ssh.Connect();
                    }
                    catch (Exception ex) when (IsAuthFailure(ex))
                    {
                        // ✅ 로그인 실패: 여기서 안내하고 "null"로 종료
                        ShowTtsLoginRequired(ex.Message);
                        LogTTS("TTS 생성 중단: 로그인 필요 (" + ex.Message + ")");
                        return null;
                    }

                    // --- 텍스트 base64 전달/스크립트 실행/경로 파싱 ---
                    string b64 = Convert.ToBase64String(Encoding.UTF8.GetBytes(text));
                    format = (format ?? "mp3").ToLowerInvariant();
                    if (format != "mp3" && format != "wav") format = "mp3";

                    string cmd =
                        $"TEXT=$(echo '{b64}' | base64 -d); " +
                        $"{scriptPath} \"$TEXT\" \"\" \"{speed}\" \"{format}\"";

                    LogTTS("명령 실행: " + cmd);

                    var r = ssh.RunCommand(cmd);

                    string stdout = (r.Result ?? "").Trim();
                    string stderr = (r.Error ?? "").Trim();
                    string combined = (stdout + "\n" + stderr).Trim();

                    string remotePath = combined
                        .Split(new[] { "\r\n", "\n" }, StringSplitOptions.RemoveEmptyEntries)
                        .Select(x => x.Trim())
                        .LastOrDefault(x => x.StartsWith("/") &&
                            (x.EndsWith(".mp3", StringComparison.OrdinalIgnoreCase) ||
                             x.EndsWith(".wav", StringComparison.OrdinalIgnoreCase)));

                    if (string.IsNullOrWhiteSpace(remotePath))
                        throw new Exception("원격 파일 경로를 찾지 못했습니다.\r\n" + combined);

                    try { ssh.Disconnect(); } catch { }
                    return remotePath;
                }
            }
            catch (Exception ex)
            {
                // 로그인 실패는 위에서 처리됨. 여기서는 그 외 오류만 처리
                SafeUI(() => { if (lblStatusTTS != null) lblStatusTTS.Text = "실패"; });
                MessageBox.Show("TTS 생성 실패:\r\n" + ex.Message);
                LogTTS("TTS 생성 실패: " + ex.Message);
                return null;
            }
        }

        private async Task<bool> DownloadRemoteTtsFileAsync(
            string host, int port, string user, string pass, string remotePath)
        {
            if (string.IsNullOrWhiteSpace(remotePath) || !remotePath.StartsWith("/"))
                return false;

            Directory.CreateDirectory(_localSaveDirTTS);

            // ✅ 원본 파일명(서버에서 내려오는 파일명)
            string fileName = Path.GetFileName(remotePath);
            if (string.IsNullOrWhiteSpace(fileName))
                fileName = "tts_download.mp3";

            // ✅ 사용자가 입력한 이름(txtTTSFileName)을 파일명에 접두어로 추가
            string userName = "";
            SafeUI(() =>
            {
                userName = (txtTTSFileName?.Text ?? "").Trim();
            });

            // Windows 파일명에 들어갈 수 없는 문자 제거
            if (!string.IsNullOrWhiteSpace(userName))
            {
                foreach (char c in Path.GetInvalidFileNameChars())
                    userName = userName.Replace(c.ToString(), "");

                // 공백/점만 남는 경우 방지
                userName = userName.Trim().Trim('.');
            }

            // 최종 파일명 결정: {사용자이름}_{원본파일명}
            string finalFileName = string.IsNullOrWhiteSpace(userName)
                ? fileName
                : $"{userName}_{fileName}";

            string localPath = Path.Combine(_localSaveDirTTS, finalFileName);

            LogTTS($"SFTP 다운로드: {remotePath} -> {localPath}");

            bool ok = false;

            await Task.Run(() =>
            {
                using (var sftp = new SftpClient(host, port, user, pass))
                {
                    sftp.ConnectionInfo.Timeout = TimeSpan.FromSeconds(10);
                    sftp.Connect();

                    var attr = sftp.GetAttributes(remotePath);
                    long total = attr.Size;

                    using (var fs = new FileStream(localPath, FileMode.Create, FileAccess.Write, FileShare.Read))
                    {
                        sftp.DownloadFile(remotePath, fs, (ulong bytes) =>
                        {
                            int percent = (total <= 0) ? 0 : (int)((long)bytes * 100 / total);
                            percent = Math.Max(0, Math.Min(100, percent));

                            SafeUI(() =>
                            {
                                if (lblStatusTTS != null) lblStatusTTS.Text = $"다운로드 {percent}%";
                                if (prgTTS != null)
                                {
                                    prgTTS.Visible = true;
                                    prgTTS.Style = ProgressBarStyle.Blocks;
                                    prgTTS.Minimum = 0;
                                    prgTTS.Maximum = 100;
                                    prgTTS.Value = percent;
                                }
                            });
                        });
                    }

                    sftp.Disconnect();
                    ok = true;
                }
            });

            if (ok)
            {
                _lastLocalFileTTS = localPath;
                LogTTS("다운로드 완료: " + _lastLocalFileTTS);

                // ✅ 같은 이름(사용자 입력) TTS는 최신 1개만 유지
                string userPrefix = "";
                SafeUI(() =>
                {
                    userPrefix = (txtTTSFileName?.Text ?? "").Trim();
                });

                CleanupSameNameTtsFiles(userPrefix, localPath);

                // 기존 전체 개수 제한 정책 유지
                CleanupLocalTtsFilesTTS(100);
                LoadMentSoundListToListBox();
            }

            return ok;
        }


        private void CleanupLocalTtsFilesTTS(int maxCount)
        {
            try
            {
                if (maxCount < 1) return;
                if (!Directory.Exists(_localSaveDirTTS)) return;

                var dir = new DirectoryInfo(_localSaveDirTTS);
                var files = dir.GetFiles()
                    .Where(f => f.Extension.Equals(".mp3", StringComparison.OrdinalIgnoreCase) ||
                                f.Extension.Equals(".wav", StringComparison.OrdinalIgnoreCase))
                    .OrderByDescending(f => f.LastWriteTimeUtc)
                    .ToList();

                if (files.Count <= maxCount) return;

                foreach (var f in files.Skip(maxCount))
                {
                    try { f.Delete(); }
                    catch { LogTTS("정리 실패: " + f.Name); }
                }

                LogTTS($"로컬 TTS 파일 정리: 최대 {maxCount}개 유지");
            }
            catch (Exception ex)
            {
                LogTTS("로컬 정리 오류: " + ex.Message);
            }
        }

        private void CleanupSameNameTtsFiles(string userPrefix, string keepFilePath)
        {
            try
            {
                if (string.IsNullOrWhiteSpace(userPrefix)) return;
                if (!Directory.Exists(_localSaveDirTTS)) return;

                string safePrefix = userPrefix.Trim();

                foreach (char c in Path.GetInvalidFileNameChars())
                    safePrefix = safePrefix.Replace(c.ToString(), "");

                if (string.IsNullOrWhiteSpace(safePrefix)) return;

                var files = Directory.GetFiles(
                    _localSaveDirTTS,
                    $"{safePrefix}_tts_*.mp3",
                    SearchOption.TopDirectoryOnly
                );

                foreach (var f in files)
                {
                    if (!string.Equals(f, keepFilePath, StringComparison.OrdinalIgnoreCase))
                    {
                        try { File.Delete(f); }
                        catch { /* 로그 필요 시 추가 */ }
                    }
                }
            }
            catch (Exception ex)
            {
                LogTTS("[TTS 정리 오류] " + ex.Message);
            }
        }
        private void LoadMentSoundListToListBox()
        {
            try
            {
                Directory.CreateDirectory(_localSaveDirTTS);

                // ✅ 표시할 확장자(필요하면 추가)
                var exts = new HashSet<string>(StringComparer.OrdinalIgnoreCase)
        {
            ".mp3", ".wav", ".wma", ".aac", ".m4a"
        };

                var files = Directory.EnumerateFiles(_localSaveDirTTS, "*.*", SearchOption.TopDirectoryOnly)
                                     .Where(f => exts.Contains(Path.GetExtension(f)))
                                     .OrderByDescending(f => File.GetLastWriteTime(f)) // 최신순
                                     .ToList();

                SafeUI(() =>
                {
                    if (lstTTSSound == null) return;

                    lstTTSSound.BeginUpdate();
                    lstTTSSound.Items.Clear();

                    foreach (var f in files)
                    {
                        // 표시 텍스트는 파일명만
                        lstTTSSound.Items.Add(new MentSoundItem
                        {
                            FileName = Path.GetFileName(f),
                            FullPath = f,
                            Modified = File.GetLastWriteTime(f)
                        });
                    }

                    lstTTSSound.DisplayMember = nameof(MentSoundItem.FileName); // 화면엔 파일명만
                    lstTTSSound.EndUpdate();
                });

                LogTTS($"[Ment] 음원 목록 로드: {files.Count}개");
            }
            catch (Exception ex)
            {
                LogTTS("[Ment] 음원 목록 로드 실패: " + ex.Message);
            }
        }

        // ✅ ListBox에 파일명만 보여주고, 실제 경로는 같이 들고가기 위한 모델
        private class MentSoundItem
        {
            public string FileName { get; set; }
            public string FullPath { get; set; }
            public DateTime Modified { get; set; }

            public override string ToString() => FileName;
        }

        private void EnsureSelectTtsIsCheckbox()
        {
            // 이미 체크박스면 종료
            if (dgvSpeakersTTS.Columns["SelectTTS"] is DataGridViewCheckBoxColumn) return;

            // 기존 SelectTTS 컬럼 제거(텍스트/불린 표시 제거)
            if (dgvSpeakersTTS.Columns.Contains("SelectTTS"))
            {
                int idx = dgvSpeakersTTS.Columns["SelectTTS"].DisplayIndex;
                dgvSpeakersTTS.Columns.Remove("SelectTTS");

                var chk = new DataGridViewCheckBoxColumn
                {
                    Name = "SelectTTS",
                    HeaderText = "선택",
                    Width = 45,
                    TrueValue = true,
                    FalseValue = false,
                    IndeterminateValue = false,
                    ThreeState = false
                };
                dgvSpeakersTTS.Columns.Insert(idx, chk);
            }
            else
            {
                // 없으면 맨 앞에 추가
                var chk = new DataGridViewCheckBoxColumn
                {
                    Name = "SelectTTS",
                    HeaderText = "선택",
                    Width = 45,
                    TrueValue = true,
                    FalseValue = false,
                    IndeterminateValue = false,
                    ThreeState = false
                };
                dgvSpeakersTTS.Columns.Insert(0, chk);
            }

            // 클릭 즉시 반영 (체크박스 UX 필수)
            dgvSpeakersTTS.EditMode = DataGridViewEditMode.EditOnEnter;
            dgvSpeakersTTS.CurrentCellDirtyStateChanged -= dgvSpeakersTTS_CurrentCellDirtyStateChanged;
            dgvSpeakersTTS.CurrentCellDirtyStateChanged += dgvSpeakersTTS_CurrentCellDirtyStateChanged;
        }
        private void dgvSpeakersTTS_CurrentCellDirtyStateChanged(object sender, EventArgs e)
        {
            if (dgvSpeakersTTS.CurrentCell == null) return;
            if (dgvSpeakersTTS.CurrentCell.OwningColumn?.Name == "SelectTTS" &&
                dgvSpeakersTTS.IsCurrentCellDirty)
            {
                dgvSpeakersTTS.CommitEdit(DataGridViewDataErrorContexts.Commit);
            }
        }

        private void StartStreamWatchdog()
        {
            if (streamWatchdogTimer != null && !streamWatchdogTimer.Enabled)
                streamWatchdogTimer.Start();
        }

        private void StopStreamWatchdog()
        {
            if (streamWatchdogTimer != null && streamWatchdogTimer.Enabled)
                streamWatchdogTimer.Stop();
        }
        private async void streamWatchdogTimer_Tick(object sender, EventArgs e)
        {
            if (!_streamingExpected) return;

            if (ffmpegProcess == null || ffmpegProcess.HasExited)
                await RecoverStreamingAsync("Watchdog: ffmpeg 종료 감지");
        }

        private void ShowInfo(string message)
        {
            MessageBox.Show(
                this,                            // 현재 폼 기준으로 모달
                message,                         // 메시지 내용
                "알림",                          // 제목은 항상 "알림"
                MessageBoxButtons.OK,            // 버튼은 항상 OK
                MessageBoxIcon.Information       // 아이콘은 항상 Information
            );
        }

        private async Task RecoverStreamingAsync(string reason)
        {
            // 0) 하드스톱: 어떤 복구도 하지 않음
            if (_bgmHardStopped)
            {
                WriteLog("[워치독] 하드스톱 상태로 복구 차단");
                return;
            }

            // 0.5) 유튜브 모드는 자동 복구 대신 사용자에게 알림만 하고 종료
            if (rbStreamYoutube != null && rbStreamYoutube.Checked)
            {
                WriteLog($"[워치독] 유튜브 스트림 종료 감지: {reason} → 자동 복구하지 않고 사용자에게 알림");

                // 더 이상 스트리밍이 기대되지 않는 상태로 전환
                _streamingExpected = false;
                try { StartStreamWatchdog(); } catch { } // 필요시 StopStreamWatchdog() 였다면 여기서 정지로 변경

                if (!IsDisposed && IsHandleCreated)
                {
                    try
                    {
                        BeginInvoke((MethodInvoker)(async () =>
                        {
                            ytStatus.Text = "유튜브 스트리밍 중단됨";
                            StreamStatus.Text = "유튜브 스트리밍 중단됨";
                            StreamProgressBar.MarqueeAnimationSpeed = 0;
                            StreamProgressBar.Style = ProgressBarStyle.Continuous;
                            StreamProgressBar.Value = 0;
                            StreamProgressBar.Visible = false;

                            // 이 한 줄로 끝
                            ShowInfo("유튜브 스트림이 재시작됩니다.\n\n확인 버튼을 누르면 즉시 재시작됩니다.");

                            await Task.Delay(5000); // 1초 기다린 후 재시작
                            btnStartStream_Click(null, EventArgs.Empty);
                        }));
                    }

                    catch { }
                }

                return; // ⬅ 유튜브는 여기서 끝. 아래 자동 복구 로직은 파일/마이크만 사용
            }

            // 1) 중복/쿨다운 체크 (파일/마이크 모드에만 적용)
            if (_isRecovering) return; // 중복 진입 방지
            if (DateTime.UtcNow - _lastRecoveryUtc < RecoveryCooldown) return; // 과도 복구 방지

            _isRecovering = true;
            _lastRecoveryUtc = DateTime.UtcNow;

            try
            {
                WriteLog($"[워치독] 스트리밍 복구 시작: {reason}");

                // 2) 현재 온라인 대상 확보 (기존 코드 유지)
                var targetIPs = lastOnlineIPs?.ToList() ?? new List<string>();

                if (targetIPs.Count == 0)
                {
                    var selectedRows = dgvSpeakersStream.Rows
                        .Cast<DataGridViewRow>()
                        .Where(r => (r.Cells["Select"].Value as bool?) == true)
                        .ToList();

                    var onlineIPs = new List<string>();
                    var tasks = new List<Task>();
                    foreach (var row in selectedRows)
                    {
                        string ip = row.Cells["IP"].Value?.ToString();
                        if (string.IsNullOrWhiteSpace(ip)) continue;

                        tasks.Add(Task.Run(() =>
                        {
                            if (TryConnectWithTimeout(ip, 8787, 500))
                                lock (onlineIPs) onlineIPs.Add(ip);
                        }));
                    }
                    try { await Task.WhenAll(tasks); } catch { }
                    targetIPs = onlineIPs;
                    lastOnlineIPs = onlineIPs; // 스냅샷 갱신
                }

                if (targetIPs.Count == 0)
                {
                    WriteLog("[워치독] 온라인 스피커 없음. 복구 중단");
                    return;
                }

                // ★ BGM은 그대로 두고, 스트림만 복구
                WriteLog("[워치독] BGM_STOP/BGM_START 명령 생략 (현재 BGM 상태 유지)");

                // 3) 스트리밍 재시작 (파일/마이크만 실질적으로 사용)
                try
                {
                    if (rbStreamMusic.Checked)
                    {
                        WriteLog("[워치독] 파일 스트리밍 재시작");
                        StreamFromFile();
                    }
                    else if (rbStreamMic.Checked)
                    {
                        WriteLog("[워치독] 마이크 스트리밍 재시작");
                        StreamFromMic();
                    }
                    else if (rbStreamYoutube.Checked)
                    {
                        // 이 분기는 정상적이면 위에서 return 되어야 함.
                        // 혹시 라디오 버튼 상태가 꼬였을 때 대비용으로만 남겨둠.
                        string url = string.IsNullOrWhiteSpace(lastYoutubeUrl)
                            ? txtYoutubeUrl.Text.Trim()
                            : lastYoutubeUrl;

                        if (!string.IsNullOrWhiteSpace(url))
                        {
                            WriteLog("[워치독] (예외 경로) 유튜브 스트리밍 재시작 시도");
                            _ = Task.Run(() =>
                            {
                                try { StreamYoutubeAudio(url); }
                                catch (Exception ex) { WriteLog("유튜브 재시작 실패: " + ex.Message); }
                            });
                        }
                    }
                    else
                    {
                        WriteLog("[워치독] 현재 스트림 타입을 확인할 수 없어 복구 중단");
                        return;
                    }
                }
                catch (Exception ex)
                {
                    WriteLog("[워치독] 스트리밍 재시작 중 예외: " + ex.Message);
                }

                // 4) 약간의 워밍업 (필요시)
                await Task.Delay(3000);

                WriteLog("[워치독] 스트리밍 복구 완료 (BGM 상태는 그대로 유지)");

                // 5) 기대 상태/타이머 유지
                _streamingExpected = true;
                StartStreamWatchdog();
            }
            finally
            {
                _isRecovering = false;
            }
        }
        private bool _suppressVolumeEvents = false;

        private bool _youtubeListInitialized = false;
        private void FormMain_Load(object sender, EventArgs e)
        {
            if (prgTTS != null)
            {
                prgTTS.Visible = true;                       // ✅ 항상 보이게
                prgTTS.Style = ProgressBarStyle.Continuous; // ✅ 바 형태
                prgTTS.Minimum = 0;
                prgTTS.Maximum = 100;
                prgTTS.Value = 0;                           // ✅ 0이어도 바 표시됨

                // 중요: Marquee 흔적 제거
                prgTTS.MarqueeAnimationSpeed = 0;

                // Windows 10/11에서 바가 안 보이는 경우 대비
                if (prgTTS.Height < 8)
                    prgTTS.Height = 8;
            }
            // TTS
            chkSelectAllTTS.CheckedChanged += chkSelectAllTTS_CheckedChanged;
            cmbGroupSelectTTS.SelectedIndexChanged += cmbGroupSelectTTS_SelectedIndexChanged;

            LoadSpeakersTTSFromFile();
            InitTtsSpeakerOfflineAutoUncheck();

            // === YouTube 콤보: 사용자 선택 시 URL 동기화/저장 ===
            cmbYoutubeList.SelectionChangeCommitted -= cmbYoutubeList_SelectionChangeCommitted;
            cmbYoutubeList.SelectionChangeCommitted += cmbYoutubeList_SelectionChangeCommitted;

            // ✅ Volume 콤보 이벤트 강제 정리 (디자이너 잔존 방지)
            cmbGroupVolume.SelectedIndexChanged -= cmbGroupVolume_SelectedIndexChanged; // 혹시 남아있으면 제거
            cmbGroupVolume.SelectionChangeCommitted -= cmbGroupVolume_SelectionChangeCommitted;
            cmbGroupVolume.SelectionChangeCommitted += cmbGroupVolume_SelectionChangeCommitted;

            // === 유튜브 리스트: 앱 최초 1회만 '마지막 선택' 복원 ===
            LoadYoutubeList(restoreIfMissing: true, preserveCurrent: false);
            _youtubeListInitialized = true;

            // ⚠ 중복 로드 금지: 아래 기본 로드는 제거 (restoreIfMissing=false 래퍼 호출 불필요)
            // LoadYoutubeList();

            // === 워치독 타이머 생성 ===
            // 필드: private System.Windows.Forms.Timer streamWatchdogTimer;
            // using System.Windows.Forms; 가 파일 상단에 있어야 함
            streamWatchdogTimer = new System.Windows.Forms.Timer();
            streamWatchdogTimer.Interval = 5000;                    // 5초마다 체크
            streamWatchdogTimer.Tick += streamWatchdogTimer_Tick;   // 핸들러 연결
            _streamingExpected = false;                              // 시작 시엔 기대 상태 아님
            StopStreamWatchdog();                                    // 안전하게 OFF

            // === 탭 스냅샷 ===
            _allTabsSnapshot.Clear();
            _origTabIndexes.Clear();
            for (int i = 0; i < tabControl1.TabPages.Count; i++)
            {
                var tp = tabControl1.TabPages[i];
                _allTabsSnapshot.Add(tp);
                if (!_origTabIndexes.ContainsKey(tp.Name))
                    _origTabIndexes.Add(tp.Name, i);
            }

            // === 라이선스 UI 초기화 ===
            EnsureLicenseStatusUi();

            LicenseManager.LoadOrCreateFallback();
            LicenseManager.LicenseStateChanged += () =>
            {
                try
                {
                    this.Invoke((MethodInvoker)(() =>
                    {
                        ApplyLicenseEnforcement();
                        RefreshLicensePanelFromState();
                    }));
                }
                catch { }
            };

            tabControl1.Selecting -= tabControl1_Selecting;
            tabControl1.Selecting += tabControl1_Selecting;

            ApplyLicenseEnforcement();
            RefreshLicensePanelFromState();
            WriteLog($"[LICENSE] ApplyLicenseEnforcement expired={LicenseManager.IsExpired}");
            AppendAppLog($"[LICENSE][STATE] expired={LicenseManager.IsExpired}, reason={LicenseManager.FailReason}, raw='{LicenseManager.Current?.expiry}'");

            // ★ 방화벽 규칙 확인/추가
            EnsureFirewallRuleForSpeakerEvent();
            EnsureSpeakerEventFirewallRule();
            StartSpeakerEventListener();

            // ★ 스피커 ffmpeg 재시작 이벤트 수신 서버 시작
            StartSpeakerEventListener();
        }
        private void EnsureSpeakerEventFirewallRule()
        {
            try
            {
                var psi = new ProcessStartInfo
                {
                    FileName = "netsh",
                    Arguments = "advfirewall firewall add rule name=\"NepisSpeakerEventAll\" dir=in action=allow protocol=TCP localport=5000 profile=any",
                    UseShellExecute = true,
                    Verb = "runas",          // 관리자 권한 요청
                    CreateNoWindow = true
                };
                Process.Start(psi);
                WriteLog("[SPK_EVT] 방화벽 규칙 추가 명령 실행 (UAC 창 확인 필요)");
            }
            catch (Exception ex)
            {
                WriteLog("[SPK_EVT] 방화벽 규칙 추가 중 예외: " + ex.Message);
            }
        }

        private void EnsureFirewallRuleForSpeakerEvent()
        {
            try
            {
                // 이미 규칙이 있는지 간단히 검사 (이름으로 조회)
                var checkInfo = new ProcessStartInfo
                {
                    FileName = "netsh",
                    Arguments = "advfirewall firewall show rule name=\"Nepis SpeakerEvent\"",
                    UseShellExecute = false,
                    RedirectStandardOutput = true,
                    CreateNoWindow = true
                };

                using (var check = Process.Start(checkInfo))
                {
                    string output = check.StandardOutput.ReadToEnd();
                    check.WaitForExit();

                    // "No rules match the specified criteria" 이런 문구가 있으면 없는 것.
                    if (!string.IsNullOrEmpty(output) &&
                        output.IndexOf("No rules match", StringComparison.OrdinalIgnoreCase) < 0 &&
                        output.IndexOf("규칙이 없습니다", StringComparison.OrdinalIgnoreCase) < 0)
                    {
                        // 이미 규칙 있음
                        WriteLog("[SPK_EVT] 방화벽 규칙 'Nepis SpeakerEvent' 이미 존재");
                        return;
                    }
                }

                // 여기까지 왔으면 규칙이 없다는 뜻 → 추가 시도
                WriteLog("[SPK_EVT] 방화벽 규칙 없음 → 추가 시도");

                var addInfo = new ProcessStartInfo
                {
                    FileName = "netsh",
                    Arguments = "advfirewall firewall add rule name=\"Nepis SpeakerEvent\" dir=in action=allow protocol=TCP localport=5000",
                    UseShellExecute = true,   // UAC 사용 위해 true
                    Verb = "runas",           // 관리자 권한 요청
                    CreateNoWindow = true
                };

                Process.Start(addInfo);

                // 여기서는 UAC 창이 떠서 사용자 선택에 따라 성공/실패가 갈릴 수 있음
                // 정확한 성공 여부는 다음 실행 때 다시 show rule 검사로 확인 가능
                WriteLog("[SPK_EVT] 방화벽 규칙 추가 명령 실행 (UAC 창 확인 필요)");
            }
            catch (Exception ex)
            {
                WriteLog("[SPK_EVT] 방화벽 규칙 추가 중 예외: " + ex.Message);
            }
        }


        private void cmbYoutubeList_SelectionChangeCommitted(object sender, EventArgs e)
        {
            var name = cmbYoutubeList.SelectedItem?.ToString();
            if (string.IsNullOrWhiteSpace(name)) return;

            if (youtubeChannelMap.TryGetValue(name, out var url))
                txtYoutubeUrl.Text = url;   // ✅ 선택 즉시 URL 반영

            try { File.WriteAllText(LastChannelPath, name); } catch { /* ignore */ }
        }
        private void EnsureLicenseStatusUi()
        {
            // 1) 기존 StatusStrip 찾기 or 만들기
            StatusStrip strip = null;
            foreach (Control c in this.Controls)
                if (c is StatusStrip s) { strip = s; break; }
            if (strip == null)
            {
                strip = new StatusStrip { SizingGrip = false };
                this.Controls.Add(strip);
            }

            // 2) 기존 라벨 찾기 or 만들기
            var existing = strip.Items.OfType<ToolStripStatusLabel>()
                                      .FirstOrDefault(i => i.Name == "toolStripStatusLabelLicense");
            if (existing == null)
            {
                toolStripStatusLabelLicense = new ToolStripStatusLabel
                {
                    Name = "toolStripStatusLabelLicense",
                    Spring = true,
                    TextAlign = ContentAlignment.MiddleLeft
                };
                strip.Items.Add(new ToolStripStatusLabel { Text = " " }); // 구분자(선택)
                strip.Items.Add(toolStripStatusLabelLicense);
            }
            else
            {
                toolStripStatusLabelLicense = existing;
            }
        }
        private void LockTabsForExpired()
        {
            var sysTab = FindTabByName(tabControl1, "tabSystem");
            if (sysTab == null) return;

            _lockedTabs.Clear();
            var pages = tabControl1.TabPages.Cast<TabPage>().ToArray();
            foreach (var tp in pages)
            {
                if (!tp.Equals(sysTab))
                {
                    tabControl1.TabPages.Remove(tp);
                    _lockedTabs.Add(tp);
                }
            }

            if (tabControl1.SelectedTab != sysTab)
                tabControl1.SelectedTab = sysTab;
            WriteLog("[LICENSE] LockTabsForExpired()");
        }

        private void RestoreTabsForActive()
        {
            // 1) _lockedTabs에 보관된 것이 있으면 그걸 우선 복구
            if (_lockedTabs.Count > 0)
            {
                _lockedTabs.Sort((a, b) =>
                {
                    int ia = _origTabIndexes.TryGetValue(a.Name, out var xa) ? xa : int.MaxValue;
                    int ib = _origTabIndexes.TryGetValue(b.Name, out var xb) ? xb : int.MaxValue;
                    return ia.CompareTo(ib);
                });

                foreach (var tp in _lockedTabs)
                {
                    int insertIndex = _origTabIndexes.TryGetValue(tp.Name, out var idx)
                        ? Math.Min(idx, tabControl1.TabPages.Count)
                        : tabControl1.TabPages.Count;
                    if (!tabControl1.TabPages.Contains(tp))
                        tabControl1.TabPages.Insert(insertIndex, tp);
                    WriteLog("[LICENSE] RestoreTabsForActive()");
                }
                _lockedTabs.Clear();
                return;
            }

            // 2) 혹시 보관 리스트가 비었어도(예: 어떤 흐름에서 클리어됨),
            //    스냅샷 기준으로 누락 탭을 재삽입하여 항상 복구되게 함
            foreach (var tp in _allTabsSnapshot)
            {
                if (tp.Name.Equals("tabSystem", StringComparison.OrdinalIgnoreCase)) continue;
                if (!tabControl1.TabPages.Contains(tp))
                {
                    int insertIndex = _origTabIndexes.TryGetValue(tp.Name, out var idx)
                        ? Math.Min(idx, tabControl1.TabPages.Count)
                        : tabControl1.TabPages.Count;
                    tabControl1.TabPages.Insert(insertIndex, tp);
                }
            }
        }

        // FormMain.cs
        private void SetControlText(string controlName, string value)
        {
            if (this.IsHandleCreated && this.InvokeRequired)
            {
                this.BeginInvoke((MethodInvoker)(() => SetControlText(controlName, value)));
                return;
            }

            var found = this.Controls.Find(controlName, true);  // 하위 컨트롤까지 검색
            if (found.Length > 0 && found[0] != null)
                found[0].Text = value ?? string.Empty;
        }

        // 기존 메서드 대체
        private void RefreshLicensePanelFromState()
        {
            var li = LicenseManager.Current;

            // ↓ 필드 직접 참조 대신 이름으로 찾아 설정
            SetControlText("txtExpiry", li?.expiry);
            SetControlText("txtHwidHash", li?.hwid_hash);
            SetControlText("txtOrderId", li?.order_id);

            // 상태 표시 라벨도 동일하게 (컨트롤 이름에 맞게 바꾸세요)
            string status;
            if (LicenseManager.IsPerpetual)
                status = $"상태: 정상 (Edition={li?.edition}, 만료=영구)";
            else if (LicenseManager.IsExpired)
                status = $"상태: 만료 (Edition={li?.edition}, 만료={li?.expiry})";
            else
                status = $"상태: 정상 (Edition={li?.edition}, 만료={li?.expiry}, D-{LicenseManager.DaysRemaining})";

            SetControlText("txtLicenseStatus", status);
        }

        private void tabControl1_Selecting(object sender, TabControlCancelEventArgs e)
        {
            if (_handlingSelecting) return;
            if (!LicenseManager.IsExpired) { _tabDeniedNotified = false; return; }
            if (e.TabPage == null) return; // ← 보강

            if (!_expiredAllowedTabNames.Contains(e.TabPage.Name))
            {
                e.Cancel = true;

                if (!_tabDeniedNotified)
                {
                    _tabDeniedNotified = true;
                    MessageBox.Show(this,
                        "라이선스가 만료되어 해당 탭에 접근할 수 없습니다.\n'설정' 탭에서 라이선스를 갱신하세요.",
                        "라이선스 만료", MessageBoxButtons.OK, MessageBoxIcon.Warning);
                }

                try
                {
                    _handlingSelecting = true;
                    var sysTab = FindTabByName(tabControl1, "tabSystem");
                    if (sysTab != null && tabControl1.SelectedTab != sysTab)
                        tabControl1.SelectedTab = sysTab;
                }
                finally { _handlingSelecting = false; }
            }
            else
            {
                _tabDeniedNotified = false;
            }
        }
        private void ApplyLicenseEnforcement()
        {
            bool expired = LicenseManager.IsExpired;

            // 상태 텍스트(있으면)
            try
            {
                string status =
                    LicenseManager.IsPerpetual
                        ? $"상태: 정상 (Edition={LicenseManager.Current?.edition}, 만료=영구)"
                        : (expired
                            ? $"상태: 만료 (Edition={LicenseManager.Current?.edition}, 만료={LicenseManager.Current?.expiry})"
                            : $"상태: 정상 (Edition={LicenseManager.Current?.edition}, 만료={LicenseManager.Current?.expiry}, D-{LicenseManager.DaysRemaining})");

                if (toolStripStatusLabelLicense != null)   // ← 이 한 줄 추가
                    toolStripStatusLabelLicense.Text = status;
            }
            catch { }

            if (expired)
                LockTabsForExpired();
            else
                RestoreTabsForActive();

            _tabDeniedNotified = false;
        }
        private TabPage FindTabByName(TabControl tc, string name)
        {
            foreach (TabPage tp in tc.TabPages)
                if (string.Equals(tp.Name, name, StringComparison.OrdinalIgnoreCase)) return tp;
            return null;
        }
        private async Task EnsureSpeakerStatusesAsync()
        {
            if (DateTime.Now - lastStatusCheckTime < statusCacheDuration)
                return; // 캐시 사용
            await CheckStatusesSafeAsync();
            lastStatusCheckTime = DateTime.Now;
        }

        private void FixCheckBoxColumnBehavior()
        {
            if (dgvSpeakersSchedule.Columns["Select_SCH"] is DataGridViewCheckBoxColumn checkCol)
            {
                checkCol.TrueValue = true;
                checkCol.FalseValue = false;
                checkCol.IndeterminateValue = null;
                checkCol.DefaultCellStyle.NullValue = false;
            }
        }
        private void FormMain_Activated(object sender, EventArgs e)
        {
            dgvSpeakersSchedule.Refresh();
            dgvSpeakersSchedule.Invalidate();
            Application.DoEvents();
        }
        private bool excludeDatesLoaded = false;
        private void timerClock_Tick(object sender, EventArgs e)
        {
            lblCurrentTime.Text = "현재 시간: " + DateTime.Now.ToString("MM-dd (ddd) HH:mm:ss");
        }
        private bool IsImportantFfmpegLine(string line)
        {
            if (string.IsNullOrEmpty(line)) return false;
            string l = line.ToLowerInvariant();
            string[] keys = {
        "error","fail","invalid","timeout","timed out","connection","reset",
        "refused","unavailable","http","403","404","5xx","ssl","tls",
        "av_interleaved_write_frame","i/o","no such file","access denied","broken pipe"
    };
            foreach (var k in keys) if (l.Contains(k)) return true;
            return false;
        }
        private void RotateFfmpegDebugIfNeeded()
        {
            try
            {
                if (File.Exists(FfmpegDebugPath))
                {
                    var fi = new FileInfo(FfmpegDebugPath);
                    if (fi.Length >= FfmpegDebugMaxBytes)
                    {
                        File.WriteAllText(FfmpegDebugPath,
                            $"[ROTATE] {DateTime.Now:yyyy-MM-dd HH:mm:ss} - file trimmed (>{FfmpegDebugMaxBytes} bytes)\n");
                    }
                }
            }
            catch { /* ignore */ }
        }
        private void DebugAppend(string text, bool important = false)
        {
            if (_ffmpegDebugMode == DebugMode.Off) return;
            if (_ffmpegDebugMode == DebugMode.ErrorsOnly && !important) return;
            try
            {
                RotateFfmpegDebugIfNeeded();
                File.AppendAllText(FfmpegDebugPath, text + Environment.NewLine);
            }
            catch { /* ignore */ }
        }
        private async void tabControl1_SelectedIndexChanged(object sender, EventArgs e)
        {
            timerClock.Start();  // 현재시간 실시간 갱신 시작
            if (isHandlingTabChange) return;
            isHandlingTabChange = true;
            LoadYoutubeList();

            try
            {
                var selectedTabName = tabControl1.SelectedTab?.Name;

                if (selectedTabName == "tabSpeakerAdd")
                {
                    if (speakerStatusMap.Count == 0)
                    {
                        InitializeStatusGrid();
                        LoadSpeakersForStatus();
                        await CheckStatusesSafeAsync();
                    }
                    LoadSpeakers();
                    LoadGroups();
                    LoadMentSoundFiles();
                }
                else if (selectedTabName == "tabSpeakerStatus")
                {
                    InitializeStatusGrid();
                    LoadSpeakersForStatus();
                    await CheckStatusesSafeAsync();

                    InitializeVolumeGrid();   // 이벤트는 내부에서 -= 후 += 로 1회만
                    LoadGroupsForVolume();    // 콤보 채움(전체 포함), SelectedIndex=0
                    LoadSpeakersForVolume();  // ✅ 항상 전체 목록 로드(필터링 X)
                }
                else if (selectedTabName == "tabStream")
                {
                    InitializeSpeakerGridStream();   // ✅ 그리드 구조 먼저 구성
                    LoadGroupsForStream();           // ✅ 그룹 먼저 로드
                    LoadSpeakersForStream();         // ✅ 스피커 목록 로드
                    await CheckStatusesSafeAsync();

                    LoadYoutubeChannels();           // ✅ 채널 먼저
                    LoadStartConfig();               // ✅ 이후 설정 반영

                    LoadStreamPort();

                    StreamTypeChanged(null, null);   // ✅ 라디오버튼 등 초기화

                    panelYoutubeControls.Visible = false;

                    timerBgmAuto.Interval = 1000;
                    timerBgmAuto.Tick -= timerBgmAuto_Tick;
                    timerBgmAuto.Tick += timerBgmAuto_Tick;
                    timerBgmAuto.Start();
                }
                else
                {
                    // ✅ 다른 탭일 경우 타이머 정지
                    timerBgmAuto.Stop();
                    timerClock.Stop();  // 타이머 중단
                }
                if (tabControl1.SelectedTab.Name == "tabSchedule")
                {
                    InitializeStatusGrid();
                    LoadSpeakers();

                    if (speakerStatusMap.Count == 0 || dgvStatus.Rows.Count == 0)
                    {
                        InitializeStatusGrid();
                        LoadSpeakersForStatus();
                        await CheckStatusesSafeAsync();
                    }

                    LoadGroupsForSchedule();
                    LoadSpeakersForSchedule();
                    FixCheckBoxColumnBehavior(); // ✅ 체크박스 동작 보정 추가

                    if (!scheduleTabInitialized)
                    {
                        InitializeScheduleTabUi();
                        LoadGroupsForSchedule();
                        LoadSpeakersForSchedule();
                        dgvSpeakersSchedule.Refresh();
                        dgvSpeakersSchedule.Invalidate();
                        Application.DoEvents();
                        FixCheckBoxColumnBehavior();

                        LoadMentSCHSoundFiles();
                        LoadScheduleFromFile();
                        InitializeDayOfWeekComboBox();

                        if (!excludeDatesLoaded)
                        {
                            LoadExcludeDates();
                            excludeDatesLoaded = true;
                        }

                        scheduleTabInitialized = true;
                    }

                    timerSchedule.Interval = 1000;
                    timerSchedule.Tick -= timerSchedule_Tick;
                    timerSchedule.Tick += timerSchedule_Tick;
                    timerSchedule.Start();
                    timerSchedule.Enabled = true;
                }
                else if (selectedTabName == "tabSystem")
                {
                    LoadStartConfig();
                    UpdateCurrentTime();
                    CheckInternetConnection();
                    CheckNtpStatus();

                    // ✔ 스피커 IP 힌트 사용
                    var ips = GetCheckedSpeakerIPs(); // 없을 수 있으니 null 안전
                    var hintIps = (ips != null && ips.Count > 0) ? ips : null;

                    string serverIp = ResolveServerIPv4(hintIps);
                    lblServerIp.Text = "NTP 서버 주소: " + serverIp;

                    chkEnableNtpServer.Checked = IsNtpServerEnabled();
                    timerClock.Start();
                }
                else
                {
                    timerClock.Stop();   // 다른 탭일 때 중지
                }
            }
            finally
            {
                isHandlingTabChange = false;
            }
        }
        private string GetLocalIPv4ForRemote(string remoteIp)
        {
            if (string.IsNullOrWhiteSpace(remoteIp)) return null;
            try
            {
                using (var s = new Socket(AddressFamily.InterNetwork, SocketType.Dgram, ProtocolType.Udp))
                {
                    // NTP 포트로 '연결'만 해서 OS가 선택한 로컬 바인딩 IP 얻기 (패킷 실제 송신 없음)
                    s.Connect(remoteIp.Trim(), 123);
                    if (s.LocalEndPoint is IPEndPoint ep)
                        return ep.Address.ToString();
                }
            }
            catch { }
            return null;
        }

        private string GetDefaultRouteIPv4()
        {
            // 게이트웨이가 있는 '활성 NIC'의 IPv4를 우선 사용
            try
            {
                var nicBlacklist = new[] { "virtual", "vmware", "hyper-v", "loopback", "tunnel", "bluetooth", "docker", "npm", "pnp" };

                var ip = NetworkInterface.GetAllNetworkInterfaces()
                    .Where(ni =>
                        ni.OperationalStatus == OperationalStatus.Up &&
                        ni.NetworkInterfaceType != NetworkInterfaceType.Loopback &&
                        ni.NetworkInterfaceType != NetworkInterfaceType.Tunnel &&
                        !nicBlacklist.Any(b => ni.Description.ToLower().Contains(b) || ni.Name.ToLower().Contains(b)))
                    .Select(ni => new
                    {
                        ni,
                        props = ni.GetIPProperties()
                    })
                    .Where(x => x.props.GatewayAddresses.Any(g => g?.Address != null &&
                                                                  g.Address.AddressFamily == AddressFamily.InterNetwork &&
                                                                  !IPAddress.IsLoopback(g.Address)))
                    .SelectMany(x => x.props.UnicastAddresses
                        .Where(ua => ua.Address.AddressFamily == AddressFamily.InterNetwork &&
                                     !IPAddress.IsLoopback(ua.Address) &&
                                     !ua.Address.ToString().StartsWith("169.254.")) // APIPA 제외
                        .Select(ua => ua.Address.ToString()))
                    .FirstOrDefault();

                if (!string.IsNullOrEmpty(ip)) return ip;
            }
            catch { }
            return null;
        }

        private string GetAnyUsableIPv4()
        {
            // 활성 NIC의 유효 IPv4 아무거나 (최후 수단)
            try
            {
                var nicBlacklist = new[] { "virtual", "vmware", "hyper-v", "loopback", "tunnel", "bluetooth", "docker", "npm", "pnp" };

                var ip = NetworkInterface.GetAllNetworkInterfaces()
                    .Where(ni =>
                        ni.OperationalStatus == OperationalStatus.Up &&
                        ni.NetworkInterfaceType != NetworkInterfaceType.Loopback &&
                        ni.NetworkInterfaceType != NetworkInterfaceType.Tunnel &&
                        !nicBlacklist.Any(b => ni.Description.ToLower().Contains(b) || ni.Name.ToLower().Contains(b)))
                    .SelectMany(ni => ni.GetIPProperties().UnicastAddresses)
                    .Select(ua => ua.Address)
                    .Where(a => a.AddressFamily == AddressFamily.InterNetwork &&
                                !IPAddress.IsLoopback(a) &&
                                !a.ToString().StartsWith("169.254."))
                    .Select(a => a.ToString())
                    .FirstOrDefault();

                if (!string.IsNullOrEmpty(ip)) return ip;
            }
            catch { }
            return null;
        }

        private string ResolveServerIPv4(IEnumerable<string> remoteHintIps)
        {
            // 1) 스피커 IP 힌트가 있으면 그쪽으로 나갈 때의 바인딩 IP
            if (remoteHintIps != null)
            {
                foreach (var r in remoteHintIps)
                {
                    var ip = GetLocalIPv4ForRemote(r);
                    if (!string.IsNullOrEmpty(ip)) return ip;
                }
            }

            // 2) 기본 라우트가 있는 NIC의 IP
            var byDefaultRoute = GetDefaultRouteIPv4();
            if (!string.IsNullOrEmpty(byDefaultRoute)) return byDefaultRoute;

            // 3) 활성 NIC의 유효 IPv4 아무거나
            var any = GetAnyUsableIPv4();
            return any ?? "IP 주소를 찾을 수 없습니다.";
        }
        private void InitializeScheduleTabUi()
        {
            cmbGroupSelectSchedule.SelectionChangeCommitted += cmbGroupSelectSchedule_SelectionChangeCommitted;
            dgvScheduleList.SelectionMode = DataGridViewSelectionMode.FullRowSelect;
            dgvScheduleList.MultiSelect = false;

            LoadGroupsForSchedule();
            LoadMentSCHSoundFiles();
            InitializeDayOfWeekComboBox();

            dgvSpeakersSchedule.CellValueChanged += dgvSpeakersSchedule_CellValueChanged;
            dgvSpeakersSchedule.CurrentCellDirtyStateChanged += (s, _) =>
            {
                if (dgvSpeakersSchedule.IsCurrentCellDirty)
                    dgvSpeakersSchedule.CommitEdit(DataGridViewDataErrorContexts.Commit);
            };

            LoadScheduleFromFile();

            if (!excludeDatesLoaded)
            {
                LoadExcludeDates();
                excludeDatesLoaded = true;
            }
        }

        private void StartScheduleTimer()
        {
            timerSchedule.Interval = 1000;
            timerSchedule.Tick -= timerSchedule_Tick;
            timerSchedule.Tick += timerSchedule_Tick;
            timerSchedule.Start();
        }
        private bool IsNtpServerEnabled()
        {
            try
            {
                using (var key = Microsoft.Win32.Registry.LocalMachine.OpenSubKey(@"SYSTEM\CurrentControlSet\Services\W32Time\TimeProviders\NtpServer"))
                {
                    if (key != null)
                    {
                        object val = key.GetValue("Enabled");
                        if (val != null && int.TryParse(val.ToString(), out int result))
                        {
                            return result == 1;
                        }
                    }
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("NTP 설정 확인 실패: " + ex.Message);
            }
            return false;
        }
        private void InitializeStatusGrid()
        {
            if (dgvStatus.Columns.Count == 0)
            {
                dgvStatus.Columns.Add("colIP", "IP 주소");
                dgvStatus.Columns.Add("colLocation", "설치 장소");
                dgvStatus.Columns.Add("colStatus", "상태");
                dgvStatus.Columns.Add("colVolume", "볼륨");
            }
        }
        private void InitializeSpeakerGrid()
        {
            checkedListSpeakers.RowHeadersVisible = false;   // ✅ 추가
            checkedListSpeakers.AutoSizeColumnsMode = DataGridViewAutoSizeColumnsMode.None;

            if (checkedListSpeakers.Columns.Count == 0)
            {
                checkedListSpeakers.Columns.Add(new DataGridViewCheckBoxColumn() { Name = "SelectColumn", HeaderText = "선택", Width = 50 });
                checkedListSpeakers.Columns.Add("SpeakerIPColumn", "IP 주소");
                checkedListSpeakers.Columns.Add("SIPNumColumn", "SIP 번호");
                checkedListSpeakers.Columns.Add("LocationColumn", "설치 장소");
                checkedListSpeakers.Columns.Add("GroupColumn", "그룹 이름");
            }
        }
        private void FormMain_FormClosing(object sender, FormClosingEventArgs e)
        {
            try
            {
                player.controls.stop();
                timerPreview.Stop();
                progressBarPreview.Value = 0;
                lblNowPlaying.Text = "재생 중: 없음";
                SaveStartConfig();
            }
            catch
            {
                // 무시해도 무방
            }
            // ★ 스피커 이벤트 리스너 정리
            StopSpeakerEventListener();
        }

        // === 스피커 ffmpeg 재시작 이벤트 수신 서버 ===
        private void StartSpeakerEventListener()
        {
            try
            {
                if (!HttpListener.IsSupported)
                {
                    WriteLog("[SPK_EVT] HttpListener 미지원 환경입니다.");
                    return;
                }

                if (_speakerEventListener != null)
                {
                    // 이미 시작됨
                    return;
                }

                _speakerEventListener = new HttpListener();
                // cvlc.py 에서 호출하는 URL: http://<서버IP>:5000/speaker_event
                // HttpListener Prefix는 반드시 슬래시로 끝나야 합니다.
                _speakerEventListener.Prefixes.Add("http://+:5000/speaker_event/");
                _speakerEventListener.Start();
                using var cts = new CancellationTokenSource(15000);
                _speakerEventCts = new CancellationTokenSource();
                Task.Run(() => SpeakerEventLoopAsync(_speakerEventCts.Token));

                WriteLog("[SPK_EVT] 스피커 이벤트 수신 서버 시작 (포트 5000, /speaker_event)");
            }
            catch (Exception ex)
            {
                WriteLog("[SPK_EVT] 리스너 시작 실패: " + ex.Message);
            }
        }

        private void StopSpeakerEventListener()
        {
            try
            {
                _speakerEventCts?.Cancel();
            }
            catch { }

            try
            {
                _speakerEventListener?.Stop();
                _speakerEventListener?.Close();
            }
            catch { }

            _speakerEventListener = null;
            _speakerEventCts = null;

            WriteLog("[SPK_EVT] 스피커 이벤트 수신 서버 종료");
        }

        private async Task SpeakerEventLoopAsync(CancellationToken token)
        {
            try
            {
                while (!token.IsCancellationRequested && _speakerEventListener != null)
                {
                    HttpListenerContext ctx = null;
                    try
                    {
                        ctx = await _speakerEventListener.GetContextAsync();
                    }
                    catch (HttpListenerException)
                    {
                        // Stop/Close 시 발생 → 루프 종료
                        break;
                    }
                    catch (ObjectDisposedException)
                    {
                        break;
                    }
                    catch (Exception ex)
                    {
                        WriteLog("[SPK_EVT] GetContext 예외: " + ex.Message);
                        continue;
                    }

                    if (ctx == null) continue;

                    // 요청 처리는 별도 Task로
                    _ = Task.Run(() => HandleSpeakerEventRequestAsync(ctx), token);
                }
            }
            catch (Exception ex)
            {
                WriteLog("[SPK_EVT] Listener 루프 예외: " + ex.Message);
            }
        }
        private async Task HandleSpeakerEventRequestAsync(HttpListenerContext ctx)
        {
            try
            {
                if (ctx.Request.HttpMethod != "POST")
                {
                    ctx.Response.StatusCode = 405; // Method Not Allowed
                    ctx.Response.Close();
                    return;
                }

                string body;
                using (var reader = new StreamReader(ctx.Request.InputStream, ctx.Request.ContentEncoding ?? Encoding.UTF8))
                {
                    body = await reader.ReadToEndAsync();
                }

                JObject json;
                try
                {
                    json = JObject.Parse(body);
                }
                catch (Exception ex)
                {
                    WriteLog("[SPK_EVT] JSON 파싱 실패: " + ex.Message + " / body=" + body);
                    ctx.Response.StatusCode = 400;
                    ctx.Response.Close();
                    return;
                }

                string eventName = (string)json["event"] ?? "";
                string speakerId = (string)json["speaker_id"] ?? "";
                long ts = (long?)json["ts"] ?? 0;

                WriteLog($"[SPK_EVT] event={eventName}, speaker={speakerId}, ts={ts}");

                if (string.Equals(eventName, "FFMPEG_RESTART", StringComparison.OrdinalIgnoreCase))
                {
                    await OnSpeakerFfmpegRestartAsync(speakerId);
                }

                // 간단한 응답
                ctx.Response.StatusCode = 200;
                using (var writer = new StreamWriter(ctx.Response.OutputStream))
                {
                    await writer.WriteAsync("OK");
                }
                ctx.Response.Close();
            }
            catch (Exception ex)
            {
                try
                {
                    WriteLog("[SPK_EVT] 요청 처리 예외: " + ex);
                    ctx.Response.StatusCode = 500;
                    ctx.Response.Close();
                }
                catch { }
            }
        }
        private Task OnSpeakerFfmpegRestartAsync(string speakerId)
        {
            // 폼이 이미 종료된 경우
            if (this.IsDisposed) return Task.CompletedTask;

            // UI 스레드로 마샬링
            if (this.InvokeRequired)
            {
                var tcs = new TaskCompletionSource<bool>();
                this.BeginInvoke(new Action(async () =>
                {
                    try
                    {
                        await OnSpeakerFfmpegRestartAsync(speakerId);
                        tcs.SetResult(true);
                    }
                    catch (Exception ex)
                    {
                        tcs.SetException(ex);
                    }
                }));
                return tcs.Task;
            }

            // === 여기부터 UI 스레드 ===
            var nowUtc = DateTime.UtcNow;
            if (nowUtc - _lastSpeakerResyncUtc < SpeakerResyncCooldown)
            {
                WriteLog("[SPK_EVT] 재동기화 쿨다운 중 → 처리 스킵");
                return Task.CompletedTask;
            }
            _lastSpeakerResyncUtc = nowUtc;

            WriteLog($"[SPK_EVT] 스피커 {speakerId} ffmpeg 재시작 감지 → BGM 재동기화 시도");

            // ★ 재동기화 대상 IP 구성
            List<string> targetIPs = null;
            try
            {
                // 1) lastOnlineIPs 스냅샷이 있으면 그걸 우선 사용
                if (lastOnlineIPs != null && lastOnlineIPs.Count > 0)
                {
                    targetIPs = new List<string>(lastOnlineIPs);
                }
                else
                {
                    // 2) 없으면 그리드에서 체크된 스피커 IP 사용
                    targetIPs = dgvSpeakersStream.Rows
                        .Cast<DataGridViewRow>()
                        .Where(r => (r.Cells["Select"].Value as bool?) == true)
                        .Select(r => r.Cells["IP"].Value?.ToString())
                        .Where(ip => !string.IsNullOrWhiteSpace(ip))
                        .Distinct()
                        .ToList();
                }
            }
            catch (Exception ex)
            {
                WriteLog("[SPK_EVT] 대상 IP 구성 중 예외: " + ex.Message);
            }

            if (targetIPs == null || targetIPs.Count == 0)
            {
                WriteLog("[SPK_EVT] 재동기화 대상 스피커 없음 → 중단");
                return Task.CompletedTask;
            }

            WriteLog($"[SPK_EVT] 재동기화 대상 스피커 수: {targetIPs.Count}");

            // 실제 BGM 재동기화는 백그라운드에서 실행
            return Task.Run(async () =>
            {
                try
                {
                    // 1) 잠깐 BGM 정지
                    foreach (var ip in targetIPs)
                    {
                        SendBGMCommand(ip, "bgm_stop");
                    }

                    await Task.Delay(500); // 버퍼/프로세스 정리 여유

                    // 2) 다시 BGM 시작
                    foreach (var ip in targetIPs)
                    {
                        SendBGMCommand(ip, "bgm_start");
                    }

                    WriteLog("[SPK_EVT] BGM 재동기화 완료 (bgm_stop → bgm_start)");
                }
                catch (Exception ex)
                {
                    WriteLog("[SPK_EVT] BGM 재동기화 중 예외: " + ex.Message);
                }
            });
        }

        private void LoadFiles()
        {
            if (Directory.Exists(musicFolder))
            {
                lstMusic.Items.Clear();
                var files = Directory.GetFiles(musicFolder, "*.mp3")
                                     .Where(f => Path.GetFileName(f).ToLower() != "all_with_silence.mp3") // 혹시 있을지 몰라 추가
                                     .Select(f => Path.GetFileName(f));
                lstMusic.Items.AddRange(files.ToArray());
            }

            if (Directory.Exists(mentFolder))
            {
                lstMent.Items.Clear();
                var files = Directory.GetFiles(mentFolder, "*.mp3")
                                     .Where(f => Path.GetFileName(f).ToLower() != "all_with_silence.mp3") // 이 줄이 핵심!
                                     .Select(f => Path.GetFileName(f));
                lstMent.Items.AddRange(files.ToArray());
            }
        }

        // 🎵 Music 탭 이벤트
        private void btnAddMusic_Click(object sender, EventArgs e)
        {
            using (OpenFileDialog ofd = new OpenFileDialog())
            {
                ofd.Filter = "오디오 파일 (*.mp3;*.wav)|*.mp3;*.wav";
                ofd.Multiselect = true;

                if (ofd.ShowDialog() == DialogResult.OK)
                {
                    foreach (string file in ofd.FileNames)
                    {
                        string extension = Path.GetExtension(file).ToLower();
                        string fileNameWithoutExt = Path.GetFileNameWithoutExtension(file);
                        string destPath = Path.Combine(musicFolder, fileNameWithoutExt + ".mp3");

                        // 현재 재생 중인 파일과 이름이 같다면 업로드 차단
                        if (player.playState == WMPPlayState.wmppsPlaying &&
                            string.Equals(player.URL, destPath, StringComparison.OrdinalIgnoreCase))
                        {
                            MessageBox.Show($"현재 재생 중인 파일은 덮어쓸 수 없습니다.\n[{fileNameWithoutExt}.mp3]",
                                "업로드 차단", MessageBoxButtons.OK, MessageBoxIcon.Warning);
                            continue;
                        }

                        // 기존 파일이 존재하면 삭제 시도
                        if (File.Exists(destPath))
                        {
                            try
                            {
                                File.Delete(destPath);
                            }
                            catch (IOException)
                            {
                                MessageBox.Show($"[{fileNameWithoutExt}.mp3] 파일을 삭제할 수 없습니다.\n다른 프로세스에서 사용 중일 수 있습니다.",
                                    "삭제 실패", MessageBoxButtons.OK, MessageBoxIcon.Error);
                                continue;
                            }
                        }

                        try
                        {
                            if (extension == ".wav")
                            {
                                // ffmpeg로 wav → mp3 변환
                                ProcessStartInfo psi = new ProcessStartInfo
                                {
                                    FileName = Path.Combine(Application.StartupPath, "lib", "ffmpeg.exe"),
                                    Arguments = $"-y -i \"{file}\" -codec:a libmp3lame -qscale:a 2 \"{destPath}\"",
                                    UseShellExecute = false,
                                    CreateNoWindow = true,
                                    RedirectStandardError = true
                                };

                                using (Process proc = Process.Start(psi))
                                {
                                    proc.WaitForExit();
                                }
                            }
                            else
                            {
                                // mp3 그대로 복사
                                File.Copy(file, destPath);
                            }
                        }
                        catch (Exception ex)
                        {
                            MessageBox.Show($"파일 처리 실패: {ex.Message}",
                                "오류", MessageBoxButtons.OK, MessageBoxIcon.Error);
                        }
                    }

                    LoadFiles();
                }
            }
        }

        private void btnDeleteMusic_Click(object sender, EventArgs e)
        {
            if (lstMusic.SelectedItems.Count == 0)
            {
                MessageBox.Show("삭제할 파일을 선택하세요.");
                return;
            }

            foreach (string fileName in lstMusic.SelectedItems)
            {
                string filePath = Path.Combine(musicFolder, fileName);
                if (File.Exists(filePath))
                {
                    try
                    {
                        File.Delete(filePath);
                    }
                    catch (Exception ex)
                    {
                        MessageBox.Show($"파일 삭제 실패: {fileName}\n{ex.Message}");
                    }
                }
            }

            LoadFiles();
        }

        private void btnRefreshMusic_Click(object sender, EventArgs e)
        {
            LoadFiles();
        }

        private void btnPreviewMusic_Click(object sender, EventArgs e)
        {
            if (lstMusic.SelectedItem == null)
            {
                MessageBox.Show("미리듣기할 파일을 선택하세요.");
                return;
            }

            string fileName = lstMusic.SelectedItem.ToString();
            string filePath = Path.Combine(musicFolder, fileName);

            if (File.Exists(filePath))
            {
                player.URL = filePath;
                player.controls.play();
                lblNowPlaying.Text = "재생 중: " + fileName;

                // ProgressBar 초기화
                progressBarPreview.Value = 0;
                timerPreview.Start();
            }
        }
        private async void timerPreview_Tick(object sender, EventArgs e)
        {
            try
            {
                // 1. 재생이 끝났을 경우 (명확하게 처리)
                if (player.playState == WMPPlayState.wmppsMediaEnded)
                {
                    timerPreview.Stop();
                    progressBarPreview.Value = 0;
                    lblNowPlaying.Text = "재생 중: 없음";
                    return;
                }

                // 2. 일반적인 진행 표시
                if (player.currentMedia != null)
                {
                    double duration = player.currentMedia.duration;
                    double current = player.controls.currentPosition;

                    if (duration > 0)
                    {
                        int percent = (int)((current / duration) * 100);
                        progressBarPreview.Value = Math.Min(percent, 100);
                    }
                }

                // 🔍 스피커 상태 자동 새로고침
                if (tabControl1.SelectedTab == tabSpeakerStatus && !isCheckingStatus)
                {
                    try
                    {
                        isCheckingStatus = true;
                        await CheckStatusesSafeAsync();  // ✅ 정상 사용 가능
                    }
                    finally
                    {
                        isCheckingStatus = false;
                    }
                }
            }
            catch
            {
                // 에러 무시
            }
        }
        private void btnStopPreview_Click(object sender, EventArgs e)
        {
            player.controls.stop();
            timerPreview.Stop();
            progressBarPreview.Value = 0;
            lblNowPlaying.Text = "재생 중: 없음";
        }

        // 🎤 Ment 탭 이벤트
        private void btnAddMent_Click(object sender, EventArgs e)
        {
            MessageBox.Show("짧은 음원(안내방송 등)을 업로드하시기 바랍니다.", "안내", MessageBoxButtons.OK, MessageBoxIcon.Information);

            using (OpenFileDialog ofd = new OpenFileDialog())
            {
                ofd.Filter = "MP3/WAV 파일 (*.mp3;*.wav)|*.mp3;*.wav";
                ofd.Multiselect = true;

                if (ofd.ShowDialog() == DialogResult.OK)
                {
                    bool anyFileProcessed = false;

                    foreach (string file in ofd.FileNames)
                    {
                        string ext = Path.GetExtension(file).ToLower();
                        string fileName = Path.GetFileNameWithoutExtension(file) + ".mp3";
                        string destPath = Path.Combine(mentFolder, fileName);

                        // 현재 재생 중이면 업로드 차단
                        if (player.playState == WMPPlayState.wmppsPlaying &&
                            string.Equals(player.URL, destPath, StringComparison.OrdinalIgnoreCase))
                        {
                            MessageBox.Show($"현재 재생 중인 파일은 덮어쓸 수 없습니다.\n[{fileName}]",
                                "업로드 차단", MessageBoxButtons.OK, MessageBoxIcon.Warning);
                            continue;
                        }

                        // 기존 파일 삭제
                        if (File.Exists(destPath))
                        {
                            try
                            {
                                File.Delete(destPath);
                            }
                            catch (IOException)
                            {
                                MessageBox.Show($"[{fileName}] 파일을 삭제할 수 없습니다.\n다른 프로세스에서 사용 중일 수 있습니다.",
                                    "삭제 실패", MessageBoxButtons.OK, MessageBoxIcon.Error);
                                continue;
                            }
                        }

                        // MP3로 변환 또는 복사
                        try
                        {
                            if (ext == ".wav")
                            {
                                string ffmpegPath = Path.Combine(Application.StartupPath, "lib", "ffmpeg.exe");

                                ProcessStartInfo psi = new ProcessStartInfo
                                {
                                    FileName = ffmpegPath,
                                    Arguments = $"-y -i \"{file}\" -codec:a libmp3lame -qscale:a 2 \"{destPath}\"",
                                    UseShellExecute = false,
                                    CreateNoWindow = true,
                                    RedirectStandardError = true
                                };

                                using (Process proc = Process.Start(psi))
                                {
                                    string error = proc.StandardError.ReadToEnd();
                                    proc.WaitForExit();

                                    if (proc.ExitCode != 0)
                                    {
                                        MessageBox.Show("FFmpeg 변환 오류:\n" + error);
                                        continue;
                                    }
                                }
                            }
                            else
                            {
                                File.Copy(file, destPath, true);
                            }

                            anyFileProcessed = true;
                        }
                        catch (Exception ex)
                        {
                            MessageBox.Show($"파일 처리 중 오류 발생: {ex.Message}", "오류", MessageBoxButtons.OK, MessageBoxIcon.Error);
                        }
                    }

                    LoadFiles(); // 리스트 갱신
                                 // ✅ 자동 병합 제거됨
                }
            }
        }

        private void MergeMentFiles()
        {
            try
            {
                if (!Directory.Exists(mentFolder))
                {
                    MessageBox.Show("멘트 폴더가 존재하지 않습니다.");
                    return;
                }

                string[] mp3Files = Directory.GetFiles(mentFolder, "*.mp3")
                                             .Where(f => !f.EndsWith("all_with_silence.mp3"))
                                             .ToArray();

                if (mp3Files.Length == 0)
                {
                    MessageBox.Show("병합할 멘트 파일이 없습니다.");
                    return;
                }

                string ffmpegPath = Path.Combine(Application.StartupPath, "lib", "ffmpeg.exe");
                string silenceFile = Path.Combine(Application.StartupPath, "lib", "silence1s.mp3");

                if (!File.Exists(ffmpegPath) || !File.Exists(silenceFile))
                {
                    MessageBox.Show("ffmpeg.exe 또는 silence1s.mp3 파일이 누락되었습니다.");
                    return;
                }

                string listPath = Path.Combine(mentFolder, "merge_list.txt");
                string outputFile = Path.Combine(mentFolder, "all_with_silence.mp3");

                using (StreamWriter sw = new StreamWriter(listPath, false))
                {
                    sw.WriteLine($"file '{silenceFile}'");
                    foreach (var file in mp3Files)
                    {
                        sw.WriteLine($"file '{file}'");
                        sw.WriteLine($"file '{silenceFile}'");
                    }
                }

                // ✅ 재인코딩 방식으로 병합
                ProcessStartInfo psi = new ProcessStartInfo
                {
                    FileName = ffmpegPath,
                    Arguments = $"-y -f concat -safe 0 -i \"{listPath}\" -acodec libmp3lame -qscale:a 2 \"{outputFile}\"",
                    UseShellExecute = false,
                    CreateNoWindow = true,
                    RedirectStandardError = true
                };

                using (Process proc = Process.Start(psi))
                {
                    string error = proc.StandardError.ReadToEnd();
                    proc.WaitForExit();

                    if (proc.ExitCode != 0)
                    {
                        MessageBox.Show("FFmpeg 병합 오류:\n" + error);
                    }
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("병합 중 예외 발생: " + ex.Message);
            }
        }
        private void LoadMentFiles()
        {
            lstMent.Items.Clear();

            if (Directory.Exists(mentFolder))
            {
                var files = Directory.GetFiles(mentFolder, "*.mp3")
                                     .Where(f => Path.GetFileName(f).ToLower() != "all_with_silence.mp3")
                                     .Select(f => Path.GetFileName(f));

                lstMent.Items.AddRange(files.ToArray());
            }
        }
        private void btnDeleteMent_Click(object sender, EventArgs e)
        {
            if (lstMent.SelectedItems.Count == 0)
            {
                MessageBox.Show("삭제할 파일을 선택하세요.");
                return;
            }

            foreach (string fileName in lstMent.SelectedItems)
            {
                string filePath = Path.Combine(mentFolder, fileName);
                if (File.Exists(filePath))
                {
                    try
                    {
                        File.Delete(filePath);
                    }
                    catch (Exception ex)
                    {
                        MessageBox.Show($"파일 삭제 실패: {fileName}\n{ex.Message}");
                    }
                }
            }

            LoadFiles();
        }


        private void btnRefreshMent_Click(object sender, EventArgs e)
        {
            LoadFiles();
        }

        private void btnPreviewMent_Click(object sender, EventArgs e)
        {
            if (lstMent.SelectedItem == null)
            {
                MessageBox.Show("미리듣기할 파일을 선택하세요.");
                return;
            }

            string fileName = lstMent.SelectedItem.ToString();

            // 병합파일 재생 방지
            if (fileName.ToLower() == "all_with_silence.mp3")
            {
                MessageBox.Show("병합된 파일은 미리듣기할 수 없습니다.");
                return;
            }

            string filePath = Path.Combine(mentFolder, fileName);

            if (File.Exists(filePath))
            {
                player.URL = filePath;
                player.controls.play();
                lblNowPlaying.Text = "재생 중: " + fileName;

                // ProgressBar 및 타이머 동기화
                progressBarPreview.Value = 0;
                timerPreview.Start();
            }
        }
        private void Player_PlayStateChange(int NewState)
        {
            if ((WMPPlayState)NewState == WMPPlayState.wmppsMediaEnded)
            {
                this.Invoke((Action)(() =>
                {
                    timerPreview.Stop();
                    progressBarPreview.Value = 0;

                    if (isSequentialPlaying)
                    {
                        // 약간의 지연 후 재생 (중첩 방지)
                        Task.Delay(300).ContinueWith(_ =>
                        {
                            this.Invoke((Action)(() => PlayNextFile()));
                        });
                    }
                    else
                    {
                        lblNowPlaying.Text = "재생 중: 없음";
                    }
                }));
            }
        }
        private void btnClose_Click(object sender, EventArgs e)
        {
            this.Close();
        }

        private void trackBarVolume_Scroll(object sender, EventArgs e)
        {
            player.settings.volume = trackBarVolume.Value;
            lblVolume.Text = "볼륨: " + trackBarVolume.Value + "%";
        }

        private void lblVolume_Click(object sender, EventArgs e)
        {
            player.settings.volume = trackBarVolume.Value;
            lblVolume.Text = "볼륨: " + trackBarVolume.Value + "%";
        }
        private void btnPlaySequential_Click(object sender, EventArgs e)
        {
            ListBox listBox = null;
            string folder = null;

            // 현재 탭에 따라 폴더/리스트 결정
            if (tabInnerControl.SelectedTab == tabPageMusic)
            {
                listBox = lstMusic;
                folder = musicFolder;
            }
            else if (tabInnerControl.SelectedTab == tabPageMent)
            {
                listBox = lstMent;
                folder = mentFolder;
            }

            playQueue.Clear();

            // 🎯 전체 MP3 파일 순차 재생 (병합파일 제외)
            string[] allFiles = Directory.GetFiles(folder, "*.mp3")
                                         .Where(f => Path.GetFileName(f).ToLower() != "all_with_silence.mp3")
                                         .ToArray();

            foreach (string file in allFiles)
            {
                playQueue.Enqueue(file);
            }

            if (playQueue.Count > 0)
            {
                isSequentialPlaying = true;
                PlayNextFile();
            }
            else
            {
                MessageBox.Show("재생할 음원이 없습니다.");
            }
        }
        private void PlayNextFile()
        {
            if (playQueue.Count == 0)
            {
                isSequentialPlaying = false;
                lblNowPlaying.Text = "재생 중: 없음";
                return;
            }

            string nextFile = playQueue.Dequeue();
            player.URL = nextFile;
            lblNowPlaying.Text = "재생 중: " + Path.GetFileName(nextFile);
            progressBarPreview.Value = 0;


            player.controls.play();  // 이 줄이 핵심!
            timerPreview.Start();
        }
        private void btnDeleteMusicAll_Click(object sender, EventArgs e)
        {
            if (Directory.Exists(musicFolder))
            {
                var files = Directory.GetFiles(musicFolder, "*.mp3");
                foreach (var file in files)
                {
                    try { File.Delete(file); }
                    catch (Exception ex)
                    {
                        MessageBox.Show($"파일 삭제 실패: {Path.GetFileName(file)}\n{ex.Message}");
                    }
                }

                LoadFiles(); // 리스트 갱신
                MessageBox.Show("모든 음악 파일이 삭제되었습니다.");
                WriteLog("모든 음악 파일이 삭제되었습니다.");
            }
        }
        private void btnDeleteMentAll_Click(object sender, EventArgs e)
        {
            if (Directory.Exists(mentFolder))
            {
                var files = Directory.GetFiles(mentFolder, "*.mp3")
                                     .Where(f => Path.GetFileName(f).ToLower() != "all_with_silence.mp3");

                foreach (var file in files)
                {
                    try { File.Delete(file); }
                    catch (Exception ex)
                    {
                        MessageBox.Show($"파일 삭제 실패: {Path.GetFileName(file)}\n{ex.Message}");
                    }
                }

                LoadFiles(); // 리스트 갱신
                MessageBox.Show("모든 멘트 파일이 삭제되었습니다. (병합 파일 제외)");
                WriteLog("모든 멘트 파일이 삭제되었습니다. (병합 파일 제외)");
            }
        }

        private void btnMoveUpMent_Click(object sender, EventArgs e)
        {
            if (lstMent.SelectedItem == null || lstMent.SelectedIndex == 0)
                return;

            int index = lstMent.SelectedIndex;
            object selected = lstMent.SelectedItem;

            lstMent.Items.RemoveAt(index);
            lstMent.Items.Insert(index - 1, selected);
            lstMent.SelectedIndex = index - 1;
        }

        private void btnMoveDownMent_Click(object sender, EventArgs e)
        {
            if (lstMent.SelectedItem == null || lstMent.SelectedIndex == lstMent.Items.Count - 1)
                return;

            int index = lstMent.SelectedIndex;
            object selected = lstMent.SelectedItem;

            lstMent.Items.RemoveAt(index);
            lstMent.Items.Insert(index + 1, selected);
            lstMent.SelectedIndex = index + 1;
        }
        private void btnMergeMent_Click(object sender, EventArgs e)
        {
            if (lstMent.Items.Count == 0)
            {
                MessageBox.Show("병합할 파일이 없습니다.");
                return;
            }

            try
            {
                string listPath = Path.Combine(mentFolder, "merge_list.txt");
                string silenceFile = Path.Combine(Application.StartupPath, "lib", "silence1s.mp3");

                using (StreamWriter sw = new StreamWriter(listPath, false))
                {
                    // 시작 무음 먼저
                    sw.WriteLine($"file '{silenceFile}'");

                    foreach (var item in lstMent.Items)
                    {
                        string fileOnly = item.ToString();
                        if (fileOnly.Equals("all_with_silence.mp3", StringComparison.OrdinalIgnoreCase))
                            continue; // 병합본은 제외
                        string filePath = Path.Combine(mentFolder, fileOnly);
                        sw.WriteLine($"file '{filePath}'");
                        sw.WriteLine($"file '{silenceFile}'");
                    }
                }

                string outputFile = Path.Combine(mentFolder, "all_with_silence.mp3");
                string ffmpegPath = Path.Combine(Application.StartupPath, "lib", "ffmpeg.exe");

                ProcessStartInfo psi = new ProcessStartInfo
                {
                    FileName = ffmpegPath,
                    Arguments = $"-y -f concat -safe 0 -i \"{listPath}\" -acodec libmp3lame -qscale:a 2 \"{outputFile}\"",
                    UseShellExecute = false,
                    CreateNoWindow = true,
                    RedirectStandardError = true
                };

                using (Process proc = Process.Start(psi))
                {
                    string errorOutput = proc.StandardError.ReadToEnd();
                    proc.WaitForExit();

                    if (proc.ExitCode != 0)
                    {
                        MessageBox.Show("FFmpeg 병합 오류:\n" + errorOutput);
                    }
                    else
                    {
                        MessageBox.Show("파일 병합이 완료되었습니다.");
                    }
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("병합 중 오류 발생: " + ex.Message);
            }
        }

        private void btnPreviewMerged_Click(object sender, EventArgs e)
        {
            string mergedFilePath = Path.Combine(mentFolder, "all_with_silence.mp3");

            if (!File.Exists(mergedFilePath))
            {
                MessageBox.Show("병합된 파일이 존재하지 않습니다.", "오류", MessageBoxButtons.OK, MessageBoxIcon.Warning);
                return;
            }

            try
            {
                player.URL = mergedFilePath;
                player.controls.play();

                lblNowPlaying.Text = "재생 중: 병합된 안내 음원";
                progressBarPreview.Value = 0;
                timerPreview.Start();
            }
            catch (Exception ex)
            {
                MessageBox.Show("병합파일 재생 중 오류 발생: " + ex.Message, "오류", MessageBoxButtons.OK, MessageBoxIcon.Error);
            }
        }

        // TTS 방송 ///
        private void EnsureTtsTabAdded()
        {
            try
            {
                // 이미 존재하면 재추가하지 않음
                if (FindTabByName(tabControl1, "tabTtsBroadcast") != null)
                    return;

                var ttsTab = new TabPage
                {
                    Name = "tabTtsBroadcast",
                    Text = "TTS 방송",
                    Padding = new Padding(3),
                    UseVisualStyleBackColor = true
                };

                // (임시) 안내 라벨 — 다음 단계에서 실제 UI로 교체
                ttsTab.Controls.Add(new Label
                {
                    AutoSize = true,
                    Text = "TTS 방송 기능 준비중",
                    Location = new Point(12, 12)
                });

                // 기준 탭: 음원파일관리
                var audioTab = FindTabByName(tabControl1, "tabAudioFileManage");

                if (audioTab != null)
                {
                    int index = tabControl1.TabPages.IndexOf(audioTab);
                    tabControl1.TabPages.Insert(index + 1, ttsTab);
                }
                else
                {
                    // 예외: 기준 탭을 못 찾으면 마지막에 추가
                    tabControl1.TabPages.Add(ttsTab);
                }
            }
            catch (Exception ex)
            {
                WriteLog("[TTS] TTS 방송 탭 추가 실패: " + ex.Message);
            }
        }

        // Speaker 등록
        // 스피커 로딩

        private void LoadSpeakers()
        {
            checkedListSpeakers.Rows.Clear();
            allSpeakers.Clear();

            if (File.Exists(speakerFile))
            {
                var lines = File.ReadAllLines(speakerFile, Encoding.UTF8);
                foreach (var line in lines)
                {
                    if (string.IsNullOrWhiteSpace(line)) continue;

                    var parts = line.Split('|');
                    if (parts.Length >= 4)
                    {
                        string ip = (parts[0] ?? "").Trim();
                        string sip = (parts[1] ?? "").Trim();
                        string location = (parts[2] ?? "").Trim();
                        string group = (parts[3] ?? "").Trim();

                        // ✅ 5번째가 있으면 model 사용, 없으면 AEPEL
                        string model = (parts.Length >= 5 ? parts[4] : "AEPEL");
                        model = (model ?? "AEPEL").Trim().ToUpperInvariant();

                        // 빈 값 방지
                        if (string.IsNullOrWhiteSpace(ip) || string.IsNullOrWhiteSpace(sip) || string.IsNullOrWhiteSpace(location))
                            continue;

                        allSpeakers.Add((ip, sip, location, group, model));

                        // ✅ 그리드에도 모델까지 같이 넣기
                        // 컬럼 순서가: Select, IP, SIP, Location, Group, SpeakerModel 인 경우
                        checkedListSpeakers.Rows.Add(false, ip, sip, location, group, model);
                    }
                }
            }

            // ✅ 내부 리스트 초기화
            lock (speakerLock)
            {
                statusSpeakers = allSpeakers.Select(s => (s.ip, s.location)).ToList();
                streamSpeakers = allSpeakers.Select(s => (s.ip, s.group)).ToList();
                scheduleSpeakers = allSpeakers.Select(s => (s.ip, s.location, s.group)).ToList();
            }
        }
        // 그룹 로딩
        private void LoadGroups()
        {
            cmbGroupSelect.SelectedIndexChanged -= cmbGroupSelect_SelectedIndexChanged;

            cmbGroupSelect.Items.Clear();
            if (File.Exists("sip_groups.txt"))
            {
                var lines = File.ReadAllLines("sip_groups.txt");
                foreach (var line in lines)
                {
                    var parts = line.Split(',');
                    if (parts.Length > 1)
                        cmbGroupSelect.Items.Add(parts[0]);
                }
            }

            // ✅ 선택 없음으로 시작
            cmbGroupSelect.SelectedIndex = -1;
            cmbGroupSelect.Text = "그룹 선택";

            cmbGroupSelect.SelectedIndexChanged += cmbGroupSelect_SelectedIndexChanged;
        }

        // 저장 버튼
        private void btnSaveSpeaker_Click(object sender, EventArgs e)
        {
            string ip = txtSpeakerIP.Text.Trim();
            string sip = txtSIP.Text.Trim();
            string location = txtLocation.Text.Trim();
            string group = txtGroupName.Text.Trim();

            // ✅ 모델(저장값)
            string model = (cmbSpeakerModel.SelectedValue?.ToString() ?? "AEPEL").Trim().ToUpperInvariant();

            if (string.IsNullOrWhiteSpace(ip) || string.IsNullOrWhiteSpace(sip) || string.IsNullOrWhiteSpace(location))
            {
                MessageBox.Show("IP, SIP, 설치 장소를 입력하세요.");
                return;
            }

            // ✅ 전체 필드 기준(모델 포함)으로 동일 레코드 검사
            bool exactExists = checkedListSpeakers.Rows.Cast<DataGridViewRow>()
                .Any(r => !r.IsNewRow
                       && (r.Cells["SpeakerIPColumn"].Value?.ToString()?.Trim() ?? "") == ip
                       && (r.Cells["SIPNumColumn"].Value?.ToString()?.Trim() ?? "") == sip
                       && (r.Cells["LocationColumn"].Value?.ToString()?.Trim() ?? "") == location
                       && (r.Cells["GroupColumn"].Value?.ToString()?.Trim() ?? "") == group
                       && ((r.Cells["SpeakerModel"].Value?.ToString()?.Trim() ?? "AEPEL").ToUpperInvariant()) == model);

            if (exactExists)
            {
                MessageBox.Show("이미 동일한 스피커·그룹·모델 조합이 등록되어 있습니다.");
                return;
            }

            // ⚠️ 같은 IP가 이미 있어도 그룹이 다르면 허용
            // ✅ 컬럼 순서가: Select, IP, SIP, Location, Group, SpeakerModel 인 경우
            checkedListSpeakers.Rows.Add(false, ip, sip, location, group, model);

            SaveSpeakersAndGroups();
            LoadGroups();

            txtSpeakerIP.Clear();
            txtSIP.Clear();
            txtLocation.Clear();
            txtGroupName.Clear();
            cmbSpeakerModel.SelectedValue = "AEPEL"; // 원하면 유지

            MessageBox.Show("스피커 등록 완료!");
            WriteLog("스피커 등록 완료!");
        }

        // 삭제 버튼
        private void btnDeleteSpeaker_Click(object sender, EventArgs e)
        {
            var toDelete = checkedListSpeakers.Rows.Cast<DataGridViewRow>()
                .Where(r => !r.IsNewRow && Convert.ToBoolean(r.Cells["SelectColumn"].Value))
                .ToList();

            if (toDelete.Count == 0)
            {
                MessageBox.Show("삭제할 항목을 선택하세요.");
                return;
            }

            foreach (var row in toDelete.OrderByDescending(r => r.Index))
                checkedListSpeakers.Rows.Remove(row);

            SaveSpeakersAndGroups();
        }

        // 그룹 저장
        private void btnSaveGroup_Click(object sender, EventArgs e)
        {
            SaveSpeakersAndGroups();
            MessageBox.Show("그룹 정보가 저장되었습니다.");
            WriteLog("그룹 정보가 저장되었습니다.");
        }

        // 그룹 일괄 수정
        private void btnEditGroupName_Click(object sender, EventArgs e)
        {
            string newGroup = txtGroupName.Text.Trim();
            if (string.IsNullOrWhiteSpace(newGroup))
            {
                MessageBox.Show("그룹명을 입력하세요.");
                return;
            }

            bool changed = false;
            foreach (DataGridViewRow row in checkedListSpeakers.Rows)
            {
                if (row.IsNewRow) continue;
                if (Convert.ToBoolean(row.Cells["SelectColumn"].Value))
                {
                    row.Cells["GroupColumn"].Value = newGroup;
                    changed = true;
                }
            }

            if (changed)
            {
                SaveSpeakersAndGroups();
                LoadGroups();
                MessageBox.Show("그룹명이 일괄 변경되었습니다.");
                WriteLog("그룹명이 일괄 변경되었습니다.");
            }
            else
            {
                MessageBox.Show("변경할 항목을 선택하세요.");
            }
        }

        // 파일 저장
        private void SaveSpeakersAndGroups()
        {
            var lines = new List<string>();
            foreach (DataGridViewRow row in checkedListSpeakers.Rows)
            {
                if (row.IsNewRow) continue;

                string ip = row.Cells["SpeakerIPColumn"].Value?.ToString()?.Trim();
                string sip = row.Cells["SIPNumColumn"].Value?.ToString()?.Trim();
                string loc = row.Cells["LocationColumn"].Value?.ToString()?.Trim();
                string group = row.Cells["GroupColumn"].Value?.ToString()?.Trim();

                // ✅ 모델(없으면 기본 AEPEL)
                string model = (row.Cells["SpeakerModel"].Value?.ToString()?.Trim() ?? "AEPEL")
                    .ToUpperInvariant();

                if (string.IsNullOrWhiteSpace(ip) || string.IsNullOrWhiteSpace(sip) || string.IsNullOrWhiteSpace(loc))
                    continue;

                // ✅ 5필드로 저장
                lines.Add($"{ip}|{sip}|{loc}|{group}|{model}");
            }
            File.WriteAllLines(speakerFile, lines, Encoding.UTF8);

            // ✅ 그룹 저장: 기존대로(그룹별 중복 IP 제거) - 모델은 그룹파일에 굳이 넣지 않아도 됨
            var groupDict = new Dictionary<string, HashSet<string>>(StringComparer.OrdinalIgnoreCase);
            foreach (var line in lines)
            {
                var parts = line.Split('|');
                if (parts.Length >= 4)
                {
                    string g = (parts[3] ?? "").Trim();
                    string gip = (parts[0] ?? "").Trim();
                    if (!string.IsNullOrEmpty(g) && !string.IsNullOrEmpty(gip))
                    {
                        if (!groupDict.TryGetValue(g, out var set))
                        {
                            set = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
                            groupDict[g] = set;
                        }
                        set.Add(gip);
                    }
                }
            }

            using (var writer = new StreamWriter("sip_groups.txt", false, Encoding.UTF8))
            {
                foreach (var kvp in groupDict)
                    writer.WriteLine($"{kvp.Key},{string.Join(",", kvp.Value)}");
            }

            // ✅ 내부 리스트 갱신(모델 포함) — 아래 튜플 구조만 바꿔주면 됨
            lock (speakerLock)
            {
                allSpeakers = lines
                    .Select(l =>
                    {
                        var p = l.Split('|');

                        string ip = (p.Length > 0 ? p[0] : "").Trim();
                        string sip = (p.Length > 1 ? p[1] : "").Trim();
                        string loc = (p.Length > 2 ? p[2] : "").Trim();
                        string grp = (p.Length > 3 ? p[3] : "").Trim();

                        // ✅ 기존 4필드 파일도 호환: model 없으면 AEPEL
                        string model = (p.Length >= 5 ? p[4] : "AEPEL").Trim().ToUpperInvariant();

                        return (ip: ip, sip: sip, location: loc, group: grp, model: model);
                    })
                    .ToList();

                statusSpeakers = allSpeakers.Select(s => (s.ip, s.location)).ToList();
                streamSpeakers = allSpeakers.Select(s => (s.ip, s.group)).ToList();
                scheduleSpeakers = allSpeakers.Select(s => (s.ip, s.location, s.group)).ToList();
            }
        }
        private void cmbGroupSelect_SelectedIndexChanged(object sender, EventArgs e)
        {
            string selectedGroup = cmbGroupSelect.SelectedItem?.ToString()?.Trim();
            if (string.IsNullOrWhiteSpace(selectedGroup))
                return;

            foreach (DataGridViewRow row in checkedListSpeakers.Rows)
            {
                if (row.IsNewRow) continue;

                string rowGroup = row.Cells["GroupColumn"].Value?.ToString()?.Trim();
                row.Cells["SelectColumn"].Value = (rowGroup == selectedGroup);
            }
        }
        private void LoadMentSoundFiles()
        {
            lstSoundFiles.Items.Clear();

            if (Directory.Exists(mentFolder))
            {
                var files = Directory.GetFiles(mentFolder, "*.mp3")
                    .Where(f => Path.GetFileName(f).ToLower() != "all_with_silence.mp3");

                foreach (var file in files)
                    lstSoundFiles.Items.Add(Path.GetFileName(file));  // 파일명만 표시
            }
        }
        private async Task<(List<string> onlineIPs, List<string> offlineIPs)> GetOnlineCheckedSpeakerIPsAsync()
        {
            var onlineIPs = new List<string>();
            var offlineIPs = new List<string>();

            var tasks = new List<Task>();

            foreach (DataGridViewRow row in checkedListSpeakers.Rows)
            {
                if (row.IsNewRow) continue;

                bool isChecked = Convert.ToBoolean(row.Cells["SelectColumn"].Value);
                if (!isChecked) continue;

                string ip = row.Cells["SpeakerIPColumn"].Value?.ToString();
                if (string.IsNullOrWhiteSpace(ip)) continue;

                var task = Task.Run(() =>
                {
                    if (TryConnectWithTimeout(ip, 8787, 800))  // ⏱ 더 빠른 응답 유도
                    {
                        lock (onlineIPs) onlineIPs.Add(ip);
                    }
                    else
                    {
                        lock (offlineIPs) offlineIPs.Add(ip);
                    }
                });

                tasks.Add(task);
            }

            await Task.WhenAll(tasks);
            return (onlineIPs, offlineIPs);
        }

        private async void btnSendSound_Click(object sender, EventArgs e)
        {
            var (selectedIPs, offlineIPs) = await GetOnlineCheckedSpeakerIPsAsync();

            // ✅ 오프라인 체크 해제
            foreach (DataGridViewRow row in checkedListSpeakers.Rows)
            {
                if (row.IsNewRow) continue;
                string ip = row.Cells["SpeakerIPColumn"].Value?.ToString();
                if (offlineIPs.Contains(ip))
                    row.Cells["SelectColumn"].Value = false;
            }

            // ✅ 온라인 대상만 전송
            if (selectedIPs.Count == 0 || lstSoundFiles.SelectedItem == null)
            {
                MessageBox.Show("스피커와 음원 파일을 모두 선택하세요.");
                return;
            }

            string fileName = lstSoundFiles.SelectedItem.ToString();
            string fullFilePath = Path.Combine(mentFolder, fileName);

            if (!File.Exists(fullFilePath))
            {
                MessageBox.Show("파일이 존재하지 않습니다:\n" + fullFilePath);
                return;
            }

            var failed = new List<string>();
            var success = new List<string>();

            foreach (string ip in selectedIPs)
            {
                bool uploaded = await Task.Run(() => UploadFileToSpeaker(ip, fullFilePath));
                if (uploaded) success.Add(ip);
                else failed.Add(ip);
            }

            foreach (string ip in success)
            {
                WriteLog($"[재생 명령 전송 전] {ip} - {fileName}");
                SendBroadcastCommand(ip, fileName);
                WriteLog($"[재생 명령 전송 완료] {ip}");
            }

            if (failed.Any())
                MessageBox.Show("전송 실패:\n" + string.Join("\n", failed));
            else
                MessageBox.Show("모든 스피커 전송 및 재생 완료!");

            if (offlineIPs.Any())
            {
                MessageBox.Show("다음 스피커는 오프라인 상태로 전송에서 제외되었습니다:\n" + string.Join("\n", offlineIPs));
                WriteLog("[전송 제외] 오프라인 스피커: " + string.Join(", ", offlineIPs));
            }

            WriteLog("전송 성공: " + string.Join(", ", success));
            if (failed.Any())
                WriteLog("전송 실패: " + string.Join(", ", failed));
        }

        private List<string> GetCheckedSpeakerIPs()
        {
            var list = new List<string>();

            foreach (DataGridViewRow row in checkedListSpeakers.Rows)
            {
                if (row.IsNewRow) continue;

                bool isChecked = row.Cells["SelectColumn"].Value as bool? ?? false;
                if (!isChecked) continue;

                string ip = row.Cells["SpeakerIPColumn"].Value?.ToString();
                if (!string.IsNullOrWhiteSpace(ip))
                    list.Add(ip);
            }

            return list;
        }
        private bool UploadFileToSpeaker(string ip, string localFilePath)
        {
            const int timeoutMs = 1500;

            if (!TryConnectWithTimeout(ip, 8787, timeoutMs))
            {
                Debug.WriteLine($"[Timeout] {ip} 스피커에 연결 실패");
                return false;
            }

            try
            {
                string fileName = Path.GetFileName(localFilePath);
                byte[] fileData = File.ReadAllBytes(localFilePath);
                byte[] header = Encoding.UTF8.GetBytes(fileName + "\n");
                byte[] sendData = new byte[header.Length + fileData.Length];

                Buffer.BlockCopy(header, 0, sendData, 0, header.Length);
                Buffer.BlockCopy(fileData, 0, sendData, header.Length, fileData.Length);

                using (TcpClient client = new TcpClient(ip, 8787))
                using (NetworkStream stream = client.GetStream())
                {
                    stream.Write(sendData, 0, sendData.Length);
                }

                return true;
            }
            catch (Exception ex)
            {
                string errorMsg = $"[전송 오류] {ip} → {ex.Message}\n{ex.StackTrace}";
                Debug.WriteLine(errorMsg);
                WriteLog(errorMsg);
                return false;
            }
        }
        private bool SendBroadcastCommand(string ip, string fileName)
        {
            try
            {
                string encodedFile = Uri.EscapeDataString(fileName);
                string message = $"mp3_play<HSK>{encodedFile}";
                byte[] data = Encoding.UTF8.GetBytes(message);

                using (var client = new TcpClient())
                {
                    client.NoDelay = true;
                    client.SendTimeout = 2000;
                    client.ReceiveTimeout = 2000;

                    // Connect timeout 직접 구현(블로킹 방지)
                    var ar = client.BeginConnect(ip, 8899, null, null);
                    if (!ar.AsyncWaitHandle.WaitOne(2000))
                    {
                        try { client.Close(); } catch { }
                        LogTTS($"[CMD FAIL] {ip}: connect timeout");
                        return false;
                    }
                    client.EndConnect(ar);

                    using (var stream = client.GetStream())
                    {
                        stream.Write(data, 0, data.Length);
                        stream.Flush(); // ✅ 명시 Flush
                    }
                }

                LogTTS($"[CMD OK] {ip}: {message}");
                return true;
            }
            catch (Exception ex)
            {
                LogTTS($"[CMD FAIL] {ip}: {ex.Message}");
                return false;
            }
        }

        private bool TryConnectWithTimeout(string ip, int port, int timeoutMs)
        {
            try
            {
                using (TcpClient client = new TcpClient())
                {
                    IAsyncResult ar = client.BeginConnect(ip, port, null, null);
                    bool success = ar.AsyncWaitHandle.WaitOne(timeoutMs);
                    if (!success) { try { client.Close(); } catch { } return false; }
                    try { client.EndConnect(ar); } catch { return false; }
                    return client.Connected;
                }
            }
            catch { return false; }
        }

        private void button3_Click(object sender, EventArgs e)
        {
            var selectedIPs = GetCheckedSpeakerIPs();
            if (selectedIPs.Count == 0)
            {
                MessageBox.Show("정지할 스피커를 체크하세요.");
                return;
            }

            foreach (string ip in selectedIPs)
            {
                try
                {
                    using (var client = new TcpClient())
                    {
                        client.Connect(ip, 39999); // 포트 39999에 stop 명령 전송
                        byte[] data = Encoding.UTF8.GetBytes("stop_play");
                        using (var stream = client.GetStream())
                        {
                            stream.Write(data, 0, data.Length);
                        }
                    }
                }
                catch (Exception ex)
                {
                    Debug.WriteLine($"[StopPlayback] {ip}: {ex.Message}");
                }
            }

            MessageBox.Show("선택한 스피커에 중지 명령 전송 완료");
            WriteLog("선택한 스피커에 중지 명령 전송 완료");
        }

        private async Task<string> GetSpeakerStatusSafeAsync(string ip)
        {
            await semaphore.WaitAsync();
            try
            {
                return await Task.Run(() => GetSpeakerStatus(ip));
            }
            finally
            {
                semaphore.Release();
            }
        }

        private async Task<string> GetSpeakerVolumeSafeAsync(string ip)
        {
            await semaphore.WaitAsync();
            try
            {
                return await Task.Run(() => GetSpeakerVolume(ip));
            }
            finally
            {
                semaphore.Release();
            }
        }
        private void FormMain_Shown(object sender, EventArgs e)
        {
            LoadSpeakers();

            timerClock.Interval = 1000;
            timerClock.Tick -= timerClock_Tick;
            timerClock.Tick += timerClock_Tick;
            timerClock.Start();

            LoadStartConfig();

            tabControl1_SelectedIndexChanged(tabControl1, EventArgs.Empty);

            // ✅ 최초 실행에서만 콤보가 0으로 잡히는 현상 방지 (가장 확실)
            BeginInvoke(new Action(() =>
            {
                cmbGroupSelectSchedule.SelectedIndex = -1;
                cmbGroupSelectSchedule.Text = "";
            }));
        }
        private void LoadSpeakersForStatus()
        {
            var speakerFile = Path.Combine(Application.StartupPath, "speakers.txt");

            dgvStatus.Invoke((MethodInvoker)(() =>
            {
                InitializeStatusGrid(); // ✅ 먼저 컬럼 구성
                dgvStatus.Rows.Clear(); // ✅ 이후 행 초기화
            }));

            var tempList = new List<(string ip, string location)>();

            if (File.Exists(speakerFile))
            {
                var lines = File.ReadAllLines(speakerFile, Encoding.UTF8);
                foreach (var line in lines)
                {
                    var parts = line.Split('|');
                    if (parts.Length >= 3)
                    {
                        string ip = parts[0];
                        string location = parts[2];

                        tempList.Add((ip, location));
                    }
                }
            }

            lock (speakerLock)
            {
                allSpeakers = tempList
                    .Select(s => (
                        ip: s.ip,
                        sip: "0000",
                        location: s.location,
                        group: "default",
                        model: "AEPEL"   // ✅ 추가
                    ))
                    .ToList();

                statusSpeakers = allSpeakers
                    .Select(s => (s.ip, s.location))
                    .ToList();

                streamSpeakers = allSpeakers
                    .Select(s => (s.ip, s.group))
                    .ToList();

                scheduleSpeakers = allSpeakers
                    .Select(s => (s.ip, s.location, s.group))
                    .ToList();
            }

            dgvStatus.Invoke((MethodInvoker)(() =>
            {
                foreach (var spk in tempList)
                {
                    dgvStatus.Rows.Add(spk.ip, spk.location, "확인 중...", "...");
                }
            }));
        }
        private async Task CheckStatusesSafeAsync()
        {
            if (!File.Exists("speakers.txt")) return;

            var lines = File.ReadAllLines("speakers.txt", Encoding.UTF8);
            var tasks = new List<Task<(string ip, string location, string status, string volume)>>();

            foreach (var line in lines)
            {
                var parts = line.Split('|');
                if (parts.Length >= 4)
                {
                    string ip = parts[0];
                    string location = parts[2];

                    // 병렬 처리: 상태 및 볼륨 가져오기
                    var task = Task.Run(async () =>
                    {
                        string status = await GetSpeakerStatusSafeAsync(ip);
                        string volume = await GetSpeakerVolumeSafeAsync(ip);
                        return (ip, location, status, volume);
                    });

                    tasks.Add(task);
                }
            }

            var results = await Task.WhenAll(tasks);  // 병렬 수행 후 결과 수집

            this.Invoke((MethodInvoker)(() =>
            {
                dgvStatus.Rows.Clear();  // UI는 마지막에 한 번만 조작
                foreach (var result in results)
                {
                    string ip = NormalizeIP(result.ip);
                    speakerStatusMap[ip] = result.status;

                    dgvStatus.Rows.Add(ip, result.location, result.status, result.volume);
                }
            }));
        }

        private string GetSpeakerStatus(string ip)
        {
            try
            {
                using (TcpClient client = new TcpClient())
                {
                    var result = client.BeginConnect(ip, 39999, null, null);
                    bool success = result.AsyncWaitHandle.WaitOne(TimeSpan.FromSeconds(2));

                    if (!success)
                        return "NO RESPONSE";

                    using (NetworkStream stream = client.GetStream())
                    {
                        byte[] data = Encoding.UTF8.GetBytes("status\n");
                        stream.Write(data, 0, data.Length);
                        stream.Flush();

                        byte[] buffer = new byte[64];
                        stream.ReadTimeout = 2000;
                        int bytesRead = stream.Read(buffer, 0, buffer.Length);
                        if (bytesRead <= 0) return "NO RESPONSE";
                        string response = Encoding.UTF8.GetString(buffer, 0, bytesRead).Trim();

                        if (response.Contains("RUN")) return "RUN";
                        if (response.Contains("STOP")) return "STOP";
                        return "UNKNOWN";
                    }
                }
            }
            catch
            {
                return "ERROR";
            }
        }
        private void SaveSelectedVolumeIPs()
        {
            selectedVolumeIPs.Clear();
            foreach (DataGridViewRow row in dgvVolumeTargets.Rows)
            {
                if (Convert.ToBoolean(row.Cells["SelectVolumeColumn"].Value))
                {
                    string ip = row.Cells["VolumeIPColumn"].Value?.ToString();
                    if (!string.IsNullOrWhiteSpace(ip))
                        selectedVolumeIPs.Add(ip);
                }
            }
        }

        private void RestoreSelectedVolumeIPs()
        {
            foreach (DataGridViewRow row in dgvVolumeTargets.Rows)
            {
                string ip = row.Cells["VolumeIPColumn"].Value?.ToString();
                if (!string.IsNullOrWhiteSpace(ip) && selectedVolumeIPs.Contains(ip))
                {
                    row.Cells["SelectVolumeColumn"].Value = true;
                }
            }
        }
        private string GetSpeakerVolume(string ip)
        {
            try
            {
                using (TcpClient client = new TcpClient())
                {
                    var result = client.BeginConnect(ip, 39999, null, null);
                    bool success = result.AsyncWaitHandle.WaitOne(TimeSpan.FromSeconds(2));

                    if (!success)
                        return "NO RESPONSE";

                    using (NetworkStream stream = client.GetStream())
                    {
                        byte[] data = Encoding.UTF8.GetBytes("get_volume\n");
                        stream.Write(data, 0, data.Length);
                        stream.Flush();

                        byte[] buffer = new byte[64];
                        stream.ReadTimeout = 2000;
                        int bytesRead = stream.Read(buffer, 0, buffer.Length);
                        string response = Encoding.UTF8.GetString(buffer, 0, bytesRead).Trim();

                        if (int.TryParse(response, out int vol))
                            return vol + "%";
                        else
                            return "UNKNOWN";
                    }
                }
            }
            catch
            {
                return "ERROR";
            }
        }

        private void trackBarSetVolume_Scroll(object sender, EventArgs e)
        {
            int percent = trackBarSetVolume.Value * 5; // 0~20 → 0~100%
            lblSetVolumeValue.Text = $"볼륨: {percent}%";
        }

        private void btnApplyVolume_Click(object sender, EventArgs e)
        {
            int percent = trackBarSetVolume.Value * 5;
            int deviceValue = (int)Math.Round(31 * percent / 100.0);

            var targetIPs = new List<string>();
            var allCheckedIPs = new List<string>();

            // ✅ 디버그용: 상태맵 전체 출력
            Debug.WriteLine("현재 speakerStatusMap 상태 목록:");
            foreach (var kv in speakerStatusMap)
            {
                Debug.WriteLine($"IP: {kv.Key}, 상태: {kv.Value}");
            }

            foreach (DataGridViewRow row in dgvVolumeTargets.Rows)
            {
                bool isChecked = Convert.ToBoolean(row.Cells["SelectVolumeColumn"].Value);
                string ipRaw = row.Cells["VolumeIPColumn"].Value?.ToString();
                string ip = NormalizeIP(ipRaw);  // ✅ 포트 제거 및 표준화

                if (isChecked && !string.IsNullOrWhiteSpace(ip))
                {
                    allCheckedIPs.Add(ipRaw); // 원래 IP도 함께 저장

                    if (speakerStatusMap.TryGetValue(ip, out string status))
                    {
                        string normalizedStatus = status?.Trim().ToUpperInvariant();

                        if (normalizedStatus == "RUN" || normalizedStatus == "STOP")
                        {
                            targetIPs.Add(ipRaw);
                            Debug.WriteLine($"✔ {ipRaw} → 상태: {normalizedStatus} → 전송 대상");
                        }
                        else
                        {
                            WriteLog($"[{ipRaw}] 스피커 상태가 '{normalizedStatus}' 이므로 볼륨 명령 제외됨.");
                            Debug.WriteLine($"✖ {ipRaw} → 상태: {normalizedStatus} → 제외됨");
                        }
                    }
                    else
                    {
                        WriteLog($"[{ipRaw}] 상태 정보가 speakerStatusMap에 존재하지 않음 → 제외됨.");
                        Debug.WriteLine($"✖ {ipRaw} → 상태 정보 없음 → 제외됨");
                    }
                }
            }

            // ✅ 상태맵 비어있을 때
            if (speakerStatusMap.Count == 0)
            {
                MessageBox.Show("스피커 상태 정보가 없습니다.\n먼저 '스피커 상태' 탭에서 상태를 불러오세요.");
                return;
            }

            // ✅ 스피커는 선택했지만 온라인 상태(RUN 또는 STOP)가 없음
            if (allCheckedIPs.Count > 0 && targetIPs.Count == 0)
            {
                MessageBox.Show("선택한 스피커는 있으나 온라인 상태(RUN 또는 STOP)인 장비가 없습니다.");
                return;
            }

            // ✅ 아무것도 선택하지 않은 경우
            if (allCheckedIPs.Count == 0)
            {
                MessageBox.Show("볼륨을 설정할 스피커를 선택하세요.");
                return;
            }

            // ✅ 볼륨 명령 전송
            foreach (string ip in targetIPs)
            {
                Task.Run(() => SendVolumeCommand(ip, deviceValue, percent));
            }

            MessageBox.Show($"온라인 스피커 {targetIPs.Count}대에 볼륨 {percent}%로 설정 명령이 전송되었습니다.");
            WriteLog($"볼륨 {percent}%로 설정 명령이 전송되었습니다. (전송 대상 수: {targetIPs.Count})");
        }

        private string NormalizeIP(string ip)
        {
            if (string.IsNullOrWhiteSpace(ip)) return "";
            return ip.Split(':')[0].Trim();
        }
        private void SendVolumeCommand(string ip, int volumeStep, int displayPercent)
        {
            try
            {
                using (TcpClient client = new TcpClient())
                {
                    client.Connect(ip, 39999);
                    using (NetworkStream stream = client.GetStream())
                    using (var writer = new StreamWriter(stream, Encoding.UTF8) { AutoFlush = true })
                    {
                        string amixerCmd = $"amixer -c0 set 'Lineout volume control' {volumeStep}";
                        string echoCmd = $"echo {displayPercent} > /var/www/html/dv.txt";

                        writer.WriteLine(amixerCmd);
                        Thread.Sleep(100);
                        writer.WriteLine(echoCmd);
                    }
                }
            }
            catch (Exception ex)
            {
                // MessageBox.Show($"[{ip}] 볼륨 전송 오류: {ex.Message}");
                WriteLog($"[{ip}] 볼륨 전송 오류: {ex.Message}");
            }
        }
        private void SendSetVolumeCommand(string ip, int volume)
        {
            try
            {
                using (TcpClient client = new TcpClient())
                {
                    client.Connect(ip, 39999);
                    using (NetworkStream stream = client.GetStream())
                    using (var writer = new StreamWriter(stream, Encoding.UTF8) { AutoFlush = true })
                    {
                        // 🎯 실제 볼륨 수치 계산 (예: 0~100%)
                        int volumeStep = volume;
                        int displayPercent = volume; // 그대로 사용 가능하거나 별도 변환 가능

                        // 볼륨 설정 명령
                        string amixerCmd = $"amixer -c0 set 'Lineout volume control' {volumeStep}";
                        string echoCmd = $"echo {displayPercent} > /var/www/html/dv.txt";

                        writer.WriteLine(amixerCmd);
                        Thread.Sleep(100); // 잠깐 대기 후 다음 명령
                        writer.WriteLine(echoCmd);
                    }
                }
            }
            catch (Exception ex)
            {
                Debug.WriteLine($"[{ip}] 볼륨 전송 오류: {ex.Message}");
            }
        }

        private void cmbGroupVolume_SelectedIndexChanged(object sender, EventArgs e)
        {
            //            if (_loadingVolumeUi) return;
            //            string selectedGroup = cmbGroupVolume.SelectedItem?.ToString();
            //            if (string.IsNullOrWhiteSpace(selectedGroup)) return;
            //
            //            dgvVolumeTargets.Rows.Clear();
            //
            //            if (File.Exists("speakers.txt"))
            //            {
            //                var lines = File.ReadAllLines("speakers.txt", Encoding.UTF8);
            //                foreach (var line in lines)
            //                {
            //                    var parts = line.Split('|');
            //                    if (parts.Length >= 4 && parts[3] == selectedGroup)
            //                    {
            //                        dgvVolumeTargets.Rows.Add(true, parts[0], parts[2], parts[3]); // ✅ 실제 group도 넣기
            //                    }
            //                }
            //            }
        }

        private void chkSelectAllVolume_CheckedChanged(object sender, EventArgs e)
        {
            if (_suppressVolumeEvents) return;
            if (isHandlingCheckAll) return;
            if (isHandlingCheckAll) return;
            isHandlingCheckAll = true;

            bool isChecked = chkSelectAllVolume.Checked;

            foreach (DataGridViewRow row in dgvVolumeTargets.Rows)
            {
                if (!row.IsNewRow)
                {
                    string ip = row.Cells["VolumeIPColumn"].Value?.ToString();
                    if (!string.IsNullOrWhiteSpace(ip))
                    {
                        row.Cells["SelectVolumeColumn"].Value = isChecked;
                        if (isChecked)
                            selectedVolumeIPs.Add(ip);
                        else
                            selectedVolumeIPs.Remove(ip);
                    }
                }
            }

            isHandlingCheckAll = false;
        }
        private void InitializeVolumeGrid()
        {
            // ✅ 이벤트 중복 연결 방지
            dgvVolumeTargets.CellValueChanged -= dgvVolumeTargets_CellValueChanged;
            dgvVolumeTargets.CurrentCellDirtyStateChanged -= dgvVolumeTargets_CurrentCellDirtyStateChanged;
            chkSelectAllVolume.CheckedChanged -= chkSelectAllVolume_CheckedChanged;

            dgvVolumeTargets.Columns.Clear();

            // ✅ 늘어남/좌측 빈칸 방지
            dgvVolumeTargets.AutoSizeColumnsMode = DataGridViewAutoSizeColumnsMode.None;
            dgvVolumeTargets.RowHeadersVisible = false;
            dgvVolumeTargets.AllowUserToAddRows = false;

            dgvVolumeTargets.Columns.Add(new DataGridViewCheckBoxColumn()
            {
                Name = "SelectVolumeColumn",
                HeaderText = "선택",
                Width = 50,
                AutoSizeMode = DataGridViewAutoSizeColumnMode.None,
                Resizable = DataGridViewTriState.False
            });

            dgvVolumeTargets.Columns.Add(new DataGridViewTextBoxColumn()
            {
                Name = "VolumeIPColumn",
                HeaderText = "IP Address",
                Width = 120,
                ReadOnly = true,
                AutoSizeMode = DataGridViewAutoSizeColumnMode.None
            });

            dgvVolumeTargets.Columns.Add(new DataGridViewTextBoxColumn()
            {
                Name = "VolumeLocationColumn",
                HeaderText = "설치 장소",
                Width = 140,
                ReadOnly = true,
                AutoSizeMode = DataGridViewAutoSizeColumnMode.None
            });

            dgvVolumeTargets.Columns.Add(new DataGridViewTextBoxColumn()
            {
                Name = "VolumeGroupColumn",
                HeaderText = "그룹",
                Width = 80,
                ReadOnly = true,
                AutoSizeMode = DataGridViewAutoSizeColumnMode.None
            });

            dgvVolumeTargets.AutoGenerateColumns = false;
            dgvVolumeTargets.CellValueChanged += dgvVolumeTargets_CellValueChanged;
            dgvVolumeTargets.CurrentCellDirtyStateChanged += dgvVolumeTargets_CurrentCellDirtyStateChanged;
            chkSelectAllVolume.CheckedChanged += chkSelectAllVolume_CheckedChanged;
        }
        private bool _loadingVolumeUi = false;
        private bool _volumeGroupsInitialized = false;
        private void LoadGroupsForVolume()
        {
            WriteLog("[VOLUME] LoadGroupsForVolume called\n" + Environment.StackTrace);
            {
                if (_volumeGroupsInitialized) return;  // ✅ 재호출 방지

                _loadingVolumeUi = true;
                try
                {
                    cmbGroupVolume.Items.Clear();
                    if (!File.Exists(speakerFile)) return;

                    var groups = new HashSet<string>();
                    var lines = File.ReadAllLines(speakerFile, Encoding.UTF8);

                    foreach (var line in lines)
                    {
                        var parts = line.Split('|');
                        if (parts.Length >= 4)
                        {
                            string group = (parts[3] ?? "").Trim();
                            if (!string.IsNullOrWhiteSpace(group))
                                groups.Add(group);
                        }
                    }

                    cmbGroupVolume.Items.Add("전체");
                    foreach (var g in groups.OrderBy(x => x))
                        cmbGroupVolume.Items.Add(g);

                    cmbGroupVolume.SelectedIndex = 0; // 최초 1회만
                    _volumeGroupsInitialized = true;
                }
                finally
                {
                    _loadingVolumeUi = false;
                }
            }
        }


        private void LoadSpeakersForVolume()
        {
            if (!File.Exists(speakerFile)) return;

            dgvVolumeTargets.Rows.Clear();

            var lines = File.ReadAllLines(speakerFile, Encoding.UTF8);
            foreach (var line in lines)
            {
                var parts = line.Split('|');
                if (parts.Length >= 4)
                {
                    string ip = (parts[0] ?? "").Trim();
                    string location = (parts[2] ?? "").Trim();
                    string group = (parts[3] ?? "").Trim();

                    bool isSelected = selectedVolumeIPs.Contains(ip);
                    dgvVolumeTargets.Rows.Add(isSelected, ip, location, group);
                }
            }

            UpdateSelectAllCheckboxState();
        }
        private void cmbGroupVolume_SelectionChangeCommitted(object sender, EventArgs e)
        {
            if (_loadingVolumeUi) return;

            string selectedGroup = cmbGroupVolume.SelectedItem?.ToString()?.Trim();
            if (string.IsNullOrWhiteSpace(selectedGroup)) return;

            _suppressVolumeEvents = true;
            isHandlingCheckAll = true;
            try
            {
                selectedVolumeIPs.Clear();

                foreach (DataGridViewRow row in dgvVolumeTargets.Rows)
                {
                    if (row.IsNewRow) continue;

                    string rowGroup = row.Cells["VolumeGroupColumn"].Value?.ToString()?.Trim();
                    string ip = row.Cells["VolumeIPColumn"].Value?.ToString()?.Trim();
                    if (string.IsNullOrWhiteSpace(ip)) continue;

                    bool shouldCheck =
                        (selectedGroup == "전체") ||
                        string.Equals(rowGroup, selectedGroup, StringComparison.OrdinalIgnoreCase);

                    row.Cells["SelectVolumeColumn"].Value = shouldCheck;
                    if (shouldCheck) selectedVolumeIPs.Add(ip);
                }
            }
            finally
            {
                isHandlingCheckAll = false;
                _suppressVolumeEvents = false;
            }

            UpdateSelectAllCheckboxState();
        }
        private void dgvVolumeTargets_CellValueChanged(object sender, DataGridViewCellEventArgs e)
        {
            if (isHandlingCheckAll) return;  // ✅ 그룹체크/전체체크 등 프로그램 변경은 무시

            if (e.RowIndex < 0) return;
            if (e.ColumnIndex == dgvVolumeTargets.Columns["SelectVolumeColumn"].Index)
            {
                var row = dgvVolumeTargets.Rows[e.RowIndex];
                string ip = row.Cells["VolumeIPColumn"].Value?.ToString()?.Trim();
                bool isChecked = Convert.ToBoolean(row.Cells["SelectVolumeColumn"].Value);

                if (!string.IsNullOrWhiteSpace(ip))
                {
                    if (isChecked) selectedVolumeIPs.Add(ip);
                    else selectedVolumeIPs.Remove(ip);
                }

                UpdateSelectAllCheckboxState();
            }
        }
        private void UpdateSelectAllCheckboxState()
        {
            if (isHandlingCheckAll) return;

            bool allChecked = dgvVolumeTargets.Rows
                .Cast<DataGridViewRow>()
                .Where(r => !r.IsNewRow)
                .All(r => Convert.ToBoolean(r.Cells["SelectVolumeColumn"].Value));

            chkSelectAllVolume.CheckedChanged -= chkSelectAllVolume_CheckedChanged;
            chkSelectAllVolume.Checked = allChecked;
            chkSelectAllVolume.CheckedChanged += chkSelectAllVolume_CheckedChanged;
        }

        private void dgvVolumeTargets_CurrentCellDirtyStateChanged(object sender, EventArgs e)
        {
            if (dgvVolumeTargets.IsCurrentCellDirty)
                dgvVolumeTargets.CommitEdit(DataGridViewDataErrorContexts.Commit);
        }


        // USB 자동인식
        private void timerUSB_Tick(object sender, EventArgs e)
        {
            var currentDrives = DriveInfo.GetDrives()
                .Where(d => d.DriveType == DriveType.Removable && d.IsReady)
                .Select(d => d.RootDirectory.FullName).ToList();

            var newDrives = currentDrives.Except(knownDrives).ToList();

            if (newDrives.Any())
            {
                string usbPath = newDrives.First(); // 첫 번째 감지된 USB
                HandleUSBInserted(usbPath);
            }

            knownDrives = currentDrives;
        }
        private void HandleUSBInserted(string usbPath)
        {
            string[] mp3Files = Directory.GetFiles(usbPath, "*.mp3", SearchOption.AllDirectories);

            if (mp3Files.Length == 0)
            {
                WriteLog($"USB 삽입됨 - MP3 파일 없음: {usbPath}");
                return;
            }

            string targetFolder;
            ListBox targetList;

            // 현재 선택된 탭에 따라 대상 폴더 결정
            if (tabInnerControl.SelectedTab == tabPageMusic)
            {
                targetFolder = musicFolder;
                targetList = lstMusic;
                WriteLog($"USB 복사 대상: 음악 폴더 선택됨 (총 {mp3Files.Length}개 감지됨)");
            }
            else if (tabInnerControl.SelectedTab == tabPageMent)
            {
                targetFolder = mentFolder;
                targetList = lstMent;
                WriteLog($"USB 복사 대상: 멘트 폴더 선택됨 (총 {mp3Files.Length}개 감지됨)");
            }
            else
            {
                WriteLog("USB 복사 무시됨 - 탭이 음악/멘트가 아님");
                return;
            }

            int added = 0;
            foreach (var file in mp3Files)
            {
                string destFile = Path.Combine(targetFolder, Path.GetFileName(file));
                try
                {
                    File.Copy(file, destFile, true);
                    if (!targetList.Items.Contains(Path.GetFileName(file)))
                    {
                        targetList.Items.Add(Path.GetFileName(file));
                        added++;
                        WriteLog("USB 복사됨: " + Path.GetFileName(file));
                    }
                }
                catch (Exception ex)
                {
                    WriteLog($"[복사 실패] {Path.GetFileName(file)} → {ex.Message}");
                }
            }

            if (added > 0)
            {
                MessageBox.Show($"USB에서 {added}개의 파일이 자동 복사되었습니다.", "USB 복사", MessageBoxButtons.OK, MessageBoxIcon.Information);
                WriteLog($"USB 자동 복사 완료: 총 {added}개 파일");
            }
            else
            {
                WriteLog("USB에서 중복으로 인해 새로 복사된 파일 없음");
            }
        }

        private void tabControl1_DrawItem(object sender, DrawItemEventArgs e)
        {
            TabPage tabPage = tabControl1.TabPages[e.Index];
            Rectangle tabRect = tabControl1.GetTabRect(e.Index);

            bool isSelected = (e.Index == tabControl1.SelectedIndex);
            Font font = isSelected ? new Font(e.Font, FontStyle.Bold) : e.Font;

            // 배경 초기화
            e.Graphics.FillRectangle(new SolidBrush(SystemColors.Control), tabRect);

            // 텍스트 정렬 및 표시
            TextRenderer.DrawText(
                e.Graphics,
                tabPage.Text,
                font,
                tabRect,
                SystemColors.ControlText,
                TextFormatFlags.HorizontalCenter | TextFormatFlags.VerticalCenter
            );
        }
        private void tabInnerControl_DrawItem(object sender, DrawItemEventArgs e)
        {
            TabControl tab = sender as TabControl;
            TabPage page = tab.TabPages[e.Index];
            Rectangle rect = tab.GetTabRect(e.Index);

            // 선택 여부에 따라 글꼴 스타일 변경
            bool isSelected = (e.Index == tab.SelectedIndex);
            Font font = isSelected ? new Font(e.Font, FontStyle.Bold) : e.Font;

            // 배경 채우기
            using (Brush backBrush = new SolidBrush(SystemColors.Control))
                e.Graphics.FillRectangle(backBrush, rect);

            // 텍스트 렌더링
            TextRenderer.DrawText(
                e.Graphics,
                page.Text,
                font,
                rect,
                SystemColors.ControlText,
                TextFormatFlags.HorizontalCenter | TextFormatFlags.VerticalCenter
            );
        }

        private void txtYoutubeUrl_TextChanged(object sender, EventArgs e)
        {

        }
        // 스트림(스피커관련)
        private void InitializeSpeakerGridStream()
        {
            // ✅ 자동 늘어남 방지
            dgvSpeakersStream.AutoSizeColumnsMode = DataGridViewAutoSizeColumnsMode.None;

            // ✅ 컬럼별로도 고정(디자이너에서 폭 맞췄다면 생략 가능하지만, 안전하게)
            dgvSpeakersStream.Columns["Select"].AutoSizeMode = DataGridViewAutoSizeColumnMode.None;
            dgvSpeakersStream.Columns["IP"].AutoSizeMode = DataGridViewAutoSizeColumnMode.None;
            dgvSpeakersStream.Columns["SIP"].AutoSizeMode = DataGridViewAutoSizeColumnMode.None;
            dgvSpeakersStream.Columns["Location"].AutoSizeMode = DataGridViewAutoSizeColumnMode.None;
            dgvSpeakersStream.Columns["StreamSpeakerModel"].AutoSizeMode = DataGridViewAutoSizeColumnMode.None;

            dgvSpeakersStream.AllowUserToAddRows = false;
            dgvSpeakersStream.RowHeadersVisible = false;
        }
        private void LoadSpeakersForStream()
        {
            dgvSpeakersStream.Rows.Clear();

            string path = Path.Combine(Application.StartupPath, "speakers.txt");
            if (!File.Exists(path)) return;

            var lines = File.ReadAllLines(path);
            foreach (var line in lines)
            {
                var parts = line.Split('|');
                if (parts.Length >= 3)
                {
                    string ip = parts[0].Trim();
                    string sip = parts[1].Trim();
                    string location = parts[2].Trim();

                    dgvSpeakersStream.Rows.Add(false, ip, sip, location);
                }
            }
        }
        private void btnSelectAllStream_Click(object sender, EventArgs e)
        {
            bool allSelected = dgvSpeakersStream.Rows.Cast<DataGridViewRow>()
                .All(row => Convert.ToBoolean(row.Cells["Select"].Value ?? false));

            foreach (DataGridViewRow row in dgvSpeakersStream.Rows)
            {
                row.Cells["Select"].Value = !allSelected;
            }
        }
        private void LoadGroupsForStream()
        {
            cmbGroupSelectStream.Items.Clear();
            cmbGroupSelectStream.Items.Add("전체");

            string path = Path.Combine(Application.StartupPath, "speakers.txt");
            if (!File.Exists(path)) return;

            var lines = File.ReadAllLines(path);
            var groups = new HashSet<string>();

            foreach (var line in lines)
            {
                var parts = line.Split('|');
                if (parts.Length >= 4)
                {
                    groups.Add(parts[3].Trim());
                }
            }

            foreach (var group in groups.OrderBy(g => g))
            {
                cmbGroupSelectStream.Items.Add(group);
            }

            isStreamGridReady = true; // 그리드 초기화가 끝났다고 표시
            cmbGroupSelectStream.SelectedIndex = 0;
        }

        private void cmbGroupSelectStream_SelectedIndexChanged(object sender, EventArgs e)
        {
            if (!isStreamGridReady) return;

            string selectedGroup = cmbGroupSelectStream.SelectedItem?.ToString()?.Trim();
            if (string.IsNullOrEmpty(selectedGroup)) return;

            dgvSpeakersStream.Rows.Clear();

            string path = Path.Combine(Application.StartupPath, "speakers.txt");
            if (!File.Exists(path)) return;

            var lines = File.ReadAllLines(path);
            foreach (var line in lines)
            {
                var parts = line.Split('|');
                if (parts.Length >= 4)
                {
                    string ip = parts[0].Trim();
                    string sip = parts[1].Trim();
                    string location = parts[2].Trim();
                    string group = parts[3].Trim();

                    // ✅ 전체 스피커 표시, 그룹일치 여부에 따라 체크
                    bool isChecked = (selectedGroup == "전체" || selectedGroup == group);
                    dgvSpeakersStream.Rows.Add(isChecked, ip, sip, location);
                }
            }
        }
        private void LoadYoutubeList()
        {
            // 리스트만 새로고침하고, 현재 선택은 가능한 보존
            LoadYoutubeList(restoreIfMissing: false, preserveCurrent: true);
        }
        //유튜브 채널 저장
        private void btnSaveYouTubeUrl_Click(object sender, EventArgs e)
        {
            string name = txtYoutubeName.Text.Trim();
            string url = txtYoutubeUrl.Text.Trim();

            if (string.IsNullOrEmpty(name) || string.IsNullOrEmpty(url))
            {
                MessageBox.Show("채널 이름과 유튜브 URL을 모두 입력하세요.");
                return;
            }

            // 파일 갱신
            var path = YoutubeListPath; // ← 통일
            var lines = File.Exists(path) ? File.ReadAllLines(path).ToList() : new List<string>();
            lines.RemoveAll(line => line.StartsWith(name + "|", StringComparison.OrdinalIgnoreCase));
            lines.Add($"{name}|{url}");
            File.WriteAllLines(path, lines);

            MessageBox.Show("유튜브 채널이 저장되었습니다.");
            WriteLog("유튜브 채널이 저장되었습니다.");

            // 리스트 갱신: 현재 선택 보존은 의미가 없으니 false, 복원도 필요 없음
            LoadYoutubeList(restoreIfMissing: false, preserveCurrent: false);

            // 방금 추가/수정한 항목으로 강제 선택
            int idx = IndexOfItem(cmbYoutubeList, name);
            cmbYoutubeList.SelectedIndexChanged -= cmbYoutubeList_SelectedIndexChanged;
            if (idx >= 0) cmbYoutubeList.SelectedIndex = idx;
            cmbYoutubeList.SelectedIndexChanged += cmbYoutubeList_SelectedIndexChanged;

            // 마지막 선택 파일에도 기록
            try { File.WriteAllText(LastChannelPath, name); } catch { }

            // 입력 필드 정리
            txtYoutubeName.Clear();
            txtYoutubeUrl.Clear();
        }
        private void btnDelYouTubeUrl_Click(object sender, EventArgs e)
        {
            if (cmbYoutubeList.SelectedItem == null)
            {
                MessageBox.Show("삭제할 채널을 선택하세요.");
                return;
            }

            string nameToDelete = cmbYoutubeList.SelectedItem.ToString();
            string path = YoutubeListPath;
            if (!File.Exists(path)) return;

            var lines = File.ReadAllLines(path).ToList();
            int removed = lines.RemoveAll(line => line.StartsWith(nameToDelete + "|", StringComparison.OrdinalIgnoreCase));

            if (removed > 0)
            {
                File.WriteAllLines(path, lines);

                // 현재 선택이 사라질 수 있으니 안전하게 다시 로드
                LoadYoutubeList(restoreIfMissing: true, preserveCurrent: false);

                // last_youtube_channel.txt가 삭제된 이름이면 비워 둠
                try
                {
                    if (File.Exists(LastChannelPath))
                    {
                        var last = (File.ReadAllText(LastChannelPath) ?? "").Trim();
                        if (string.Equals(last, nameToDelete, StringComparison.OrdinalIgnoreCase))
                            File.WriteAllText(LastChannelPath, "");
                    }
                }
                catch { }

                txtYoutubeName.Clear();
                txtYoutubeUrl.Clear();

                MessageBox.Show("채널이 삭제되었습니다.");
                WriteLog("채널이 삭제되었습니다.");
            }
            else
            {
                MessageBox.Show("삭제할 채널을 찾을 수 없습니다.");
            }
        }

        private bool _isLoadingYoutubeList = false;
        private DateTime? _lastListMtime = null;
        private void btnLoadYouTubeUrls_Click(object sender, EventArgs e)
        {
            LoadYoutubeList();
        }
        private void LoadYoutubeList(bool restoreIfMissing, bool preserveCurrent)
        {
            // 파일 변경 없으면 스킵
            if (File.Exists(YoutubeListPath))
            {
                var mtime = File.GetLastWriteTimeUtc(YoutubeListPath);
                if (_lastListMtime.HasValue && _lastListMtime.Value == mtime)
                {
                    // 파일 수정 없음 → 아무 것도 안 함
                    return;
                }
                _lastListMtime = mtime;
            }
            else
            {
                _lastListMtime = null;
            }

            _isLoadingYoutubeList = true;
            try
            {
                // 현재 선택 보존용
                string currentSel = cmbYoutubeList.SelectedItem?.ToString();

                cmbYoutubeList.BeginUpdate();

                cmbYoutubeList.Items.Clear();
                youtubeChannelMap.Clear();
                youtubeChannels.Clear();

                if (!File.Exists(YoutubeListPath))
                {
                    cmbYoutubeList.EndUpdate();
                    return;
                }

                var lines = File.ReadAllLines(YoutubeListPath);
                foreach (var raw in lines)
                {
                    var line = (raw ?? "").Trim();
                    if (line.Length == 0 || line.StartsWith("#")) continue;

                    var parts = line.Split('|');
                    if (parts.Length >= 2)
                    {
                        string name = parts[0].Trim();
                        string url = parts[1].Trim();
                        if (name.Length == 0 || url.Length == 0) continue;

                        youtubeChannelMap[name] = url;
                        youtubeChannels[name] = url;
                        cmbYoutubeList.Items.Add(name);
                    }
                }

                // 선택 우선순위:
                // 1) preserveCurrent=true 이고 기존 선택이 여전히 존재하면 그대로 유지
                // 2) last_youtube_channel.txt 복원 (restoreIfMissing = true일 때만)
                // 3) 아무 것도 없으면 첫 항목
                bool selected = false;

                if (preserveCurrent && !string.IsNullOrWhiteSpace(currentSel))
                {
                    int idx = IndexOfItem(cmbYoutubeList, currentSel);
                    if (idx >= 0)
                    {
                        cmbYoutubeList.SelectedIndexChanged -= cmbYoutubeList_SelectedIndexChanged;
                        cmbYoutubeList.SelectedIndex = idx;
                        cmbYoutubeList.SelectedIndexChanged += cmbYoutubeList_SelectedIndexChanged;
                        selected = true;
                    }
                }

                if (!selected && restoreIfMissing)
                {
                    string last = ReadLastChannel();
                    if (!string.IsNullOrWhiteSpace(last))
                    {
                        int idx = FindBestMatchIndex(last);
                        if (idx >= 0)
                        {
                            cmbYoutubeList.SelectedIndexChanged -= cmbYoutubeList_SelectedIndexChanged;
                            cmbYoutubeList.SelectedIndex = idx;
                            cmbYoutubeList.SelectedIndexChanged += cmbYoutubeList_SelectedIndexChanged;
                            selected = true;
                        }
                    }
                }

                if (!selected && cmbYoutubeList.Items.Count > 0)
                {
                    cmbYoutubeList.SelectedIndexChanged -= cmbYoutubeList_SelectedIndexChanged;
                    cmbYoutubeList.SelectedIndex = 0;
                    cmbYoutubeList.SelectedIndexChanged += cmbYoutubeList_SelectedIndexChanged;
                }

                cmbYoutubeList.EndUpdate();
            }
            finally
            {
                _isLoadingYoutubeList = false;
            }
        }

        // 마지막 선택 저장
        private void cmbYoutubeList_SelectedIndexChanged(object sender, EventArgs e)
        {
            if (_isLoadingYoutubeList) return;
            var sel = cmbYoutubeList.SelectedItem?.ToString();
            if (string.IsNullOrWhiteSpace(sel)) return;
            try { File.WriteAllText(LastChannelPath, sel); } catch { }
        }
        private string ReadLastChannel()
        {
            try
            {
                if (!File.Exists(LastChannelPath)) return null;
                return (File.ReadAllText(LastChannelPath) ?? "").Trim();
            }
            catch { return null; }
        }
        private int IndexOfItem(ComboBox cb, string text)
        {
            for (int i = 0; i < cb.Items.Count; i++)
            {
                if (string.Equals(cb.Items[i]?.ToString(), text, StringComparison.OrdinalIgnoreCase))
                    return i;
            }
            return -1;
        }
        private int FindBestMatchIndex(string last)
        {
            if (string.IsNullOrWhiteSpace(last)) return -1;
            last = last.Trim();

            // 1) 완전 일치
            int idx = IndexOfItem(cmbYoutubeList, last);
            if (idx >= 0) return idx;

            // 2) 부분 포함
            for (int i = 0; i < cmbYoutubeList.Items.Count; i++)
            {
                var name = cmbYoutubeList.Items[i]?.ToString() ?? "";
                if (name.IndexOf(last, StringComparison.OrdinalIgnoreCase) >= 0)
                    return i;
            }

            return -1;
        }

        // 마지막 선택 복원
        private void RestoreLastYoutubeSelection()
        {
            if (!File.Exists(LastChannelPath)) return;

            string last = (File.ReadAllText(LastChannelPath) ?? "").Trim();
            if (string.IsNullOrEmpty(last)) return;

            // 1) 완전 일치 우선
            for (int i = 0; i < cmbYoutubeList.Items.Count; i++)
            {
                if (string.Equals(cmbYoutubeList.Items[i]?.ToString(),
                                  last, StringComparison.OrdinalIgnoreCase))
                {
                    cmbYoutubeList.SelectedIndex = i;
                    return;
                }
            }

            // 2) 부분 포함 매칭(이름이 조금 바뀌었을 수 있는 경우)
            for (int i = 0; i < cmbYoutubeList.Items.Count; i++)
            {
                var name = cmbYoutubeList.Items[i]?.ToString() ?? "";
                if (name.IndexOf(last, StringComparison.OrdinalIgnoreCase) >= 0)
                {
                    cmbYoutubeList.SelectedIndex = i;
                    return;
                }
            }
        }

        // 스트리밍 포트
        private void LoadStreamPort()
        {
            if (File.Exists(streamPortFilePath))
            {
                string content = File.ReadAllText(streamPortFilePath).Trim();
                if (int.TryParse(content, out int savedPort))
                {
                    numSelectStreamPort.Value = savedPort;
                }
            }
            else
            {
                // 기본값 5004
                numSelectStreamPort.Value = 5004;
            }
        }
        private void btnSavePort_Click(object sender, EventArgs e)
        {
            int port = (int)numSelectStreamPort.Value;

            try
            {
                File.WriteAllText(streamPortFilePath, port.ToString());
                MessageBox.Show($"포트 번호 {port}가 저장되었습니다.", "저장 완료");
                WriteLog($"스트리밍 포트 저장됨: {port}");  // ✅ 로그 기록
            }
            catch (Exception ex)
            {
                MessageBox.Show("포트 저장 중 오류 발생: " + ex.Message);
                WriteLog($"[포트 저장 오류] {ex.Message}");  // ✅ 예외 로그 기록
            }
        }
        //마이크등 장치검색 저장
        private void btnLoadMicDevices_Click(object sender, EventArgs e)
        {
            cmbMicDevices.Items.Clear();

            Process ffmpegList = new Process();
            ffmpegList.StartInfo.FileName = ffmpegPath;
            ffmpegList.StartInfo.Arguments = "-list_devices true -f dshow -i dummy";
            ffmpegList.StartInfo.UseShellExecute = false;
            ffmpegList.StartInfo.RedirectStandardError = true;
            ffmpegList.StartInfo.StandardErrorEncoding = Encoding.UTF8;
            ffmpegList.StartInfo.CreateNoWindow = true;
            ffmpegList.Start();

            string output = ffmpegList.StandardError.ReadToEnd();
            ffmpegList.WaitForExit();

            foreach (var line in output.Split('\n'))
            {
                var trimmedLine = line.Trim();
                if (trimmedLine.Contains("(audio)") && trimmedLine.Contains("\""))
                {
                    int firstQuote = trimmedLine.IndexOf('"');
                    int lastQuote = trimmedLine.LastIndexOf('"');
                    if (firstQuote >= 0 && lastQuote > firstQuote)
                    {
                        string deviceName = trimmedLine.Substring(firstQuote + 1, lastQuote - firstQuote - 1);
                        cmbMicDevices.Items.Add(deviceName);
                    }
                }
            }

            string savedDevicePath = "selected_mic_device.txt";
            bool autoSelected = false;

            if (File.Exists(savedDevicePath))
            {
                string savedDevice = File.ReadAllText(savedDevicePath, Encoding.UTF8);
                int index = cmbMicDevices.Items.IndexOf(savedDevice);
                if (index >= 0)
                {
                    cmbMicDevices.SelectedIndex = index;
                    autoSelected = true;
                }
            }

            if (cmbMicDevices.Items.Count > 0)
            {
                if (!autoSelected)
                    MessageBox.Show("마이크 장치 검색 완료.");
            }
            else
            {
                MessageBox.Show("마이크 장치를 찾을 수 없습니다.");
            }
        }
        private void btnSaveMicDevice_Click(object sender, EventArgs e)
        {
            if (cmbMicDevices.SelectedItem == null)
            {
                MessageBox.Show("저장할 마이크 장치를 선택하세요.");
                return;
            }

            string selectedDevice = cmbMicDevices.SelectedItem.ToString();
            string path = Path.Combine(Application.StartupPath, "selected_mic_device.txt");

            try
            {
                File.WriteAllText(path, selectedDevice);
                MessageBox.Show("마이크 장치가 저장되었습니다.");
                WriteLog("마이크 장치가 저장되었습니다.");
            }
            catch (Exception ex)
            {
                MessageBox.Show("저장 중 오류 발생: " + ex.Message);
            }
        }
        private async Task LoadSavedMicDeviceAsync()
        {
            cmbMicDevices.Items.Clear();

            await Task.Run(() =>
            {
                Process ffmpegList = new Process();
                ffmpegList.StartInfo.FileName = ffmpegPath;
                ffmpegList.StartInfo.Arguments = "-list_devices true -f dshow -i dummy";
                ffmpegList.StartInfo.UseShellExecute = false;
                ffmpegList.StartInfo.RedirectStandardError = true;
                ffmpegList.StartInfo.StandardErrorEncoding = Encoding.UTF8;
                ffmpegList.StartInfo.CreateNoWindow = true;
                ffmpegList.Start();

                string output = ffmpegList.StandardError.ReadToEnd();
                ffmpegList.WaitForExit();

                List<string> foundDevices = new List<string>();
                foreach (var line in output.Split('\n'))
                {
                    var trimmed = line.Trim();
                    if (trimmed.Contains("(audio)") && trimmed.Contains("\""))
                    {
                        int first = trimmed.IndexOf('"');
                        int last = trimmed.LastIndexOf('"');
                        if (first >= 0 && last > first)
                        {
                            string deviceName = trimmed.Substring(first + 1, last - first - 1);
                            foundDevices.Add(deviceName);
                        }
                    }
                }

                // UI 쓰레드로 전환하여 콤보박스에 반영
                Invoke((MethodInvoker)(() =>
                {
                    foreach (var d in foundDevices)
                        cmbMicDevices.Items.Add(d);

                    if (File.Exists("selected_mic_device.txt"))
                    {
                        string saved = File.ReadAllText("selected_mic_device.txt", Encoding.UTF8);
                        int index = cmbMicDevices.Items.IndexOf(saved);
                        if (index >= 0)
                            cmbMicDevices.SelectedIndex = index;
                    }

                    if (cmbMicDevices.Items.Count == 0)
                        MessageBox.Show("마이크 장치를 찾을 수 없습니다.");
                }));
            });
        }
        private void StreamTypeChanged(object sender, EventArgs e)
        {
            if (rbStreamYoutube == null || rbStreamMusic == null || rbStreamMic == null || ytStatus == null)
                return;

            panelYoutubeControls.Visible = rbStreamYoutube.Checked;
            panelMusicControls.Visible = rbStreamMusic.Checked;
            panelMicControls.Visible = rbStreamMic.Checked;

            // ✅ 상태 표시 라벨 설정
            if (rbStreamYoutube.Checked)
            {
                ytStatus.Text = "유튜브 스트리밍 모드 선택됨";
            }
            else if (rbStreamMusic.Checked)
            {
                ytStatus.Text = "음원 파일 스트리밍 모드 선택됨";
            }
            else if (rbStreamMic.Checked)
            {
                ytStatus.Text = "마이크 실시간 스트리밍 모드 선택됨";
            }
        }
        // 스트리밍 //////////////////
        private void LoadYoutubeChannels()
        {
            LoadYoutubeList();
        }
        private async Task<bool> SendBgmSafeAsync(string ip, string cmd)
        {
            await _bgmSendLock.WaitAsync();
            try
            {
                return await Task.Run(() =>
                {
                    try { SendBGMCommand(ip, cmd); return true; }
                    catch (Exception ex) { WriteLog($"BGM '{cmd}' 실패({ip}): {ex.Message}"); return false; }
                });
            }
            finally { _bgmSendLock.Release(); }
        }
        private async Task<(int ok, int fail)> BroadcastBgmAsync(IEnumerable<string> ips, string cmd, int retry = 1, int spacingMs = 80)
        {
            int ok = 0, fail = 0;
            foreach (var ip in ips)
            {
                bool sent = false;
                for (int t = 0; t <= retry && !sent; t++)
                    sent = await SendBgmSafeAsync(ip, cmd);
                if (sent) ok++; else fail++;
                if (spacingMs > 0) await Task.Delay(spacingMs);
            }
            return (ok, fail);
        }
        private async Task<bool> SendBgmSafeAsync(string ip, string cmd, bool doubleTap = false)
        {
            await _bgmSendLock.WaitAsync();
            try
            {
                return await Task.Run(() =>
                {
                    try
                    {
                        // 1차 전송
                        SendBGMCommand(ip, cmd);
                        WriteLog($"[BGM->{ip}] {cmd} 1st OK");

                        if (doubleTap)
                        {
                            // 일부 장치가 바쁠 때 1회 무시하는 현상 보완
                            Thread.Sleep(120); // 짧은 간격
                            SendBGMCommand(ip, cmd);
                            WriteLog($"[BGM->{ip}] {cmd} 2nd OK");
                        }
                        return true;
                    }
                    catch (Exception ex1)
                    {
                        WriteLog($"[BGM->{ip}] {cmd} 실패: {ex1.Message}");
                        // 마지막 한 번 더 시도(재시도 1회)
                        try
                        {
                            Thread.Sleep(160);
                            SendBGMCommand(ip, cmd);
                            WriteLog($"[BGM->{ip}] {cmd} 재시도 OK");
                            return true;
                        }
                        catch (Exception ex2)
                        {
                            WriteLog($"[BGM->{ip}] {cmd} 재시도 실패: {ex2.Message}");
                            return false;
                        }
                    }
                });
            }
            finally
            {
                _bgmSendLock.Release();
            }
        }

        // 다수 IP 순차 브로드캐스트 (간격 포함)
        private async Task<(int ok, int fail)> BroadcastBgmAsync(
            IEnumerable<string> ips, string cmd, bool doubleTap = false, int spacingMs = 80)
        {
            int ok = 0, fail = 0;
            foreach (var ip in ips)
            {
                var sent = await SendBgmSafeAsync(ip, cmd, doubleTap);
                if (sent) ok++; else fail++;
                if (spacingMs > 0) await Task.Delay(spacingMs);
            }
            return (ok, fail);
        }
        private async void btnStartStream_Click(object sender, EventArgs e)
        {
            // (0) 기존 ffmpeg 정리(안전)
            try
            {
                if (ffmpegProcess != null)
                {
                    try { if (!ffmpegProcess.HasExited) ffmpegProcess.Kill(); } catch { }
                    try { ffmpegProcess.Dispose(); } catch { }
                    ffmpegProcess = null;
                    WriteLog("기존 스트리밍 프로세스 종료됨");
                }
            }
            catch (Exception ex) { WriteLog("기존 ffmpeg 종료 중 예외(무시): " + ex.Message); }

            if (chkAutoBgmControl.Checked)
            {
                // (1) 파라미터 유효성
                if (!rbStreamYoutube.Checked && !rbStreamMusic.Checked && !rbStreamMic.Checked)
                {
                    MessageBox.Show("스트리밍 종류를 선택하세요.");
                    WriteLog("스트리밍 종류를 선택하세요.");
                    return;
                }
                if (rbStreamYoutube.Checked)
                {
                    bool noChannel = (cmbYoutubeList.SelectedItem == null);
                    bool noUrl = string.IsNullOrWhiteSpace(txtYoutubeUrl.Text);
                    if (noChannel && noUrl)
                    {
                        MessageBox.Show("유튜브 채널을 선택하거나 주소를 입력하세요.");
                        WriteLog("유튜브 채널을 선택하거나 주소를 입력하세요.");
                        return;
                    }
                }

                // (2) 선택된 스피커
                var selectedRows = dgvSpeakersStream.Rows
                    .Cast<DataGridViewRow>()
                    .Where(row => (row.Cells["Select"].Value as bool?) == true)
                    .ToList();

                if (selectedRows.Count == 0)
                {
                    MessageBox.Show("스트리밍 대상 스피커를 선택하세요.");
                    WriteLog("스트리밍 대상 스피커를 선택하세요.");
                    return;
                }

                // (3) 온라인 확인 및 오프라인 체크 해제
                var onlineIPs = new List<string>();
                var tasks = new List<Task>();
                foreach (var row in selectedRows)
                {
                    string ip = row.Cells["IP"].Value?.ToString();
                    if (string.IsNullOrWhiteSpace(ip)) continue;

                    tasks.Add(Task.Run(() =>
                    {
                        if (TryConnectWithTimeout(ip, 8787, 500))
                        {
                            lock (onlineIPs) onlineIPs.Add(ip);
                        }
                        else
                        {
                            try
                            {
                                if (!IsDisposed && IsHandleCreated)
                                {
                                    BeginInvoke((MethodInvoker)(() =>
                                    {
                                        row.Cells["Select"].Value = false;
                                        WriteLog($"❌ 오프라인 스피커 체크 해제됨: {ip}");
                                    }));
                                }
                            }
                            catch { }
                        }
                    }));
                }

                try { await Task.WhenAll(tasks); }
                catch (Exception ex) { WriteLog("온라인 점검 집계 중 예외(무시 가능): " + ex.Message); }

                if (onlineIPs.Count == 0)
                {
                    MessageBox.Show("온라인 상태인 스피커가 없습니다. 스트리밍을 중단합니다.");
                    WriteLog("⚠️ 온라인 스피커 없음, 스트리밍 중단");
                    return;
                }

                // ✅ 온라인 스냅샷 확정
                lastOnlineIPs = onlineIPs.ToList();

                // (4) BGM 정지 전송
                try
                {
                    var (okStop, failStop) = await BroadcastBgmAsync(lastOnlineIPs, "bgm_stop", retry: 1, spacingMs: 80);
                    WriteLog($"bgm_stop 전송: 대상 {lastOnlineIPs.Count} → 성공 {okStop}, 실패 {failStop}");
                }
                catch (Exception ex) { WriteLog("bgm_stop 전송 중 예외: " + ex.Message); }

                // UI: 정지 상태
                lblBgmStatus.Text = "BGM 정지됨";
                BGMprogressBar.MarqueeAnimationSpeed = 0;
                BGMprogressBar.Style = ProgressBarStyle.Continuous;
                BGMprogressBar.Value = 0;
                BGMprogressBar.Visible = false;

                // ✅ (4.5) 현재 그리드의 선택 상태로 "선택 스피커 목록" 즉시 저장
                //     SaveFullConfig() 내부에서 selected_speakers=... 를 파일로 기록합니다.
                try
                {
                    SaveFullConfig();
                    WriteLog("📌 현재 선택 스피커 리스트 저장됨");
                }
                catch (Exception ex)
                {
                    WriteLog("선택 스피커 리스트 저장 실패: " + ex.Message);
                }
            }

            // (5) 스트리밍 시작
            ytStatus.Text = "";
            if (rbStreamYoutube.Checked)
            {
                string youtubeUrl = txtYoutubeUrl.Text.Trim();
                lastYoutubeUrl = youtubeUrl;
                isYoutubeRepeating = true;
                _ = Task.Run(() => { try { StreamYoutubeAudio(youtubeUrl); } catch (Exception ex) { WriteLog("유튜브 시작 실패: " + ex.Message); } });
            }
            else if (rbStreamMusic.Checked)
            {
                isYoutubeRepeating = false;
                lastYoutubeUrl = null;
                StreamFromFile();
            }
            else if (rbStreamMic.Checked)
            {
                isYoutubeRepeating = false;
                lastYoutubeUrl = null;
                StreamFromMic();
            }


            // (6) BGM 자동 시작 (지연 후 전송)
            if (chkAutoBgmControl.Checked)
            {
                try
                {
                    await Task.Delay(5000);

                    var (okStart, failStart) = await BroadcastBgmAsync(lastOnlineIPs, "bgm_start", retry: 2, spacingMs: 80);
                    WriteLog($"bgm_start 전송: 대상 {lastOnlineIPs.Count} → 성공 {okStart}, 실패 {failStart}");

                    bgmStartedByAuto = okStart > 0;
                    lblBgmStatus.Text = okStart > 0 ? "BGM 시작됨..." : "BGM 시작 실패";
                    if (okStart > 0)
                    {
                        BGMprogressBar.Style = ProgressBarStyle.Marquee;
                        BGMprogressBar.Visible = true;
                        BGMprogressBar.MarqueeAnimationSpeed = 40;
                    }
                    else
                    {
                        BGMprogressBar.MarqueeAnimationSpeed = 0;
                        BGMprogressBar.Style = ProgressBarStyle.Continuous;
                        BGMprogressBar.Value = 0;
                        BGMprogressBar.Visible = false;
                    }
                }
                catch (Exception ex)
                {
                    WriteLog("bgm_start 지연/전송 중 예외: " + ex.Message);
                }
            }

            // (7) 유튜브 자동 재시작 타이머 제거: 스트림은 사용자가 정지할 때까지 유지
            youtubeRestartTimer.Stop(); // 혹시 이전 스트림에서 돌고 있던 타이머가 있으면 정지
            WriteLog("유튜브 자동 재시작 타이머 비활성화 (사용자가 정지할 때까지 유지)");

            // ✅✅ (8) 마지막 스트림 “전체 설정” 저장: 스트림 타입/URL/채널/선택 스피커 포함
            try
            {
                SaveFullConfig();
                WriteLog("📌 마지막 스트림 설정 & 스피커 리스트 최종 저장됨");


            }
            catch (Exception ex)

            {
                WriteLog("마지막 스트림 설정 저장 실패: " + ex.Message);
            }
        }

        private async void StreamYoutubeAudio(string url)
        {
            try
            {
                string ytDlpPath = Path.Combine(Application.StartupPath, "lib", "yt-dlp.exe");
                string extractedUrl = null;

                // --- yt-dlp: 실제 오디오 URL 추출 ---
                var ytProcess = new Process();
                ytProcess.StartInfo.FileName = ytDlpPath;
                ytProcess.StartInfo.Arguments = $"-f \"bestaudio[protocol^=m3u8]/bestaudio\" --no-cache-dir -g \"{url}\"";
                ytProcess.StartInfo.UseShellExecute = false;
                ytProcess.StartInfo.RedirectStandardOutput = true;
                ytProcess.StartInfo.RedirectStandardError = true;
                ytProcess.StartInfo.CreateNoWindow = true;
                ytProcess.Start();

                extractedUrl = ytProcess.StandardOutput.ReadLine();
                string ytErrorOutput = ytProcess.StandardError.ReadToEnd();
                ytProcess.WaitForExit();

                if (string.IsNullOrEmpty(extractedUrl))
                {
                    DebugAppend($"[yt-dlp][EXIT {ytProcess.ExitCode}] Error:\n{ytErrorOutput}", important: true);
                    this.Invoke((MethodInvoker)(() =>
                    {
                        ytStatus.Text = "URL 추출 실패";
                        MessageBox.Show("yt-dlp URL 추출 실패:\n\n" + ytErrorOutput);
                        WriteLog("yt-dlp URL 추출 실패:\n\n" + ytErrorOutput);
                    }));
                    return;
                }
                else
                {
                    if (!string.IsNullOrWhiteSpace(ytErrorOutput))
                        DebugAppend($"[yt-dlp][EXIT {ytProcess.ExitCode}] Stderr:\n{ytErrorOutput}", important: false);
                }

                // --- 스피커 준비: 무음 전송 2회 ---
                SendSilenceToFlush();
                await Task.Delay(1000);
                SendSilenceToFlush();
                await Task.Delay(1000);

                string arguments =
                    $"-re -user_agent \"Mozilla/5.0\" -i \"{extractedUrl}\" " +
                    $"-acodec libmp3lame -ab 128k -f rtp rtp://{multicastAddress}:{port} -sdp_file \"{sdpPath}\"";

                // ★ 필드에 바로 넣지 말고 로컬 변수로 구성
                var proc = new Process();
                proc.StartInfo.FileName = ffmpegPath;
                proc.StartInfo.Arguments = arguments;
                proc.StartInfo.UseShellExecute = false;
                proc.StartInfo.RedirectStandardOutput = true;
                proc.StartInfo.RedirectStandardError = true;
                proc.StartInfo.StandardErrorEncoding = Encoding.UTF8;
                proc.StartInfo.CreateNoWindow = true;
                proc.EnableRaisingEvents = true;

                var seenImportant = new HashSet<string>();

                proc.OutputDataReceived += (s, e) =>
                {
                    if (string.IsNullOrEmpty(e.Data)) return;
                    DebugAppend("[stdout] " + e.Data, important: false);
                };

                proc.ErrorDataReceived += (s, e) =>
                {
                    if (string.IsNullOrEmpty(e.Data)) return;

                    bool important = IsImportantFfmpegLine(e.Data);

                    // 인코딩/전송 시작 신호 감지 시 UI 업데이트
                    if (e.Data.IndexOf("bitrate", StringComparison.OrdinalIgnoreCase) >= 0)
                    {
                        this.Invoke((MethodInvoker)(() => { StreamStatus.Text = "스트리밍 중..."; }));
                    }

                    DebugAppend("[stderr] " + e.Data, important);

                    // 메인 로그는 생략, 세션 중복만 관리
                    if (important)
                    {
                        string key = e.Data.Length > 160 ? e.Data.Substring(0, 160) : e.Data;
                        seenImportant.Add(key);
                    }
                };

                // ★ Exited에서 'ffmpegProcess' 대신 sender 사용 + 복구만 트리거(종료 UI 갱신 금지)
                EventHandler exitedHandler = null;
                exitedHandler = async (s, e) =>
                {
                    try
                    {
                        var p = s as Process;
                        int code = (p?.HasExited ?? false) ? p.ExitCode : -1;
                        DebugAppend($"[ffmpeg exited] code={code}", important: code != 0);
                        if (code != 0)
                            WriteLog($"ffmpeg 프로세스 종료(code={code}) — 스트리밍 중단 감지");

                        // ✅ 스트리밍이 의도적으로 중단된 상태가 아니고(예: Stop 버튼 아님)
                        //    현재 스트리밍이 유지되어야 하는 상황이면 복구 시작
                        if (_streamingExpected && !_isRecovering)
                        {
                            // 선택: 스트리밍 상태 UI만 "복구 중..."으로 가볍게 표시 (BGM UI는 건드리지 않음)
                            if (!IsDisposed && IsHandleCreated)
                            {
                                BeginInvoke((MethodInvoker)(() =>
                                {
                                    StreamStatus.Text = "스트리밍 복구 중...";
                                    StreamProgressBar.Style = ProgressBarStyle.Marquee;
                                    StreamProgressBar.MarqueeAnimationSpeed = 80;
                                    StreamProgressBar.Visible = true;
                                }));
                            }

                            await RecoverStreamingAsync("ffmpeg Exited");
                        }
                    }
                    catch (Exception ex)
                    {
                        DebugAppend("[ffmpeg exited handler error] " + ex.Message, important: true);
                    }
                    finally
                    {
                        try { (s as Process).Exited -= exitedHandler; } catch { }
                        try { (s as Process)?.Dispose(); } catch { }
                    }
                };
                proc.Exited += exitedHandler;


                // ★ 이제 필드에 등록 (다른 곳에서 Stop 눌렀을 때 교체 가능)
                ffmpegProcess = proc;

                proc.Start();
                proc.BeginOutputReadLine();
                proc.BeginErrorReadLine();

                // ▶ ffmpeg가 실제로 시작된 후에만 워치독/기대상태 ON
                _streamingExpected = true;
                _bgmHardStopped = false;
                try
                {
                    StartStreamWatchdog();
                }
                catch (Exception ex)
                {
                    WriteLog("스트림 워치독 시작 중 예외: " + ex.Message);
                }

                // --- 시작 UI/로그 ---
                this.Invoke(new Action(() =>
                {
                    ytStatus.Text = "유튜브 스트리밍 시작";
                    StreamProgressBar.Style = ProgressBarStyle.Marquee;
                    StreamProgressBar.MarqueeAnimationSpeed = 100;
                    StreamProgressBar.Visible = true;
                    WriteLog("유튜브 스트리밍 시작");
                }));

                this.Invoke(new Action(() => ytStatus.Text = "유튜브 스트리밍 중..."));
            }
            catch (Exception ex)
            {
                this.Invoke(new Action(() =>
                {
                    ytStatus.Text = "유튜브 스트리밍 오류";
                    MessageBox.Show("유튜브 스트리밍 오류:\n\n" + ex.Message);
                    WriteLog("유튜브 스트리밍 오류:\n\n" + ex.Message);
                }));
                DebugAppend($"[EXCEPTION] {ex.Message}", important: true);
            }
        }


        private async void btnStopStream_Click(object sender, EventArgs e)
        {
            // 🔵 수동 정지이므로, 자동 복구/재시작 관련 상태 먼저 끄기
            _streamingExpected = false;         // 이제 스트리밍이 없어도 정상 상태
            try { StopStreamWatchdog(); } catch { }
            try { youtubeRestartTimer?.Stop(); } catch { }
            try
            {
                // 1) ffmpeg 안전 종료 (원자적 교체)
                var p = System.Threading.Interlocked.Exchange(ref ffmpegProcess, null); // 필드를 즉시 비움
                if (p != null)
                {
                    try
                    {
                        // Exited 핸들러가 있다면 해제(중복/지연 호출 방지)
                        try { p.Exited -= ffmpegExitedHandler; } catch { /* 없을 수 있음 */ }

                        // ★ HasExited 접근 시 "이 개체와 연결된 프로세스가 없습니다." 예외를 흡수
                        bool needKill = false;
                        try
                        {
                            needKill = !p.HasExited;
                        }
                        catch (InvalidOperationException)
                        {
                            // 이 개체와 연결된 프로세스가 없음 → 이미 종료된 것으로 간주
                            needKill = false;
                        }
                        catch
                        {
                            // 기타 예외도 "이미 종료된 상태"로 취급
                            needKill = false;
                        }

#if NET5_0_OR_GREATER
                if (needKill) { try { p.Kill(true); } catch { } }  // 트리 종료
#else
                        if (needKill) { try { p.Kill(); } catch { } }
#endif
                        try { p.WaitForExit(3000); } catch { } // 3초 대기 (필요시 조정)
                    }
                    finally
                    {
                        try { p.Dispose(); } catch { }
                    }

                    // 1-2) 디버그 파일 writer 정리
                    lock (debugFileLock)
                    {
                        if (ffmpegLogWriter != null)
                        {
                            try { ffmpegLogWriter.Flush(); ffmpegLogWriter.Close(); }
                            catch { }
                            ffmpegLogWriter = null;
                        }
                    }

                    // UI
                    if (InvokeRequired)
                    {
                        BeginInvoke((MethodInvoker)(() =>
                        {
                            ytStatus.Text = "스트리밍 정지됨";
                            StreamStatus.Text = "스트리밍 정지됨";
                            StreamProgressBar.Style = ProgressBarStyle.Continuous;
                            StreamProgressBar.Value = 0;
                            StreamProgressBar.Visible = true;
                        }));
                    }
                    else
                    {
                        ytStatus.Text = "스트리밍 정지됨";
                        StreamStatus.Text = "스트리밍 정지됨";
                        StreamProgressBar.Style = ProgressBarStyle.Continuous;
                        StreamProgressBar.Value = 0;
                        StreamProgressBar.Visible = true;
                    }

                    WriteLog("스트리밍 정지됨 (프로세스 종료됨)");
                }
                else
                {
                    WriteLog("ffmpegProcess 없음 또는 이미 종료됨");
                }

                // 2) 혹시 남은 ffmpeg 강제 종료 (다른 인스턴스 청소용)
                KillAllFFmpegProcesses();

                // 3) 무음 전송 (버퍼 플러시)
                SendSilenceToFlush();
            }
            catch (Exception ex)
            {
                // 여기까지 오는 예외는 HasExited 관련이 아니라 정말 예상치 못한 예외
                MessageBox.Show("스트리밍 정지 중 오류:\n" + ex.Message);
                WriteLog("스트리밍 정지 중 오류:\n" + ex.Message);
            }

            // 4) 온라인 스피커만 BGM 정지
            await Task.Delay(3000);

            var selectedRows = dgvSpeakersStream.Rows
                .Cast<DataGridViewRow>()
                .Where(row => Convert.ToBoolean(row.Cells["Select"].Value))
                .ToList();

            var onlineIPs = new List<string>();
            var tasks = new List<Task>();

            foreach (var row in selectedRows)
            {
                var currentRow = row; // 캡처 안전
                string ip = currentRow.Cells["IP"].Value?.ToString();
                if (string.IsNullOrEmpty(ip)) continue;

                tasks.Add(Task.Run(() =>
                {
                    if (TryConnectWithTimeout(ip, 8787, 500))
                    {
                        lock (onlineIPs) onlineIPs.Add(ip);
                    }
                    else
                    {
                        Invoke((MethodInvoker)(() =>
                        {
                            currentRow.Cells["Select"].Value = false;
                            WriteLog($"❌ 오프라인 스피커 체크 해제됨: {ip}");
                        }));
                    }
                }));
            }

            await Task.WhenAll(tasks);

            foreach (var ip in onlineIPs)
                SendBGMCommand(ip, "bgm_stop");

            bgmStartedByAuto = false;

            // UI
            if (InvokeRequired)
            {
                BeginInvoke((MethodInvoker)(() =>
                {
                    lblBgmStatus.Text = "BGM 종료됨";
                    BGMprogressBar.Style = ProgressBarStyle.Continuous;
                    BGMprogressBar.Value = 0;
                    BGMprogressBar.Visible = true;
                }));
            }
            else
            {
                lblBgmStatus.Text = "BGM 종료됨";
                BGMprogressBar.Style = ProgressBarStyle.Continuous;
                BGMprogressBar.Value = 0;
                BGMprogressBar.Visible = true;
            }
        }

        private void SafeKillAndDispose(ref Process p)
        {
            var proc = Interlocked.Exchange(ref p, null);
            if (proc == null) return;
            try
            {
                if (!proc.HasExited) proc.Kill();
            }
            catch { /* ignore */ }
            try { proc.Dispose(); } catch { /* ignore */ }
        }
        private void KillAllFFmpegProcesses()
        {
            var ffmpegs = Process.GetProcessesByName("ffmpeg");
            foreach (var proc in ffmpegs)
            {
                try
                {
                    proc.Kill();
                    proc.WaitForExit();
                    WriteLog($"[백업 종료] ffmpeg 프로세스 강제 종료됨 (PID: {proc.Id})");
                }
                catch (Exception ex)
                {
                    WriteLog($"[백업 종료 실패] PID: {proc.Id} - {ex.Message}");
                }
            }

            if (ffmpegs.Length == 0)
                WriteLog("[백업 종료] 실행 중인 ffmpeg 없음");
        }
        private void SendSilenceToFlush()
        {
            try
            {
                string ffmpegPath = Path.Combine(Application.StartupPath, "lib", "ffmpeg.exe");
                string silencePath = Path.Combine(Application.StartupPath, "lib", "silence1s.mp3");

                if (!File.Exists(ffmpegPath) || !File.Exists(silencePath))
                {
                    return;
                }

                string multicastAddress = "239.255.0.1";
                int port = 5004;

                string arguments = $"-re -i \"{silencePath}\" -acodec copy -f rtp rtp://{multicastAddress}:{port}";

                Process flushProcess = new Process();
                flushProcess.StartInfo.FileName = ffmpegPath;
                flushProcess.StartInfo.Arguments = arguments;
                flushProcess.StartInfo.UseShellExecute = false;
                flushProcess.StartInfo.CreateNoWindow = true;
                flushProcess.Start();

                // 최대 2초 내 자동 종료되도록 대기
                flushProcess.WaitForExit(2000);
                flushProcess.Close();
            }
            catch (Exception ex)
            {
                File.AppendAllText("ffmpeg_debug.txt", $"[FLUSH_EXCEPTION] {ex.Message}\n");
            }
        }
        private void RadioMode_CheckedChanged(object sender, EventArgs e)
        {
            if (rbStreamYoutube.Checked)
            {
                panelYoutubeControls.Visible = true;
                ytStatus.Text = "YouTube 스트리밍 모드 선택됨";
                StreamStatus.Text = "YouTube 스트리밍 모드 선택됨";
            }
            else if (rbStreamMusic.Checked)
            {
                panelYoutubeControls.Visible = false;
                ytStatus.Text = "음원 스트리밍 모드 선택됨";
                StreamStatus.Text = "음원 스트리밍 모드 선택됨";
            }
            else if (rbStreamMic.Checked)
            {
                panelYoutubeControls.Visible = false;
                ytStatus.Text = "마이크 스트리밍 모드 선택됨";
                StreamStatus.Text = "마이크 스트리밍 모드 선택됨";
            }
        }
        private void StartYoutubeStreaming()
        {
            string youtubeUrl = txtYoutubeUrl.Text.Trim();

            if (string.IsNullOrEmpty(youtubeUrl))
            {
                MessageBox.Show("유튜브 주소를 입력하거나 선택하세요.");
                WriteLog("유튜브 주소를 입력하거나 선택하세요.");
                return;
            }

            lastYoutubeUrl = youtubeUrl;
            isYoutubeRepeating = true;
            ytStatus.Text = "";
            StreamProgressBar.Visible = true;
            StreamProgressBar.Style = ProgressBarStyle.Marquee;

            Task.Run(() =>
            {
                StreamYoutubeAudio(youtubeUrl);
                this.Invoke(new Action(() =>
                {
                    StreamProgressBar.Visible = false;
                    ytStatus.Text = "스트리밍 완료";
                }));
            });
        }
        private void radioFile_CheckedChanged(object sender, EventArgs e)
        {
            if (rbStreamMusic.Checked)
            {
                // 유튜브 스트리밍 상태 초기화
                isYoutubeRepeating = false;
                lastYoutubeUrl = null;
                ytStatus.Text = "";
                StreamStatus.Text = "파일 스트리밍 모드 선택됨";
                StreamProgressBar.Visible = false;
            }
        }
        private void radioMic_CheckedChanged(object sender, EventArgs e)
        {
            if (rbStreamMic.Checked)
            {
                isYoutubeRepeating = false;
                lastYoutubeUrl = null;
                ytStatus.Text = "";
                StreamStatus.Text = "마이크 스트리밍 모드 선택됨";
                StreamProgressBar.Visible = false;
            }
        }

        private void StreamFromFile()
        {
            try
            {
                // 기존 ffmpeg 종료
                if (ffmpegProcess != null)
                {
                    try
                    {
                        if (!ffmpegProcess.HasExited)
                        {
                            ffmpegProcess.Kill();
                            ffmpegProcess.WaitForExit();
                        }
                        ffmpegProcess.Dispose();
                    }
                    catch (Exception ex)
                    {
                        MessageBox.Show("기존 FFmpeg 종료 오류:\n" + ex.Message);
                        WriteLog("기존 FFmpeg 종료 오류:\n" + ex.Message);
                    }
                    finally
                    {
                        ffmpegProcess = null;
                    }
                }

                string musicFolder = Path.Combine(Application.StartupPath, "Music");
                var mp3Files = Directory.GetFiles(musicFolder, "*.mp3").OrderBy(f => f).ToList();

                if (mp3Files.Count == 0)
                {
                    MessageBox.Show("Music 폴더에 MP3 파일이 없습니다.");
                    WriteLog("Music 폴더에 MP3 파일이 없습니다.");
                    return;
                }

                string playlistPath = Path.Combine(musicFolder, "playlist.txt");

                using (StreamWriter writer = new StreamWriter(playlistPath, false, new UTF8Encoding(false)))
                {
                    if (chkRepeatMusic.Checked)
                    {
                        int repeatCount = (int)numRepeatCount.Value;
                        for (int i = 0; i < repeatCount; i++)
                        {
                            foreach (string file in mp3Files)
                                writer.WriteLine($"file '{file.Replace("\\", "\\\\")}'");
                        }
                    }
                    else
                    {
                        foreach (string file in mp3Files)
                            writer.WriteLine($"file '{file.Replace("\\", "\\\\")}'");
                    }
                }

                string arguments = $"-re -f concat -safe 0 -i \"{playlistPath}\" " +
                                   $"-acodec libmp3lame -b:a 128k -f rtp rtp://{multicastAddress}:{port}";

                ffmpegProcess = new Process();
                ffmpegProcess.StartInfo.FileName = ffmpegPath;
                ffmpegProcess.StartInfo.Arguments = arguments;
                ffmpegProcess.StartInfo.UseShellExecute = false;
                ffmpegProcess.StartInfo.RedirectStandardOutput = true;
                ffmpegProcess.StartInfo.RedirectStandardError = true;
                ffmpegProcess.StartInfo.StandardErrorEncoding = Encoding.UTF8;
                ffmpegProcess.StartInfo.CreateNoWindow = true;
                ffmpegProcess.EnableRaisingEvents = true;

                // ✅ 로그 파일 오픈 (StreamWriter 사용)
                string logPath = Path.Combine(Application.StartupPath, "ffmpeg_debug.txt");
                ffmpegLogWriter = new StreamWriter(logPath, true, Encoding.UTF8);
                ffmpegLogWriter.AutoFlush = true;

                ffmpegProcess.OutputDataReceived += (s, e) =>
                {
                    if (!string.IsNullOrEmpty(e.Data))
                    {
                        lock (debugFileLock)
                        {
                            ffmpegLogWriter?.WriteLine("[stdout] " + e.Data);
                        }
                    }
                };

                ffmpegProcess.ErrorDataReceived += (s, e) =>
                {
                    if (!string.IsNullOrEmpty(e.Data))
                    {
                        lock (debugFileLock)
                        {
                            ffmpegLogWriter?.WriteLine("[stderr] " + e.Data);
                        }

                        // bitrate 로그 포함 시 상태 업데이트
                        if (e.Data.Contains("bitrate") || e.Data.Contains("frame="))
                        {
                            this.Invoke((MethodInvoker)(() =>
                            {
                                ytStatus.Text = "음원 스트리밍 중...";
                                StreamStatus.Text = "음원 스트리밍 중...";
                            }));
                        }
                    }
                };

                ffmpegProcess.Start();
                ffmpegProcess.BeginOutputReadLine();
                ffmpegProcess.BeginErrorReadLine();

                this.Invoke(new Action(() =>
                {
                    ytStatus.Text = "음원 스트리밍 시작";
                    StreamStatus.Text = "음원 스트리밍 중...";
                    StreamProgressBar.Style = ProgressBarStyle.Marquee;
                    StreamProgressBar.MarqueeAnimationSpeed = 100;
                    StreamProgressBar.Visible = true;
                    WriteLog("음원 스트리밍 시작됨");
                }));
            }
            catch (Exception ex)
            {
                this.Invoke(new Action(() =>
                {
                    ytStatus.Text = "음원 스트리밍 오류";
                    MessageBox.Show("음원 스트리밍 오류:\n\n" + ex.Message);
                    WriteLog("음원 스트리밍 오류:\n\n" + ex.Message);
                }));

                lock (debugFileLock)
                {
                    ffmpegLogWriter?.WriteLine($"[MUSIC_EXCEPTION] {ex.Message}");
                }
            }
        }

        private void StreamFromMic()
        {
            try
            {
                string micDevicePath = Path.Combine(Application.StartupPath, "selected_mic_device.txt");
                if (!File.Exists(micDevicePath))
                {
                    MessageBox.Show("선택된 마이크 장치가 없습니다.");
                    WriteLog("선택된 마이크 장치가 없습니다.");
                    return;
                }

                string micDevice = File.ReadAllText(micDevicePath).Trim();

                string multicastAddress = "239.255.0.1";
                int port = 5004;
                string sdpPath = Path.Combine(Application.StartupPath, "mic_stream.sdp");
                string ffmpegPath = Path.Combine(Application.StartupPath, "lib", "ffmpeg.exe");

                string arguments = $"-f dshow -i audio=\"{micDevice}\" " +
                                   $"-acodec libmp3lame -ab 128k -f rtp rtp://{multicastAddress}:{port} -sdp_file \"{sdpPath}\"";

                ffmpegProcess = new Process();
                ffmpegProcess.StartInfo.FileName = ffmpegPath;
                ffmpegProcess.StartInfo.Arguments = arguments;
                ffmpegProcess.StartInfo.UseShellExecute = false;
                ffmpegProcess.StartInfo.RedirectStandardOutput = true;
                ffmpegProcess.StartInfo.RedirectStandardError = true;
                ffmpegProcess.StartInfo.StandardErrorEncoding = Encoding.UTF8;
                ffmpegProcess.StartInfo.CreateNoWindow = true;
                ffmpegProcess.EnableRaisingEvents = true;

                ffmpegProcess.OutputDataReceived += (s, e) =>
                {
                    if (!string.IsNullOrEmpty(e.Data))
                    {
                        File.AppendAllText("ffmpeg_debug.txt", "[stdout] " + e.Data + Environment.NewLine);
                    }
                };

                ffmpegProcess.ErrorDataReceived += (s, e) =>
                {
                    if (!string.IsNullOrEmpty(e.Data))
                    {
                        File.AppendAllText("ffmpeg_debug.txt", "[stderr] " + e.Data + Environment.NewLine);

                        if (e.Data.Contains("bitrate"))
                        {
                            this.Invoke((MethodInvoker)(() =>
                            {
                                StreamStatus.Text = "스트리밍 중...";
                            }));
                        }
                    }
                };

                ffmpegProcess.Start();
                ffmpegProcess.BeginOutputReadLine();
                ffmpegProcess.BeginErrorReadLine();

                this.Invoke(new Action(() =>
                {
                    ytStatus.Text = "마이크 스트리밍 시작";
                    StreamStatus.Text = "마이크 스트리밍 중...";
                    StreamProgressBar.Style = ProgressBarStyle.Marquee;
                    StreamProgressBar.MarqueeAnimationSpeed = 100;
                    StreamProgressBar.Visible = true;
                    WriteLog("마이크 스트리밍 시작");
                }));
            }
            catch (Exception ex)
            {
                this.Invoke(new Action(() =>
                {
                    ytStatus.Text = "마이크 스트리밍 오류";
                    MessageBox.Show("마이크 스트리밍 오류:\n\n" + ex.Message);
                    WriteLog("마이크 스트리밍 오류:\n\n" + ex.Message);
                }));
                File.AppendAllText("ffmpeg_debug.txt", $"[MIC_EXCEPTION] {ex.Message}\n");
            }
        }
        // BGM 제어
        private bool SendBGMCommand(string ip, string command, int timeoutMs = 1200, bool waitAck = true)
        {
            try
            {
                using (var client = new TcpClient())
                {
                    var connectTask = client.ConnectAsync(ip, 39999);
                    if (!connectTask.Wait(timeoutMs)) { WriteLog($"[BGM:{command}] {ip} 연결 타임아웃"); return false; }

                    client.NoDelay = true; // ★ Nagle 비활성화 — 즉시 전송
                    client.ReceiveTimeout = timeoutMs;
                    client.SendTimeout = timeoutMs;

                    using (var stream = client.GetStream())
                    using (var writer = new StreamWriter(stream, Encoding.UTF8) { AutoFlush = true, NewLine = "\n" })
                    using (var reader = new StreamReader(stream, Encoding.UTF8, detectEncodingFromByteOrderMarks: false, bufferSize: 1024, leaveOpen: true))
                    {
                        writer.WriteLine(command); // "\n" 보장
                        WriteLog($"[BGM:{command}] → {ip}");

                        if (waitAck)
                        {
                            // 스피커가 "OK" / "DONE" / "STOPPED" 등 간단한 응답을 준다면 확인
                            // 모르면 한 줄만 읽고 로깅(타임아웃 시 예외)
                            try
                            {
                                var sw = Stopwatch.StartNew();
                                while (sw.ElapsedMilliseconds < timeoutMs)
                                {
                                    if (stream.DataAvailable)
                                    {
                                        var line = reader.ReadLine();
                                        WriteLog($"[BGM:{command}] {ip} ack='{line}'");
                                        break;
                                    }
                                    Thread.Sleep(50);
                                }
                            }
                            catch (Exception ex)
                            {
                                WriteLog($"[BGM:{command}] {ip} ack 수신 실패: {ex.Message}");
                            }
                        }
                    }
                }
                return true;
            }
            catch (Exception ex)
            {
                WriteLog($"[BGM:{command}] {ip} 실패: {ex.Message}");
                return false;
            }
        }

        private async void btnBGMStart_Click(object sender, EventArgs e)
        {
            btnBGMStart.Enabled = false;
            WriteLog("🔊 BGM 시작 버튼 클릭됨");

            // ⬇️ UI를 먼저 갱신해 즉시 리페인트되게 함
            lblBgmStatus.Text = "BGM 시작 중...";
            BGMprogressBar.Style = ProgressBarStyle.Marquee;
            BGMprogressBar.Visible = true;

            try
            {
                // ⬇️ 한 틱 양보 → 버튼 눌림상태가 바로 풀림
                await Task.Yield();

                var onlineIPs = await GetOnlineSpeakersForStreamAsync();

                if (onlineIPs.Count == 0)
                {
                    MessageBox.Show("온라인 상태인 스피커가 없습니다.\nBGM 전송이 취소됩니다.");
                    lblBgmStatus.Text = "BGM 대기";
                    BGMprogressBar.Visible = false; // 취소 시만 숨김
                    return;
                }

                // ⬇️ 동기 전송이라면 병렬 처리
                await Task.WhenAll(onlineIPs.Select(ip => Task.Run(() => SendBGMCommand(ip, "bgm_start"))));

                lblBgmStatus.Text = "BGM 시작됨";
                // 기존 동작 유지: 시작 후에도 Marquee + Visible 유지
                WriteLog($"BGM 스트리밍 명령 전송 완료 (온라인 수: {onlineIPs.Count})");
                bgmStartedByAuto = true;
            }
            catch (Exception ex)
            {
                WriteLog($"[BGM 시작 오류] {ex}");
                lblBgmStatus.Text = "BGM 시작 실패";
                BGMprogressBar.Visible = false;
            }
            finally
            {
                btnBGMStart.Enabled = true;
            }
        }

        private async void btnBGMStop_Click(object sender, EventArgs e)
        {
            btnBGMStop.Enabled = false;
            WriteLog("⛔ BGM 정지 버튼 클릭됨");

            // ⬇️ UI를 먼저 갱신 (기존 동작 유지)
            lblBgmStatus.Text = "BGM 정지 중...";
            BGMprogressBar.Style = ProgressBarStyle.Continuous;
            BGMprogressBar.Value = 0;
            BGMprogressBar.Visible = true;

            try
            {
                // ⬇️ 한 틱 양보 → 버튼 눌림상태가 바로 풀림
                await Task.Yield();

                var onlineIPs = await GetOnlineSpeakersForStreamAsync();

                if (onlineIPs.Count == 0)
                {
                    MessageBox.Show("온라인 상태인 스피커가 없습니다.\n정지 명령이 취소됩니다.");
                    lblBgmStatus.Text = "BGM 대기";
                    // 정지 취소 시에도 기존과 충돌 없도록 숨김
                    BGMprogressBar.Visible = false;
                    return;
                }

                await Task.WhenAll(onlineIPs.Select(ip => Task.Run(() => SendBGMCommand(ip, "bgm_stop"))));

                lblBgmStatus.Text = "BGM 정지됨";
                // 기존 동작 유지: Style=Continuous, Value=0, Visible=true
                WriteLog($"BGM 정지 명령 전송 완료 (온라인 수: {onlineIPs.Count})");
                bgmStartedByAuto = false;  // 수동 정지 시 자동 시작 상태 해제
            }
            catch (Exception ex)
            {
                WriteLog($"[BGM 정지 오류] {ex}");
                lblBgmStatus.Text = "BGM 정지 실패";
                BGMprogressBar.Visible = false;
            }
            finally
            {
                btnBGMStop.Enabled = true;
            }
        }

        private async Task<List<string>> GetOnlineSpeakersForStreamAsync()
        {
            var onlineIPs = new List<string>();
            var tasks = new List<Task>();

            foreach (DataGridViewRow row in dgvSpeakersStream.Rows)
            {
                if (Convert.ToBoolean(row.Cells["Select"].Value))
                {
                    string ip = row.Cells["IP"].Value?.ToString();
                    if (string.IsNullOrWhiteSpace(ip)) continue;

                    tasks.Add(Task.Run(() =>
                    {
                        if (TryConnectWithTimeout(ip, 8787, 500))
                        {
                            lock (onlineIPs) onlineIPs.Add(ip);
                        }
                        else
                        {
                            // 체크 해제는 UI 스레드에서
                            this.Invoke((MethodInvoker)(() =>
                            {
                                row.Cells["Select"].Value = false;
                            }));
                        }
                    }));
                }
            }

            await Task.WhenAll(tasks);
            return onlineIPs;
        }


        private async void timerBgmAuto_Tick(object sender, EventArgs e)
        {
            DateTime now = DateTime.Now;

            // 🔸 자동 시작 조건
            if (chkBgmAutoOn.Checked && !bgmStartedByAuto)
            {
                DateTime startTime = dtpBgmAutoOnTime.Value;
                if (now.Hour == startTime.Hour && now.Minute == startTime.Minute && now.Second == 0)
                {
                    // 1) 먼저 스트리밍 시작 (기존 [스트리밍 시작] 버튼 로직 재사용)
                    WriteLog("⏱ 자동 BGM 시작 시각 도달 → [스트리밍 시작] 실행");
                    // sender는 의미 없으니 null 또는 btnStartStream 아무거나 전달해도 됩니다.
                    btnStartStream_Click(btnStartStream, EventArgs.Empty);

                    // 2) 스트림 안정화 대기 (약 10초)
                    await Task.Delay(10000);

                    // 3) 현재 온라인 스피커 재확인 후 BGM 시작
                    var onlineIPs = await GetOnlineSpeakersForStreamAsync();

                    var selectedIPs = new List<string>();

                    dgvSpeakersStream.SuspendLayout();
                    foreach (DataGridViewRow row in dgvSpeakersStream.Rows)
                    {
                        if (Convert.ToBoolean(row.Cells["Select"].Value))
                        {
                            string ip = row.Cells["IP"].Value?.ToString();
                            if (!string.IsNullOrEmpty(ip))
                            {
                                if (onlineIPs.Contains(ip))
                                {
                                    selectedIPs.Add(ip);
                                }
                                else
                                {
                                    // 오프라인이면 체크 해제
                                    row.Cells["Select"].Value = false;
                                    dgvSpeakersStream.Refresh();
                                    WriteLog($"❌ 오프라인 스피커 체크 해제됨: {ip}");
                                }
                            }
                        }
                    }
                    dgvSpeakersStream.ResumeLayout();

                    if (selectedIPs.Count == 0)
                    {
                        // 스트림만 켜져 있고 실제로 BGM을 보낼 온라인 스피커는 없는 경우
                        WriteLog("⚠️ 자동 시작할 온라인 스피커가 없습니다. (스트림만 켜진 상태)");
                        return;
                    }

                    foreach (string ip in selectedIPs)
                    {
                        SendBGMCommand(ip, "bgm_start");
                    }

                    bgmStartedByAuto = true;
                    lblBgmStatus.Text = "BGM 시작됨";
                    BGMprogressBar.Style = ProgressBarStyle.Marquee;
                    BGMprogressBar.Visible = true;
                    WriteLog($"🟢 자동 BGM 시작 완료 (대상 수: {selectedIPs.Count})");
                }
            }

            // 🔸 자동 종료 조건
            if (chkBgmAutoOff.Checked && bgmStartedByAuto)
            {
                DateTime offTime = dtpBgmOffTime.Value;
                if (now.Hour == offTime.Hour && now.Minute == offTime.Minute && now.Second == 0)
                {
                    var onlineIPs = await GetOnlineSpeakersForStreamAsync();

                    foreach (string ip in onlineIPs)
                    {
                        SendBGMCommand(ip, "bgm_stop");
                    }

                    bgmStartedByAuto = false;
                    lblBgmStatus.Text = "BGM 종료됨";
                    BGMprogressBar.Style = ProgressBarStyle.Continuous;
                    BGMprogressBar.Value = 0;
                    BGMprogressBar.Visible = false;

                    WriteLog($"🔴 자동 BGM 종료됨 (대상 수: {onlineIPs.Count})");

                    // ✅ BGM 자동종료 후 즉시 스트리밍 완전 정지
                    WriteLog("⛔ 자동 BGM 종료 후 [스트리밍 정지] 실행");
                    btnStopStream_Click(btnStopStream, EventArgs.Empty);
                }
            }
        }


        private void chkBgmAutoOn_CheckedChanged(object sender, EventArgs e)
        {
            isBgmAutoOnChecked = chkBgmAutoOn.Checked;
        }

        private void chkBgmAutoOff_CheckedChanged(object sender, EventArgs e)
        {
            isBgmAutoOffChecked = chkBgmAutoOff.Checked;
            ArmAutoStop(); // 설정이 바뀌면 즉시 재예약
        }
        private void dtpBgmOffTime_ValueChanged(object sender, EventArgs e)
        {
            ArmAutoStop();
        }

        //예약방송
        private async Task<List<string>> FilterOnlineIPsAsync(List<string> ipList)
        {
            var onlineIPs = new List<string>();
            var tasks = new List<Task>();

            foreach (var ip in ipList)
            {
                tasks.Add(Task.Run(() =>
                {
                    if (IsSpeakerOnline(ip))
                    {
                        lock (onlineIPs)
                        {
                            onlineIPs.Add(ip);
                        }
                    }
                }));
            }

            await Task.WhenAll(tasks);
            return onlineIPs;
        }
        private bool IsSpeakerOnline(string ip, int port = 8787, int timeoutMs = 1000)
        {
            try
            {
                using (var client = new TcpClient())
                {
                    var result = client.BeginConnect(ip, port, null, null);
                    bool success = result.AsyncWaitHandle.WaitOne(timeoutMs);
                    if (!success) return false;
                    client.EndConnect(result);
                    return true;
                }
            }
            catch
            {
                return false;
            }
        }

        private void LoadSpeakersForSchedule()
        {
            string filePath = Path.Combine(Application.StartupPath, "speakers.txt");

            if (!File.Exists(filePath))
            {
                MessageBox.Show("speakers.txt 파일이 없습니다.");
                WriteLog("speakers.txt 파일이 없습니다.");
                return;
            }

            dgvSpeakersSchedule.Rows.Clear();

            var lines = File.ReadAllLines(filePath);
            foreach (var line in lines)
            {
                string[] parts = line.Split('|');
                if (parts.Length < 4) continue;

                int rowIndex = dgvSpeakersSchedule.Rows.Add();
                DataGridViewRow row = dgvSpeakersSchedule.Rows[rowIndex];

                row.Cells["Select_SCH"].Value = false;
                row.Cells["IP_SCH"].Value = parts[0];
                row.Cells["SIP_SCH"].Value = parts[1];
                row.Cells["Location_SCH"].Value = parts[2];

                string group = parts[3].Trim();

                row.Cells["Group_SCH"].Value = group;  // ✅ 그룹 컬럼 표시
                row.Tag = group;                       // ✅ 그룹 필터용 (유지)
            }
        }
        private void cmbGroupSelectSchedule_SelectionChangeCommitted(object sender, EventArgs e)
        {
            string selectedGroup = cmbGroupSelectSchedule.SelectedItem?.ToString()?.Trim();
            if (string.IsNullOrWhiteSpace(selectedGroup)) return;

            isApplyingGroupSelection = true;
            try
            {
                foreach (DataGridViewRow row in dgvSpeakersSchedule.Rows)
                {
                    if (row.IsNewRow) continue;

                    string group = row.Tag?.ToString()?.Trim();
                    bool match = string.Equals(group, selectedGroup, StringComparison.OrdinalIgnoreCase);

                    row.Cells["Select_SCH"].Value = match;   // ✅ 핵심
                }
            }
            finally
            {
                isApplyingGroupSelection = false;
            }

            dgvSpeakersSchedule.RefreshEdit();
        }
        private void LoadGroupsForSchedule()
        {
            string filePath = Path.Combine(Application.StartupPath, "speakers.txt");

            if (!File.Exists(filePath))
            {
                MessageBox.Show("speakers.txt 파일이 없습니다.");
                WriteLog("speakers.txt 파일이 없습니다.");
                return;
            }

            HashSet<string> groupSet = new HashSet<string>();

            var lines = File.ReadAllLines(filePath);
            foreach (var line in lines)
            {
                string[] parts = line.Split('|');
                if (parts.Length >= 4)
                {
                    var g = (parts[3] ?? "").Trim();
                    if (!string.IsNullOrWhiteSpace(g))
                        groupSet.Add(g);
                }
            }

            // ✅ 이벤트 연쇄 방지(선택사항이지만 안전)
            cmbGroupSelectSchedule.SelectionChangeCommitted -= cmbGroupSelectSchedule_SelectionChangeCommitted;

            cmbGroupSelectSchedule.Items.Clear();
            foreach (string group in groupSet.OrderBy(g => g))
                cmbGroupSelectSchedule.Items.Add(group);

            // ✅ 처음에는 아무 그룹도 선택하지 않음
            cmbGroupSelectSchedule.SelectedIndex = -1;
            cmbGroupSelectSchedule.Text = ""; // DropDownList가 아니면 표시 정리용

            cmbGroupSelectSchedule.SelectionChangeCommitted += cmbGroupSelectSchedule_SelectionChangeCommitted;
        }
        // 음원파일(멘트)읽기
        private void LoadMentSCHSoundFiles()
        {
            string mentFolderPath = Path.Combine(Application.StartupPath, "Ment");

            // 폴더가 없으면 생성
            if (!Directory.Exists(mentFolderPath))
            {
                Directory.CreateDirectory(mentFolderPath);
            }

            txtFolderPathMent.Items.Clear();

            var mp3Files = Directory.GetFiles(mentFolderPath, "*.mp3");

            foreach (var file in mp3Files)
            {
                string fileName = Path.GetFileName(file);

                // all_with_silence.mp3는 제외
                if (fileName.Equals("all_with_silence.mp3", StringComparison.OrdinalIgnoreCase))
                    continue;

                txtFolderPathMent.Items.Add(fileName);
            }
        }
        private void btnSaveSchedule_Click(object sender, EventArgs e)
        {
            // 1. 요일 선택
            string selectedDay = cmbDayOfWeek.SelectedItem?.ToString();
            if (string.IsNullOrEmpty(selectedDay))
            {
                MessageBox.Show("요일을 선택하세요.");
                return;
            }

            // 2. 시간 선택
            string selectedTime = dateTimePickerSchedule.Value.ToString("HH:mm");

            // 3. 음원 선택
            if (txtFolderPathMent.SelectedItem == null)
            {
                MessageBox.Show("음원 파일을 선택하세요.");
                return;
            }
            string selectedSound = txtFolderPathMent.SelectedItem.ToString();

            // 4. 예외 날짜 리스트
            List<string> excludeDates = new List<string>();
            foreach (var item in lstExcludeDates.Items)
            {
                excludeDates.Add(item.ToString());
            }

            // 5. 매일 여부 확인
            string repeatFlag = (selectedDay == "매일") ? "Y" : "N";

            bool added = false;

            // 6. 그룹 선택 확인
            string selectedGroup = cmbGroupSelectSchedule.SelectedItem?.ToString();
            if (!string.IsNullOrEmpty(selectedGroup))
            {
                dgvScheduleList.Rows.Add(
                    selectedDay,
                    selectedTime,
                    repeatFlag,
                    selectedSound,
                    "그룹",
                    selectedGroup,
                    string.Join(",", excludeDates)
                );
                added = true;
                MessageBox.Show("예약이 저장되었습니다. (그룹)");
                WriteLog("예약이 저장되었습니다. (그룹)");
            }
            else
            {
                // 7. 개별 스피커 선택 확인
                List<string> selectedIPs = new List<string>();
                foreach (DataGridViewRow row in dgvSpeakersSchedule.Rows)
                {
                    bool isChecked = Convert.ToBoolean(row.Cells["Select_SCH"].Value);
                    if (isChecked)
                    {
                        string ip = row.Cells["IP_SCH"].Value?.ToString();
                        if (!string.IsNullOrEmpty(ip))
                            selectedIPs.Add(ip);
                    }
                }

                if (selectedIPs.Count == 0)
                {
                    MessageBox.Show("대상 스피커를 선택하세요.");
                    return;
                }

                dgvScheduleList.Rows.Add(
                    selectedDay,
                    selectedTime,
                    repeatFlag,
                    selectedSound,
                    "개별",
                    string.Join(",", selectedIPs),
                    string.Join(",", excludeDates)
                );
                added = true;
                MessageBox.Show("예약이 저장되었습니다. (개별)");
                WriteLog("예약이 저장되었습니다. (개별)");
            }

            // ✅ 공통 저장 처리
            if (added)
                SaveScheduleToFile();
        }
        private readonly HashSet<string> alreadyPlayedSchedule = new HashSet<string>();
        // 1분 전 사전 업로드 상태 관리
        private readonly System.Collections.Concurrent.ConcurrentDictionary<string, bool> _preUploadDone
            = new System.Collections.Concurrent.ConcurrentDictionary<string, bool>();

        // 사전 업로드 성공 IP 목록 보관 (키: 스케줄 키)
        private readonly System.Collections.Concurrent.ConcurrentDictionary<string, System.Collections.Generic.List<string>> _preUploadSuccess
            = new System.Collections.Concurrent.ConcurrentDictionary<string, System.Collections.Generic.List<string>>();
        private async void timerSchedule_Tick(object sender, EventArgs e)
        {
            DateTime now = DateTime.Now;
            string today = now.ToString("yyyy-MM-dd");
            string currentDay = now.ToString("ddd", new System.Globalization.CultureInfo("ko-KR")); // 예: 월, 화
            string currentTime = now.ToString("HH:mm");

            lblScheduleTime.Text = now.ToString("M월 dd일 (ddd) HH:mm:ss");

            foreach (DataGridViewRow row in dgvScheduleList.Rows)
            {
                string day = row.Cells["colDay"].Value?.ToString();
                string time = row.Cells["colTime"].Value?.ToString();
                string repeat = row.Cells["colRepeat"].Value?.ToString();
                string sound = row.Cells["colSound"].Value?.ToString();
                string targetType = row.Cells["colType"].Value?.ToString()?.Trim();
                string targets = row.Cells["colTarget"].Value?.ToString();
                string excludes = row.Cells["colExclude"].Value?.ToString();

                if (string.IsNullOrEmpty(day) || string.IsNullOrEmpty(time) || string.IsNullOrEmpty(sound))
                    continue;

                // ========== A) 1분 전 강조 처리(그림 효과) ==========
                bool highlight = false;
                if (TimeSpan.TryParse(time, out TimeSpan scheduleTime))
                {
                    TimeSpan nowTime = now.TimeOfDay;
                    TimeSpan diff = scheduleTime - nowTime;
                    highlight = (diff.TotalMinutes >= 0 && diff.TotalMinutes < 1);

                    foreach (DataGridViewCell cell in row.Cells)
                    {
                        if (highlight)
                        {
                            cell.Style.BackColor = Color.Red;
                            cell.Style.ForeColor = Color.White;
                            cell.Style.SelectionBackColor = Color.Red;
                            cell.Style.SelectionForeColor = Color.White;
                        }
                        else
                        {
                            cell.Style.BackColor = Color.White;
                            cell.Style.ForeColor = Color.Black;
                            cell.Style.SelectionBackColor = Color.White;
                            cell.Style.SelectionForeColor = Color.Black;
                        }
                    }
                }

                // ========== B) 예외 날짜 필터 ==========
                if (!string.IsNullOrEmpty(excludes))
                {
                    var excludeList = excludes.Split(',');
                    if (excludeList.Contains(today))
                        continue;
                }

                string excludeFile = "exclude_dates.txt";
                if (File.Exists(excludeFile))
                {
                    var excludedDates = File.ReadAllLines(excludeFile)
                        .Select(line => line.Trim())
                        .Where(line => !string.IsNullOrWhiteSpace(line))
                        .ToHashSet();
                    if (excludedDates.Contains(today))
                    {
                        Debug.WriteLine($"[예약 무시] 오늘은 예외 날짜 {today}입니다.");
                        return; // 시간 표시는 유지
                    }
                }

                // ========== C) 대상 IP 목록 구성 (개별/그룹) ==========
                var ipList = new List<string>();
                if (targetType == "개별")
                {
                    ipList = (targets ?? string.Empty)
                        .Split(new[] { ',', '\x1F' }, StringSplitOptions.RemoveEmptyEntries)
                        .Select(ip => ip.Trim())
                        .ToList();
                }
                else if (targetType == "그룹")
                {
                    string groupFile = "sip_groups.txt";
                    if (File.Exists(groupFile))
                    {
                        var groupLines = File.ReadAllLines(groupFile);
                        foreach (var line in groupLines)
                        {
                            var parts = line.Split(',');
                            if (parts.Length > 1 && parts[0].Trim() == (targets ?? string.Empty).Trim())
                            {
                                ipList.AddRange(parts.Skip(1).Select(p => p.Trim()));
                                break;
                            }
                        }
                    }
                }

                // 파일 경로 미리 확인
                string filePath = Path.Combine(Application.StartupPath, "Ment", sound);
                if (!File.Exists(filePath))
                    continue; // 준비 안 된 항목은 건너뜀

                // 스케줄 키(사전 업로드/송출 모두 같은 키로 관리)
                string scheduleKey = $"{today}-{day}-{time}-{sound}-{targets}";

                // ========== D) 1분 전(강조중)일 때: "사전 업로드" 단 한 번 실행 ==========
                if (highlight)
                {
                    // 같은 스케줄에 대해 사전 업로드를 한 번만 수행
                    if (!_preUploadDone.ContainsKey(scheduleKey))
                    {
                        _preUploadDone[scheduleKey] = true; // 마킹 (중복 방지)

                        // 1) 온라인 필터
                        var onlineIPs = await FilterOnlineIPsAsync(ipList);
                        if (onlineIPs.Count == 0)
                        {
                            WriteLog($"[사전업로드 건너뜀] 대상 모두 오프라인: {scheduleKey}");
                        }
                        else
                        {
                            // 2) 업로드(동시성 제한)
                            var successList = new List<string>();
                            var sem = new System.Threading.SemaphoreSlim(5); // 상황 맞게 3~8
                            await Task.WhenAll(onlineIPs.Select(async ip =>
                            {
                                await sem.WaitAsync();
                                try
                                {
                                    bool ok = UploadFileToSpeaker(ip, filePath);
                                    if (ok)
                                    {
                                        lock (successList) successList.Add(ip);
                                        WriteLog($"[사전업로드 성공] {ip} ← {sound}");
                                    }
                                    else
                                    {
                                        WriteLog($"[사전업로드 실패] {ip} ← {sound}");
                                    }
                                }
                                finally
                                {
                                    sem.Release();
                                }
                            }));

                            _preUploadSuccess[scheduleKey] = successList;
                            WriteLog($"[사전업로드 완료] key={scheduleKey}, 성공수={successList.Count}/{onlineIPs.Count}");
                        }
                    }
                }

                // ========== E) 정시(실행 조건) 확인 ==========
                bool shouldRun = (repeat == "Y") ? (time == currentTime)
                                                 : (day == currentDay && time == currentTime);
                if (!shouldRun) continue;

                // 이미 실행된 스케줄은 무시
                if (alreadyPlayedSchedule.Contains(scheduleKey))
                    continue;
                alreadyPlayedSchedule.Add(scheduleKey);

                // ========== F) 방송 송출: 사전업로드 성공 리스트 우선 사용 ==========
                List<string> readyIPs = null;
                if (_preUploadSuccess.TryGetValue(scheduleKey, out var preList) && preList != null && preList.Count > 0)
                {
                    readyIPs = preList;
                    WriteLog($"[예약방송] 사전업로드 성공 리스트 사용: {preList.Count}대");
                }
                else
                {
                    // 사전업로드가 없거나 모두 실패한 경우: 즉시 온라인 필터 후 송출
                    var onlineIPsNow = await FilterOnlineIPsAsync(ipList);
                    if (onlineIPsNow.Count == 0)
                    {
                        WriteLog($"[예약 방송 무시] 모든 스피커가 오프라인 상태 (정시)");
                        continue;
                    }
                    readyIPs = onlineIPsNow;
                    WriteLog($"[예약방송] 사전업로드 미사용: 즉시 송출 대상 {readyIPs.Count}대");
                }

                // 동시 송출 (스피커 측 수정 없이 기존 명령 사용)
                Parallel.ForEach(readyIPs, ip =>
                {
                    try
                    {
                        SendBroadcastCommand(ip, sound);
                        WriteLog($"[예약방송] 시작명령 전송: {ip} ← {sound}");
                    }
                    catch (Exception ex)
                    {
                        WriteLog($"[예외] 시작명령 전송 실패: {ip} ({ex.Message})");
                    }
                });

                // 한 스케줄 처리 후 캐시 정리(선택)
                _preUploadSuccess.TryRemove(scheduleKey, out _);
                _preUploadDone.TryRemove(scheduleKey, out _);
            }

            // ========== G) 자정에는 중복 실행 목록 초기화 ==========
            if (currentTime == "00:00")
            {
                alreadyPlayedSchedule.Clear();
                // 선택: 전날 사전업로드 마크도 정리
                _preUploadSuccess.Clear();
                _preUploadDone.Clear();
            }
        }


        private void InitializeDayOfWeekComboBox()
        {
            cmbDayOfWeek.Items.Clear();
            cmbDayOfWeek.Items.Add("매일");
            cmbDayOfWeek.Items.Add("일");
            cmbDayOfWeek.Items.Add("월");
            cmbDayOfWeek.Items.Add("화");
            cmbDayOfWeek.Items.Add("수");
            cmbDayOfWeek.Items.Add("목");
            cmbDayOfWeek.Items.Add("금");
            cmbDayOfWeek.Items.Add("토");

            cmbDayOfWeek.SelectedIndex = 0; // 기본 선택: "매일"
        }
        private void dgvSpeakersSchedule_CellValueChanged(object sender, DataGridViewCellEventArgs e)
        {
            if (isApplyingGroupSelection) return;  // ✅ 추가(가장 안전)

            if (e.RowIndex < 0) return;
            if (e.ColumnIndex == dgvSpeakersSchedule.Columns["Select_SCH"].Index)
            {
                cmbGroupSelectSchedule.SelectedIndex = -1; // 사용자가 체크를 바꾸면 그룹 모드 해제
            }
        }
        private void cmbGroupSelectSchedule_SelectedIndexChanged(object sender, EventArgs e)
        {

        }
        private void SaveScheduleToFile()
        {
            string filePath = Path.Combine(Application.StartupPath, "schedule.txt");

            using (StreamWriter writer = new StreamWriter(filePath, false, Encoding.UTF8))
            {
                foreach (DataGridViewRow row in dgvScheduleList.Rows)
                {
                    if (!row.IsNewRow)
                    {
                        List<string> values = new List<string>();
                        for (int i = 0; i < dgvScheduleList.Columns.Count; i++)
                        {
                            string cellValue = row.Cells[i].Value?.ToString() ?? "";
                            values.Add(cellValue.Replace(",", "␟"));  // 쉼표 충돌 방지
                        }
                        writer.WriteLine(string.Join(",", values));
                    }
                }
            }

            //MessageBox.Show("예약이 schedule.txt에 저장되었습니다.");
        }
        private void LoadScheduleFromFile()
        {
            string filePath = Path.Combine(Application.StartupPath, "schedule.txt");

            if (!File.Exists(filePath)) return;

            dgvScheduleList.Rows.Clear();

            var lines = File.ReadAllLines(filePath);
            foreach (string line in lines)
            {
                if (string.IsNullOrWhiteSpace(line)) continue;

                string[] parts = line.Split(',');
                for (int i = 0; i < parts.Length; i++)
                    parts[i] = parts[i].Replace("␟", ",");

                if (parts.Length >= 7)
                {
                    dgvScheduleList.Rows.Add(
                        parts[0], parts[1], parts[2], parts[3],
                        parts[4], parts[5], parts[6]
                    );
                }
            }
        }
        private void btnSaveScheduleToFile_Click(object sender, EventArgs e)
        {
            SaveScheduleToFile();
        }
        private void btnCheckScheduleDel_Click(object sender, EventArgs e)
        {
            if (dgvScheduleList.SelectedRows.Count == 0)
            {
                MessageBox.Show("삭제할 예약 항목을 선택하세요.");
                return;
            }

            foreach (DataGridViewRow row in dgvScheduleList.SelectedRows)
            {
                if (!row.IsNewRow)
                {
                    dgvScheduleList.Rows.Remove(row);
                }
            }

            SaveScheduleToFile();  // 삭제 후 저장
        }
        private void btnCheckScheduleAllDel_Click(object sender, EventArgs e)
        {
            if (dgvScheduleList.Rows.Count == 0)
            {
                MessageBox.Show("삭제할 예약이 없습니다.");
                return;
            }

            var confirm = MessageBox.Show("모든 예약을 삭제하시겠습니까?", "확인", MessageBoxButtons.YesNo, MessageBoxIcon.Warning);
            if (confirm == DialogResult.Yes)
            {
                dgvScheduleList.Rows.Clear();
                SaveScheduleToFile();  // 저장 파일도 갱신
                MessageBox.Show("모든 예약이 삭제되었습니다.");
                WriteLog("모든 예약이 삭제되었습니다.");
            }
        }
        // 제와날짜등록
        private void LoadExcludeDates()
        {
            lstExcludeDates.Items.Clear();
            if (File.Exists(excludeDateFilePath))
            {
                var lines = File.ReadAllLines(excludeDateFilePath);
                foreach (var line in lines)
                {
                    if (!string.IsNullOrWhiteSpace(line))
                        lstExcludeDates.Items.Add(line.Trim());
                }
            }
        }
        private void btnAddExcludeDate_Click(object sender, EventArgs e)
        {
            string selectedDate = dtpExcludeDateSchedule.Value.ToString("yyyy-MM-dd");

            if (!lstExcludeDates.Items.Contains(selectedDate))
            {
                lstExcludeDates.Items.Add(selectedDate);
                File.AppendAllLines(excludeDateFilePath, new[] { selectedDate });
            }
            else
            {
                MessageBox.Show("이미 등록된 날짜입니다.");
            }
        }
        private void btnRemoveExcludeDate_Click(object sender, EventArgs e)
        {
            if (lstExcludeDates.SelectedItem != null)
            {
                string selectedDate = lstExcludeDates.SelectedItem.ToString();
                lstExcludeDates.Items.Remove(selectedDate);

                var updatedDates = lstExcludeDates.Items.Cast<string>().ToList();
                File.WriteAllLines(excludeDateFilePath, updatedDates);
            }
            else
            {
                MessageBox.Show("제거할 날짜를 선택하세요.");
            }
        }


        // 설정 부분
        private void SaveStreamingConfig()
        {
            try
            {
                using (StreamWriter writer = new StreamWriter(configPath, false))
                {
                    writer.WriteLine("auto_bgm_control=" + chkAutoBgmControl.Checked.ToString().ToLower());
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("설정 저장 중 오류 발생: " + ex.Message);
            }
        }
        private void LoadStreamingConfig()
        {
            if (!File.Exists(configPath)) return;

            try
            {
                string[] lines = File.ReadAllLines(configPath);
                foreach (string line in lines)
                {
                    if (line.StartsWith("auto_bgm_control"))
                    {
                        string value = line.Split('=')[1].Trim().ToLower();
                        chkAutoBgmControl.Checked = (value == "true");
                    }
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("설정 불러오기 중 오류 발생: " + ex.Message);
            }
        }
        private void chkAutoBgmControl_CheckedChanged(object sender, EventArgs e)
        {
            SaveStreamingConfig();
        }
        private void InitializeStreamingSettings()
        {
            LoadStreamingConfig();
        }
        private static readonly object logLock = new object();

        private void WriteLog(string message)
        {
            try
            {
                string logEntry = $"[{DateTime.Now:yyyy-MM-dd HH:mm:ss}] {message}";

                lock (logLock)
                {
                    using (var writer = new StreamWriter(logFilePath, true, Encoding.UTF8))
                    {
                        writer.WriteLine(logEntry);
                    }
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("로그 저장 실패: " + ex.Message);
            }
        }

        private void InitLogViewerUi()
        {
            txtLogViewer.ReadOnly = true;
            txtLogViewer.DetectUrls = false;
            txtLogViewer.WordWrap = false; // 긴 줄 렌더링 최적화
        }
        private async void btnViewLog_Click(object sender, EventArgs e)
        {
            const int MAX_BYTES = 2 * 1024 * 1024; // 최근 2MB만 표시 (필요시 5MB로)
            try
            {
                if (!File.Exists(logFilePath))
                {
                    txtLogViewer.Text = "로그 파일이 존재하지 않습니다.";
                    return;
                }

                btnViewLog.Enabled = false;
                _logCts?.Cancel();
                _logCts = new System.Threading.CancellationTokenSource();
                var ct = _logCts.Token;

                string text = await ReadTailAsync(logFilePath, MAX_BYTES, ct);

                if (ct.IsCancellationRequested) return;

                // UI 반영
                if (txtLogViewer.InvokeRequired)
                {
                    txtLogViewer.Invoke(new Action(() =>
                    {
                        ApplyLogText(text);
                    }));
                }
                else
                {
                    ApplyLogText(text);
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("로그 파일 불러오기 오류: " + ex.Message);
            }
            finally
            {
                btnViewLog.Enabled = true;
            }
        }
        private async Task<string> ReadTailAsync(string path, int maxBytes, System.Threading.CancellationToken ct)
        {
            // 공유 읽기 + 비동기 옵션
            using (var fs = new FileStream(
                path,
                FileMode.Open,
                FileAccess.Read,
                FileShare.ReadWrite,
                bufferSize: 4096,
                options: FileOptions.Asynchronous | FileOptions.SequentialScan))
            {
                long len = fs.Length;
                long start = Math.Max(0, len - maxBytes);
                if (start > 0) fs.Seek(start, SeekOrigin.Begin);

                using (var sr = new StreamReader(fs, detectEncodingFromByteOrderMarks: true))
                {
                    string chunk = await sr.ReadToEndAsync();
                    ct.ThrowIfCancellationRequested();

                    // 중간에서 시작했으면 첫 줄은 잘린 줄일 수 있으니 버림
                    if (start > 0)
                    {
                        int idx = chunk.IndexOf('\n');
                        if (idx >= 0 && idx + 1 < chunk.Length)
                            chunk = chunk.Substring(idx + 1);
                    }
                    return chunk;
                }
            }
        }

        // RichTextBox에 빠르게 반영
        private void ApplyLogText(string text)
        {
            txtLogViewer.SuspendLayout();
            try
            {
                txtLogViewer.Clear();
                // AppendText가 Text 할당보다 큰 텍스트에서 빠른 편
                txtLogViewer.AppendText(text);

                // 끝으로 스크롤
                txtLogViewer.SelectionStart = txtLogViewer.TextLength;
                txtLogViewer.ScrollToCaret();
            }
            finally
            {
                txtLogViewer.ResumeLayout();
            }
        }
        // 자동 시작 설정
        private void SaveStartConfig()
        {
            if (isLoadingStartConfig) return;

            List<string> lines = new List<string>
    {
        $"auto_bgm_control={chkAutoBgmControl.Checked.ToString().ToLower()}",
        $"auto_start_bgm={chkBgmAutoOn.Checked.ToString().ToLower()}",
        $"auto_stop_bgm={chkBgmAutoOff.Checked.ToString().ToLower()}",
        $"auto_resume_last_stream={chkAutoResumeLastStream.Checked.ToString().ToLower()}"
    };

            if (rbStreamYoutube.Checked)
            {
                lines.Add("last_stream_type=youtube");
                lines.Add($"last_youtube_url={txtYoutubeUrl.Text.Trim()}");
                lines.Add($"last_youtube_channel={cmbYoutubeList.SelectedItem}");
            }
            else if (rbStreamMusic.Checked)
            {
                lines.Add("last_stream_type=music");
            }
            else if (rbStreamMic.Checked)
            {
                lines.Add("last_stream_type=mic");
            }

            List<string> selectedIPs = new List<string>();
            foreach (DataGridViewRow row in dgvSpeakersStream.Rows)
            {
                if (row.Cells["Select"].Value != null && (bool)row.Cells["Select"].Value)
                    selectedIPs.Add(row.Cells["IP"].Value.ToString());
            }

            lines.Add($"selected_speakers={string.Join(",", selectedIPs)}");

            try
            {
                //    File.WriteAllLines(configPath, lines);
            }
            catch (Exception ex)
            {
                MessageBox.Show("설정 저장 중 오류 발생: " + ex.Message);
            }
        }
        private void timerBgmCheck_Tick(object sender, EventArgs e)
        {
            if (!chkBgmAutoOff.Checked || hasBgmStoppedToday) return;

            TimeSpan now = DateTime.Now.TimeOfDay;
            TimeSpan stopTime = dtpBgmOffTime.Value.TimeOfDay;

            if (Math.Abs((now - stopTime).TotalMinutes) < 1) // 오차 1분 허용
            {
                hasBgmStoppedToday = true;
                AutoStopBGM();
            }
        }
        private void timerMidnightReset_Tick(object sender, EventArgs e)
        {
            if (DateTime.Now.Hour == 0 && DateTime.Now.Minute == 0)
            {
                hasBgmStoppedToday = false;
                WriteLog("🕛 자정 도달 → hasBgmStoppedToday 초기화됨");
            }
        }
        private void LoadStartConfig()
        {
            if (!File.Exists(configPath)) return;
            isLoadingStartConfig = true;

            try
            {
                string[] lines = File.ReadAllLines(configPath);
                foreach (string rawLine in lines)
                {
                    string line = rawLine.Trim();
                    if (string.IsNullOrWhiteSpace(line) || !line.Contains("=")) continue;

                    string[] parts = line.Split(new[] { '=' }, 2);
                    string key = parts[0].Trim();
                    string value = parts[1].Trim();

                    switch (key)
                    {
                        case "auto_bgm_control":
                            chkAutoBgmControl.CheckedChanged -= chkAutoBgmControl_CheckedChanged;
                            chkAutoBgmControl.Checked = value.ToLower() == "true";
                            chkAutoBgmControl.CheckedChanged += chkAutoBgmControl_CheckedChanged;
                            break;

                        case "auto_start_bgm":
                            chkBgmAutoOn.Checked = value.ToLower() == "true";
                            break;

                        case "auto_stop_bgm":
                            chkBgmAutoOff.Checked = value.ToLower() == "true";
                            break;

                        case "bgm_auto_on_time":
                            if (TimeSpan.TryParse(value, out TimeSpan onTime))
                                dtpBgmAutoOnTime.Value = DateTime.Today.Add(onTime);
                            else if (DateTime.TryParse(value, out DateTime onTimeDT))
                                dtpBgmAutoOnTime.Value = onTimeDT;
                            break;

                        case "bgm_auto_off_time":
                            if (TimeSpan.TryParse(value, out TimeSpan offTime))
                                dtpBgmOffTime.Value = DateTime.Today.Add(offTime);
                            else if (DateTime.TryParse(value, out DateTime offTimeDT))
                                dtpBgmOffTime.Value = offTimeDT;
                            break;

                        case "auto_resume_last_stream":
                            chkAutoResumeLastStream.CheckedChanged -= chkAutoResumeLastStream_CheckedChanged;
                            chkAutoResumeLastStream.Checked = value.ToLower() == "true";
                            chkAutoResumeLastStream.CheckedChanged += chkAutoResumeLastStream_CheckedChanged;
                            break;

                        case "last_stream_type":
                            if (value == "youtube") rbStreamYoutube.Checked = true;
                            else if (value == "music") rbStreamMusic.Checked = true;
                            else if (value == "mic") rbStreamMic.Checked = true;
                            break;

                        case "last_youtube_url":
                            txtYoutubeUrl.Text = value;
                            break;

                        case "last_youtube_channel":
                            foreach (var item in cmbYoutubeList.Items)
                            {
                                if (item.ToString() == value)
                                {
                                    cmbYoutubeList.SelectedItem = item;
                                    break;
                                }
                            }
                            break;

                        case "selected_speakers":
                            string[] selected = value.Split(',');
                            foreach (DataGridViewRow row in dgvSpeakersStream.Rows)
                            {
                                try
                                {
                                    string ip = row.Cells["IP"].Value?.ToString();
                                    if (!string.IsNullOrEmpty(ip) && selected.Contains(ip))
                                        row.Cells["Select"].Value = true;
                                }
                                catch { }
                            }
                            break;
                    }
                }
            }
            catch (Exception ex)
            {
                MessageBox.Show("설정 불러오기 중 오류 발생:\n" + ex.Message);
            }

            isLoadingStartConfig = false;

            // 🎯 자동 BGM 시작
            AutoStartBGMIfEnabled();
        }
        // 1회성 로그 헬퍼
        private void WriteLogOnce(string key, string message)
        {
            bool shouldWrite = false;
            lock (_logOnceLock)
            {
                if (!_logOnce.Contains(key))
                {
                    _logOnce.Add(key);
                    shouldWrite = true;
                }
            }
            if (shouldWrite) WriteLog(message);
        }
        private async void AutoStartBGMIfEnabled()
        {
            // 기존 예약 취소 → 중복 스케줄 방지
            _autoBgmCts?.Cancel();
            _autoBgmCts = new CancellationTokenSource();
            var ct = _autoBgmCts.Token;

            await Task.Delay(2000); // 초기 UI 안정화

            if (!chkBgmAutoOn.Checked)
            {
                WriteLogOnce("AutoBGM.Disabled", "⚠️ 자동 BGM 시작 기능 꺼져 있음 ― 실행 안 함");
                return;
            }

            DateTime now = DateTime.Now;
            DateTime onTime = dtpBgmAutoOnTime.Value;
            DateTime offTime = dtpBgmOffTime.Value;

            // 이미 시작 시각이 지났으면 오늘은 스킵 (한 번만 로그)
            if (now > onTime)
            {
                WriteLogOnce("AutoBGM.SkippedToday",
                    $"⏩ 현재 {now:HH:mm:ss}, 시작 예약 {onTime:HH:mm} 이미 지남 → 오늘 자동 시작 건너뜀");
                return;
            }

            // 아직 시간이 안 됐으면 예약만 걸어두기 (한 번만 로그)
            TimeSpan wait = onTime - now;
            WriteLogOnce("AutoBGM.ScheduledStart",
                $"🕒 자동 BGM 시작 예약: {onTime:HH:mm} ( {wait.TotalMinutes:F0}분 후 )");

            _ = Task.Run(async () =>
            {
                try
                {
                    // 예약 대기 중 취소 가능
                    await Task.Delay(wait, ct);
                    if (ct.IsCancellationRequested) return;

                    // UI 스레드에서 실행
                    Invoke((MethodInvoker)(async () =>
                    {
                        // 실제 시작/종료 예약은 기존 로직 그대로
                        await StartBgmOnceAsync();
                        ScheduleAutoStopIfNeeded();
                    }));
                }
                catch (TaskCanceledException)
                {
                    // 예약 취소 시 조용히 종료 (중복 호출 방지용)
                }
            }, ct);
        }
        private async Task StartBgmOnceAsync()
        {
            // 0) 새로 자동으로 BGM을 켜는 순간이므로,
            //    이전 AutoStopBGM 에서 걸어 둔 하드스톱 플래그를 해제
            _bgmHardStopped = false;

            if (bgmStartedByAuto) return;           // 중복 방지

            // 1) 자동 BGM을 켜기 전에 ffmpeg 스트림이 살아 있는지 확인
            try
            {
                bool needStartStream = false;
                var p = ffmpegProcess;

                if (p == null)
                {
                    needStartStream = true;
                }
                else
                {
                    try
                    {
                        if (p.HasExited)
                            needStartStream = true;
                    }
                    catch
                    {
                        // HasExited 조회 중 "이 개체와 연결된 프로세스가 없습니다." 등 예외 발생 시
                        // 이미 종료된 것으로 간주
                        needStartStream = true;
                    }
                }

                if (needStartStream)
                {
                    WriteLog("⚠️ 자동 BGM 시작 시 ffmpeg 프로세스가 없거나 종료 상태라서 스트림을 먼저 다시 시작합니다.");

                    // 기존 스트리밍 시작 버튼 로직 재사용
                    // (async void 이므로 호출만 해 두면 내부에서 비동기로 ffmpeg 를 띄움)
                    btnStartStream_Click(null, EventArgs.Empty);
                }
            }
            catch (Exception ex)
            {
                WriteLog("자동 BGM 시작 전 스트림 상태 확인/재시작 중 예외: " + ex.Message);
            }

            // 2) 온라인 스피커 목록 구성
            var onlineIPs = await GetOnlineSpeakersForStreamAsync();
            var targets = new List<string>();

            foreach (DataGridViewRow row in dgvSpeakersStream.Rows)
            {
                if (Convert.ToBoolean(row.Cells["Select"].Value))
                {
                    string ip = row.Cells["IP"].Value?.ToString();
                    if (!string.IsNullOrWhiteSpace(ip) && onlineIPs.Contains(ip))
                        targets.Add(ip);
                }
            }

            if (targets.Count == 0)
            {
                WriteLog("⚠️ 자동 시작할 온라인 스피커가 없습니다.");
                return;
            }

            // 3) 스피커에 bgm_start 전송
            foreach (var ip in targets)
                SendBGMCommand(ip, "bgm_start");

            // 4) UI/상태 갱신
            bgmStartedByAuto = true;
            lblBgmStatus.Text = "BGM 자동 시작됨";
            BGMprogressBar.Style = ProgressBarStyle.Marquee;
            BGMprogressBar.Visible = true;
            WriteLog($"🟢 자동 BGM 시작 완료 (대상 {targets.Count}대)");
        }


        /* 자동 종료 예약(기존 코드 유지 ‑ 필요한 부분만 분리) */
        private void ScheduleAutoStopIfNeeded()
        {
            if (!chkBgmAutoOff.Checked) return;

            DateTime now = DateTime.Now;
            DateTime offTime = dtpBgmOffTime.Value;
            if (offTime <= now) offTime = offTime.AddDays(1);  // 이미 지나갔으면 내일

            TimeSpan delay = offTime - now;
            WriteLog($"⏱ 자동 종료 예약: {offTime:HH:mm} ( {delay.TotalMinutes:F0}분 후 )");

            _ = Task.Run(async () =>
            {
                await Task.Delay(delay);
                Invoke((MethodInvoker)(() => AutoStopBGM()));
            });
        }
        private async void AutoStopBGM()
        {
            WriteLog("🔴 자동 종료 타이머 도달 → BGM 종료 전송");

            // === 자동 재가동 차단 & 타이머 중단 ===
            _bgmHardStopped = true;          // 이후 자동 재시작/복구 경로 전부 차단
            _streamingExpected = false;      // 워치독 기대 상태 해제
            StopStreamWatchdog();            // 워치독 타이머 정지
            try { youtubeRestartTimer?.Stop(); } catch { } // 1시간 재시작 타이머 정지

            var onlineIPs = await GetOnlineSpeakersForStreamAsync();
            var selectedIPs = new List<string>();

            dgvSpeakersStream.SuspendLayout();

            foreach (DataGridViewRow row in dgvSpeakersStream.Rows)
            {
                if (row.Cells["Select"].Value != null &&
                    Convert.ToBoolean(row.Cells["Select"].Value))
                {
                    string ip = row.Cells["IP"].Value?.ToString();
                    if (!string.IsNullOrEmpty(ip))
                    {
                        if (onlineIPs.Contains(ip))
                        {
                            selectedIPs.Add(ip);
                        }
                        else
                        {
                            row.Cells["Select"].Value = false;
                            dgvSpeakersStream.Refresh();
                            WriteLog($"❌ 오프라인 스피커 체크 해제됨: {ip}");
                        }
                    }
                }
            }

            dgvSpeakersStream.ResumeLayout();

            // BGM 정지 전송 (있을 때만)
            if (selectedIPs.Count > 0)
            {
                foreach (string ip in selectedIPs)
                    SendBGMCommand(ip, "stop_play");

                lblBgmStatus.Text = "BGM 자동 종료됨";
                BGMprogressBar.Visible = false;

                WriteLog($"✅ BGM 자동 종료됨 (대상 IP 수: {selectedIPs.Count})");
            }
            else
            {
                WriteLog("⚠️ 종료할 온라인 스피커 없음 → BGM 종료 생략");
            }

            // 🔻 여기서부터는 BGM 여부와 상관없이 스트리밍도 반드시 정지 + UI 정리
            WriteLog("⛔ 자동 BGM 종료 후 [스트리밍 정지] 실행");

            // 버튼에 들어있는 정지 로직 재사용
            btnStopStream_Click(btnStopStream, EventArgs.Empty);

            // 혹시 내부 로직이 이미 끝났거나 ffmpeg가 미리 종료된 경우를 대비해서
            // UI 상태를 한 번 더 확실히 정리
            try
            {
                StreamStatus.Text = "스트리밍 정지됨";
                StreamProgressBar.Style = ProgressBarStyle.Continuous;
                StreamProgressBar.Value = 0;
                StreamProgressBar.Visible = false;
            }
            catch { /* 컨트롤 dispose 상황 대비 */ }
        }



        private void chkAutoResumeLastStream_CheckedChanged(object sender, EventArgs e)
        {
            if (isLoadingStartConfig) return; // 🔥 로딩 중에는 저장 금지
            SaveFullConfig();
        }

        private void rbStreamYoutube_CheckedChanged(object sender, EventArgs e)
        {
            if (isLoadingStartConfig) return;
            SaveFullConfig();
        }

        private void rbStreamMusic_CheckedChanged(object sender, EventArgs e)
        {
            if (isLoadingStartConfig) return;
            SaveFullConfig();
        }

        private void rbStreamMic_CheckedChanged(object sender, EventArgs e)
        {
            if (isLoadingStartConfig) return;
            SaveFullConfig();
        }

        private void linkLabel1_LinkClicked(object sender, LinkLabelLinkClickedEventArgs e)
        {
            System.Diagnostics.Process.Start(new System.Diagnostics.ProcessStartInfo
            {
                FileName = "http://www.aepel.co.kr/",
                UseShellExecute = true
            });
        }

        private void btnManual_Click(object sender, EventArgs e)
        {
            // 실행파일과 같은 폴더 기준
            string pdfPath = Path.Combine(Application.StartupPath, "Manual_Streaming_Server.pdf");

            if (File.Exists(pdfPath))
            {
                try
                {
                    Process.Start(new ProcessStartInfo
                    {
                        FileName = pdfPath,
                        UseShellExecute = true
                    });
                }
                catch (Exception ex)
                {
                    MessageBox.Show("PDF 파일을 여는 중 오류 발생: " + ex.Message);
                }
            }
            else
            {
                MessageBox.Show("설명서 PDF 파일이 존재하지 않습니다:\n" + pdfPath);
            }

        }
        private void btnBackup_Click(object sender, EventArgs e)
        {
            using (FolderBrowserDialog dialog = new FolderBrowserDialog())
            {
                dialog.Description = "백업 파일을 저장할 폴더를 선택하세요.";
                if (dialog.ShowDialog() == DialogResult.OK)
                {
                    string backupFolder = dialog.SelectedPath;
                    string zipFileName = $"backup_{DateTime.Now:yyyyMMdd_HHmmss}.zip";
                    string zipFilePath = Path.Combine(backupFolder, zipFileName);

                    try
                    {
                        // 임시 작업 폴더 생성
                        string tempFolder = Path.Combine(Path.GetTempPath(), "NepisBackup_" + Guid.NewGuid().ToString());
                        Directory.CreateDirectory(tempFolder);

                        // 0) 라이선스 파일 백업 (C:\ProgramData\Nepis_Server\license.json 등)
                        try
                        {
                            string licensePath = LicenseService.LicenseStorePath; // 이미 프로젝트에 있음
                            if (File.Exists(licensePath))
                            {
                                string licDst = Path.Combine(tempFolder, @"license\license.json");
                                Directory.CreateDirectory(Path.GetDirectoryName(licDst));
                                File.Copy(licensePath, licDst, true);
                            }
                        }
                        catch { /* 읽기 실패 무시(권한 문제 등) */ }

                        // 1) MicroSIP 파일 복사
                        string microSIPSource = Path.Combine(Application.StartupPath, "lib", "MicroSIP");
                        string microSIPTarget = Path.Combine(tempFolder, @"lib\MicroSIP");
                        Directory.CreateDirectory(microSIPTarget);

                        File.Copy(Path.Combine(microSIPSource, "Contacts.xml"), Path.Combine(microSIPTarget, "Contacts.xml"), true);
                        File.Copy(Path.Combine(microSIPSource, "microsip.ini"), Path.Combine(microSIPTarget, "microsip.ini"), true);

                        // 2) Debug 루트 파일 복사
                        string debugPath = Application.StartupPath;
                        string[] filesToBackup = new string[]
                        {
                    "exclude_dates.txt",
                    "schedule.txt",
                    "selected_mic_device.txt",
                    "sip_groups.txt",
                    "speakers.txt",
                    "stream_port.txt",
                    "streaming_config.txt",
                    "youtube_channels.txt"
                        };

                        foreach (string file in filesToBackup)
                        {
                            string src = Path.Combine(debugPath, file);
                            string dst = Path.Combine(tempFolder, file);
                            if (File.Exists(src))
                                File.Copy(src, dst, true);
                        }

                        // 3) ZIP으로 압축
                        ZipFile.CreateFromDirectory(tempFolder, zipFilePath);

                        // 4) 정리
                        Directory.Delete(tempFolder, true);

                        MessageBox.Show($"백업이 완료되었습니다.\n{zipFilePath}", "백업 성공",
                            MessageBoxButtons.OK, MessageBoxIcon.Information);
                        WriteLog($"백업이 완료되었습니다. 경로: {zipFilePath}");
                    }
                    catch (Exception ex)
                    {
                        MessageBox.Show($"백업 중 오류 발생:\n{ex.Message}", "백업 실패",
                            MessageBoxButtons.OK, MessageBoxIcon.Error);
                    }
                }
            }
        }
        private void btnRestore_Click(object sender, EventArgs e)
        {
            using (OpenFileDialog dialog = new OpenFileDialog())
            {
                dialog.Title = "복원할 백업 ZIP 파일을 선택하세요.";
                dialog.Filter = "ZIP 파일 (*.zip)|*.zip";

                if (dialog.ShowDialog() == DialogResult.OK)
                {
                    string zipFilePath = dialog.FileName;

                    var result = MessageBox.Show("기존 설정 파일을 덮어쓰고 복원하시겠습니까?",
                        "복원 확인", MessageBoxButtons.YesNo, MessageBoxIcon.Warning);
                    if (result != DialogResult.Yes)
                        return;

                    try
                    {
                        // 임시 압축 해제 폴더
                        string tempExtractPath = Path.Combine(Path.GetTempPath(), "NepisRestore_" + Guid.NewGuid().ToString());
                        Directory.CreateDirectory(tempExtractPath);

                        ZipFile.ExtractToDirectory(zipFilePath, tempExtractPath);

                        // 원본 경로
                        string debugPath = Application.StartupPath;
                        string microSIPPath = Path.Combine(Application.StartupPath, "lib", "MicroSIP");

                        // 0) 라이선스 복원
                        try
                        {
                            string licSrc = Path.Combine(tempExtractPath, @"license\license.json");
                            if (File.Exists(licSrc))
                            {
                                string licDst = LicenseService.LicenseStorePath; // ProgramData or AppData
                                Directory.CreateDirectory(Path.GetDirectoryName(licDst));
                                File.Copy(licSrc, licDst, true);
                            }
                        }
                        catch { /* 권한 문제 등은 무시하고 진행 */ }

                        // 1) MicroSIP 복원
                        string extractedMicroSIP = Path.Combine(tempExtractPath, @"lib\MicroSIP");
                        if (Directory.Exists(extractedMicroSIP))
                        {
                            Directory.CreateDirectory(microSIPPath);
                            foreach (string file in Directory.GetFiles(extractedMicroSIP))
                            {
                                string fileName = Path.GetFileName(file);
                                File.Copy(file, Path.Combine(microSIPPath, fileName), true);
                            }
                        }

                        // 2) 설정파일 복원
                        string[] filesToRestore = new string[]
                        {
                    "exclude_dates.txt",
                    "schedule.txt",
                    "selected_mic_device.txt",
                    "sip_groups.txt",
                    "speakers.txt",
                    "stream_port.txt",
                    "streaming_config.txt",
                    "youtube_channels.txt"
                        };

                        foreach (string file in filesToRestore)
                        {
                            string src = Path.Combine(tempExtractPath, file);
                            string dst = Path.Combine(debugPath, file);
                            if (File.Exists(src))
                                File.Copy(src, dst, true);
                        }

                        // 정리
                        Directory.Delete(tempExtractPath, true);

                        // 복원 후 즉시 라이선스 재검증(같은 PC라면 OK, 다른 PC면 HWID 불일치 안내)
                        var (ok, reason, info) = LicenseService.LoadAndValidate();
                        if (!ok)
                        {
                            MessageBox.Show(
                                "설정 복원은 완료되었습니다.\n" +
                                $"[라이선스 상태] {reason}\n\n" +
                                "※ 다른 PC로 복원한 경우 HWID 불일치로 사용할 수 없습니다. 새 라이선스 발급이 필요합니다.",
                                "복원 완료(주의)", MessageBoxButtons.OK, MessageBoxIcon.Warning);
                        }
                        else
                        {
                            MessageBox.Show("복원이 완료되었습니다. 프로그램을 다시 시작합니다.",
                                "복원 성공", MessageBoxButtons.OK, MessageBoxIcon.Information);
                        }

                        WriteLog("복원이 완료되었습니다.");
                        Application.Restart();
                    }
                    catch (Exception ex)
                    {
                        MessageBox.Show($"복원 중 오류 발생:\n{ex.Message}", "복원 실패",
                            MessageBoxButtons.OK, MessageBoxIcon.Error);
                    }
                }
            }
        }
        private void btnOpenBrowser_Click(object sender, EventArgs e)
        {
            string ip = txtDeviceip.Text.Trim();

            if (string.IsNullOrEmpty(ip))
            {
                MessageBox.Show("IP 주소를 입력하세요.");
                return;
            }

            try
            {
                // 브라우저로 http://{ip} 열기
                string url = $"http://{ip}";
                System.Diagnostics.Process.Start(url);
            }
            catch (Exception ex)
            {
                MessageBox.Show("웹 페이지를 여는 중 오류 발생: " + ex.Message);
            }
        }

        private async void youtubeRestartTimer_Tick(object sender, EventArgs e)
        {
            if (_bgmHardStopped) { WriteLog("⛔ 재시작 차단: 하드스톱 상태"); return; }
            // 유튜브 모드가 아니거나 URL이 비어 있으면 중단
            if (!rbStreamYoutube.Checked) return;
            if (string.IsNullOrWhiteSpace(txtYoutubeUrl.Text)) return;

            // 재진입(중복) 차단
            if (Interlocked.Exchange(ref _autoRestartGate, 1) == 1)
            {
                WriteLog("⏭ 재시작 중복요청 스킵");
                return;
            }

            try
            {
                WriteLog($"[타이머 실행됨] {DateTime.Now:yyyy-MM-dd HH:mm:ss}");
                await RestartYoutubeStreamAsync();   // 비동기 재시작
            }
            catch (Exception ex)
            {
                WriteLog($"⚠️ 타이머 재시작 예외: {ex.Message}");
            }
            finally
            {
                Interlocked.Exchange(ref _autoRestartGate, 0);
            }
        }
        private async Task WaitUntilStreamReadyAsync(int maxWaitMs = 8000)
        {
            var deadline = DateTime.UtcNow.AddMilliseconds(maxWaitMs);
            while (!_streamReady && DateTime.UtcNow < deadline)
                await Task.Delay(100);
        }
        private async Task RestartYoutubeStreamAsync()
        {
            if (_bgmHardStopped) { WriteLog("[재시작] 차단됨(하드스톱)"); return; }
            if (isRestartInProgress) { WriteLog("[재시작] 진행 중 요청 스킵"); return; }
            isRestartInProgress = true;

            // 🔒 현재 워치독 기대 상태를 저장
            bool prevStreamingExpected = _streamingExpected;

            try
            {
                // ▶ 의도적인 재시작 구간: 워치독 일시 정지
                _streamingExpected = false;
                try { StopStreamWatchdog(); } catch { }

                // 0) 유튜브 모드/URL 검증
                if (!rbStreamYoutube.Checked)
                {
                    WriteLog("[재시작] 유튜브 모드 아님");
                    return;
                }

                string url = txtYoutubeUrl.Text?.Trim();
                if (cmbYoutubeList.SelectedItem != null &&
                    youtubeChannels.TryGetValue(cmbYoutubeList.SelectedItem.ToString(), out var mapped))
                {
                    url = mapped;
                    txtYoutubeUrl.Text = url;
                }
                if (string.IsNullOrWhiteSpace(url))
                {
                    WriteLog("[재시작] URL 없음");
                    return;
                }

                // 1) 대상 IP: lastOnlineIPs 우선(스냅샷) → 없으면 그리드
                var targetIPs =
                    (lastOnlineIPs != null && lastOnlineIPs.Count > 0)
                    ? new List<string>(lastOnlineIPs)
                    : dgvSpeakersStream.Rows
                        .Cast<DataGridViewRow>()
                        .Where(r => (r.Cells["Select"].Value as bool?) == true)
                        .Select(r => r.Cells["IP"].Value?.ToString())
                        .Where(ip => !string.IsNullOrWhiteSpace(ip))
                        .Distinct()
                        .ToList();

                if (targetIPs.Count == 0)
                {
                    // 기존 동작 유지: 스피커 없으면 재시작 스킵
                    WriteLog("[재시작] 대상 스피커 0");
                    return;
                }

                WriteLog($"[재시작] 대상 스피커: {string.Join(", ", targetIPs)}");
                WriteLog("[재시작] BGM 상태 유지, 유튜브 스트림만 재시작");

                // 2) 기존 ffmpeg 종료 + 1.5초 여유
                var old = Interlocked.Exchange(ref ffmpegProcess, null);
                if (old != null)
                {
                    try
                    {
                        bool alive = false;
                        try { alive = !old.HasExited; } catch { }
                        if (alive)
                        {
                            try { old.Kill(); } catch { }
                            try { old.WaitForExit(5000); } catch { }
                        }
                    }
                    finally
                    {
                        try { old.Dispose(); } catch { }
                    }
                }
                await Task.Delay(1500);
                WriteLog("[재시작] ffmpeg 종료 완료");

                // 3) 스트림 재시작
                ytStatus.Text = "";
                lastYoutubeUrl = url;
                isYoutubeRepeating = true;

                _ = Task.Run(() =>
                {
                    try { StreamYoutubeAudio(url); }
                    catch (Exception ex) { WriteLog("[재시작] 스트림 시작 실패: " + ex.Message); }
                });

                if (IsHandleCreated)
                {
                    BeginInvoke((MethodInvoker)(() =>
                    {
                        ytStatus.Text = "유튜브 스트리밍 중(재시작)";
                        StreamStatus.Text = "유튜브 스트리밍 중(재시작)";
                    }));
                }

                // 🔔 BGM은 건드리지 않음 (bgm_stop / bgm_start 제거)
                WriteLog("[재시작] 완료 (BGM 유지)");
            }
            catch (Exception ex)
            {
                WriteLog("[재시작] 예외: " + ex);
            }
            finally
            {
                // ▶ 의도적인 재시작 구간이 끝났으니 워치독 상태 복구
                if (prevStreamingExpected && !_bgmHardStopped)
                {
                    _streamingExpected = true;
                    try { StartStreamWatchdog(); } catch { }
                }

                isRestartInProgress = false;
            }
        }


        private void btnMonitorStream_Click(object sender, EventArgs e)
        {
            string vlcPath = Path.Combine(Application.StartupPath, "lib", "vlc", "vlc.exe");

            // ✅ 선택된 스트리밍 포트 가져오기
            int port = (int)numSelectStreamPort.Value;
            string args = $"rtp://@239.255.0.1:{port} --network-caching=1000 --quiet --intf dummy";

            if (vlcMonitorProcess == null || vlcMonitorProcess.HasExited)
            {
                // VLC 실행
                try
                {
                    ProcessStartInfo psi = new ProcessStartInfo
                    {
                        FileName = vlcPath,
                        Arguments = args,
                        UseShellExecute = false,
                        CreateNoWindow = true,
                        WindowStyle = ProcessWindowStyle.Hidden
                    };

                    vlcMonitorProcess = Process.Start(psi);
                    btnMonitorStream.Text = "모니터링 중지";
                    btnMonitorStream.BackColor = Color.Red; // 🔴 빨간색
                    WriteLog($"[스트리밍 모니터링 시작됨] {DateTime.Now:yyyy-MM-dd HH:mm:ss} (포트 {port})");
                }
                catch (Exception ex)
                {
                    MessageBox.Show("VLC 실행 실패: " + ex.Message);
                    WriteLog($"[에러] VLC 실행 실패: {ex.Message}");
                }
            }
            else
            {
                // VLC 종료
                try
                {
                    vlcMonitorProcess.Kill();
                    vlcMonitorProcess.Dispose();
                    vlcMonitorProcess = null;
                    btnMonitorStream.Text = "모니터링 시작";
                    btnMonitorStream.BackColor = Color.Green; // 🟢 녹색
                    WriteLog($"[스트리밍 모니터링 중지됨] {DateTime.Now:yyyy-MM-dd HH:mm:ss}");
                }
                catch (Exception ex)
                {
                    MessageBox.Show("VLC 종료 실패: " + ex.Message);
                    WriteLog($"[에러] VLC 종료 실패: {ex.Message}");
                }
            }
        }

        protected override void OnFormClosing(FormClosingEventArgs e)
        {
            // 1) VLC 모니터 프로세스 정리
            try
            {
                if (vlcMonitorProcess != null)
                {
                    if (!vlcMonitorProcess.HasExited)
                    {
                        try { vlcMonitorProcess.CloseMainWindow(); } catch { }
                        if (!vlcMonitorProcess.WaitForExit(1000))
                        {
                            try { vlcMonitorProcess.Kill(); } catch { }
                            try { vlcMonitorProcess.WaitForExit(1000); } catch { }
                        }
                    }

                    try { vlcMonitorProcess.Dispose(); } catch { }
                    vlcMonitorProcess = null;
                }
            }
            catch { /* ignore */ }

            // 2) 스피커 상태 스트림 정리
            try { StopSPStatusStream(); } catch { /* ignore */ }

            // 3) ffmpeg 로그 writer 정리
            try { ffmpegLogWriter?.Dispose(); } catch { /* ignore */ }
            ffmpegLogWriter = null;

            // 4) ✅ SIP 등록/Transport 정리 (앞서 만든 함수가 있다고 가정)
            try { StopRegistration(); } catch { /* ignore */ }
            try { _sipTransport?.Shutdown(); } catch { /* ignore */ }
            _sipTransport = null;

            base.OnFormClosing(e);
        }

        protected override void OnFormClosed(FormClosedEventArgs e)
        {
            base.OnFormClosed(e);
            try
            {
                player.controls.stop();
                // Marshal.FinalReleaseComObject(player); // 필요 시
            }
            catch { }
        }
        // 1. 현재 시스템 시간 표시
        private void UpdateCurrentTime()
        {
            lblCurrentTime.Text = "현재 시간: " + DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss");
        }

        // 2. 시간 수동 설정
        private void btnSetLocalTime_Click(object sender, EventArgs e)
        {
            // 임시 폼 생성
            Form timeForm = new Form
            {
                Width = 300,
                Height = 150,
                Text = "시간 설정",
                StartPosition = FormStartPosition.CenterParent,
                FormBorderStyle = FormBorderStyle.FixedDialog,
                MaximizeBox = false,
                MinimizeBox = false
            };

            // DateTimePicker 구성
            DateTimePicker dtPicker = new DateTimePicker
            {
                Format = DateTimePickerFormat.Custom,
                CustomFormat = "yyyy-MM-dd HH:mm:ss",
                Value = DateTime.Now,
                Location = new Point(20, 20),
                Width = 250
            };

            // 확인 버튼
            Button btnOK = new Button
            {
                Text = "확인",
                DialogResult = DialogResult.OK,
                Location = new Point(100, 60),
                Width = 80
            };

            timeForm.Controls.Add(dtPicker);
            timeForm.Controls.Add(btnOK);
            timeForm.AcceptButton = btnOK;

            // ShowDialog로 날짜 선택 폼 표시
            if (timeForm.ShowDialog() == DialogResult.OK)
            {
                SetSystemTime(dtPicker.Value);
                UpdateCurrentTime(); // UI 갱신
            }
        }

        // Windows 시간 설정 (관리자 권한 필요)

        private void SetSystemTime(DateTime dt)
        {
            SYSTEMTIME st = new SYSTEMTIME
            {
                wYear = (short)dt.Year,
                wMonth = (short)dt.Month,
                wDay = (short)dt.Day,
                wHour = (short)dt.Hour,
                wMinute = (short)dt.Minute,
                wSecond = (short)dt.Second
            };
            SetLocalTime(ref st);
        }

        [DllImport("kernel32.dll", SetLastError = true)]
        private static extern bool SetLocalTime(ref SYSTEMTIME time);

        [StructLayout(LayoutKind.Sequential)]
        private struct SYSTEMTIME
        {
            public short wYear, wMonth, wDayOfWeek, wDay,
                         wHour, wMinute, wSecond, wMilliseconds;
        }

        // 3. 인터넷 연결 확인
        private void CheckInternetConnection()
        {
            bool connected = false;

            try
            {
                using (Ping ping = new Ping())
                {
                    PingReply reply = ping.Send("8.8.8.8", 1000);
                    connected = (reply.Status == IPStatus.Success);
                }
            }
            catch
            {
                connected = false;
            }

            lblInternetStatus.Text = connected ? "🌐 인터넷 연결됨" : "❌ 인터넷 없음";
            lblInternetStatus.ForeColor = connected ? System.Drawing.Color.Green : System.Drawing.Color.Red;
        }

        // 4. 체크박스로 NTP 서버 활성화/비활성화
        private void chkEnableNtpServer_CheckedChanged(object sender, EventArgs e)
        {
            if (!this.Visible || !this.Focused) return; // 탭 이동 중일 때는 무시

            if (chkEnableNtpServer.Checked)
                EnableNtpServer();
            else
                DisableNtpServer();

            CheckNtpStatus();
        }

        // 5. Apply 버튼 클릭 시 설정 재적용
        private void btnApplyNtpSettings_Click(object sender, EventArgs e)
        {
            if (chkEnableNtpServer.Checked)
                EnableNtpServer();
            else
                DisableNtpServer();

            CheckNtpStatus();
        }

        // 6. NTP 서버 상태 확인
        private void CheckNtpStatus()
        {
            string output = RunCommand("w32tm /query /configuration");
            lblNtpStatus.Text = output.Contains("AnnounceFlags: 5") ? "🟢 NTP 서버 활성화됨" : "⚪ NTP 서버 비활성화됨";
        }
        private void OpenNtpFirewallPort()
        {
            RunCommand("netsh advfirewall firewall add rule name=\"NTP Server\" dir=in action=allow protocol=UDP localport=123");
        }
        private void CloseNtpFirewallPort()
        {
            RunCommand("netsh advfirewall firewall delete rule name=\"NTP Server\"");
        }

        // ✅ NTP 서버 활성화
        private void EnableNtpServer()
        {
            // 1) NTP 서버 기능 ON
            RunCommand("reg add \"HKLM\\SYSTEM\\CurrentControlSet\\Services\\W32Time\\TimeProviders\\NtpServer\" /v Enabled /t REG_DWORD /d 1 /f");

            // 2) 이 PC를 '신뢰할 수 있는 시간 서버'로 광고
            RunCommand("reg add \"HKLM\\SYSTEM\\CurrentControlSet\\Services\\W32Time\\Config\" /v AnnounceFlags /t REG_DWORD /d 5 /f");

            // ❌ 기존 코드에서 manualpeerlist, syncfromflags 건드는 부분은 제거
            //    → 외부 시간 소스는 Windows 기본 설정/도메인 정책/관리자가 결정하도록 둠

            RunCommand("net stop w32time");
            RunCommand("net start w32time");
            RunCommand("w32tm /config /update");

            OpenNtpFirewallPort();
        }

        // ❌ NTP 서버 비활성화
        private void DisableNtpServer()
        {
            RunCommand("reg add \"HKLM\\SYSTEM\\CurrentControlSet\\Services\\W32Time\\TimeProviders\\NtpServer\" /v Enabled /t REG_DWORD /d 0 /f");
            RunCommand("reg add \"HKLM\\SYSTEM\\CurrentControlSet\\Services\\W32Time\\Config\" /v AnnounceFlags /t REG_DWORD /d 10 /f");

            RunCommand("net stop w32time");
            RunCommand("net start w32time");
            RunCommand("w32tm /config /update");

            CloseNtpFirewallPort();
        }

        // 명령 실행 유틸리티
        private string RunCommand(string command)
        {
            var psi = new ProcessStartInfo("cmd.exe", "/c " + command)
            {
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                UseShellExecute = false,   // 출력 캡처 가능
                CreateNoWindow = true
            };

            using (var process = Process.Start(psi))
            {
                string output = process.StandardOutput.ReadToEnd();
                process.WaitForExit();
                return output;
            }
        }
        private string GetLocalIPAddress()
        {
            var host = System.Net.Dns.GetHostEntry(System.Net.Dns.GetHostName());
            foreach (var ip in host.AddressList)
            {
                if (ip.AddressFamily == System.Net.Sockets.AddressFamily.InterNetwork)
                {
                    return ip.ToString();
                }
            }
            return "IP 주소를 찾을 수 없습니다.";
        }
        private string GetLocalIPAddress(string remoteHintIp = null)
        {
            // 1) 힌트(IP) 있으면 그쪽으로 UDP '연결'하여 로컬 바인딩 IP 확인 (패킷 실제 전송 없음)
            if (!string.IsNullOrWhiteSpace(remoteHintIp))
            {
                try
                {
                    using (var s = new Socket(AddressFamily.InterNetwork, SocketType.Dgram, ProtocolType.Udp))
                    {
                        s.Connect(remoteHintIp.Trim(), 123); // NTP 포트
                        if (s.LocalEndPoint is IPEndPoint ep) return ep.Address.ToString();
                    }
                }
                catch { /* fallback */ }
            }

            // 2) 인터넷 경로로 바인딩 IP 추론
            foreach (var probe in new[] { "8.8.8.8", "1.1.1.1" })
            {
                try
                {
                    using (var s = new Socket(AddressFamily.InterNetwork, SocketType.Dgram, ProtocolType.Udp))
                    {
                        s.Connect(probe, 123);
                        if (s.LocalEndPoint is IPEndPoint ep) return ep.Address.ToString();
                    }
                }
                catch { /* next */ }
            }

            // 3) 활성 NIC 중 유효 IPv4 1개 선택 (루프백/APIPA/가상 제외)
            try
            {
                var nicBlacklist = new[] { "virtual", "vmware", "hyper-v", "loopback", "tunnel", "bluetooth", "docker", "npm", "pnp" };
                var ip = NetworkInterface.GetAllNetworkInterfaces()
                    .Where(ni =>
                           ni.OperationalStatus == OperationalStatus.Up &&
                           ni.NetworkInterfaceType != NetworkInterfaceType.Loopback &&
                           ni.NetworkInterfaceType != NetworkInterfaceType.Tunnel &&
                           !nicBlacklist.Any(b => ni.Description.ToLower().Contains(b) || ni.Name.ToLower().Contains(b)))
                    .SelectMany(ni => ni.GetIPProperties().UnicastAddresses)
                    .Select(ua => ua.Address)
                    .Where(a =>
                           a.AddressFamily == AddressFamily.InterNetwork &&
                           !IPAddress.IsLoopback(a) &&
                           !a.ToString().StartsWith("169.254."))
                    .Select(a => a.ToString())
                    .FirstOrDefault();

                if (!string.IsNullOrEmpty(ip)) return ip;
            }
            catch { }

            return "IP 주소를 찾을 수 없습니다.";
        }

        private void btnApplyBgmAutoSettings_Click(object sender, EventArgs e)
        {
            SaveFullConfig();
            MessageBox.Show("BGM 자동 설정이 저장되었습니다.", "설정 저장", MessageBoxButtons.OK, MessageBoxIcon.Information);
            ArmAutoStop();
        }
        private void SaveFullConfig()
        {
            try
            {
                var lines = new List<string>();
                lines.Add($"auto_start_bgm={(chkBgmAutoOn.Checked ? "true" : "false")}");
                lines.Add($"auto_stop_bgm={(chkBgmAutoOff.Checked ? "true" : "false")}");
                lines.Add($"bgm_auto_on_time={dtpBgmAutoOnTime.Value:HH\\:mm\\:ss}");
                lines.Add($"bgm_auto_off_time={dtpBgmOffTime.Value:HH\\:mm\\:ss}");
                lines.Add($"auto_bgm_control={(chkAutoBgmControl.Checked ? "true" : "false")}");
                lines.Add($"auto_resume_last_stream={(chkAutoResumeLastStream.Checked ? "true" : "false")}");
                lines.Add($"last_stream_type={(rbStreamYoutube.Checked ? "youtube" : rbStreamMusic.Checked ? "music" : "mic")}");
                lines.Add($"last_youtube_url={txtYoutubeUrl.Text}");
                lines.Add($"last_youtube_channel={cmbYoutubeList.SelectedItem?.ToString()}");

                var selectedIPs = new List<string>();
                foreach (DataGridViewRow row in dgvSpeakersStream.Rows)
                {
                    try
                    {
                        if (Convert.ToBoolean(row.Cells["Select"].Value))
                        {
                            string ip = row.Cells["IP"].Value?.ToString();
                            if (!string.IsNullOrEmpty(ip))
                                selectedIPs.Add(ip);
                        }
                    }
                    catch { }
                }
                lines.Add($"selected_speakers={string.Join(",", selectedIPs)}");

                File.WriteAllLines(configPath, lines);
            }
            catch (Exception ex)
            {
                MessageBox.Show("설정 저장 중 오류 발생: " + ex.Message);
            }
        }
        private void ArmAutoStop()
        {
            try { _autoStopCts?.Cancel(); } catch { }
            _autoStopCts?.Dispose();
            _autoStopCts = null;
            _armedAutoStopAt = DateTime.MinValue;

            if (!chkBgmAutoOff.Checked)
            {
                WriteLog("⏸ 자동 종료 미사용(체크 해제). 예약 안 함.");
                return;
            }

            var now = DateTime.Now;
            var off = new DateTime(now.Year, now.Month, now.Day,
                                   dtpBgmOffTime.Value.Hour,
                                   dtpBgmOffTime.Value.Minute,
                                   dtpBgmOffTime.Value.Second);
            if (off <= now) off = off.AddDays(1);

            var delay = off - now;
            if (delay <= TimeSpan.Zero) delay = TimeSpan.FromSeconds(1);

            var cts = new CancellationTokenSource();
            var token = cts.Token;
            var target = off;

            _autoStopCts = cts;
            _armedAutoStopAt = target;

            WriteLog($"⏱ 자동 종료 예약: {target:yyyy-MM-dd HH:mm:ss} (약 {delay.TotalMinutes:F0}분 후)");

            Task.Run(async () =>
            {
                try
                {
                    // 예외 없는 대기: 완료 vs 취소 신호 중 먼저 끝나는 것
                    var delayTask = Task.Delay(delay);
                    var cancelTask = Task.Delay(Timeout.Infinite, token);
                    var completed = await Task.WhenAny(delayTask, cancelTask);

                    if (completed == cancelTask || token.IsCancellationRequested) return;
                    if (IsDisposed || !IsHandleCreated) return;

                    BeginInvoke((MethodInvoker)(() =>
                    {
                        var now2 = DateTime.Now;

                        // 발화 중복 방지
                        bool timeOK = Math.Abs((now2 - target).TotalMinutes) <= 2;
                        bool notDup = (_lastAutoStopFired == DateTime.MinValue) ||
                                       ((now2 - _lastAutoStopFired).TotalMinutes > 2);

                        if (timeOK && notDup)
                        {
                            WriteLog("🛑 자동 종료 발화");
                            _lastAutoStopFired = now2;
                            AutoStopBGM();

                            // ✔ 발화한 경우에만 재무장
                            if (chkBgmAutoOff.Checked) ArmAutoStop();
                        }
                    }));
                }
                catch (Exception ex)
                {
                    if (!IsDisposed && IsHandleCreated)
                    {
                        BeginInvoke((MethodInvoker)(() =>
                            WriteLog("자동 종료 예약 중 예외: " + ex.Message)
                        ));
                    }
                }
                // ❌ finally에서 재무장하지 않습니다. 중복 예약 원인
            });
        }


        // 스피커 상태
        private void check_SP_Status_CheckedChanged(object sender, EventArgs e)
        {
            if (_suppressSpCheckEvent) return;

            if (check_SP_Status.Checked)
                StartSPStatusStream();
            else
            {
                StopSPStatusStream();
                SafeSetTimeProgress(0);
            }
        }
        // 시간 진행률 전용 세터: null(또는 -1) → Marquee, 0~100 → Blocks 값 표시
        private void SafeSetTimeProgress(int? pctOrNull)
        {
            if (!progressBar_SP_Status.IsHandleCreated) return;

            progressBar_SP_Status.BeginInvoke((MethodInvoker)(() =>
            {
                try
                {
                    if (pctOrNull == null || pctOrNull.Value < 0)
                    {
                        // 수신 없음 → 마키로 전환
                        if (progressBar_SP_Status.Style != ProgressBarStyle.Marquee)
                            progressBar_SP_Status.Style = ProgressBarStyle.Marquee;

                        // 0이면 애니메이션이 멈춤
                        if (progressBar_SP_Status.MarqueeAnimationSpeed <= 0)
                            progressBar_SP_Status.MarqueeAnimationSpeed = 60; // 40~100 추천
                    }
                    else
                    {
                        if (progressBar_SP_Status.Style != ProgressBarStyle.Blocks)
                            progressBar_SP_Status.Style = ProgressBarStyle.Blocks;

                        int v = Math.Max(0, Math.Min(100, pctOrNull.Value));
                        if (progressBar_SP_Status.Value != v)
                            progressBar_SP_Status.Value = v;
                    }
                }
                catch { }
            }));
        }
        private void StartSPStatusStream()
        {
            StopSPStatusStream(); // 중복 방지

            var ips = GetCheckedSpeakerIPs();
            if (ips.Count == 0)
            {
                SafeSetTimeProgress(0);
                return;
            }

            string ip = ips[0];
            spStatusStreamCts = new CancellationTokenSource();
            var token = spStatusStreamCts.Token;

            Task.Run(async () =>
            {
                StreamReader reader = null;
                StreamWriter writer = null;
                NetworkStream ns = null;
                TcpClient client = null;

                try
                {
                    client = new TcpClient();

                    // 연결 타임아웃 5초
                    var connectTask = client.ConnectAsync(ip, 39999);
                    var timeoutTask = Task.Delay(TimeSpan.FromSeconds(5), token);
                    if (await Task.WhenAny(connectTask, timeoutTask) == timeoutTask)
                        throw new TimeoutException("status_stream connect timeout");

                    client.NoDelay = true;
                    ns = client.GetStream();
                    try { ns.ReadTimeout = 5000; ns.WriteTimeout = 2000; } catch { }

                    writer = new StreamWriter(ns, Encoding.UTF8) { AutoFlush = true };
                    reader = new StreamReader(ns, Encoding.UTF8);

                    spStatusTcpClient = client;
                    spStatusNs = ns;
                    spStatusReader = reader;

                    // 대기 표시
                    SafeSetTimeProgress(null);

                    // 명령 전송
                    await writer.WriteLineAsync("status_stream");

                    // (선택) 핸드셰이크 한 줄 무시
                    try { _ = await reader.ReadLineAsync(); } catch { }

                    while (!token.IsCancellationRequested)
                    {
                        string line = null;
                        try
                        {
                            line = await reader.ReadLineAsync(); // \n 필요
                            if (line == null) break;
                        }
                        catch (IOException)
                        {
                            // 잠시 끊김 → 마키 유지
                            SafeSetTimeProgress(null);
                            continue;
                        }
                        catch (ObjectDisposedException) { break; }

                        var s = (line ?? "").Trim();
                        if (s.Length == 0) continue;

                        if (int.TryParse(s, out int pct))
                        {
                            if (pct < 0) pct = 0; else if (pct > 100) pct = 100;
                            SafeSetTimeProgress(pct);
                        }
                        // 숫자가 아니면 무시 (로그/볼륨 문자열 등)
                    }
                }
                catch
                {
                    SafeSetTimeProgress(0);
                }
                finally
                {
                    try { reader?.Dispose(); } catch { }
                    try { writer?.Dispose(); } catch { }
                    try { ns?.Dispose(); } catch { }
                    try { client?.Close(); } catch { }

                    spStatusReader = null;
                    spStatusNs = null;
                    spStatusTcpClient = null;
                }
            }, token);
        }
        //======================
        // TTS
        //======================
        private void chkShowPassword_CheckedChanged(object sender, EventArgs e)
        {
            try
            {
                // 체크하면 보이게, 해제하면 마스킹
                txtTTSServerPass.UseSystemPasswordChar = !chkShowPassword.Checked;
            }
            catch { /* ignore */ }
        }
        private void numTTSServerPort_ValueChanged(object sender, EventArgs e)
        {
            // 포트 변경 시 즉시 재점검
            _ = CheckTtsServerAsync();
        }

        private void TtsServerFields_Changed(object sender, EventArgs e)
        {
            // 입력값 변경 시 즉시 재점검(너무 잦으면 디바운스 추가 가능)
            _ = CheckTtsServerAsync();
        }
        private async Task CheckTtsServerAsync()
        {
            // 너무 자주 중첩 실행 방지(타이머/텍스트변경이 겹칠 수 있음)
            if (_ttsStatusChecking) return;
            _ttsStatusChecking = true;

            int mySeq = Interlocked.Increment(ref _ttsServerCheckSeq);

            string host = (txtTTSServerIp.Text ?? "").Trim();
            int port = 22;
            try { port = (int)numTTSServerPort.Value; } catch { port = 22; }

            string user = (txtTTSServerUser.Text ?? "").Trim();
            string pass = txtTTSServerPass.Text ?? "";

            if (string.IsNullOrWhiteSpace(host))
            {
                SafeUI(() =>
                {
                    pnlTTSServerLamp.BackColor = System.Drawing.Color.Gray;
                    lblTTSServerStatus.Text = "서버: IP 미입력";
                });
                _ttsStatusChecking = false;
                return;
            }

            SafeUI(() =>
            {
                pnlTTSServerLamp.BackColor = System.Drawing.Color.Gray;
                lblTTSServerStatus.Text = "서버: 확인 중…";
            });

            var result = await Task.Run(() =>
            {
                bool pingOk = true;

                // 1) PING (현장에 따라 ICMP 차단 가능 → 실패해도 SSH는 계속 시도)
                try
                {
                    using (var ping = new Ping())
                    {
                        var reply = ping.Send(host, 800);
                        if (reply == null || reply.Status != IPStatus.Success)
                            pingOk = false;
                    }
                }
                catch
                {
                    pingOk = false;
                }

                // 2) SSH 로그인
                if (string.IsNullOrWhiteSpace(user))
                    return (ok: false, step: "SSH", msg: "계정 미입력", pingOk: pingOk);

                try
                {
                    using (var ssh = new SshClient(host, port, user, pass))
                    {
                        ssh.ConnectionInfo.Timeout = TimeSpan.FromSeconds(3);
                        ssh.Connect();

                        // 3) ENGINE 체크
                        // - 스크립트 실행 가능
                        // - 결과 폴더 존재
                        // 필요하면 경로를 실제 서버에 맞춰 조정하세요.
                        var cmd = ssh.RunCommand(
                            "test -x /usr/local/bin/rs_tts_makemp3.sh && " +
                            "test -d /usr/vt/result/tts_mp3 && " +
                            "echo OK || echo FAIL"
                        );

                        var outp = (cmd.Result ?? "").Trim();

                        ssh.Disconnect();

                        if (!string.Equals(outp, "OK", StringComparison.OrdinalIgnoreCase))
                            return (ok: false, step: "ENGINE", msg: "TTS 환경 미확인", pingOk: pingOk);

                        return (ok: true, step: "OK", msg: "정상", pingOk: pingOk);
                    }
                }
                catch (Exception ex)
                {
                    return (ok: false, step: "SSH", msg: ex.Message, pingOk: pingOk);
                }
            });

            // 최신 체크만 반영
            if (mySeq != _ttsServerCheckSeq)
            {
                _ttsStatusChecking = false;
                return;
            }

            SafeUI(() =>
            {
                if (result.ok)
                {
                    pnlTTSServerLamp.BackColor = System.Drawing.Color.LimeGreen;

                    // PING 차단 환경 고려한 문구
                    if (result.pingOk)
                        lblTTSServerStatus.Text = "서버: 정상 (PING/SSH/ENGINE)";
                    else
                        lblTTSServerStatus.Text = "서버: 정상 (SSH/ENGINE, PING 차단)";
                }
                else
                {
                    pnlTTSServerLamp.BackColor = System.Drawing.Color.OrangeRed;
                    lblTTSServerStatus.Text = $"서버: 오류 ({result.step})";

                    // 상세는 로그로 남기는 것을 권장
                    // WriteLog($"[TTS] 서버 상태 오류({result.step}): {result.msg}");
                }
            });

            _ttsStatusChecking = false;
        }


        private bool TestTcpConnect(string host, int port, int timeoutMs)
        {
            try
            {
                using (var client = new System.Net.Sockets.TcpClient())
                {
                    var task = client.ConnectAsync(host, port);
                    if (!task.Wait(timeoutMs)) return false;
                    return client.Connected;
                }
            }
            catch
            {
                return false;
            }
        }
        private void SetTtsServerLamp(TtsServerState state, string text)
        {
            if (this.IsDisposed) return;

            void apply()
            {
                try
                {
                    lblTTSServerStatus.Text = text;

                    // 색상 규칙(필요하면 기존 Nepis 색 규칙에 맞추세요)
                    switch (state)
                    {
                        case TtsServerState.Online:
                            pnlTTSServerLamp.BackColor = System.Drawing.Color.LimeGreen;
                            break;
                        case TtsServerState.Offline:
                            pnlTTSServerLamp.BackColor = System.Drawing.Color.IndianRed;
                            break;
                        default:
                            pnlTTSServerLamp.BackColor = System.Drawing.Color.Goldenrod; // Checking
                            break;
                    }
                }
                catch { /* ignore */ }
            }

            if (this.InvokeRequired) this.BeginInvoke((Action)apply);
            else apply();
        }

        // CGI

        private bool ConvertMp3ToUlaw(string inputMp3, string outputUlaw)
        {
            try
            {
                string ffmpegExe = Path.Combine(AppDomain.CurrentDomain.BaseDirectory, "lib", "ffmpeg.exe");
                if (!File.Exists(ffmpegExe)) return false;

                // ✅ -f mulaw 옵션이 핵심입니다. (헤더 없는 순수 데이터 생성)
                string args = $"-y -i \"{inputMp3}\" -ar 8000 -ac 1 -codec:a pcm_mulaw -f mulaw \"{outputUlaw}\"";

                var psi = new ProcessStartInfo
                {
                    FileName = ffmpegExe,
                    Arguments = args,
                    CreateNoWindow = true,
                    UseShellExecute = false
                };

                using (var p = Process.Start(psi))
                {
                    p.WaitForExit(10000);
                    return p.ExitCode == 0;
                }
            }
            catch { return false; }
        }
        private async Task AutoSendTtsToSpeakersAsync(string localMp3Path)
        {
            if (!File.Exists(localMp3Path)) return;

            var selectedList = new List<(string ip, string model)>();
            foreach (DataGridViewRow row in dgvSpeakersTTS.Rows)
            {
                if (row.IsNewRow) continue;

                bool sel = false;
                try { sel = Convert.ToBoolean(row.Cells["SelectTTS"].Value); } catch { }

                if (!sel) continue;

                var ip = row.Cells["IPTTS"].Value?.ToString();
                var model = row.Cells["ModelColumnTTS"].Value?.ToString();

                if (!string.IsNullOrWhiteSpace(ip))
                    selectedList.Add((ip, (model ?? "").Trim().ToUpperInvariant()));
            }

            if (selectedList.Count == 0) return;

            // ✅ 실행 시작 시점 체크 상태 고정
            bool useCgi = chkUseCgi.Checked;

            // ✅ 방송 중 변경 방지
            SafeUI(() => chkUseCgi.Enabled = false);

            using (var cts = new CancellationTokenSource())
            {
                try
                {
                    LogTTS($"[방송시작] 대상: {selectedList.Count}대, 방식: {(useCgi ? "CGI" : "TCP")}");

                    var tasks = selectedList.Select(info => Task.Run(async () =>
                    {
                        // ✅ 스피커 1대당 최대 20초 제한 (필요시 30초)
                        using var per = new CancellationTokenSource(TimeSpan.FromSeconds(20));
                        using var linked = CancellationTokenSource.CreateLinkedTokenSource(cts.Token, per.Token);

                        bool success = false;

                        try
                        {
                            LogTTS($"[DBG] START {info.ip} {info.model} mode={(useCgi ? "CGI" : "TCP")}");

                            if (useCgi && (info.model == "AXIS" || info.model == "AEPEL"))
                            {
                                success = await SendTtsToCgiDigestAsync(info.ip, info.model, localMp3Path, linked.Token)
                                                .ConfigureAwait(false);
                            }
                            else
                            {
                                try { SendStopPlayToSpeaker(info.ip); } catch { }
                                await Task.Delay(800, linked.Token).ConfigureAwait(false);

                                if (TryConnectWithTimeout(info.ip, 8787, 1500))
                                {
                                    // ✅ 블로킹 가능 구간이라 linked.Token을 반영하도록 Upload 함수도 개선 필요
                                    success = UploadFileToSpeaker(info.ip, localMp3Path);

                                    if (success)
                                    {
                                        await Task.Delay(600, linked.Token).ConfigureAwait(false);
                                        SendBroadcastCommand(info.ip, Path.GetFileName(localMp3Path));
                                    }
                                }
                            }

                            LogTTS($"[DBG] END   {info.ip} success={success}");
                        }
                        catch (OperationCanceledException)
                        {
                            LogTTS($"[DBG] TIMEOUT {info.ip} (작업 시간 초과)");
                            success = false;
                        }
                        catch (Exception ex)
                        {
                            LogTTS($"[DBG] EX {info.ip}: {ex.Message}");
                            success = false;
                        }

                        LogTTS($"[TTS 결과] {info.ip}({info.model}): {(success ? "성공" : "실패")}");
                    })).ToList();

                    await Task.WhenAll(tasks).ConfigureAwait(false);

                    SafeUI(() => MessageBox.Show("TTS 방송 전송 처리가 완료되었습니다."));
                }
                finally
                {
                    // ✅ 반드시 복구
                    SafeUI(() => chkUseCgi.Enabled = true);
                }
            }
        }


        private void SendStopPlayToSpeaker(string ip)
        {
            using (var client = new TcpClient())
            {
                client.SendTimeout = 1500;
                client.ReceiveTimeout = 1500;
                client.Connect(ip, 39999);

                byte[] data = Encoding.UTF8.GetBytes("stop_play");
                using (var stream = client.GetStream())
                {
                    stream.Write(data, 0, data.Length);
                    stream.Flush();
                }
            }

            LogTTS($"[STOP] {ip} stop_play 전송");
        }

        private async Task<bool> SendTtsToCgiDigestAsync(string ip, string model, string localMp3Path, CancellationToken ct)
        {
            string ulawPath = Path.ChangeExtension(localMp3Path, ".ul");
            TcpClient client = null;

            try
            {
                if (!ConvertMp3ToUlaw(localMp3Path, ulawPath)) return false;
                byte[] audioData = File.ReadAllBytes(ulawPath);
                int audioLength = audioData.Length;

                // ✅ 포트: Aepel도 우선 80으로 시도 권장 (필요 시 설정값으로 분리하세요)
                bool isAxis = string.Equals(model?.Trim(), "AXIS", StringComparison.OrdinalIgnoreCase);
                int port = (model == "AXIS") ? 80 : 8888;
                string uri = (model == "AXIS") ? "/axis-cgi/audio/transmit.cgi" : "/cgi-bin/transmit.cgi";

                client = new TcpClient();
                client.NoDelay = true;
                await client.ConnectAsync(ip, port);
                var stream = client.GetStream();

                // [1] 401 유도
                string req1 =
                    $"POST {uri} HTTP/1.1\r\n" +
                    $"Host: {ip}:{port}\r\n" +
                    $"Connection: close\r\n" +
                    $"Content-Length: 0\r\n\r\n";

                await WriteAsciiAsync(stream, req1, ct);
                string resp1 = await ReadHttpHeaderAsync(stream, ct);
                if (!resp1.Contains("401 Unauthorized"))
                {
                    LogTTS($"[CGI] {ip}({model}): 401 응답이 아님. resp1=\n{resp1}");
                    return false;
                }

                var challenge = ParseDigestChallenge(resp1);

                // ✅ qop는 챌린지 기반으로
                string qop = string.IsNullOrWhiteSpace(challenge.Qop) ? "" : "auth";
                string nc = "00000001";
                string cnonce = Guid.NewGuid().ToString("N").Substring(0, 16);

                string ha1 = MD5Hex($"{CGI_ID}:{challenge.Realm}:{CGI_PW}");
                string ha2 = MD5Hex($"POST:{uri}");

                string response;
                bool useQop = !string.IsNullOrWhiteSpace(qop);

                if (useQop)
                    response = MD5Hex($"{ha1}:{challenge.Nonce}:{nc}:{cnonce}:{qop}:{ha2}");
                else
                    response = MD5Hex($"{ha1}:{challenge.Nonce}:{ha2}");

                // ✅ Authorization 헤더 구성
                string authHeader;
                if (model == "AXIS")
                {
                    if (useQop)
                    {
                        authHeader =
                            $"Digest username=\"{CGI_ID}\", realm=\"{challenge.Realm}\", nonce=\"{challenge.Nonce}\", uri=\"{uri}\", " +
                            $"qop=\"{qop}\", nc={nc}, cnonce=\"{cnonce}\", response=\"{response}\"";
                    }
                    else
                    {
                        authHeader =
                            $"Digest username=\"{CGI_ID}\", realm=\"{challenge.Realm}\", nonce=\"{challenge.Nonce}\", uri=\"{uri}\", " +
                            $"response=\"{response}\"";
                    }
                }
                else // AEPEL
                {
                    string opaque = challenge.Opaque; // opaque 없으면 아예 빼는게 안전(임의 생성 비권장)

                    var parts = new List<string>
            {
                $"username=\"{CGI_ID}\"",
                $"realm=\"{challenge.Realm}\"",
                $"nonce=\"{challenge.Nonce}\"",
                $"uri=\"{uri}\"",
                $"response=\"{response}\"",
                "algorithm=\"MD5\""
            };

                    if (useQop)
                    {
                        parts.Add($"qop=\"{qop}\"");
                        parts.Add($"nc={nc}");
                        parts.Add($"cnonce=\"{cnonce}\"");
                    }

                    if (!string.IsNullOrWhiteSpace(opaque))
                        parts.Add($"opaque=\"{opaque}\"");

                    authHeader = "Digest " + string.Join(", ", parts);
                }

                // ✅ IMPORTANT: req2는 새 연결로 보내는 게 더 안정적일 때가 많습니다.
                // (일부 기기는 401 받은 소켓을 재사용하면 이상동작)
                stream.Dispose();
                client.Close();
                client.Dispose();

                client = new TcpClient();
                client.NoDelay = true;
                await client.ConnectAsync(ip, port);
                stream = client.GetStream();

                string req2 =
                    $"POST {uri} HTTP/1.1\r\n" +
                    $"Host: {ip}:{port}\r\n" +
                    "Content-Type: audio/basic\r\n" +
                    $"Content-Length: {audioLength}\r\n" +
                    "Connection: close\r\n" +
                    $"Authorization: {authHeader}\r\n\r\n";

                await WriteAsciiAsync(stream, req2, ct);

                // ✅ 오디오는 1번만 전송
                await SendUlawPacedAsync(stream, audioData, ct);

                // ✅ EOF 명확히 알림
                try { client.Client.Shutdown(System.Net.Sockets.SocketShutdown.Send); } catch { }

                // ✅ 응답 헤더는 "가능하면" 확인
                try
                {
                    string resp2 = await ReadHttpHeaderAsync(stream, ct, timeoutMs: 8000);

                    if (!(resp2.Contains("200 OK") || resp2.Contains("204") || resp2.Contains("201")))
                    {
                        LogTTS($"[CGI] {ip}({model}): req2 실패 응답.\n{resp2}");
                        return false;
                    }
                }
                catch (TimeoutException)
                {
                    // ✅ AEPEL은 응답 헤더가 늦거나 없을 수 있음 → 전송 완료로 간주
                    if (string.Equals(model?.Trim(), "AXIS", StringComparison.OrdinalIgnoreCase))
                        throw;

                    LogTTS($"[CGI] {ip}({model}): HTTP 헤더 타임아웃이지만 전송 완료로 간주");
                }

                // 재생 대기(필요 시)
                int playMs = (int)(audioLength / 8.0) + 1500;
                LogTTS($"[CGI] {ip}({model}): 전송 완료, 재생 대기 {playMs}ms");
                await Task.Delay(playMs, ct);

                return true;
            }
            catch (Exception ex)
            {
                LogTTS($"[CGI 에러] {ip} 예외: {ex}");
                return false;
            }
            finally
            {
                try { client?.Close(); client?.Dispose(); } catch { }
                if (File.Exists(ulawPath)) { try { File.Delete(ulawPath); } catch { } }
            }
        }
        private static async Task SendUlawPacedAsync(NetworkStream stream, byte[] audio, CancellationToken ct)
        {
            const int chunk = 160;   // 20ms @ 8000 bytes/sec
            const int frameMs = 20;

            int offset = 0;
            var sw = Stopwatch.StartNew();
            int frame = 0;

            while (offset < audio.Length)
            {
                int n = Math.Min(chunk, audio.Length - offset);
                await stream.WriteAsync(audio, offset, n, ct);
                offset += n;
                frame++;

                // 목표 시간까지 대기 (드리프트 보정)
                long target = frame * frameMs;
                long elapsed = sw.ElapsedMilliseconds;
                int wait = (int)(target - elapsed);
                if (wait > 0) await Task.Delay(wait, ct);
            }

            await stream.FlushAsync(ct);
        }

        // Digest 인증 정보를 담는 구조체
        public struct DigestChallenge
        {
            public string Realm;
            public string Nonce;
            public string Qop;
            public string Opaque;
        }

        // ASCII 문자열 전송 전용
        private static async Task WriteAsciiAsync(NetworkStream s, string text, CancellationToken ct)
        {
            byte[] b = Encoding.ASCII.GetBytes(text);
            await s.WriteAsync(b, 0, b.Length, ct);
        }

        // HTTP 응답 헤더 읽기 (타임아웃 포함)
        private static async Task<string> ReadHttpHeaderAsync(NetworkStream s, CancellationToken ct, int timeoutMs = 3000)
        {
            using var ms = new MemoryStream();
            byte[] buf = new byte[1024];

            while (true)
            {
                // ✅ ReadAsync를 timeout과 경쟁시켜 무한대기 방지
                Task<int> readTask = s.ReadAsync(buf, 0, buf.Length, ct);
                Task delayTask = Task.Delay(timeoutMs, ct);

                Task finished = await Task.WhenAny(readTask, delayTask).ConfigureAwait(false);

                if (finished == delayTask)
                    throw new TimeoutException($"HTTP 헤더 수신 타임아웃({timeoutMs}ms)");

                int n = await readTask.ConfigureAwait(false);
                if (n <= 0) break;

                ms.Write(buf, 0, n);

                // ✅ 매번 ToArray()는 비싸지만 헤더 크기는 작으니 OK
                string txt = Encoding.ASCII.GetString(ms.ToArray());

                int idx = txt.IndexOf("\r\n\r\n", StringComparison.Ordinal);
                if (idx >= 0)
                    return txt.Substring(0, idx + 4); // ✅ 헤더까지만 반환

                if (ms.Length > 64 * 1024)
                    throw new Exception("HTTP 헤더 초과");
            }

            return Encoding.ASCII.GetString(ms.ToArray());
        }


        // Digest 챌린지 파싱
        private DigestChallenge ParseDigestChallenge(string authHeader)
        {
            string GetVal(string key)
            {
                // 따옴표 유무에 상관없이 값을 추출
                var m = Regex.Match(authHeader, key + "=(?:\"([^\"]+)\"|([^, \r\n]+))", RegexOptions.IgnoreCase);
                if (m.Success)
                    return !string.IsNullOrEmpty(m.Groups[1].Value) ? m.Groups[1].Value : m.Groups[2].Value;
                return "";
            }

            return new DigestChallenge
            {
                Realm = GetVal("realm"),
                Nonce = GetVal("nonce"),
                Qop = GetVal("qop"),
                Opaque = GetVal("opaque")
            };
        }

        private string MD5Hex(string input)
        {
            using (var md5 = System.Security.Cryptography.MD5.Create())
            {
                byte[] bytes = md5.ComputeHash(Encoding.UTF8.GetBytes(input));
                return BitConverter.ToString(bytes).Replace("-", "").ToLower(); // ✅ 소문자 필수
            }
        }

        private void StopSPStatusStream()
        {
            try { spStatusStreamCts?.Cancel(); } catch { }
            try { spStatusStreamCts?.Dispose(); } catch { }
            spStatusStreamCts = null;

            try { spStatusReader?.Dispose(); } catch { }
            try { spStatusNs?.Dispose(); } catch { }
            try { spStatusTcpClient?.Close(); } catch { }
            spStatusReader = null;
            spStatusNs = null;
            spStatusTcpClient = null;
        }

        // SIP Client
        private void chkSIPPasswordView_CheckedChanged(object sender, EventArgs e)
        {
            txtSIPPassword.UseSystemPasswordChar = !chkSIPPasswordView.Checked;
        }
        private void chkSIPReRegister_CheckedChanged(object sender, EventArgs e)
        {
            if (chkSIPReRegister.Checked)
            {
                _regKeepTimer.Start();

                // 등록이 아직 아니면 바로 등록 시도
                if (_regUa == null || !_registered)
                    StartRegistrationFromUi();
            }
            else
            {
                _regKeepTimer.Stop();
                // ✅ 여기서 "등록 해제"까지 할지 여부는 정책입니다.
                // 원하시면 아래 주석을 해제하면 체크 해제 시 등록도 Stop 합니다.
                StopRegistration();
            }
        }
        private void btnSIPRegister_Click(object sender, EventArgs e)
        {
            if (_registered)
            {
                StopRegistration();
            }
            else
            {
                StartRegistrationFromUi();
            }
        }
        private (string host, int port, string domain) ParseSipServer(string s)
        {
            s = (s ?? "").Trim();
            if (string.IsNullOrWhiteSpace(s)) throw new Exception("서버주소가 비어있습니다.");

            string host = s;
            int port = 5060;

            // host:port 형태
            var parts = s.Split(':');
            if (parts.Length == 2 && int.TryParse(parts[1], out int p))
            {
                host = parts[0];
                port = p;
            }

            // SIPSorcery 등록은 "domain" 문자열에 host 또는 host:port를 넣어도 동작합니다(예제도 domain 사용) :contentReference[oaicite:1]{index=1}
            string domain = (port == 5060) ? host : $"{host}:{port}";
            return (host, port, domain);
        }


        private void StartRegistrationFromUi()
        {
            try
            {
                string server = txtSIPServer.Text;
                string user = (txtSIPUser.Text ?? "").Trim();
                string pass = txtSIPPassword.Text ?? "";

                if (string.IsNullOrWhiteSpace(user))
                {
                    MessageBox.Show("사용자ID를 입력하세요.");
                    return;
                }

                var (host, port, domain) = ParseSipServer(server);

                // (재)생성
                CreateOrResetSipStackIfNeeded();

                // 기존 regUA 정리
                if (_regUa != null)
                {
                    try { _regUa.Stop(); } catch { /* ignore */ }
                    _regUa = null;
                }

                int expiry = 300; // 5분(권장: 120~600 사이)
                _regUa = new SIPRegistrationUserAgent(_sipTransport, user, pass, domain, expiry);

                // Event handlers (SIPSorcery 10.x 시그니처)
                _regUa.RegistrationSuccessful += (uri, resp) =>
                {
                    _registered = true;
                    _lastRegOkUtc = DateTime.UtcNow;

                    SafeUi(() =>
                    {
                        SetStatus($"등록성공: {uri}", Color.Green);
                        btnSIPRegister.Text = "등록중지";
                    });
                };

                _regUa.RegistrationFailed += (uri, resp, err) =>
                {
                    _registered = false;

                    SafeUi(() =>
                    {
                        // resp.Status / resp.ReasonPhrase 를 같이 보여주면 디버깅이 쉬움
                        string respTxt = (resp != null) ? $"{(int)resp.Status} {resp.ReasonPhrase}" : "no response";
                        SetStatus($"등록실패: {err}", Color.Red);
                        btnSIPRegister.Text = "등록";
                    });
                };

                _regUa.RegistrationTemporaryFailure += (uri, resp, msg) =>
                {
                    _registered = false;

                    SafeUi(() =>
                    {
                        string respTxt = (resp != null) ? $"{(int)resp.Status} {resp.ReasonPhrase}" : "no response";
                        SetStatus($"일시실패: {msg}", Color.DarkOrange);
                        btnSIPRegister.Text = "등록";
                    });
                };

                _regUa.RegistrationRemoved += (uri, resp) =>
                {
                    _registered = false;

                    SafeUi(() =>
                    {
                        string respTxt = (resp != null) ? $"{(int)resp.Status} {resp.ReasonPhrase}" : "no response";
                        SetStatus($"등록해제/만료", Color.Gray);
                        btnSIPRegister.Text = "등록";
                    });
                };

                SetStatus("등록 시도중...", Color.DarkBlue);
                btnSIPRegister.Text = "등록중...";
                _regUa.Start(); // 핵심 :contentReference[oaicite:2]{index=2}
            }
            catch (Exception ex)
            {
                MessageBox.Show("SIP 등록 시작 오류:\n" + ex.Message);
                SetStatus("등록 오류");
                btnSIPRegister.Text = "등록";
            }
        }
        private void CreateOrResetSipStackIfNeeded()
        {
            if (_sipTransport != null) return;

            _sipTransport = new SIPTransport();

            // UDP 채널 추가 (로컬 포트 0 = OS가 임의 포트 배정)
            var udpChannel = new SIPUDPChannel(new IPEndPoint(IPAddress.Any, 0));
            _sipTransport.AddSIPChannel(udpChannel);
        }
        private void StopRegistration()
        {
            try
            {
                _regKeepTimer.Stop();

                if (_regUa != null)
                {
                    _regUa.Stop();
                    _regUa = null;
                }

                _registered = false;
                SetStatus("등록중지됨");
                btnSIPRegister.Text = "등록";
            }
            catch (Exception ex)
            {
                MessageBox.Show("등록 중지 오류:\n" + ex.Message);
            }
        }
        private void KeepRegistrationIfNeeded()
        {
            if (!chkSIPReRegister.Checked) return;

            // 등록이 살아있으면 OK
            if (_registered) return;

            // 너무 자주 재시도 방지: 마지막 성공/시도 후 일정 시간 지나면 재시도
            var sinceOk = DateTime.UtcNow - _lastRegOkUtc;

            // 마지막 성공이 오래전이거나(=아예 성공한 적 없거나) 지금 미등록이면 재시도
            if (_regUa == null || sinceOk > TimeSpan.FromSeconds(15))
            {
                SafeUi(() => SetStatus("등록유지: 재등록 시도..."));
                StartRegistrationFromUi();
            }
        }
        private void SafeUi(Action a)
        {
            if (IsDisposed) return;
            if (InvokeRequired) BeginInvoke(a);
            else a();
        }

        private void SetStatus(string s)
        {
            lblSIPStatus.Text = s;
        }
        private void SetStatus(string text, Color? color = null)
        {
            lblSIPStatus.Text = text;

            if (color.HasValue)
                lblSIPStatus.ForeColor = color.Value;
        }


        private void MicCapture_DataAvailable(object sender, WaveInEventArgs e)
        {
            float max = 0f;

            for (int i = 0; i < e.BytesRecorded; i += 2)
            {
                short sample = (short)(e.Buffer[i] | (e.Buffer[i + 1] << 8));

                int adjusted = (int)(sample * _micGain);
                if (adjusted > short.MaxValue) adjusted = short.MaxValue;
                if (adjusted < short.MinValue) adjusted = short.MinValue;

                float v = Math.Abs(adjusted / 32768f);
                if (v > max) max = v;
            }

            int level = Math.Max(0, Math.Min(100, (int)(max * 100)));

            SafeUi(() => progressBarSoundMic.Value = level);
        }
        private void trackBarMic_Scroll(object sender, EventArgs e)
        {
            _micGain = trackBarMic.Value / 100f;
        }
        private void trackBarSpk_Scroll(object sender, EventArgs e)
        {
            if (_uiUpdating) return;

            // 시스템 스피커 마스터 볼륨 조절
            if (_spkDevice != null)
                _spkDevice.AudioEndpointVolume.MasterVolumeLevelScalar = trackBarSpk.Value / 100f;

            _spkGain = trackBarSpk.Value / 100f;
        }
        private void VuTimer_Tick(object sender, EventArgs e)
        {
            try
            {
                if (_micDevice != null)
                {
                    var vol = _micDevice.AudioEndpointVolume;
                    float peak = _micDevice.AudioMeterInformation.MasterPeakValue;

                    int micLevel = Clamp0_100((int)(peak * 100));
                    progressBarSoundMic.Value = micLevel;

                    // ✅ 눈으로 확인용(임시)
                   //blSIPStatus.Text = $"MicPeak={micLevel}%  Mute={vol.Mute}  Vol={(int)(vol.MasterVolumeLevelScalar * 100)}%";
                }

                if (_spkDevice != null)
                {
                    float spkPeak = _spkDevice.AudioMeterInformation.MasterPeakValue;
                    int spkLevel = Clamp0_100((int)(spkPeak * 100));
                    progressBarSoundSpk.Value = spkLevel;
                }
            }
            catch (Exception ex)
            {
                lblSIPStatus.Text = "VU 예외: " + ex.Message;
            }
        }
        private int FindMicWaveInDeviceIndex()
        {
            var sb = new StringBuilder();
            int best = -1;

            for (int i = 0; i < WaveIn.DeviceCount; i++)
            {
                var caps = WaveIn.GetCapabilities(i);
                sb.AppendLine($"Index {i} : {caps.ProductName}");

                // 한국어/영어 모두 대응
                var name = (caps.ProductName ?? "").ToLower();
                if (best < 0 && (name.Contains("마이크") || name.Contains("microphone")))
                    best = i;
            }

        //    MessageBox.Show(sb.ToString(), "WaveIn Devices");

            return (best >= 0) ? best : 0;
        }



        // 라이센스관련
        // === 라이선스 UI 이벤트 연결 ===
        private void WireLicenseUi()
        {
            // 기존 바인딩
            txtKeyAll.TextChanged += txtKeyAll_TextChanged;
            txtKeyAll.KeyDown += txtKeyAll_KeyDown;
            btnShowHwid.Click += btnShowHwid_Click;
            btnActivate.Click += btnActivate_Click;
            lnkLicenseHelp.LinkClicked += lnkLicenseHelp_LinkClicked;

            // 상태 변경 이벤트 → 표시 통일
            LicenseManager.LicenseStateChanged += () =>
            {
                if (InvokeRequired) BeginInvoke((Action)UpdateLicenseStatusFromManager);
                else UpdateLicenseStatusFromManager();
            };
        }

        // === 시작 시 저장된 라이선스 검사 ===
        private void EnsureLicensed()
        {
            AppendAppLog($"[LICENSE][STARTUP] exists={File.Exists(LicenseService.LicenseStorePath)} path={LicenseService.LicenseStorePath}");

            // 매니저가 파일 읽고 상태 계산
            LicenseManager.LoadOrCreateFallback();

            // HWID 표기
            txtHwid.Text = LicenseService.GetMachineHwid();

            // 라벨은 항상 전용 함수로 갱신
            UpdateLicenseStatusFromManager();
        }

        // === HWID 보기/복사 ===
        private void btnShowHwid_Click(object sender, EventArgs e)
        {
            var hwid = LicenseService.GetMachineHwid();
            txtHwid.Text = hwid;
            try { Clipboard.SetText(hwid); } catch { }
            txtLicenseStatus.Text = "HWID를 클립보드에 복사했습니다.";
        }

        // === 제품키 등록/활성화 ===
        private void btnActivate_Click(object sender, EventArgs e)
        {
            var key = ReadUserEnteredKey();
            var (ok, reason, info) = LicenseService.VerifyKey(key);

            // 만료(E7)는 저장 허용, 그 외 실패는 중단
            bool isExpiredFromVerify = reason?.StartsWith("E7") == true;
            if (!ok && !isExpiredFromVerify)
            {
                txtLicenseStatus.Text = $"실패: {reason}";
                txtLicenseStatus.ForeColor = Color.Firebrick;
                return;
            }

            // 저장 (만료여도 저장)
            if (!LicenseService.SaveActivated(info, key))
            {
                txtLicenseStatus.Text = "실패: 라이선스 저장 오류";
                txtLicenseStatus.ForeColor = Color.Firebrick;
                MessageBox.Show($"라이선스 저장 실패\n경로: {LicenseService.LicenseStorePath}",
                    "저장 실패", MessageBoxButtons.OK, MessageBoxIcon.Error);
                AppendAppLog($"[LICENSE][SAVE][FAIL] path={LicenseService.LicenseStorePath}");
                return;
            }

            // 저장 후 매니저로 다시 읽고 상태 반영
            LicenseManager.LoadOrCreateFallback();
            ApplyLicenseEnforcement();
            RefreshLicensePanelFromState();

            // ✅ 표시는 항상 매니저 상태 기반
            UpdateLicenseStatusFromManager();

            AppendAppLog($"[LICENSE][DEBUG] expiry={info?.expiry}, manager.expired={LicenseManager.IsExpired}, path={LicenseManager.LicenseFilePath}");
        }
        // 상태 라벨/색상 갱신: 항상 LicenseManager 상태만 사용
        private void UpdateLicenseStatusFromManager()
        {
            var info = LicenseManager.Current;
            var expiryText = LicenseManager.IsPerpetual ? "영구" : (info?.expiry ?? "-");

            if (info != null && !LicenseManager.IsExpired)
            {
                txtLicenseStatus.Text = $"상태: 정상 (Edition={info?.edition ?? "-"}, 만료={expiryText})";
                txtLicenseStatus.ForeColor = Color.ForestGreen;
            }
            else
            {
                var reason = string.IsNullOrEmpty(LicenseManager.FailReason)
                    ? "라이선스 미등록/만료"
                    : LicenseManager.FailReason;
                txtLicenseStatus.Text = $"상태: {reason}";
                txtLicenseStatus.ForeColor = Color.Firebrick;
                try { tabControl1.SelectedTab = tabSystem; } catch { }
            }
        }


        private void txtKeyAll_KeyDown(object sender, KeyEventArgs e)
        {
            if (e.Control && e.KeyCode == Keys.V)
            {
                try
                {
                    var clip = Clipboard.GetText()?.Trim();
                    if (string.IsNullOrEmpty(clip)) return;

                    if (clip.Contains(".")) // payload.sig 전체키
                    {
                        txtKeyAll.Text = clip;
                        txtKeyAll.SelectionStart = txtKeyAll.Text.Length;
                        e.SuppressKeyPress = true;
                        return;
                    }

                    // 그 외 긴 문자열: 영숫자만 추출 후 대문자
                    var cleaned = new string(clip.Where(char.IsLetterOrDigit).ToArray()).ToUpperInvariant();
                    txtKeyAll.Text = cleaned;
                    txtKeyAll.SelectionStart = txtKeyAll.Text.Length;
                    e.SuppressKeyPress = true;
                }
                catch { }
            }

            // 엔터로 바로 등록
            if (e.KeyCode == Keys.Enter)
            {
                e.SuppressKeyPress = true;
                btnActivate.PerformClick();
            }
        }

        // === 도움말 ===
        private void lnkLicenseHelp_LinkClicked(object sender, LinkLabelLinkClickedEventArgs e)
        {
            MessageBox.Show(
                "1) 'HWID 보기/복사'로 이 PC의 HWID를 복사합니다.\n" +
                "2) HWID를 회사에 전달하여 제품 키(payload.sig)를 발급받습니다.\n" +
                "3) 발급된 제품 키를 입력 후 '등록/활성화'를 클릭하세요.\n" +
                "4) PC 교체 시 새 HWID로 재발급을 요청하세요.",
                "라이선스 안내", MessageBoxButtons.OK, MessageBoxIcon.Information);
        }

        // === 보조: 사용자 입력에서 키 읽기 ===
        // - 발급툴의 전체키(payload.sig, '.' 포함)를 그대로 붙여넣은 경우도 지원
        // - 4칸(16자)만 입력한 경우엔 그대로 합쳐서 처리
        private string ReadUserEnteredKey()
        {
            var s = txtKeyAll?.Text?.Trim();
            if (string.IsNullOrWhiteSpace(s)) return null;

            // 허용문자만 남기기 (영숫자/.-_)
            var cleaned = new string(s.Where(c => char.IsLetterOrDigit(c) || c == '.' || c == '-' || c == '_').ToArray());

            // payload.sig 형태면 앞의 두 조각만 사용(여분 제거)
            if (cleaned.Contains("."))
            {
                var parts = cleaned.Split('.');
                if (parts.Length >= 2) return parts[0] + "." + parts[1];
            }

            // 그 외(단축키 등)는 그대로 반환
            return cleaned.ToUpperInvariant();
        }
        private void txtKeyAll_TextChanged(object sender, EventArgs e)
        {
            var tb = txtKeyAll;
            int caret = tb.SelectionStart;

            var filtered = new string(tb.Text
                .Where(c => char.IsLetterOrDigit(c) || c == '.' || c == '-' || c == '_')
                .ToArray());

            // 전체키(payload.sig)가 아니면만 대문자화(단축키 호환)
            if (!filtered.Contains("."))
                filtered = filtered.ToUpperInvariant();

            if (filtered != tb.Text)
            {
                tb.Text = filtered;
                tb.SelectionStart = Math.Min(caret, tb.Text.Length);
            }
        }

        private void AppendAppLog(string line)
        {
            try
            {
                File.AppendAllText(logFilePath,
                    $"[{DateTime.Now:yyyy-MM-dd HH:mm:ss}] {line}{Environment.NewLine}",
                    Encoding.UTF8);
            }
            catch
            {
                // 로그 실패 무시
            }
        }
        private void LogLicense(string action, bool ok, string reason, LicenseInfo info, string rawKey)
        {
            // 영구판 여부 체크
            string expiryRaw = info?.expiry ?? "-";
            bool isPerpetual = LicenseManager.IsPerpetual
                               || expiryRaw.StartsWith("9999-12-31", StringComparison.Ordinal)  // 백업 안전장치
                               || expiryRaw == "-"
                               || expiryRaw.Equals("PERPETUAL", StringComparison.OrdinalIgnoreCase);

            string expiryText = isPerpetual ? "영구" : expiryRaw;

            string summary = string.Format(
                "[LICENSE][{0}][{1}] reason={2} hwid={3} edition={4} expiry={5} order={6} keyhash={7}",
                action,
                ok ? "OK" : "FAIL",
                string.IsNullOrEmpty(reason) ? "-" : reason,
                LicenseService.GetMachineHwid(),
                info?.edition ?? "-",
                expiryText,
                info?.order_id ?? "-",
                KeyHash12(rawKey)
            );

            AppendAppLog(summary);
        }


        private static string KeyHash12(string key)
        {
            if (string.IsNullOrWhiteSpace(key)) return "-";
            try
            {
                // 공백/대시 등 정규화(서버 검증과 동일 규칙으로)
                string compact = LicenseService.NormalizeKey(key) ?? key;

                using (var sha = SHA256.Create())
                {
                    byte[] hash = sha.ComputeHash(Encoding.UTF8.GetBytes(compact));
                    // 앞 6바이트 → 12 hex 문자
                    var sb = new StringBuilder(12);
                    for (int i = 0; i < 6; i++)
                        sb.Append(hash[i].ToString("x2"));
                    return sb.ToString();
                }
            }
            catch
            {
                return "-";
            }
        }
        public static string NormalizeKey(string key)
        {
            if (string.IsNullOrWhiteSpace(key)) return null;
            var s = key.Trim();

            if (s.Contains(".")) // payload.sig 전체키 → 원형 유지
            {
                return new string(s.Where(c => char.IsLetterOrDigit(c) || c == '.' || c == '-' || c == '_').ToArray());
            }
            else // 4칸(16자) 단축키만 대문자화
            {
                var raw = new string(s.Where(char.IsLetterOrDigit).ToArray());
                return raw.ToUpperInvariant();
            }
        }
    }
}
