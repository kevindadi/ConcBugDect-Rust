use axum::extract::{Path, State};
use axum::http::{HeaderMap, HeaderValue, StatusCode, header};
use axum::response::{Html, IntoResponse, Response};
use axum::routing::{get, post};
use axum::{Json, Router};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::fs;
use std::net::SocketAddr;
use std::path::{Component, Path as FsPath, PathBuf};
use tokio::process::Command;

const DEFAULT_OUTPUT_ROOT: &str = "./tmp";

#[derive(Clone)]
struct AppState {
    runs_root: PathBuf,
    cases_root: PathBuf,
}

#[derive(Serialize)]
struct RunEntry {
    name: String,
    has_summary: bool,
}

#[derive(Serialize)]
struct CaseEntry {
    path: String,
}

#[derive(Deserialize)]
struct GenerateRequest {
    case_path: String,
    mode: String,
    no_reduce: Option<bool>,
}

#[derive(Serialize)]
struct GenerateResponse {
    run_name: String,
    output_dir: String,
    logs: String,
}

#[tokio::main]
async fn main() {
    let (runs_root, cases_root, port) = parse_args();
    let state = AppState {
        runs_root: runs_root.clone(),
        cases_root: cases_root.clone(),
    };

    let app = Router::new()
        .route("/", get(index))
        .route("/reduction", get(reduction_index))
        .route("/app.js", get(app_js))
        .route("/reduction.js", get(reduction_js))
        .route("/api/runs", get(list_runs))
        .route("/api/cases", get(list_cases))
        .route("/api/generate", post(generate_run))
        .route("/api/run/{name}/summary", get(run_summary))
        .route("/api/run/{name}/artifact/{kind}", get(run_artifact))
        .route("/health", get(health))
        .with_state(state);

    let addr = SocketAddr::from(([127, 0, 0, 1], port));
    log::debug!(
        "pn-web cases={} runs={} at http://{}",
        cases_root.display(),
        runs_root.display(),
        addr
    );

    let listener = tokio::net::TcpListener::bind(addr)
        .await
        .expect("bind pn-web listener");
    axum::serve(listener, app).await.expect("serve pn-web");
}

fn parse_args() -> (PathBuf, PathBuf, u16) {
    let mut runs_root = PathBuf::from(DEFAULT_OUTPUT_ROOT);
    let mut cases_root = PathBuf::from("./benchmarks");
    let mut port: u16 = 7878;

    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--runs-root" | "--root" => {
                if let Some(v) = args.next() {
                    runs_root = PathBuf::from(v);
                }
            }
            "--cases-root" => {
                if let Some(v) = args.next() {
                    cases_root = PathBuf::from(v);
                }
            }
            "--port" => {
                if let Some(v) = args.next() {
                    if let Ok(p) = v.parse::<u16>() {
                        port = p;
                    }
                }
            }
            _ => {}
        }
    }

    (runs_root, cases_root, port)
}

async fn index() -> Html<&'static str> {
    Html(INDEX_HTML)
}

async fn reduction_index() -> Html<&'static str> {
    Html(REDUCTION_HTML)
}

async fn app_js() -> Response {
    let mut headers = HeaderMap::new();
    headers.insert(
        header::CONTENT_TYPE,
        HeaderValue::from_static("application/javascript; charset=utf-8"),
    );
    (headers, APP_JS).into_response()
}

async fn reduction_js() -> Response {
    let mut headers = HeaderMap::new();
    headers.insert(
        header::CONTENT_TYPE,
        HeaderValue::from_static("application/javascript; charset=utf-8"),
    );
    (headers, REDUCTION_JS).into_response()
}

async fn health() -> &'static str {
    "ok"
}

async fn list_runs(State(state): State<AppState>) -> Result<Json<Vec<RunEntry>>, ApiError> {
    let mut runs = Vec::new();
    fs::create_dir_all(&state.runs_root).map_err(ApiError::io)?;
    let mut stack = vec![(state.runs_root.clone(), 0usize)];

    while let Some((dir, depth)) = stack.pop() {
        for entry in fs::read_dir(&dir).map_err(ApiError::io)? {
            let entry = entry.map_err(ApiError::io)?;
            let path = entry.path();
            if !path.is_dir() {
                continue;
            }

            let has_summary = path.join("summary.json").exists();
            let has_artifacts = path.join("petrinet_raw.dot").exists()
                || path.join("petrinet.dot").exists()
                || path.join("stategraph.dot").exists()
                || path.join("callgraph.dot").exists();

            if has_summary || has_artifacts {
                let rel = path
                    .strip_prefix(&state.runs_root)
                    .map_err(|e| ApiError::bad_request(e.to_string()))?
                    .to_string_lossy()
                    .to_string();
                runs.push(RunEntry {
                    name: rel,
                    has_summary,
                });
            }
            if depth < 6 {
                stack.push((path, depth + 1));
            }
        }
    }

    runs.sort_by(|a, b| a.name.cmp(&b.name));
    Ok(Json(runs))
}

async fn list_cases(State(state): State<AppState>) -> Result<Json<Vec<CaseEntry>>, ApiError> {
    let mut cases = Vec::new();
    if !state.cases_root.exists() {
        return Ok(Json(cases));
    }

    let mut stack = vec![(state.cases_root.clone(), 0usize)];
    while let Some((dir, depth)) = stack.pop() {
        for entry in fs::read_dir(&dir).map_err(ApiError::io)? {
            let entry = entry.map_err(ApiError::io)?;
            let path = entry.path();
            if path.is_dir() {
                if depth < 8 {
                    stack.push((path, depth + 1));
                }
                continue;
            }
            if path.extension().and_then(|s| s.to_str()) != Some("rs") {
                continue;
            }
            let rel = path
                .strip_prefix(&state.cases_root)
                .map_err(|e| ApiError::bad_request(e.to_string()))?
                .to_string_lossy()
                .to_string();
            cases.push(CaseEntry { path: rel });
        }
    }

    cases.sort_by(|a, b| a.path.cmp(&b.path));
    Ok(Json(cases))
}

async fn generate_run(
    State(state): State<AppState>,
    Json(req): Json<GenerateRequest>,
) -> Result<Json<GenerateResponse>, ApiError> {
    let mode = match req.mode.as_str() {
        "deadlock" | "datarace" | "atomic" | "all" | "pointsto" => req.mode,
        _ => return Err(ApiError::bad_request("invalid mode")),
    };

    let case_file = case_file_path(&state.cases_root, &req.case_path)?;
    let out_root = state.runs_root.clone();

    ensure_safe_output_root(&out_root)?;
    clear_dir_contents(&out_root)?;

    let crate_stem = FsPath::new(&req.case_path)
        .file_stem()
        .and_then(|s| s.to_str())
        .ok_or_else(|| ApiError::bad_request("invalid case file name"))?
        .to_string();

    let mut cmd = Command::new("cargo");
    if mode == "atomic" {
        cmd.arg("run")
            .arg("--features")
            .arg("atomic-violation")
            .arg("--bin")
            .arg("pn");
    } else {
        cmd.arg("run").arg("--bin").arg("pn");
    }

    cmd.arg("--")
        .arg("-f")
        .arg(&case_file)
        .arg("-m")
        .arg(&mode)
        .arg("--pn-analysis-dir")
        .arg(&out_root)
        .arg("--viz-callgraph")
        .arg("--viz-petrinet")
        .arg("--viz-stategraph");

    if req.no_reduce.unwrap_or(false) {
        cmd.arg("--no-reduce");
    }

    cmd.arg("--").arg(&case_file);

    let output = cmd.output().await.map_err(ApiError::io)?;
    let mut logs = String::new();
    logs.push_str(&String::from_utf8_lossy(&output.stdout));
    logs.push_str(&String::from_utf8_lossy(&output.stderr));

    if !output.status.success() {
        return Err(ApiError {
            status: StatusCode::BAD_REQUEST,
            msg: format!("analysis failed:\n{logs}"),
        });
    }

    let out_dir = out_root.join(&crate_stem);
    Ok(Json(GenerateResponse {
        run_name: crate_stem,
        output_dir: out_dir.display().to_string(),
        logs,
    }))
}

async fn run_summary(
    State(state): State<AppState>,
    Path(name): Path<String>,
) -> Result<Json<Value>, ApiError> {
    let run_dir = run_dir(&state.runs_root, &name)?;
    let summary_path = run_dir.join("summary.json");
    if summary_path.exists() {
        let data = fs::read_to_string(summary_path).map_err(ApiError::io)?;
        let v: Value = serde_json::from_str(&data).map_err(ApiError::bad_request)?;
        return Ok(Json(v));
    }

    let v = serde_json::json!({
        "crate_name": name,
        "mode": "unknown",
        "reduced": null,
        "metrics": {
            "callable_functions": count_state_nodes(&run_dir.join("callgraph.dot"))?,
            "places": count_prefix_nodes(&run_dir.join("petrinet.dot"), "place_")?,
            "transitions": count_prefix_nodes(&run_dir.join("petrinet.dot"), "trans_")?,
            "state_classes": count_state_nodes(&run_dir.join("stategraph.dot"))?,
            "state_edges": count_state_edges(&run_dir.join("stategraph.dot"))?,
            "deadlock_states": null,
            "truncated": null
        }
    });
    Ok(Json(v))
}

async fn run_artifact(
    State(state): State<AppState>,
    Path((name, kind)): Path<(String, String)>,
) -> Result<Response, ApiError> {
    let run_dir = run_dir(&state.runs_root, &name)?;
    let rel = match kind.as_str() {
        "callgraph" => "callgraph.dot",
        "petrinet" => "petrinet.dot",
        "petrinet_raw" => "petrinet_raw.dot",
        "petrinet_reduce_1" => "petrinet_reduce_1_loop.dot",
        "petrinet_reduce_2" => "petrinet_reduce_2_sequence.dot",
        "petrinet_reduce_3" => "petrinet_reduce_3_intermediate.dot",
        "stategraph" => "stategraph.dot",
        "summary" => "summary.json",
        "deadlock" => "deadlock_report.txt.json",
        "datarace" => "datarace_report.txt.json",
        "atomic" => "atomicity_report.txt.json",
        "pointsto" => "points_to_report.txt",
        _ => return Err(ApiError::bad_request("unknown artifact kind")),
    };

    let path = run_dir.join(rel);
    if !path.exists() {
        return Err(ApiError::not_found("artifact not found"));
    }
    let body = fs::read_to_string(path).map_err(ApiError::io)?;

    let mime = if rel.ends_with(".json") {
        "application/json; charset=utf-8"
    } else {
        "text/plain; charset=utf-8"
    };
    let mut headers = HeaderMap::new();
    headers.insert(header::CONTENT_TYPE, HeaderValue::from_str(mime).unwrap());
    Ok((headers, body).into_response())
}

fn clear_dir_contents(dir: &FsPath) -> Result<(), ApiError> {
    fs::create_dir_all(dir).map_err(ApiError::io)?;
    for entry in fs::read_dir(dir).map_err(ApiError::io)? {
        let entry = entry.map_err(ApiError::io)?;
        let path = entry.path();
        if path.is_dir() {
            fs::remove_dir_all(path).map_err(ApiError::io)?;
        } else {
            fs::remove_file(path).map_err(ApiError::io)?;
        }
    }
    Ok(())
}

fn ensure_safe_output_root(dir: &FsPath) -> Result<(), ApiError> {
    let comp_cnt = dir.components().count();
    if comp_cnt <= 1 {
        return Err(ApiError::bad_request("pn_analysis_dir is too broad"));
    }
    if dir == FsPath::new("/") {
        return Err(ApiError::bad_request("pn_analysis_dir cannot be root"));
    }
    Ok(())
}

fn run_dir(root: &FsPath, name: &str) -> Result<PathBuf, ApiError> {
    let rel = FsPath::new(name);
    if rel.is_absolute() {
        return Err(ApiError::bad_request("invalid run name"));
    }
    if rel
        .components()
        .any(|c| matches!(c, Component::ParentDir | Component::Prefix(_)))
    {
        return Err(ApiError::bad_request("invalid run name"));
    }
    let p = root.join(rel);
    if !p.exists() || !p.is_dir() {
        return Err(ApiError::not_found("run not found"));
    }
    Ok(p)
}

fn case_file_path(root: &FsPath, case_path: &str) -> Result<PathBuf, ApiError> {
    let rel = FsPath::new(case_path);
    if rel.is_absolute() {
        return Err(ApiError::bad_request("invalid case path"));
    }
    if rel
        .components()
        .any(|c| matches!(c, Component::ParentDir | Component::Prefix(_)))
    {
        return Err(ApiError::bad_request("invalid case path"));
    }
    let p = root.join(rel);
    if !p.exists() || !p.is_file() {
        return Err(ApiError::not_found("case file not found"));
    }
    Ok(p)
}

fn count_state_nodes(path: &FsPath) -> Result<usize, ApiError> {
    count_dot_lines(path, |line| {
        let t = line.trim_start();
        t.chars().next().is_some_and(|c| c.is_ascii_digit()) && t.contains('[')
    })
}

fn count_prefix_nodes(path: &FsPath, prefix: &str) -> Result<usize, ApiError> {
    count_dot_lines(path, |line| {
        line.trim_start().starts_with(prefix) && line.contains('[')
    })
}

fn count_state_edges(path: &FsPath) -> Result<usize, ApiError> {
    count_dot_lines(path, |line| line.contains("->"))
}

fn count_dot_lines(path: &FsPath, predicate: impl Fn(&str) -> bool) -> Result<usize, ApiError> {
    use std::io::BufRead;

    match fs::File::open(path) {
        Ok(file) => Ok(std::io::BufReader::new(file)
            .lines()
            .map_while(Result::ok)
            .filter(|line| predicate(line))
            .count()),
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(0),
        Err(err) => Err(ApiError::io(err)),
    }
}

#[derive(Debug)]
struct ApiError {
    status: StatusCode,
    msg: String,
}

impl ApiError {
    fn io(err: std::io::Error) -> Self {
        Self {
            status: StatusCode::INTERNAL_SERVER_ERROR,
            msg: err.to_string(),
        }
    }

    fn bad_request<E: ToString>(e: E) -> Self {
        Self {
            status: StatusCode::BAD_REQUEST,
            msg: e.to_string(),
        }
    }

    fn not_found<E: ToString>(e: E) -> Self {
        Self {
            status: StatusCode::NOT_FOUND,
            msg: e.to_string(),
        }
    }
}

impl IntoResponse for ApiError {
    fn into_response(self) -> Response {
        let body = Json(serde_json::json!({"error": self.msg}));
        (self.status, body).into_response()
    }
}

const INDEX_HTML: &str = r#"<!doctype html>
<html lang='zh'>
<head>
  <meta charset='utf-8'>
  <meta name='viewport' content='width=device-width, initial-scale=1'>
  <title>RustPTA Web Viewer</title>
  <style>
    :root { --bg:#f7fafc; --fg:#0f172a; --card:#ffffff; --line:#dbe2ea; --accent:#0f766e; }
    html, body { height:100%; }
    body { margin:0; font-family: ui-sans-serif, system-ui, -apple-system, Segoe UI; background:var(--bg); color:var(--fg); }
    .top { display:flex; flex-wrap:wrap; gap:8px; align-items:center; padding:10px 14px; background:var(--card); border-bottom:1px solid var(--line); position:sticky; top:0; z-index:5; }
    select, button, input { padding:6px 8px; border:1px solid var(--line); border-radius:8px; background:white; }
    input { min-width: 340px; }
    button.active { border-color:var(--accent); color:var(--accent); }
    .grid { display:grid; grid-template-columns: 1.45fr 0.55fr; gap:10px; padding:10px; height: calc(100vh - 92px); box-sizing:border-box; }
    .card { background:var(--card); border:1px solid var(--line); border-radius:10px; overflow:hidden; min-height:0; }
    .card h3 { margin:0; font-size:14px; padding:8px 10px; border-bottom:1px solid var(--line); }
    .graph-wrap { height: calc(100% - 94px); }
    #graph { height:100%; width:100%; overflow:hidden; }
    #summary, #report, #status { white-space:pre-wrap; font-family: ui-monospace, SFMono-Regular, Menlo, monospace; font-size:12px; padding:10px; }
    #status { border-top:1px solid var(--line); max-height:94px; overflow:auto; }
    #graph svg { width:100% !important; height:100% !important; }
  </style>
  <script src='https://cdn.jsdelivr.net/npm/viz.js@2.1.2/viz.js'></script>
  <script src='https://cdn.jsdelivr.net/npm/viz.js@2.1.2/full.render.js'></script>
  <script src='https://cdn.jsdelivr.net/npm/svg-pan-zoom@3.6.1/dist/svg-pan-zoom.min.js'></script>
</head>
<body>
  <div class='top'>
    <strong>RustPTA Viewer</strong>
    <a href='/reduction'>Reduction stages</a>
    <label>Case: <select id='caseSelect'></select></label>
    <label>Mode:
      <select id='modeSelect'>
        <option value='deadlock'>deadlock</option>
        <option value='datarace'>datarace</option>
        <option value='atomic'>atomic</option>
      </select>
    </label>
    <button id='generateBtn'>Generate</button>
    <label>Run: <select id='runSelect'></select></label>
    <button data-kind='callgraph'>Call Graph</button>
    <button data-kind='petrinet_raw' class='active'>Petri Net (Raw)</button>
    <button data-kind='petrinet'>Petri Net (Final)</button>
    <button data-kind='stategraph'>State Graph</button>
    <button id='fitBtn'>Fit</button>
    <button id='reloadBtn'>Reload</button>
  </div>
  <div class='grid'>
    <div class='card'>
      <h3 id='graphTitle'>Graph</h3>
      <div class='graph-wrap'>
        <div id='graph'>Loading...</div>
      </div>
      <div id='status'></div>
    </div>
    <div style='display:grid; grid-template-rows: 0.7fr 1.3fr; gap:10px; min-height:0;'>
      <div class='card'>
        <h3>Summary</h3>
        <div id='summary'></div>
      </div>
      <div class='card'>
        <h3>Report</h3>
        <div id='report'></div>
      </div>
    </div>
  </div>
  <script src='/app.js'></script>
</body>
</html>
"#;

const REDUCTION_HTML: &str = r#"<!doctype html>
<html lang='zh'>
<head>
  <meta charset='utf-8'>
  <meta name='viewport' content='width=device-width, initial-scale=1'>
  <title>RustPTA Reduction Viewer</title>
  <style>
    :root { --bg:#f7fafc; --fg:#0f172a; --card:#ffffff; --line:#dbe2ea; }
    html, body { height:100%; }
    body { margin:0; font-family: ui-sans-serif, system-ui, -apple-system, Segoe UI; background:var(--bg); color:var(--fg); }
    .top { display:flex; flex-wrap:wrap; gap:8px; align-items:center; padding:10px 14px; background:var(--card); border-bottom:1px solid var(--line); position:sticky; top:0; z-index:5; }
    select, button { padding:6px 8px; border:1px solid var(--line); border-radius:8px; background:white; }
    .grid { display:grid; grid-template-columns: 1fr; grid-template-rows: repeat(3, 1fr); gap:10px; padding:10px; height: calc(100vh - 72px); box-sizing:border-box; }
    .card { background:var(--card); border:1px solid var(--line); border-radius:10px; overflow:hidden; min-height:0; }
    .card h3 { margin:0; font-size:14px; padding:8px 10px; border-bottom:1px solid var(--line); }
    .graph { width:100%; height:calc(100% - 36px); overflow:hidden; }
    .graph svg { width:100% !important; height:100% !important; }
  </style>
  <script src='https://cdn.jsdelivr.net/npm/viz.js@2.1.2/viz.js'></script>
  <script src='https://cdn.jsdelivr.net/npm/viz.js@2.1.2/full.render.js'></script>
  <script src='https://cdn.jsdelivr.net/npm/svg-pan-zoom@3.6.1/dist/svg-pan-zoom.min.js'></script>
</head>
<body>
  <div class='top'>
    <strong>Petri Net Reduction Stages</strong>
    <a href='/'>Home</a>
    <label>Run: <select id='runSelect'></select></label>
    <button id='reloadBtn'>Reload</button>
    <button id='fitBtn'>Fit All</button>
  </div>
  <div class='grid'>
    <div class='card'><h3>Stage 1: Loop Removal</h3><div id='g1' class='graph'></div></div>
    <div class='card'><h3>Stage 2: Sequence Merge</h3><div id='g2' class='graph'></div></div>
    <div class='card'><h3>Stage 3: Intermediate Elimination</h3><div id='g3' class='graph'></div></div>
  </div>
  <script src='/reduction.js'></script>
</body>
</html>
"#;

const APP_JS: &str = r#"
let currentKind = 'petrinet_raw';
let viz = new Viz();
let pz = null;

function setStatus(msg) {
  document.getElementById('status').textContent = msg || '';
}

async function loadCases() {
  const cases = await fetch('/api/cases').then(r => r.json());
  const sel = document.getElementById('caseSelect');
  sel.innerHTML = '';
  for (const c of cases) {
    const o = document.createElement('option');
    o.value = c.path;
    o.textContent = c.path;
    sel.appendChild(o);
  }
}

async function loadRuns(prefer) {
  const runs = await fetch('/api/runs').then(r => r.json());
  const sel = document.getElementById('runSelect');
  const prev = prefer || sel.value;
  sel.innerHTML = '';
  for (const r of runs) {
    const o = document.createElement('option');
    o.value = r.name;
    o.textContent = r.name + (r.has_summary ? '' : ' (no summary)');
    sel.appendChild(o);
  }
  if (runs.length > 0) {
    const hit = runs.find(x => x.name === prev);
    sel.value = hit ? prev : runs[runs.length - 1].name;
    await loadRun(sel.value);
  } else {
    document.getElementById('graph').textContent = 'No runs found.';
    document.getElementById('summary').textContent = '';
    document.getElementById('report').textContent = '';
  }
}

async function loadRun(name) {
  await Promise.all([loadSummary(name), loadGraph(name, currentKind), loadReport(name)]);
}

async function generate() {
  const casePath = document.getElementById('caseSelect').value;
  const mode = document.getElementById('modeSelect').value;
  if (!casePath) {
    setStatus('Please select a case first.');
    return;
  }
  setStatus(`Generating ${mode} for ${casePath} ...`);
  const payload = { case_path: casePath, mode };
  const res = await fetch('/api/generate', {
    method: 'POST',
    headers: { 'content-type': 'application/json' },
    body: JSON.stringify(payload)
  });
  const text = await res.text();
  if (!res.ok) {
    setStatus(text);
    return;
  }
  const data = JSON.parse(text);
  setStatus(data.logs || `Generated: ${data.run_name}`);
  await loadRuns(data.run_name);
}

function formatSummary(j) {
  const m = j.metrics || {};
  return [
    `crate: ${j.crate_name ?? '-'}`,
    `mode: ${j.mode ?? '-'}`,
    `reduced: ${j.reduced ?? '-'}`,
    `callable_functions: ${m.callable_functions ?? '-'}`,
    `petri_places: ${m.places ?? '-'}`,
    `petri_transitions: ${m.transitions ?? '-'}`,
    `state_classes: ${m.state_classes ?? '-'}`,
    `state_edges: ${m.state_edges ?? '-'}`,
    `deadlock_states: ${m.deadlock_states ?? '-'}`,
    `truncated: ${m.truncated ?? '-'}`
  ].join('\n');
}

async function loadSummary(name) {
  const data = await fetch(`/api/run/${encodeURIComponent(name)}/summary`).then(r => r.json());
  document.getElementById('summary').textContent = formatSummary(data);
}

async function loadGraph(name, kind) {
  const title = document.getElementById('graphTitle');
  title.textContent = kind;
  const graph = document.getElementById('graph');
  graph.textContent = 'Rendering...';

  const res = await fetch(`/api/run/${encodeURIComponent(name)}/artifact/${kind}`);
  if (!res.ok) {
    graph.textContent = `Artifact not found: ${kind}`;
    return;
  }
  const dot = await res.text();

  try {
    const svg = await viz.renderSVGElement(dot);
    graph.innerHTML = '';
    graph.appendChild(svg);
    if (pz) pz.destroy();
    pz = svgPanZoom(svg, {
      zoomEnabled: true,
      controlIconsEnabled: true,
      fit: true,
      center: true,
      minZoom: 0.02,
      maxZoom: 100,
      contain: true
    });
    await highlightDeadlocksInGraph(svg);
  } catch (e) {
    graph.textContent = 'Render failed. Showing DOT text.\n\n' + dot;
    viz = new Viz();
  }
}

async function loadReport(name) {
  const report = document.getElementById('report');
  for (const k of ['deadlock', 'datarace', 'atomic']) {
    const res = await fetch(`/api/run/${encodeURIComponent(name)}/artifact/${k}`);
    if (res.ok) {
      const body = await res.text();
      try {
        report.textContent = buildReadableReport(k, JSON.parse(body));
      } catch {
        report.textContent = body;
      }
      return;
    }
  }
  report.textContent = 'No report artifact found.';
}

function buildReadableReport(kind, j) {
  if (kind === 'deadlock') {
    let s = '';
    s += `Type: deadlock detection\n`;
    s += `Deadlock: ${j.has_deadlock ? 'yes' : 'no'}\n`;
    s += `Deadlock count: ${j.deadlock_count ?? 0}\n`;
    if (j.state_space_info) {
      s += `State space: states=${j.state_space_info.total_states}, transitions=${j.state_space_info.total_transitions}, reachable=${j.state_space_info.reachable_states}\n`;
    }
    if (Array.isArray(j.deadlock_states) && j.deadlock_states.length > 0) {
      s += `\nDeadlock states (global positions):\n`;
      for (const st of j.deadlock_states) {
        s += `- ${st.state_id}: ${st.description ?? ''}\n`;
      }
    }
    return s;
  }
  if (kind === 'datarace') return `Type: data race\nRace: ${j.has_race ? 'yes' : 'no'}\nRace count: ${j.race_count ?? 0}`;
  if (kind === 'atomic') return `Type: atomicity violation\nViolation: ${j.has_violation ? 'yes' : 'no'}\nViolation count: ${j.violation_count ?? 0}`;
  return JSON.stringify(j, null, 2);
}

async function highlightDeadlocksInGraph(svg) {
  if (currentKind !== 'stategraph') return;
  const name = document.getElementById('runSelect').value;
  if (!name) return;
  const res = await fetch(`/api/run/${encodeURIComponent(name)}/artifact/deadlock`);
  if (!res.ok) return;
  let j;
  try { j = await res.json(); } catch { return; }
  if (!Array.isArray(j.deadlock_states)) return;
  const ids = new Set(j.deadlock_states.map(x => x.state_id).filter(Boolean));
  if (ids.size === 0) return;
  for (const t of svg.querySelectorAll('text')) {
    const txt = (t.textContent || '').trim();
    if (ids.has(txt)) {
      const g = t.closest('g.node');
      if (!g) continue;
      const shape = g.querySelector('ellipse,polygon,path');
      if (shape) {
        shape.setAttribute('stroke', '#dc2626');
        shape.setAttribute('stroke-width', '3');
      }
    }
  }
}

document.getElementById('runSelect').addEventListener('change', (e) => loadRun(e.target.value));
document.getElementById('reloadBtn').addEventListener('click', async () => { await loadCases(); await loadRuns(); });
document.getElementById('fitBtn').addEventListener('click', () => { if (pz) { pz.fit(); pz.center(); } });
document.getElementById('generateBtn').addEventListener('click', generate);
for (const btn of document.querySelectorAll('button[data-kind]')) {
  btn.addEventListener('click', async () => {
    for (const b of document.querySelectorAll('button[data-kind]')) b.classList.remove('active');
    btn.classList.add('active');
    currentKind = btn.dataset.kind;
    const name = document.getElementById('runSelect').value;
    if (name) await loadGraph(name, currentKind);
  });
}

(async () => {
  await loadCases();
  await loadRuns();
})();
"#;

const REDUCTION_JS: &str = r#"
let viz1 = new Viz();
let viz2 = new Viz();
let viz3 = new Viz();
let pz1 = null;
let pz2 = null;
let pz3 = null;

async function loadRuns(prefer) {
  const runs = await fetch('/api/runs').then(r => r.json());
  const sel = document.getElementById('runSelect');
  const prev = prefer || sel.value;
  sel.innerHTML = '';
  for (const r of runs) {
    const o = document.createElement('option');
    o.value = r.name;
    o.textContent = r.name;
    sel.appendChild(o);
  }
  if (runs.length > 0) {
    const hit = runs.find(x => x.name === prev);
    sel.value = hit ? prev : runs[runs.length - 1].name;
    await loadAll(sel.value);
  }
}

async function renderInto(id, run, kind, viz, oldPz) {
  const root = document.getElementById(id);
  const res = await fetch(`/api/run/${encodeURIComponent(run)}/artifact/${kind}`);
  if (!res.ok) {
    root.textContent = `Missing artifact: ${kind}`;
    return null;
  }
  const dot = await res.text();
  try {
    const svg = await viz.renderSVGElement(dot);
    root.innerHTML = '';
    root.appendChild(svg);
    if (oldPz) oldPz.destroy();
    return svgPanZoom(svg, {
      zoomEnabled: true,
      controlIconsEnabled: true,
      fit: true,
      center: true,
      minZoom: 0.02,
      maxZoom: 100,
      contain: true
    });
  } catch {
    root.textContent = 'Render failed.';
    return null;
  }
}

async function loadAll(run) {
  pz1 = await renderInto('g1', run, 'petrinet_reduce_1', viz1, pz1);
  pz2 = await renderInto('g2', run, 'petrinet_reduce_2', viz2, pz2);
  pz3 = await renderInto('g3', run, 'petrinet_reduce_3', viz3, pz3);
}

document.getElementById('runSelect').addEventListener('change', (e) => loadAll(e.target.value));
document.getElementById('reloadBtn').addEventListener('click', () => loadRuns());
document.getElementById('fitBtn').addEventListener('click', () => {
  if (pz1) { pz1.fit(); pz1.center(); }
  if (pz2) { pz2.fit(); pz2.center(); }
  if (pz3) { pz3.fit(); pz3.center(); }
});

(async () => { await loadRuns(); })();
"#;
