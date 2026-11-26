//! Memoizes a finished analysis from the source tree, options, and driver binary.
//! A hit restores the stored output and skips translation and exploration.
//! It does not decide what a fresh run would report.

use crate::options::Options;
use log::{info, warn};
use serde_json::{Value, json};
use std::fs;
use std::io;
use std::path::{Component, Path, PathBuf};
use std::time::UNIX_EPOCH;

pub const CACHE_SCHEMA: &str = "pn-analysis-cache/1";
pub const NET_HASH_SCHEMA: &str = "pn-plan-net-hash/1";
const KEY_SCHEMA: &str = "pn-analysis-cache-key/1";
const SOURCE_SCHEMA: &str = "pn-analysis-source-tree/1";
const ARTIFACT_SCHEMA: &str = "pn-analysis-cache-artifacts/1";

// ---------------------------------------------------------------------------
// SHA-256 (tiny in-tree implementation; the workspace has no hash dependency
// and `Cargo.toml` is outside this task's writable set).
// ---------------------------------------------------------------------------

const SHA256_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// Streaming SHA-256 (used for source trees, artifacts and cache keys).
pub struct Sha256 {
    state: [u32; 8],
    buffer: [u8; 64],
    buffered: usize,
    length: u64,
}

impl Default for Sha256 {
    fn default() -> Self {
        Self::new()
    }
}

impl Sha256 {
    pub fn new() -> Self {
        Self {
            state: [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
                0x5be0cd19,
            ],
            buffer: [0; 64],
            buffered: 0,
            length: 0,
        }
    }

    pub fn update(&mut self, mut data: &[u8]) {
        self.length = self.length.wrapping_add(data.len() as u64);
        if self.buffered > 0 {
            let take = (64 - self.buffered).min(data.len());
            self.buffer[self.buffered..self.buffered + take].copy_from_slice(&data[..take]);
            self.buffered += take;
            data = &data[take..];
            if self.buffered == 64 {
                let block = self.buffer;
                self.compress(&block);
                self.buffered = 0;
            }
        }
        while data.len() >= 64 {
            let mut block = [0u8; 64];
            block.copy_from_slice(&data[..64]);
            self.compress(&block);
            data = &data[64..];
        }
        if !data.is_empty() {
            self.buffer[..data.len()].copy_from_slice(data);
            self.buffered = data.len();
        }
    }

    fn compress(&mut self, block: &[u8; 64]) {
        let mut w = [0u32; 64];
        for (index, chunk) in block.chunks_exact(4).enumerate() {
            w[index] = u32::from_be_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
        }
        for index in 16..64 {
            let s0 = w[index - 15].rotate_right(7)
                ^ w[index - 15].rotate_right(18)
                ^ (w[index - 15] >> 3);
            let s1 = w[index - 2].rotate_right(17)
                ^ w[index - 2].rotate_right(19)
                ^ (w[index - 2] >> 10);
            w[index] = w[index - 16]
                .wrapping_add(s0)
                .wrapping_add(w[index - 7])
                .wrapping_add(s1);
        }
        let mut a = self.state[0];
        let mut b = self.state[1];
        let mut c = self.state[2];
        let mut d = self.state[3];
        let mut e = self.state[4];
        let mut f = self.state[5];
        let mut g = self.state[6];
        let mut h = self.state[7];
        for index in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let t1 = h
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(SHA256_K[index])
                .wrapping_add(w[index]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(maj);
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        self.state[0] = self.state[0].wrapping_add(a);
        self.state[1] = self.state[1].wrapping_add(b);
        self.state[2] = self.state[2].wrapping_add(c);
        self.state[3] = self.state[3].wrapping_add(d);
        self.state[4] = self.state[4].wrapping_add(e);
        self.state[5] = self.state[5].wrapping_add(f);
        self.state[6] = self.state[6].wrapping_add(g);
        self.state[7] = self.state[7].wrapping_add(h);
    }

    pub fn finish(mut self) -> [u8; 32] {
        let bit_len = self.length.wrapping_mul(8);
        self.update(&[0x80]);
        while self.buffered != 56 {
            self.update(&[0]);
        }
        self.update(&bit_len.to_be_bytes());
        let mut out = [0u8; 32];
        for (index, word) in self.state.iter().enumerate() {
            out[4 * index..4 * index + 4].copy_from_slice(&word.to_be_bytes());
        }
        out
    }
}

/// Lowercase hex SHA-256 of `data`.
pub fn sha256_hex(data: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(data);
    hex_digest(&hasher.finish())
}

/// Lowercase hex of a finished digest (no re-hashing).
pub fn hex_digest(digest: &[u8; 32]) -> String {
    let mut text = String::with_capacity(64);
    for byte in digest {
        text.push_str(&format!("{byte:02x}"));
    }
    text
}

// ---------------------------------------------------------------------------
// Source tree hash
// ---------------------------------------------------------------------------

/// Hash a crate package tree by relative path and content.
///
/// Hidden entries and `target/` directories are skipped (build state is not an
/// input), symlinks are not followed (deterministic, no cycles). Files are
/// visited in sorted relative-path order so the digest is stable across
/// copies of the same tree at different absolute locations.
pub fn hash_source_tree(root: &Path) -> io::Result<(String, usize)> {
    let mut files = Vec::new();
    collect_source_files(root, root, &mut files)?;
    files.sort_by(|a, b| a.0.cmp(&b.0));
    let mut hasher = Sha256::new();
    hasher.update(SOURCE_SCHEMA.as_bytes());
    hasher.update(b"\n");
    for (relative, path) in &files {
        let data = fs::read(path)?;
        hasher.update(relative.as_bytes());
        hasher.update(b"\0");
        hasher.update(&(data.len() as u64).to_le_bytes());
        hasher.update(&data);
    }
    Ok((hex_digest(&hasher.finish()), files.len()))
}

fn collect_source_files(
    root: &Path,
    directory: &Path,
    out: &mut Vec<(String, PathBuf)>,
) -> io::Result<()> {
    let mut entries = fs::read_dir(directory)?.collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let name = entry.file_name().to_string_lossy().to_string();
        if name.starts_with('.') {
            continue;
        }
        let path = entry.path();
        let metadata = fs::symlink_metadata(&path)?;
        if metadata.file_type().is_symlink() {
            continue;
        }
        if metadata.is_dir() {
            if name == "target" {
                continue;
            }
            collect_source_files(root, &path, out)?;
        } else if metadata.is_file() {
            let relative = path
                .strip_prefix(root)
                .unwrap_or(&path)
                .to_string_lossy()
                .replace('\\', "/");
            out.push((relative, path));
        }
    }
    Ok(())
}

/// The crate package root: the nearest ancestor with a `Cargo.toml`, starting
/// from `-f <file>` when given and otherwise from the rustc working directory
/// (cargo runs rustc in the package root).
fn source_root_for(options: &Options) -> Option<PathBuf> {
    if let Some(file) = &options.input_file {
        if let Some(root) = package_root_of(file) {
            return Some(root);
        }
    }
    let cwd = std::env::current_dir().ok()?;
    if cwd.join("Cargo.toml").is_file() {
        return Some(cwd);
    }
    None
}

fn package_root_of(file: &Path) -> Option<PathBuf> {
    let mut directory = if file.is_dir() {
        file.to_path_buf()
    } else {
        file.parent()?.to_path_buf()
    };
    loop {
        if directory.join("Cargo.toml").is_file() {
            return Some(directory);
        }
        directory = directory.parent()?.to_path_buf();
    }
}

// ---------------------------------------------------------------------------
// Key material
// ---------------------------------------------------------------------------

/// A deterministic fingerprint of everything in `Options` that can change the
/// analysis result. The output directory and the cache root are deliberately
/// excluded: moving the output must not change the key.
pub fn options_fingerprint(options: &Options) -> String {
    let config = serde_json::to_value(&options.config).unwrap_or(Value::Null);
    let refinements = options.exclude_candidates.as_ref().map(|path| {
        let digest = fs::read(path)
            .map(|bytes| sha256_hex(&bytes))
            .unwrap_or_else(|_| "missing".to_string());
        json!({
            "path": path.to_string_lossy(),
            "sha256": digest,
        })
    });
    let dump = &options.dump_options;
    let value = json!({
        "detector_kind": format!("{:?}", options.detector_kind),
        "crate_name": options.crate_name,
        "input_file": options.input_file.as_ref().map(|path| path.to_string_lossy().to_string()),
        "crate_filter": format!("{:?}", options.crate_filter),
        "cross_crate": options.cross_crate,
        "exclude_candidates": refinements,
        "stop_after": format!("{:?}", options.stop_after),
        "dump": {
            "call_graph": dump.dump_call_graph,
            "petri_net": dump.dump_petri_net,
            "state_graph": dump.dump_state_graph,
            "unsafe_info": dump.dump_unsafe_info,
            "points_to": dump.dump_points_to,
            "mir": dump.dump_mir,
            "cir": dump.dump_cir,
            "resource_map": dump.dump_resource_map,
        },
        "config": config,
    });
    let text = serde_json::to_string(&value).unwrap_or_default();
    sha256_hex(text.as_bytes())
}

/// Identity of the driver binary (path, length, mtime): a rebuilt `spn` must
/// not reuse entries produced by the previous binary.
fn exe_fingerprint() -> String {
    match std::env::current_exe() {
        Ok(path) => match fs::metadata(&path) {
            Ok(metadata) => {
                let modified = metadata
                    .modified()
                    .ok()
                    .and_then(|time| time.duration_since(UNIX_EPOCH).ok())
                    .map(|duration| duration.as_nanos())
                    .unwrap_or(0);
                format!("{}:{}:{}", path.display(), metadata.len(), modified)
            }
            Err(_) => format!("{}:unknown", path.display()),
        },
        Err(_) => "unknown".to_string(),
    }
}

// ---------------------------------------------------------------------------
// Cache entry
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub struct CacheKey {
    /// Digest of the key material; this is the on-disk entry name.
    pub hex: String,
    pub crate_name: String,
    pub source_hash: String,
    pub source_files: usize,
    /// Informational only: not part of the digest, so copies of the same tree
    /// share an entry.
    pub source_root: PathBuf,
    pub options_fingerprint: String,
    pub exe_fingerprint: String,
}

#[derive(Debug, Clone)]
pub struct AnalysisCache {
    root: PathBuf,
}

impl AnalysisCache {
    pub fn new(root: PathBuf) -> Self {
        Self { root }
    }

    /// `SPN_CACHE_DIR`, else `$XDG_CACHE_HOME/spn-analysis`, else
    /// `$HOME/.cache/spn-analysis`; `SPN_CACHE_DISABLE=1` turns the cache off.
    pub fn from_env() -> Option<Self> {
        if std::env::var_os("SPN_CACHE_DISABLE").is_some_and(|value| value == "1") {
            return None;
        }
        if let Some(directory) = std::env::var_os("SPN_CACHE_DIR") {
            if !directory.is_empty() {
                return Some(Self::new(PathBuf::from(directory)));
            }
        }
        if let Some(xdg) = std::env::var_os("XDG_CACHE_HOME") {
            if !xdg.is_empty() {
                return Some(Self::new(PathBuf::from(xdg).join("spn-analysis")));
            }
        }
        if let Some(home) = std::env::var_os("HOME") {
            if !home.is_empty() {
                return Some(Self::new(
                    PathBuf::from(home).join(".cache").join("spn-analysis"),
                ));
            }
        }
        None
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn entry_dir(&self, key: &CacheKey) -> PathBuf {
        self.root.join(&key.hex)
    }

    /// Build the cache key for one analysed crate.
    pub fn key_for(&self, options: &Options, crate_name: &str) -> io::Result<CacheKey> {
        let source_root = source_root_for(options).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::NotFound,
                "cannot locate the crate package root (no Cargo.toml next to the rustc \
                 working directory and no -f input file)",
            )
        })?;
        let (source_hash, source_files) = hash_source_tree(&source_root)?;
        let options_fingerprint = options_fingerprint(options);
        let exe_fingerprint = exe_fingerprint();
        let material = format!(
            "{KEY_SCHEMA}\ncrate={crate_name}\nexe={exe_fingerprint}\noptions={options_fingerprint}\nsource={source_hash}\n"
        );
        Ok(CacheKey {
            hex: sha256_hex(material.as_bytes()),
            crate_name: crate_name.to_string(),
            source_hash,
            source_files,
            source_root,
            options_fingerprint,
            exe_fingerprint,
        })
    }

    /// Copy a stored snapshot back into `output_dir`, verifying every artifact
    /// against the manifest first. Returns `Ok(false)` when the entry is
    /// missing or corrupt; the caller then runs the full analysis.
    pub fn restore(&self, key: &CacheKey, output_dir: &Path) -> io::Result<bool> {
        let entry = self.entry_dir(key);
        let manifest_path = entry.join("manifest.json");
        if !manifest_path.is_file() {
            return Ok(false);
        }
        let manifest: Value = match fs::read_to_string(&manifest_path)
            .ok()
            .and_then(|text| serde_json::from_str(&text).ok())
        {
            Some(value) => value,
            None => {
                warn!("analysis cache: unreadable manifest at {:?}", manifest_path);
                return Ok(false);
            }
        };
        if manifest["schema"] != CACHE_SCHEMA || manifest["key"] != key.hex {
            warn!(
                "analysis cache: manifest at {:?} does not match the key",
                manifest_path
            );
            return Ok(false);
        }
        let artifacts = match manifest["artifacts"].as_array() {
            Some(list) if !list.is_empty() => list.clone(),
            _ => return Ok(false),
        };
        let net_sha256 = manifest["net_sha256"].as_str().map(str::to_string);
        let mut planned: Vec<(PathBuf, Vec<u8>)> = Vec::with_capacity(artifacts.len());
        for artifact in &artifacts {
            let relative = match artifact["path"].as_str().and_then(safe_relative_path) {
                Some(path) => path,
                None => {
                    warn!(
                        "analysis cache: unsafe artifact path in {:?}",
                        manifest_path
                    );
                    return Ok(false);
                }
            };
            let cached = entry.join("artifacts").join(&relative);
            let data = match fs::read(&cached) {
                Ok(data) => data,
                Err(_) => {
                    warn!("analysis cache: missing artifact {:?}", cached);
                    return Ok(false);
                }
            };
            let expected = artifact["sha256"].as_str().unwrap_or("");
            let actual = sha256_hex(&data);
            if actual != expected {
                warn!(
                    "analysis cache: artifact {:?} failed its hash check; recomputing",
                    relative
                );
                return Ok(false);
            }
            if relative == Path::new("petrinet.dot") {
                if let Some(net) = &net_sha256 {
                    if &actual != net {
                        warn!(
                            "analysis cache: petrinet.dot does not match the recorded net hash; recomputing"
                        );
                        return Ok(false);
                    }
                }
            }
            planned.push((relative, data));
        }
        fs::create_dir_all(output_dir)?;
        for (relative, data) in &planned {
            let destination = output_dir.join(relative);
            if let Some(parent) = destination.parent() {
                fs::create_dir_all(parent)?;
            }
            fs::write(&destination, data)?;
        }
        info!(
            "analysis cache hit: restored {} artifact(s) for {} (key {}, {} source file(s))",
            planned.len(),
            key.crate_name,
            &key.hex[..12.min(key.hex.len())],
            key.source_files
        );
        Ok(true)
    }

    /// Snapshot `output_dir` into the cache entry for `key`.
    pub fn store(&self, key: &CacheKey, output_dir: &Path) -> io::Result<PathBuf> {
        fs::create_dir_all(&self.root)?;
        let final_dir = self.entry_dir(key);
        let temporary = self
            .root
            .join(format!("{}.tmp-{}", key.hex, std::process::id()));
        if temporary.exists() {
            let _ = fs::remove_dir_all(&temporary);
        }
        let artifacts_dir = temporary.join("artifacts");
        fs::create_dir_all(&artifacts_dir)?;
        let mut artifacts = Vec::new();
        collect_artifacts(output_dir, output_dir, &artifacts_dir, &mut artifacts)?;
        if artifacts.is_empty() {
            let _ = fs::remove_dir_all(&temporary);
            return Err(io::Error::new(
                io::ErrorKind::NotFound,
                format!("no analysis artifacts under {output_dir:?}"),
            ));
        }
        artifacts.sort_by(|a, b| {
            a["path"]
                .as_str()
                .unwrap_or("")
                .cmp(b["path"].as_str().unwrap_or(""))
        });
        let net_sha256 = artifacts
            .iter()
            .find(|artifact| artifact["path"] == "petrinet.dot")
            .and_then(|artifact| artifact["sha256"].as_str())
            .map(str::to_string);
        let manifest = json!({
            "schema": CACHE_SCHEMA,
            "artifact_schema": ARTIFACT_SCHEMA,
            "key": key.hex,
            "crate": key.crate_name,
            "source_hash": key.source_hash,
            "source_files": key.source_files,
            "source_root": key.source_root.to_string_lossy(),
            "options_fingerprint": key.options_fingerprint,
            "exe_fingerprint": key.exe_fingerprint,
            "net_hash_schema": NET_HASH_SCHEMA,
            "net_sha256": net_sha256,
            "artifacts": artifacts,
        });
        let text = serde_json::to_string_pretty(&manifest).unwrap_or_default() + "\n";
        fs::write(temporary.join("manifest.json"), text)?;
        if final_dir.exists() {
            let _ = fs::remove_dir_all(&final_dir);
        }
        fs::rename(&temporary, &final_dir)?;
        info!(
            "analysis cache stored {} artifact(s) for {} (key {})",
            manifest["artifacts"].as_array().map(Vec::len).unwrap_or(0),
            key.crate_name,
            &key.hex[..12.min(key.hex.len())]
        );
        Ok(final_dir)
    }
}

fn collect_artifacts(
    root: &Path,
    directory: &Path,
    cache_dir: &Path,
    out: &mut Vec<Value>,
) -> io::Result<()> {
    let mut entries = fs::read_dir(directory)?.collect::<Result<Vec<_>, _>>()?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let path = entry.path();
        let metadata = fs::symlink_metadata(&path)?;
        if metadata.file_type().is_symlink() {
            continue;
        }
        if metadata.is_dir() {
            collect_artifacts(root, &path, cache_dir, out)?;
        } else if metadata.is_file() {
            let relative = match path.strip_prefix(root) {
                Ok(relative) => relative.to_path_buf(),
                Err(_) => continue,
            };
            let data = fs::read(&path)?;
            let sha256 = sha256_hex(&data);
            let cached = cache_dir.join(&relative);
            if let Some(parent) = cached.parent() {
                fs::create_dir_all(parent)?;
            }
            fs::write(&cached, &data)?;
            out.push(json!({
                "path": relative.to_string_lossy().replace('\\', "/"),
                "sha256": sha256,
                "bytes": data.len(),
            }));
        }
    }
    Ok(())
}

fn safe_relative_path(relative: &str) -> Option<PathBuf> {
    if relative.is_empty() {
        return None;
    }
    let path = Path::new(relative);
    let mut out = PathBuf::new();
    for component in path.components() {
        match component {
            Component::Normal(part) => out.push(part),
            _ => return None,
        }
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::SystemTime;

    static COUNTER: AtomicUsize = AtomicUsize::new(0);

    fn temp_dir(label: &str) -> PathBuf {
        let nonce = COUNTER.fetch_add(1, Ordering::SeqCst);
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "spn-cache-{label}-{}-{stamp}-{nonce}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir_all(&directory).unwrap();
        directory
    }

    fn write(path: &Path, text: &str) {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(path, text).unwrap();
    }

    fn read(path: &Path) -> String {
        fs::read_to_string(path).unwrap()
    }

    #[test]
    fn sha256_matches_known_vectors() {
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(
            sha256_hex(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
        assert_eq!(
            sha256_hex(&[b'x'; 100]),
            "09ecb6ebc8bcefc733f6f2ec44f791abeed6a99edf0cc31519637898aebd52d8"
        );
        // Streaming across block boundaries must agree with the one-shot form.
        let mut streamed = Sha256::new();
        streamed.update(&[b'x'; 100]);
        streamed.update(&[b'y'; 300]);
        let oneshot = sha256_hex(&[vec![b'x'; 100], vec![b'y'; 300]].concat());
        assert_eq!(hex_digest(&streamed.finish()), oneshot);
    }

    #[test]
    fn source_hash_is_content_addressed() {
        let root = temp_dir("source");
        write(&root.join("src/main.rs"), "fn main() {}\n");
        write(&root.join("Cargo.toml"), "[package]\nname=\"demo\"\n");
        let (first, files) = hash_source_tree(&root).unwrap();
        assert_eq!(files, 2);

        // A pure copy at a different location hashes identically.
        let copy = temp_dir("source-copy");
        write(&copy.join("src/main.rs"), "fn main() {}\n");
        write(&copy.join("Cargo.toml"), "[package]\nname=\"demo\"\n");
        let (second, _) = hash_source_tree(&copy).unwrap();
        assert_eq!(first, second);

        // Build state and hidden entries are not inputs.
        write(&root.join("target/rustc/x"), "junk\n");
        write(&root.join(".hidden"), "junk\n");
        assert_eq!(hash_source_tree(&root).unwrap().0, first);

        // Same file set, changed content: a different hash.
        write(&root.join("src/main.rs"), "fn main() { let _ = 1; }\n");
        assert_ne!(hash_source_tree(&root).unwrap().0, first);

        // Added file: a different hash.
        write(&root.join("src/main.rs"), "fn main() {}\n");
        write(&root.join("src/lib.rs"), "pub fn helper() {}\n");
        assert_ne!(hash_source_tree(&root).unwrap().0, first);

        let _ = fs::remove_dir_all(&root);
        let _ = fs::remove_dir_all(&copy);
    }

    fn key_options(root: &Path, crate_name: &str) -> Options {
        write(&root.join("Cargo.toml"), "[package]\nname=\"demo\"\n");
        write(&root.join("src/main.rs"), "fn main() {}\n");
        let mut options = Options::default();
        options.crate_name = crate_name.to_string();
        options.input_file = Some(root.join("src/main.rs"));
        options
    }

    #[test]
    fn cache_key_tracks_source_options_and_crate() {
        let root = temp_dir("key");
        let cache = AnalysisCache::new(temp_dir("key-store"));
        let options = key_options(&root, "demo");
        let first = cache.key_for(&options, "demo").unwrap();
        assert_eq!(first.source_files, 2);
        assert_eq!(first.source_hash.len(), 64);
        assert_eq!(first.hex.len(), 64);

        // Deterministic for unchanged inputs.
        assert_eq!(cache.key_for(&options, "demo").unwrap().hex, first.hex);

        // A different crate name is a different key.
        assert_ne!(cache.key_for(&options, "other").unwrap().hex, first.hex);

        // A changed source file is a different key.
        write(&root.join("src/main.rs"), "fn main() { let _ = 2; }\n");
        assert_ne!(cache.key_for(&options, "demo").unwrap().hex, first.hex);

        // A changed option is a different key.
        write(&root.join("src/main.rs"), "fn main() {}\n");
        let mut tuned = options.clone();
        tuned.config.state_limit = Some(11);
        assert_ne!(cache.key_for(&tuned, "demo").unwrap().hex, first.hex);

        // The output directory must not be part of the key.
        let mut elsewhere = options.clone();
        elsewhere.output = Some(PathBuf::from("/somewhere/else"));
        assert_eq!(cache.key_for(&elsewhere, "demo").unwrap().hex, first.hex);

        let _ = fs::remove_dir_all(&root);
    }

    fn snapshot_example(output: &Path) {
        write(&output.join("petrinet.dot"), "digraph net { a -> b }\n");
        write(&output.join("deadlocks.json"), "{\"deadlocks\": []}\n");
        write(
            &output.join("predicates.json"),
            "{\"candidates\": [], \"crate\": \"demo\"}\n",
        );
        write(&output.join("nested/report.txt"), "nested\n");
    }

    #[test]
    fn store_then_restore_is_byte_identical() {
        let root = temp_dir("roundtrip");
        let options = key_options(&root, "demo");
        let cache = AnalysisCache::new(temp_dir("roundtrip-store"));
        let key = cache.key_for(&options, "demo").unwrap();

        // Miss on an empty cache.
        assert!(!cache.restore(&key, &root.join("out")).unwrap());

        let output = root.join("out");
        snapshot_example(&output);
        let expected: Vec<(String, String)> = vec![
            ("petrinet.dot".into(), read(&output.join("petrinet.dot"))),
            (
                "deadlocks.json".into(),
                read(&output.join("deadlocks.json")),
            ),
            (
                "predicates.json".into(),
                read(&output.join("predicates.json")),
            ),
            (
                "nested/report.txt".into(),
                read(&output.join("nested/report.txt")),
            ),
        ];
        cache.store(&key, &output).unwrap();

        let manifest: Value =
            serde_json::from_str(&read(&cache.entry_dir(&key).join("manifest.json"))).unwrap();
        assert_eq!(manifest["schema"], CACHE_SCHEMA);
        assert_eq!(manifest["net_hash_schema"], NET_HASH_SCHEMA);
        assert_eq!(
            manifest["net_sha256"],
            sha256_hex(b"digraph net { a -> b }\n")
        );
        assert_eq!(manifest["artifacts"].as_array().unwrap().len(), 4);

        fs::remove_dir_all(&output).unwrap();
        assert!(cache.restore(&key, &output).unwrap());
        for (relative, text) in expected {
            assert_eq!(read(&output.join(&relative)), text, "{relative}");
        }

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn corrupt_entry_is_a_miss_not_a_wrong_hit() {
        let root = temp_dir("corrupt");
        let options = key_options(&root, "demo");
        let cache = AnalysisCache::new(temp_dir("corrupt-store"));
        let key = cache.key_for(&options, "demo").unwrap();
        let output = root.join("out");
        snapshot_example(&output);
        cache.store(&key, &output).unwrap();

        // Damage one stored artifact: restore must refuse the whole entry.
        let cached = cache.entry_dir(&key).join("artifacts").join("petrinet.dot");
        fs::write(&cached, "tampered\n").unwrap();
        let fresh = root.join("out2");
        assert!(!cache.restore(&key, &fresh).unwrap());
        assert!(!fresh.exists());

        // Missing entry is a miss too.
        let absent = root.join("out3");
        assert!(!cache.restore(&key, &absent).unwrap());

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn source_change_produces_a_miss() {
        let root = temp_dir("invalidate");
        let options = key_options(&root, "demo");
        let cache = AnalysisCache::new(temp_dir("invalidate-store"));
        let first = cache.key_for(&options, "demo").unwrap();
        let output = root.join("out");
        snapshot_example(&output);
        cache.store(&first, &output).unwrap();

        write(&root.join("src/main.rs"), "fn main() { let _ = 3; }\n");
        let second = cache.key_for(&options, "demo").unwrap();
        assert_ne!(first.hex, second.hex);
        let fresh = root.join("out-new");
        assert!(!cache.restore(&second, &fresh).unwrap());

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn options_fingerprint_is_stable_and_content_aware() {
        let root = temp_dir("options");
        let options = key_options(&root, "demo");
        let first = options_fingerprint(&options);
        assert_eq!(options_fingerprint(&options), first);

        let mut changed = options.clone();
        changed.config.por_enabled = true;
        assert_ne!(options_fingerprint(&changed), first);

        // Refinement *content* matters, not just its path.
        let refinements = root.join("refinements.json");
        write(&refinements, "{\"excluded\": []}\n");
        let mut with_refinements = options.clone();
        with_refinements.exclude_candidates = Some(refinements.clone());
        let before = options_fingerprint(&with_refinements);
        write(&refinements, "{\"excluded\": [3]}\n");
        assert_ne!(options_fingerprint(&with_refinements), before);

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn restore_rejects_unsafe_manifest_paths() {
        assert!(safe_relative_path("a/b.txt").is_some());
        assert!(safe_relative_path("../escape").is_none());
        assert!(safe_relative_path("/absolute").is_none());
        assert!(safe_relative_path("").is_none());
        assert!(safe_relative_path("./current").is_none());
    }
}
