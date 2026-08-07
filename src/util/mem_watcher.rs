use libc::pid_t;
use nom::IResult;
use nom::Parser;
use nom::bytes::streaming::tag;
use nom::character::complete::digit1;
use nom::combinator::map_res;
use nom::multi::count;
use nom::sequence::terminated;
use std::io::{Error, ErrorKind, Result};
use std::sync::{Arc, Mutex};
use std::thread::{self, JoinHandle};
use std::{fs::File, io::Read};

#[derive(Debug, Default, PartialEq, Eq, Hash)]
pub struct Statm {
    pub size: usize,
    pub resident: usize,
    pub share: usize,
    pub text: usize,
    pub data: usize,
}

pub struct MemoryWatcher {
    init_resident: usize,
    max_resident: Arc<Mutex<usize>>,
    handle: Option<JoinHandle<()>>,
    enabled: bool,
}

impl Default for MemoryWatcher {
    fn default() -> Self {
        MemoryWatcher {
            init_resident: 0,
            max_resident: Arc::new(Mutex::new(0)),
            handle: None,
            enabled: false,
        }
    }
}

impl MemoryWatcher {
    pub fn new() -> Self {
        if let Ok(statm) = statm_self() {
            MemoryWatcher {
                init_resident: statm.resident,
                max_resident: Arc::new(Mutex::new(0)),
                handle: None,
                enabled: true,
            }
        } else {
            log::warn!("memory watcher disabled: unable to read process memory statistics");
            MemoryWatcher::default()
        }
    }

    pub fn start(&mut self) {
        if !self.enabled {
            return;
        }
        let max_resident = self.max_resident.clone();
        self.handle = Some(thread::spawn(move || {
            loop {
                if let Ok(statm) = statm_self() {
                    let mut max_rss = max_resident.lock().unwrap();
                    if statm.resident > *max_rss {
                        *max_rss = statm.resident;
                    }
                }

                thread::sleep(std::time::Duration::from_millis(100));
            }
        }));
    }

    pub fn stop(&mut self) {
        if !self.enabled {
            return;
        }
        if let Some(handle) = self.handle.take() {
            drop(handle);
        }

        let max_rss = *self.max_resident.lock().unwrap();
        log::info!(
            "Used Memory Before Analysis: {} MB",
            rss_in_megabytes(self.init_resident)
        );
        log::info!("Max Memory in Analysis: {} MB", rss_in_megabytes(max_rss));
    }
}

#[allow(unused)]
fn rss_in_kilobytes(rss_pages: usize) -> usize {
    rss_pages * 4
}

#[allow(unused)]
fn rss_in_megabytes(rss_pages: usize) -> usize {
    rss_pages * 4 / 1024
}

#[allow(unused)]
fn rss_in_gigabytes(rss_pages: usize) -> usize {
    rss_pages * 4 / 1024 / 1024
}

pub fn map_result<T>(result: IResult<&str, T>) -> Result<T> {
    match result {
        IResult::Ok((remaining, val)) => {
            if remaining.is_empty() {
                Result::Ok(val)
            } else {
                Result::Err(Error::new(
                    ErrorKind::InvalidInput,
                    format!("unable to parse whole input, remaining: {:?}", remaining),
                ))
            }
        }
        IResult::Err(err) => Result::Err(Error::new(
            ErrorKind::InvalidInput,
            format!("unable to parse input: {:?}", err),
        )),
    }
}

#[allow(unused)]
fn parse_usize(input: &str) -> IResult<&str, usize> {
    map_res(digit1, |s: &str| s.parse::<usize>()).parse(input)
}

#[allow(unused)]
fn parse_statm(input: &str) -> IResult<&str, Statm> {
    (count(terminated(parse_usize, tag(" ")), 6), parse_usize)
        .parse(input)
        .map(|(next_input, res)| {
            let statm = Statm {
                size: res.0[0],
                resident: res.0[1],
                share: res.0[2],
                text: res.0[3],
                data: res.0[5],
            };
            (next_input, statm)
        })
}

#[allow(unused)]
fn statm_file(file: &mut File) -> Result<Statm> {
    let mut buf = String::new();
    file.read_to_string(&mut buf)
        .expect("Unable to read string");
    map_result(parse_statm(&buf.trim()))
}

#[cfg(target_os = "linux")]
pub fn statm(pid: pid_t) -> Result<Statm> {
    statm_file(&mut File::open(&format!("/proc/{}/statm", pid))?)
}

#[cfg(target_os = "linux")]
pub fn statm_self() -> Result<Statm> {
    statm_file(&mut File::open("/proc/self/statm")?)
}

#[cfg(target_os = "linux")]
pub fn statm_task(process_id: pid_t, thread_id: pid_t) -> Result<Statm> {
    statm_file(&mut File::open(&format!(
        "/proc/{}/task/{}/statm",
        process_id, thread_id
    ))?)
}

#[cfg(not(target_os = "linux"))]
pub fn statm(_pid: pid_t) -> Result<Statm> {
    Err(Error::new(
        ErrorKind::Unsupported,
        "statm(pid) is only available on Linux",
    ))
}

#[cfg(not(target_os = "linux"))]
pub fn statm_task(_process_id: pid_t, _thread_id: pid_t) -> Result<Statm> {
    Err(Error::new(
        ErrorKind::Unsupported,
        "statm_task is only available on Linux",
    ))
}

#[cfg(not(target_os = "linux"))]
pub fn statm_self() -> Result<Statm> {
    use std::mem::MaybeUninit;

    let mut usage = MaybeUninit::<libc::rusage>::uninit();
    let ret = unsafe { libc::getrusage(libc::RUSAGE_SELF, usage.as_mut_ptr()) };
    if ret != 0 {
        return Err(Error::last_os_error());
    }
    let usage = unsafe { usage.assume_init() };

    let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    if page_size <= 0 {
        return Err(Error::new(
            ErrorKind::Other,
            "unable to determine system page size",
        ));
    }
    let page_size = page_size as usize;

    #[cfg(any(target_os = "macos", target_os = "ios"))]
    let rss_bytes = usage.ru_maxrss as usize;
    #[cfg(not(any(target_os = "macos", target_os = "ios")))]
    let rss_bytes = (usage.ru_maxrss as isize * 1024) as usize;

    let resident_pages = rss_bytes / page_size;

    Ok(Statm {
        size: resident_pages,
        resident: resident_pages,
        share: 0,
        text: 0,
        data: 0,
    })
}
