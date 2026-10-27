//! Performance regression gate over .ilean corpus scanning plus timing
//! of incremental daemon re-indexing.

use lean_analyzer::batch_scanner::{BatchILeanScanner, DaemonIndexTracker};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant, SystemTime};

const SCAN_MEDIAN_BUDGET: Duration = Duration::from_millis(600);
const LOOKUP_P99_BUDGET: Duration = Duration::from_micros(50);
const INCREMENTAL_BUDGET: Duration = Duration::from_millis(250);

fn corpus() -> Option<PathBuf> {
    if let Ok(env_p) = std::env::var("LEAN_ANALYZER_CORPUS_DIR") {
        let p = PathBuf::from(env_p);
        if p.exists() {
            return Some(p);
        }
    }
    ["tests/fixtures/ilean", "crates/lean-analyzer/tests/fixtures/ilean"]
        .iter()
        .map(PathBuf::from)
        .find(|p| p.exists())
}

fn ilean_files(root: &Path, out: &mut Vec<PathBuf>) {
    let Ok(rd) = fs::read_dir(root) else { return };
    for e in rd.flatten() {
        let p = e.path();
        if p.is_dir() {
            ilean_files(&p, out);
        } else if p.extension().is_some_and(|x| x == "ilean") {
            out.push(p);
        }
    }
}

#[test]
fn corpus_scan_and_lookup_within_budget() {
    let Some(root) = corpus() else {
        eprintln!("corpus not built, skipping gate");
        return;
    };
    let mut times = Vec::new();
    let mut last = None;
    for _ in 0..5 {
        let mut sc = BatchILeanScanner::new();
        let t = Instant::now();
        sc.scan_directory(&root).expect("scan");
        times.push(t.elapsed());
        last = Some(sc);
    }
    times.sort();
    let median = times[times.len() / 2];
    assert!(median < SCAN_MEDIAN_BUDGET, "scan median {median:?} exceeds {SCAN_MEDIAN_BUDGET:?}");

    let sc = last.unwrap();
    let names: Vec<String> = sc.search_by_prefix("").into_iter().map(|(n, _)| n.to_string()).collect();
    assert!(!names.is_empty());
    let mut lat: Vec<Duration> = names
        .iter()
        .map(|n| {
            let t = Instant::now();
            assert!(sc.lookup(n).is_some());
            t.elapsed()
        })
        .collect();
    lat.sort();
    let p99 = lat[((lat.len() - 1) as f64 * 0.99) as usize];
    assert!(p99 < LOOKUP_P99_BUDGET, "lookup p99 {p99:?} exceeds {LOOKUP_P99_BUDGET:?}");
}

#[test]
fn daemon_incremental_update_is_cheap_and_exact() {
    let Some(root) = corpus() else {
        eprintln!("corpus not built, skipping daemon timing");
        return;
    };
    let mut files = Vec::new();
    ilean_files(&root, &mut files);
    files.sort();
    files.truncate(60);
    assert!(files.len() >= 10, "need a corpus sample");

    let tmp = std::env::temp_dir().join(format!("lean_analyzer_daemon_{}", std::process::id()));
    let _ = fs::remove_dir_all(&tmp);
    fs::create_dir_all(&tmp).unwrap();
    for (i, f) in files.iter().enumerate() {
        fs::copy(f, tmp.join(format!("m{i}.ilean"))).unwrap();
    }

    let mut d = DaemonIndexTracker::new();
    let t = Instant::now();
    let first = d.poll_and_update(&tmp).unwrap();
    let cold = t.elapsed();
    assert_eq!(first.files_added, files.len());
    assert!(first.symbols_added > 0);

    // Unchanged tree: nothing to do.
    let t = Instant::now();
    let idle = d.poll_and_update(&tmp).unwrap();
    let idle_t = t.elapsed();
    assert_eq!((idle.files_added, idle.files_modified, idle.files_removed), (0, 0, 0));

    // Touch exactly one file (mtime has 1 s granularity, so push it forward).
    let victim = tmp.join("m3.ilean");
    let f = fs::OpenOptions::new().write(true).open(&victim).unwrap();
    f.set_modified(SystemTime::now() + Duration::from_secs(10)).unwrap();
    drop(f);
    let t = Instant::now();
    let touched = d.poll_and_update(&tmp).unwrap();
    let incr = t.elapsed();
    assert_eq!(touched.files_modified, 1);
    assert_eq!(touched.symbols_added, touched.symbols_removed, "re-index of identical bytes must be symbol-neutral");

    // Delete one file.
    fs::remove_file(tmp.join("m5.ilean")).unwrap();
    let gone = d.poll_and_update(&tmp).unwrap();
    assert_eq!(gone.files_removed, 1);

    println!("daemon: cold {cold:?} | idle poll {idle_t:?} | single-file re-index {incr:?}");
    assert!(incr < INCREMENTAL_BUDGET, "incremental {incr:?} exceeds {INCREMENTAL_BUDGET:?}");
    let _ = fs::remove_dir_all(&tmp);
}
