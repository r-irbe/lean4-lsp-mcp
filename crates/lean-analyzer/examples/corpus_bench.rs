//! examples/corpus_bench.rs
//! End-to-end corpus benchmark: cold/warm scan latency, throughput, lookup
//! latency percentiles, and resident-set growth over real .ilean files.
//!
//! Usage: cargo run --release -p lean-analyzer --example corpus_bench -- [DIR] [RUNS]
//! 

use lean_analyzer::batch_scanner::BatchILeanScanner;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

fn rss_kb() -> Option<u64> {
    let s = std::fs::read_to_string("/proc/self/status").ok()?;
    s.lines()
        .find(|l| l.starts_with("VmRSS:"))?
        .split_whitespace()
        .nth(1)?
        .parse()
        .ok()
}

fn dir_bytes(root: &Path) -> u64 {
    let mut total = 0;
    let mut stack = vec![root.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(rd) = std::fs::read_dir(&d) else { continue };
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
            } else if p.extension().map(|x| x == "ilean").unwrap_or(false) {
                total += e.metadata().map(|m| m.len()).unwrap_or(0);
            }
        }
    }
    total
}

fn pct(sorted: &[Duration], p: f64) -> Duration {
    let i = ((sorted.len() as f64 - 1.0) * p).round() as usize;
    sorted[i]
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let default = "tests/fixtures/ilean";
    let root = PathBuf::from(args.get(1).map(String::as_str).unwrap_or(default));
    let runs: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(5);
    if !root.exists() {
        eprintln!("corpus dir {} not found", root.display());
        std::process::exit(2);
    }

    let bytes = dir_bytes(&root);
    let rss0 = rss_kb().unwrap_or(0);
    let mut times = Vec::with_capacity(runs);
    let mut last: Option<BatchILeanScanner> = None;
    let mut files = 0;
    for _ in 0..runs {
        let mut sc = BatchILeanScanner::new();
        let t = Instant::now();
        files = sc.scan_directory(&root).expect("scan");
        times.push(t.elapsed());
        last = Some(sc);
    }
    let rss1 = rss_kb().unwrap_or(0);
    let sc = last.expect("at least one run");

    let mut sorted = times.clone();
    sorted.sort();
    let median = pct(&sorted, 0.5);
    let mb = bytes as f64 / 1.0e6;
    println!("corpus: {}", root.display());
    println!("files: {files} | ilean bytes: {bytes} ({mb:.1} MB)");
    println!(
        "symbols: {} | modules: {}",
        sc.total_symbols(),
        sc.total_modules()
    );
    println!(
        "scan: cold {:?} | median {:?} | best {:?} | {:.1} MB/s (median)",
        times[0],
        median,
        sorted[0],
        mb / median.as_secs_f64().max(1e-9)
    );
    println!(
        "index memory estimate: {} KiB | RSS delta over {} runs: {} KiB",
        sc.estimated_memory_bytes() / 1024,
        runs,
        rss1.saturating_sub(rss0)
    );

    // Lookup latency over every indexed name (exact-match probe).
    let names: Vec<String> = sc
        .search_by_prefix("")
        .into_iter()
        .map(|(n, _)| n.to_string())
        .collect();
    let mut lat = Vec::with_capacity(names.len());
    let mut hits = 0usize;
    for n in &names {
        let t = Instant::now();
        if sc.lookup(n).is_some() {
            hits += 1;
        }
        lat.push(t.elapsed());
    }
    lat.sort();
    if !lat.is_empty() {
        println!(
            "lookup: n={} hits={} p50={:?} p99={:?} max={:?}",
            lat.len(),
            hits,
            pct(&lat, 0.5),
            pct(&lat, 0.99),
            lat[lat.len() - 1]
        );
    }
}
