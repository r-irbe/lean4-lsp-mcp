//! Integration test and zero-copy mmap throughput benchmark for BatchILeanScanner.

use lean_analyzer::batch_scanner::BatchILeanScanner;
use std::path::{Path, PathBuf};
use std::time::Instant;

#[test]
fn test_corpus_ilean_scan_benchmark() {
    let env_dir = std::env::var("LEAN_ANALYZER_CORPUS_DIR").ok().map(PathBuf::from);
    let p1 = Path::new("tests/fixtures/ilean");
    let p2 = Path::new("crates/lean-analyzer/tests/fixtures/ilean");
    let ir_dir: &Path = if let Some(ref d) = env_dir {
        if d.exists() {
            d.as_path()
        } else {
            return;
        }
    } else if p1.exists() {
        p1
    } else if p2.exists() {
        p2
    } else {
        eprintln!("Fixture .ilean dir does not exist, skipping scan test.");
        return;
    };

    let mut scanner = BatchILeanScanner::new();
    let start = Instant::now();
    let scanned = scanner
        .scan_directory(ir_dir)
        .expect("Scan directory should succeed");
    let elapsed = start.elapsed();

    println!(
        "BatchILeanScanner: Scanned {} .ilean files in {:?}",
        scanned, elapsed
    );
    println!("Total indexed symbols: {}", scanner.total_symbols());

    assert!(scanned > 0, "Should have scanned at least one .ilean file");
    assert!(scanner.total_symbols() > 0, "Should have indexed symbols");
    assert!(scanner.total_modules() > 0, "Should have indexed modules");

    let largest = scanner.largest_module();
    assert!(largest.is_some(), "Should find largest module");
    if let Some((mod_name, count)) = largest {
        println!("Largest module: {} ({} declarations)", mod_name, count);
        assert!(count > 0);
    }

    let prefix_res = scanner.search_by_prefix("SampleProject.");
    println!("Declarations starting with 'SampleProject.': {}", prefix_res.len());
}
