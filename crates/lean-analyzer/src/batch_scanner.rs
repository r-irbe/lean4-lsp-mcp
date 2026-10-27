//! src/batch_scanner.rs
//! High-performance zero-copy batch scanner for Lean 4 .ilean metadata artifacts.
//! Leverages MmapReader and page-aligned memory mapping from llama.cpp / rust-mmap-engine.
//! 

use std::collections::HashMap;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use crate::ilean_parser::ILeanParser;
use crate::mmap_reader::MmapReader;

#[derive(Debug, Clone)]
pub struct IndexedDeclaration {
    pub module: String,
    pub file_path: PathBuf,
    pub range: [u32; 4],
    pub def_range: [u32; 4],
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScannerStats {
    pub total_symbols: usize,
    pub total_modules: usize,
    pub total_files: usize,
    pub estimated_memory_bytes: usize,
    pub largest_module: Option<(String, usize)>,
}

pub struct BatchILeanScanner {
    // Symbol index: declaration name -> declaration metadata
    symbols: HashMap<String, IndexedDeclaration>,
    // Module index: module name -> list of declaration names
    modules: HashMap<String, Vec<String>>,
    // File to module mapping
    file_modules: HashMap<PathBuf, String>,
    // Total files scanned
    file_count: usize,
}

impl BatchILeanScanner {
    pub fn new() -> Self {
        Self {
            symbols: HashMap::new(),
            modules: HashMap::new(),
            file_modules: HashMap::new(),
            file_count: 0,
        }
    }

    /// Recursively scans a directory for .ilean files and indexes declarations via mmap.
    pub fn scan_directory<P: AsRef<Path>>(&mut self, root: P) -> io::Result<usize> {
        let mut count = 0;
        self.walk_and_index(root.as_ref(), &mut count)?;
        self.file_count += count;
        Ok(count)
    }

    /// Climbs up directory hierarchy from a file or directory path to find the nearest Lean package root
    /// containing lakefile.lean or lakefile.toml.
    pub fn climb_to_lean_root(start: &Path) -> Option<PathBuf> {
        let mut curr = if start.is_file() {
            start.parent()?.to_path_buf()
        } else {
            start.to_path_buf()
        };

        loop {
            if curr.join("lakefile.lean").exists() || curr.join("lakefile.toml").exists() {
                return Some(curr);
            }
            if !curr.pop() {
                break;
            }
        }
        None
    }

    /// Discovers all Lean package roots (directories containing lakefile.lean or lakefile.toml)
    /// under a workspace root (e.g. root, lean/, packages/*).
    pub fn discover_all_package_roots(workspace_root: &Path) -> Vec<PathBuf> {
        let mut roots = Vec::new();
        if workspace_root.join("lakefile.lean").exists()
            || workspace_root.join("lakefile.toml").exists()
        {
            roots.push(workspace_root.to_path_buf());
        }

        // Check packages/ directory
        let packages_dir = workspace_root.join("packages");
        if packages_dir.is_dir() {
            if let Ok(entries) = fs::read_dir(packages_dir) {
                for entry in entries.flatten() {
                    let p = entry.path();
                    if p.is_dir()
                        && (p.join("lakefile.lean").exists() || p.join("lakefile.toml").exists())
                    {
                        roots.push(p);
                    }
                }
            }
        }

        // Check standalone lean/ directory
        let local_lean = workspace_root.join("lean");
        if local_lean.is_dir()
            && (local_lean.join("lakefile.lean").exists()
                || local_lean.join("lakefile.toml").exists())
            && !roots.contains(&local_lean)
        {
            roots.push(local_lean);
        }

        roots
    }

    /// Dynamically scans all discovered Lean packages in a workspace, indexing their build .ilean files.
    pub fn scan_all_packages(&mut self, workspace_root: &Path) -> io::Result<usize> {
        let roots = Self::discover_all_package_roots(workspace_root);
        let mut total_scanned = 0;
        for root in roots {
            let build_lib = root.join(".lake").join("build").join("lib");
            if build_lib.exists() {
                total_scanned += self.scan_directory(&build_lib)?;
            }
        }
        Ok(total_scanned)
    }

    fn walk_and_index(&mut self, path: &Path, count: &mut usize) -> io::Result<()> {
        if path.is_dir() {
            for entry in fs::read_dir(path)? {
                let entry = entry?;
                let p = entry.path();
                if p.is_dir() {
                    self.walk_and_index(&p, count)?;
                } else if p.extension().is_some_and(|ext| ext == "ilean") {
                    if let Ok(mmap) = MmapReader::open(&p) {
                        self.index_mmap_buffer(&p, mmap.as_slice());
                        *count += 1;
                    }
                }
            }
        } else if path.extension().is_some_and(|ext| ext == "ilean") {
            if let Ok(mmap) = MmapReader::open(path) {
                self.index_mmap_buffer(path, mmap.as_slice());
                *count += 1;
            }
        }
        Ok(())
    }

    /// Parses and indexes an .ilean buffer in memory without heap copying.
    pub fn index_mmap_buffer(&mut self, path: &Path, buffer: &[u8]) {
        let mut parser = ILeanParser::new(buffer);
        if let Some(summary) = parser.parse() {
            let mod_name = summary.module.to_string();
            let mut decl_names = Vec::with_capacity(summary.decls.len());

            for decl in summary.decls {
                let name = decl.name.to_string();
                decl_names.push(name.clone());

                let indexed = IndexedDeclaration {
                    module: mod_name.clone(),
                    file_path: path.to_path_buf(),
                    range: decl.range,
                    def_range: decl.def_range,
                };
                self.symbols.insert(name, indexed);
            }

            self.modules.insert(mod_name.clone(), decl_names);
            self.file_modules.insert(path.to_path_buf(), mod_name);
        }
    }

    pub fn lookup(&self, name: &str) -> Option<&IndexedDeclaration> {
        self.symbols.get(name)
    }

    pub fn module_declarations(&self, module: &str) -> Option<&[String]> {
        self.modules.get(module).map(|v| v.as_slice())
    }

    pub fn search_by_prefix<'a>(
        &'a self,
        prefix: &'a str,
    ) -> Vec<(&'a str, &'a IndexedDeclaration)> {
        self.symbols
            .iter()
            .filter(|(name, _)| name.starts_with(prefix))
            .map(|(name, decl)| (name.as_str(), decl))
            .collect()
    }

    pub fn declarations_in_file<'a>(
        &'a self,
        path: &Path,
    ) -> Vec<(&'a str, &'a IndexedDeclaration)> {
        self.symbols
            .iter()
            .filter(|(_, decl)| decl.file_path == path)
            .map(|(name, decl)| (name.as_str(), decl))
            .collect()
    }

    pub fn largest_module(&self) -> Option<(&str, usize)> {
        self.modules
            .iter()
            .max_by_key(|(_, decls)| decls.len())
            .map(|(name, decls)| (name.as_str(), decls.len()))
    }

    pub fn total_modules(&self) -> usize {
        self.modules.len()
    }

    pub fn total_symbols(&self) -> usize {
        self.symbols.len()
    }

    pub fn total_files(&self) -> usize {
        self.file_count
    }

    pub fn search_by_substring<'a>(
        &'a self,
        query: &'a str,
    ) -> Vec<(&'a str, &'a IndexedDeclaration)> {
        self.symbols
            .iter()
            .filter(|(name, _)| name.contains(query))
            .map(|(name, decl)| (name.as_str(), decl))
            .collect()
    }

    pub fn filter_by_module_prefix<'a>(
        &'a self,
        mod_prefix: &'a str,
    ) -> Vec<(&'a str, &'a IndexedDeclaration)> {
        self.symbols
            .iter()
            .filter(|(_, decl)| decl.module.starts_with(mod_prefix))
            .map(|(name, decl)| (name.as_str(), decl))
            .collect()
    }

    pub fn estimated_memory_bytes(&self) -> usize {
        let symbol_bytes = self.symbols.iter().fold(0, |acc, (k, v)| {
            acc + k.len() + v.module.len() + v.file_path.as_os_str().len() + std::mem::size_of::<IndexedDeclaration>()
        });
        let module_bytes = self.modules.iter().fold(0, |acc, (k, v)| {
            acc + k.len() + v.iter().map(|s| s.len()).sum::<usize>() + (v.len() * std::mem::size_of::<String>())
        });
        symbol_bytes + module_bytes + std::mem::size_of::<Self>()
    }

    pub fn batch_lookup<'a>(&'a self, names: &[&str]) -> Vec<Option<&'a IndexedDeclaration>> {
        names.iter().map(|&name| self.lookup(name)).collect()
    }

    pub fn export_symbol_table_ndjson(&self) -> String {
        let mut out = String::with_capacity(self.symbols.len() * 128);
        for (name, decl) in &self.symbols {
            out.push_str("{\"name\":\"");
            out.push_str(name);
            out.push_str("\",\"module\":\"");
            out.push_str(&decl.module);
            out.push_str("\",\"range\":[");
            out.push_str(&decl.range[0].to_string());
            out.push(',');
            out.push_str(&decl.range[1].to_string());
            out.push(',');
            out.push_str(&decl.range[2].to_string());
            out.push(',');
            out.push_str(&decl.range[3].to_string());
            out.push_str("]}\n");
        }
        out
    }

    /// Removes all indexed declarations associated with a file path.
    /// Returns (symbols_removed, files_removed).
    pub fn remove_file(&mut self, path: &Path) -> (usize, usize) {
        let mut symbols_removed = 0;
        let mut affected_modules = Vec::new();

        let file_mod = self.file_modules.remove(path);
        if let Some(ref mod_name) = file_mod {
            affected_modules.push(mod_name.clone());
        }

        self.symbols.retain(|_, decl| {
            if decl.file_path == path {
                symbols_removed += 1;
                if !affected_modules.contains(&decl.module) {
                    affected_modules.push(decl.module.clone());
                }
                false
            } else {
                true
            }
        });

        for mod_name in affected_modules {
            if let Some(decls) = self.modules.get_mut(&mod_name) {
                decls.retain(|name| self.symbols.contains_key(name));
                if decls.is_empty() {
                    self.modules.remove(&mod_name);
                }
            }
        }

        let was_indexed = symbols_removed > 0 || file_mod.is_some();
        let files_removed = if was_indexed && self.file_count > 0 {
            self.file_count -= 1;
            1
        } else {
            0
        };

        (symbols_removed, files_removed)
    }

    pub fn stats(&self) -> ScannerStats {
        ScannerStats {
            total_symbols: self.total_symbols(),
            total_modules: self.total_modules(),
            total_files: self.total_files(),
            estimated_memory_bytes: self.estimated_memory_bytes(),
            largest_module: self.largest_module().map(|(s, n)| (s.to_string(), n)),
        }
    }
}

impl Default for BatchILeanScanner {
    fn default() -> Self {
        Self::new()
    }
}

/// Delta report from a background daemon index tracking update.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DaemonUpdateDelta {
    pub files_added: usize,
    pub files_modified: usize,
    pub files_removed: usize,
    pub symbols_added: usize,
    pub symbols_removed: usize,
}

/// Background daemon index tracker for Lean 4 .ilean build artifacts.
/// Monitors file modification times and applies incremental index updates.
pub struct DaemonIndexTracker {
    pub scanner: BatchILeanScanner,
    file_mtimes: HashMap<PathBuf, u64>,
}

impl DaemonIndexTracker {
    pub fn new() -> Self {
        Self {
            scanner: BatchILeanScanner::new(),
            file_mtimes: HashMap::new(),
        }
    }

    pub fn with_scanner(scanner: BatchILeanScanner) -> Self {
        Self {
            scanner,
            file_mtimes: HashMap::new(),
        }
    }

    /// Recursively collects .ilean files and their modification timestamps (seconds since UNIX epoch).
    pub fn collect_ilean_mtimes(path: &Path, acc: &mut HashMap<PathBuf, u64>) -> io::Result<()> {
        if path.is_dir() {
            for entry in fs::read_dir(path)? {
                let entry = entry?;
                let p = entry.path();
                if p.is_dir() {
                    Self::collect_ilean_mtimes(&p, acc)?;
                } else if p.extension().is_some_and(|ext| ext == "ilean") {
                    if let Ok(meta) = entry.metadata() {
                        let mtime = meta
                            .modified()
                            .ok()
                            .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
                            .map(|d| d.as_secs())
                            .unwrap_or(0);
                        acc.insert(p, mtime);
                    }
                }
            }
        } else if path.extension().is_some_and(|ext| ext == "ilean") {
            if let Ok(meta) = path.metadata() {
                let mtime = meta
                    .modified()
                    .ok()
                    .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
                    .map(|d| d.as_secs())
                    .unwrap_or(0);
                acc.insert(path.to_path_buf(), mtime);
            }
        }
        Ok(())
    }

    /// Polls a directory for added, modified, or removed .ilean files and updates the index incrementally.
    pub fn poll_and_update(&mut self, root: &Path) -> io::Result<DaemonUpdateDelta> {
        let mut delta = DaemonUpdateDelta::default();
        let mut current_files = HashMap::new();
        Self::collect_ilean_mtimes(root, &mut current_files)?;

        // 1. Detect removed files
        let tracked_paths: Vec<PathBuf> = self.file_mtimes.keys().cloned().collect();
        for path in tracked_paths {
            if path.starts_with(root) && !current_files.contains_key(&path) {
                let (syms_rem, files_rem) = self.scanner.remove_file(&path);
                self.file_mtimes.remove(&path);
                delta.files_removed += files_rem;
                delta.symbols_removed += syms_rem;
            }
        }

        // 2. Detect added or modified files
        for (path, mtime) in current_files {
            match self.file_mtimes.get(&path) {
                None => {
                    // Added file
                    let prev_syms = self.scanner.total_symbols();
                    if let Ok(mmap) = MmapReader::open(&path) {
                        self.scanner.index_mmap_buffer(&path, mmap.as_slice());
                        self.scanner.file_count += 1;
                        self.file_mtimes.insert(path, mtime);
                        delta.files_added += 1;
                        delta.symbols_added += self.scanner.total_symbols().saturating_sub(prev_syms);
                    }
                }
                Some(&prev_mtime) if mtime > prev_mtime => {
                    // Modified file
                    let (syms_rem, _) = self.scanner.remove_file(&path);
                    let prev_syms = self.scanner.total_symbols();
                    if let Ok(mmap) = MmapReader::open(&path) {
                        self.scanner.index_mmap_buffer(&path, mmap.as_slice());
                        self.scanner.file_count += 1;
                        self.file_mtimes.insert(path, mtime);
                        delta.files_modified += 1;
                        delta.symbols_removed += syms_rem;
                        delta.symbols_added += self.scanner.total_symbols().saturating_sub(prev_syms);
                    }
                }
                _ => {}
            }
        }

        Ok(delta)
    }

    /// Ingests a memory buffer directly with a simulated mtime for testing or daemon event feeding.
    pub fn index_buffer_with_mtime(&mut self, path: &Path, buffer: &[u8], mtime: u64) -> DaemonUpdateDelta {
        let mut delta = DaemonUpdateDelta::default();
        let is_mod = self.file_mtimes.contains_key(path);
        let mut syms_rem = 0;
        if is_mod {
            let (sr, _) = self.scanner.remove_file(path);
            syms_rem = sr;
            delta.files_modified = 1;
        } else {
            delta.files_added = 1;
        }

        let prev_syms = self.scanner.total_symbols();
        self.scanner.index_mmap_buffer(path, buffer);
        self.scanner.file_count += 1;
        self.file_mtimes.insert(path.to_path_buf(), mtime);
        delta.symbols_removed = syms_rem;
        delta.symbols_added = self.scanner.total_symbols().saturating_sub(prev_syms);
        delta
    }

    pub fn lookup(&self, name: &str) -> Option<&IndexedDeclaration> {
        self.scanner.lookup(name)
    }

    pub fn stats(&self) -> ScannerStats {
        self.scanner.stats()
    }

    pub fn tracked_files_count(&self) -> usize {
        self.file_mtimes.len()
    }
}

impl Default for DaemonIndexTracker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_batch_scanner_index_buffer() {
        let mut scanner = BatchILeanScanner::new();
        let sample = br#"{"version": 3, "module": "SampleProject.Test", "directImports": [], "decls": {"test_thm": [10, 0, 10, 8, 10, 0, 10, 8], "test_helper": [12, 0, 12, 11, 12, 0, 12, 11]}}"#;
        scanner.index_mmap_buffer(Path::new("/dummy/Test.ilean"), sample);

        assert_eq!(scanner.total_symbols(), 2);
        assert_eq!(scanner.total_modules(), 1);

        let decl = scanner.lookup("test_thm").expect("Symbol should exist");
        assert_eq!(decl.module, "SampleProject.Test");
        assert_eq!(decl.range, [10, 0, 10, 8]);

        let prefix_matches = scanner.search_by_prefix("test_");
        assert_eq!(prefix_matches.len(), 2);

        let file_decls = scanner.declarations_in_file(Path::new("/dummy/Test.ilean"));
        assert_eq!(file_decls.len(), 2);

        let largest = scanner
            .largest_module()
            .expect("Should have largest module");
        assert_eq!(largest.0, "SampleProject.Test");
        assert_eq!(largest.1, 2);

        let sub_matches = scanner.search_by_substring("helper");
        assert_eq!(sub_matches.len(), 1);
        assert_eq!(sub_matches[0].0, "test_helper");

        let mod_matches = scanner.filter_by_module_prefix("SampleProject.");
        assert_eq!(mod_matches.len(), 2);

        let mem_est = scanner.estimated_memory_bytes();
        assert!(mem_est > 0);

        let batch_res = scanner.batch_lookup(&["test_thm", "non_existent"]);
        assert_eq!(batch_res.len(), 2);
        assert!(batch_res[0].is_some());
        assert!(batch_res[1].is_none());

        let ndjson = scanner.export_symbol_table_ndjson();
        assert!(ndjson.contains("\"name\":\"test_thm\""));
        assert!(ndjson.contains("\"module\":\"SampleProject.Test\""));

        let st = scanner.stats();
        assert_eq!(st.total_symbols, 2);
        assert_eq!(st.total_modules, 1);
        assert_eq!(st.largest_module, Some(("SampleProject.Test".to_string(), 2)));
        assert!(st.estimated_memory_bytes > 0);
    }

    #[test]
    fn test_package_roots_discovery() {
        let repo_root = if Path::new("lean/lakefile.lean").exists() {
            Path::new(".")
        } else if Path::new("crates/lean-analyzer/lean/lakefile.lean").exists() {
            Path::new("crates/lean-analyzer")
        } else {
            Path::new(".")
        };
        let roots = BatchILeanScanner::discover_all_package_roots(repo_root);
        let has_root = roots.iter().any(|r| r.to_string_lossy().ends_with("lean"));
        assert!(has_root, "Should discover at least one Lean package root");
    }

    #[test]
    fn test_daemon_index_tracker_incremental_update() {
        let mut tracker = DaemonIndexTracker::new();
        let path1 = Path::new("/virtual/FileA.ilean");
        let sample1 = br#"{"version": 3, "module": "ModuleA", "directImports": [], "decls": {"decl1": [1, 0, 1, 5, 1, 0, 1, 5], "decl2": [3, 0, 3, 5, 3, 0, 3, 5]}}"#;

        // Ingest initial file at time 100
        let delta1 = tracker.index_buffer_with_mtime(path1, sample1, 100);
        assert_eq!(delta1.files_added, 1);
        assert_eq!(delta1.symbols_added, 2);
        assert_eq!(tracker.lookup("decl1").unwrap().module, "ModuleA");
        assert_eq!(tracker.stats().total_symbols, 2);

        // Update file at time 200 with new declaration
        let sample1_v2 = br#"{"version": 3, "module": "ModuleA", "directImports": [], "decls": {"decl1": [1, 0, 1, 5, 1, 0, 1, 5], "decl3": [5, 0, 5, 5, 5, 0, 5, 5]}}"#;
        let delta2 = tracker.index_buffer_with_mtime(path1, sample1_v2, 200);
        assert_eq!(delta2.files_modified, 1);
        assert_eq!(delta2.symbols_removed, 2);
        assert_eq!(delta2.symbols_added, 2);

        assert!(tracker.lookup("decl1").is_some());
        assert!(tracker.lookup("decl2").is_none());
        assert!(tracker.lookup("decl3").is_some());

        // Remove file
        let (syms_rem, files_rem) = tracker.scanner.remove_file(path1);
        assert_eq!(syms_rem, 2);
        assert_eq!(files_rem, 1);
        assert_eq!(tracker.stats().total_symbols, 0);
    }

    #[test]
    fn test_empty_module_lifecycle_and_zero_decl_tracker() {
        let mut tracker = DaemonIndexTracker::new();
        let empty_path = Path::new("/virtual/Empty.ilean");
        let empty_sample = br#"{"version": 3, "module": "ModuleEmpty", "directImports": [], "decls": {}}"#;

        // Ingest empty file (0 declarations)
        let delta1 = tracker.index_buffer_with_mtime(empty_path, empty_sample, 100);
        assert_eq!(delta1.files_added, 1);
        assert_eq!(delta1.symbols_added, 0);
        assert_eq!(tracker.stats().total_symbols, 0);
        assert_eq!(tracker.stats().total_files, 1);
        assert_eq!(tracker.stats().total_modules, 1);

        // Update empty file: still empty, mtime 200
        let delta2 = tracker.index_buffer_with_mtime(empty_path, empty_sample, 200);
        assert_eq!(delta2.files_modified, 1);
        assert_eq!(delta2.symbols_removed, 0);
        assert_eq!(delta2.symbols_added, 0);
        assert_eq!(tracker.stats().total_files, 1); // must not leak file count!
        assert_eq!(tracker.stats().total_modules, 1);

        // Remove empty file
        let (syms_rem, files_rem) = tracker.scanner.remove_file(empty_path);
        assert_eq!(syms_rem, 0);
        assert_eq!(files_rem, 1);
        assert_eq!(tracker.stats().total_files, 0);
        assert_eq!(tracker.stats().total_modules, 0);
    }
}
