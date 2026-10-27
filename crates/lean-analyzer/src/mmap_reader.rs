//! src/mmap_reader.rs
//! High-performance memory-mapped zero-copy reader for Lean 4 artifacts.
//! Inspired by llama-mmap.h / llama-mmap.cpp techniques in llama.cpp:
//! - Direct memory mapping avoids copying multi-megabyte .ilean and .olean files into heap.
//! - Read-only page-aligned buffer mapping.
//! - Zero heap allocation during AST and symbol queries.
//! 

use std::fs::File;
use std::io;
use std::path::Path;

#[cfg(unix)]
use std::os::unix::io::AsRawFd;

pub struct MmapReader {
    ptr: *const u8,
    len: usize,
    _file: File,
}

impl MmapReader {
    #[cfg(unix)]
    pub fn open<P: AsRef<Path>>(path: P) -> io::Result<Self> {
        let file = File::open(path)?;
        let meta = file.metadata()?;
        let len = meta.len() as usize;

        if len == 0 {
            return Ok(Self {
                ptr: std::ptr::null(),
                len: 0,
                _file: file,
            });
        }

        let fd = file.as_raw_fd();
        let ptr = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                len,
                libc::PROT_READ,
                libc::MAP_PRIVATE,
                fd,
                0,
            )
        };

        if ptr == libc::MAP_FAILED {
            return Err(io::Error::last_os_error());
        }

        // Advise sequential access pattern for fast AST streaming
        unsafe {
            libc::madvise(ptr, len, libc::MADV_WILLNEED | libc::MADV_SEQUENTIAL);
        }

        Ok(Self {
            ptr: ptr as *const u8,
            len,
            _file: file,
        })
    }

    #[cfg(not(unix))]
    pub fn open<P: AsRef<Path>>(path: P) -> io::Result<Self> {
        // Fallback for non-unix platforms
        let mut file = File::open(path)?;
        let mut buf = Vec::new();
        use std::io::Read;
        file.read_to_end(&mut buf)?;
        let len = buf.len();
        let leaked = Box::leak(buf.into_boxed_slice());
        Ok(Self {
            ptr: leaked.as_ptr(),
            len,
            _file: file,
        })
    }

    pub fn as_slice(&self) -> &[u8] {
        if self.len == 0 || self.ptr.is_null() {
            &[]
        } else {
            unsafe { std::slice::from_raw_parts(self.ptr, self.len) }
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn starts_with(&self, prefix: &[u8]) -> bool {
        self.as_slice().starts_with(prefix)
    }

    pub fn read_subslice(&self, start: usize, len: usize) -> Option<&[u8]> {
        let end = start.checked_add(len)?;
        if end <= self.len {
            Some(&self.as_slice()[start..end])
        } else {
            None
        }
    }

    pub fn validate_utf8_prefix(&self, max_bytes: usize) -> bool {
        let slice = self.as_slice();
        let check_len = slice.len().min(max_bytes);
        std::str::from_utf8(&slice[..check_len]).is_ok()
    }

    pub fn find_subslice(&self, needle: &[u8]) -> Option<usize> {
        if needle.is_empty() || needle.len() > self.len {
            return None;
        }
        self.as_slice()
            .windows(needle.len())
            .position(|window| window == needle)
    }
}

impl Drop for MmapReader {
    fn drop(&mut self) {
        #[cfg(unix)]
        if !self.ptr.is_null() && self.len > 0 {
            unsafe {
                libc::munmap(self.ptr as *mut libc::c_void, self.len);
            }
        }
    }
}

unsafe impl Send for MmapReader {}
unsafe impl Sync for MmapReader {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    #[test]
    fn test_mmap_reader_read_file() {
        let temp_dir = std::env::temp_dir();
        let test_file = temp_dir.join("lean_analyzer_mmap_test.txt");
        {
            let mut f = File::create(&test_file).expect("create temp file");
            f.write_all(b"{\"module\":\"TestMmap\",\"version\":5}")
                .expect("write temp file");
        }

        let reader = MmapReader::open(&test_file).expect("open mmap");
        assert_eq!(reader.len(), 33);
        assert_eq!(
            reader.as_slice(),
            b"{\"module\":\"TestMmap\",\"version\":5}"
        );
        assert!(reader.starts_with(b"{\"module\""));
        assert!(!reader.starts_with(b"invalid"));
        assert_eq!(reader.read_subslice(0, 9), Some(&b"{\"module\""[..]));
        assert_eq!(reader.read_subslice(30, 10), None);
        assert!(reader.validate_utf8_prefix(33));
        assert_eq!(reader.find_subslice(b"\"version\":5"), Some(21));
        assert_eq!(reader.find_subslice(b"nonexistent"), None);

        let _ = std::fs::remove_file(test_file);
    }
}
