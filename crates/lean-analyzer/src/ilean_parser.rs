//! src/ilean_parser.rs
//! Zero-allocation / zero-dependency fast streaming parser for Lean 4 `.ilean` metadata.
//! Provides instant symbol resolution and hover/definition lookups in WASM.
//! 

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ILeanDecl<'a> {
    pub name: &'a str,
    pub range: [u32; 4],     // start_line, start_col, end_line, end_col
    pub def_range: [u32; 4], // def_line, def_col, def_end_line, def_end_col
}

#[derive(Debug, Clone, Default)]
pub struct ILeanSummary<'a> {
    pub version: u32,
    pub module: &'a str,
    pub decls: Vec<ILeanDecl<'a>>,
    pub direct_imports: Vec<&'a str>,
    pub references_count: usize,
}

/// Lightweight, zero-dependency token scanner for .ilean JSON format.
pub struct ILeanParser<'a> {
    input: &'a [u8],
    pos: usize,
}

impl<'a> ILeanParser<'a> {
    pub fn new(input: &'a [u8]) -> Self {
        Self { input, pos: 0 }
    }

    fn skip_whitespace(&mut self) {
        while self.pos < self.input.len() {
            let b = self.input[self.pos];
            if b == b' ' || b == b'\t' || b == b'\n' || b == b'\r' {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    fn peek(&mut self) -> Option<u8> {
        self.skip_whitespace();
        if self.pos < self.input.len() {
            Some(self.input[self.pos])
        } else {
            None
        }
    }

    fn consume_byte(&mut self, expected: u8) -> bool {
        self.skip_whitespace();
        if self.pos < self.input.len() && self.input[self.pos] == expected {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn parse_string(&mut self) -> Option<&'a str> {
        self.skip_whitespace();
        if !self.consume_byte(b'"') {
            return None;
        }
        let start = self.pos;
        while self.pos < self.input.len() {
            let b = self.input[self.pos];
            if b == b'\\' {
                self.pos += 2; // skip escape
            } else if b == b'"' {
                let slice = &self.input[start..self.pos];
                self.pos += 1;
                return std::str::from_utf8(slice).ok();
            } else {
                self.pos += 1;
            }
        }
        None
    }

    fn parse_u32(&mut self) -> Option<u32> {
        self.skip_whitespace();
        let start = self.pos;
        while self.pos < self.input.len() && self.input[self.pos].is_ascii_digit() {
            self.pos += 1;
        }
        if start == self.pos {
            return None;
        }
        let s = std::str::from_utf8(&self.input[start..self.pos]).ok()?;
        s.parse::<u32>().ok()
    }

    fn skip_value(&mut self) -> bool {
        self.skip_whitespace();
        if self.pos >= self.input.len() {
            return false;
        }
        match self.input[self.pos] {
            b'"' => self.parse_string().is_some(),
            b'{' => {
                self.pos += 1;
                let mut depth = 1;
                while self.pos < self.input.len() && depth > 0 {
                    match self.input[self.pos] {
                        b'{' => depth += 1,
                        b'}' => depth -= 1,
                        b'"' => {
                            self.parse_string();
                            continue;
                        }
                        _ => {}
                    }
                    self.pos += 1;
                }
                depth == 0
            }
            b'[' => {
                self.pos += 1;
                let mut depth = 1;
                while self.pos < self.input.len() && depth > 0 {
                    match self.input[self.pos] {
                        b'[' => depth += 1,
                        b']' => depth -= 1,
                        b'"' => {
                            self.parse_string();
                            continue;
                        }
                        _ => {}
                    }
                    self.pos += 1;
                }
                depth == 0
            }
            _ => {
                while self.pos < self.input.len() {
                    let b = self.input[self.pos];
                    if b == b',' || b == b'}' || b == b']' || b == b' ' || b == b'\n' || b == b'\r'
                    {
                        break;
                    }
                    self.pos += 1;
                }
                true
            }
        }
    }

    pub fn parse(&mut self) -> Option<ILeanSummary<'a>> {
        self.skip_whitespace();
        if !self.consume_byte(b'{') {
            return None;
        }

        let mut summary = ILeanSummary::default();

        while self.peek()? != b'}' {
            let key = self.parse_string()?;
            if !self.consume_byte(b':') {
                return None;
            }

            match key {
                "version" => {
                    summary.version = self.parse_u32()?;
                }
                "module" => {
                    summary.module = self.parse_string()?;
                }
                "directImports" => {
                    if self.consume_byte(b'[') {
                        while self.peek()? != b']' {
                            if self.consume_byte(b'[') {
                                if let Some(imp) = self.parse_string() {
                                    summary.direct_imports.push(imp);
                                }
                                while self.peek()? != b']' {
                                    self.skip_value();
                                    self.consume_byte(b',');
                                }
                                self.consume_byte(b']');
                            } else {
                                self.skip_value();
                            }
                            self.consume_byte(b',');
                        }
                        self.consume_byte(b']');
                    }
                }
                "decls" => {
                    if self.consume_byte(b'{') {
                        while self.peek()? != b'}' {
                            let decl_name = self.parse_string()?;
                            if !self.consume_byte(b':') || !self.consume_byte(b'[') {
                                return None;
                            }
                            let s_line = self.parse_u32()?;
                            self.consume_byte(b',');
                            let s_col = self.parse_u32()?;
                            self.consume_byte(b',');
                            let e_line = self.parse_u32()?;
                            self.consume_byte(b',');
                            let e_col = self.parse_u32()?;
                            self.consume_byte(b',');
                            let d_line = self.parse_u32()?;
                            self.consume_byte(b',');
                            let d_col = self.parse_u32()?;
                            self.consume_byte(b',');
                            let de_line = self.parse_u32()?;
                            self.consume_byte(b',');
                            let de_col = self.parse_u32()?;

                            summary.decls.push(ILeanDecl {
                                name: decl_name,
                                range: [s_line, s_col, e_line, e_col],
                                def_range: [d_line, d_col, de_line, de_col],
                            });

                            if !self.consume_byte(b']') {
                                return None;
                            }
                            self.consume_byte(b',');
                        }
                        self.consume_byte(b'}');
                    }
                }
                "references" => {
                    // Count references without deep full tree building
                    if self.consume_byte(b'{') {
                        let mut count = 0;
                        while self.peek()? != b'}' {
                            let _ref_key = self.parse_string()?;
                            if !self.consume_byte(b':') {
                                return None;
                            }
                            self.skip_value();
                            count += 1;
                            self.consume_byte(b',');
                        }
                        self.consume_byte(b'}');
                        summary.references_count = count;
                    }
                }
                _ => {
                    self.skip_value();
                }
            }
            self.consume_byte(b',');
        }

        self.consume_byte(b'}');
        Some(summary)
    }

    /// Fast lookup: find declaration enclosing (line, col)
    pub fn find_decl_at(
        summary: &'a ILeanSummary<'a>,
        line: u32,
        col: u32,
    ) -> Option<&'a ILeanDecl<'a>> {
        for decl in &summary.decls {
            let [s_line, s_col, e_line, e_col] = decl.range;
            if line > s_line && line < e_line {
                return Some(decl);
            }
            if line == s_line && line == e_line {
                if col >= s_col && col <= e_col {
                    return Some(decl);
                }
            } else if line == s_line && col >= s_col {
                return Some(decl);
            } else if line == e_line && col <= e_col {
                return Some(decl);
            }
        }
        None
    }

    /// Fast lookup: find declaration by exact name
    pub fn find_decl_by_name(
        summary: &'a ILeanSummary<'a>,
        name: &str,
    ) -> Option<&'a ILeanDecl<'a>> {
        summary.decls.iter().find(|d| d.name == name)
    }

    /// Checks if (line, col) falls precisely inside the def_range token.
    pub fn is_in_def_range(decl: &ILeanDecl, line: u32, col: u32) -> bool {
        let [s_line, s_col, e_line, e_col] = decl.def_range;
        if line > s_line && line < e_line {
            return true;
        }
        if line == s_line && line == e_line {
            col >= s_col && col <= e_col
        } else if line == s_line {
            col >= s_col
        } else if line == e_line {
            col <= e_col
        } else {
            false
        }
    }

    /// Computes the span length in lines for a declaration.
    pub fn range_line_count(decl: &ILeanDecl) -> u32 {
        decl.range[2].saturating_sub(decl.range[0]) + 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_sample_ilean() {
        let json = br#"{"decls":{"Mathlib.Data.Nat.Basic.add_comm_verified":[58,0,102,44,65,8,65,29]},"directImports":[["Init",false,false,false]],"module":"FinalCheck","references":{"foo":{"definition":null,"usages":[[1,2,3,4]]}},"version":5}"#;
        let mut parser = ILeanParser::new(json);
        let summary = parser.parse().expect("Failed to parse ilean JSON");

        assert_eq!(summary.version, 5);
        assert_eq!(summary.module, "FinalCheck");
        assert_eq!(summary.direct_imports, vec!["Init"]);
        assert_eq!(summary.decls.len(), 1);
        assert_eq!(
            summary.decls[0].name,
            "Mathlib.Data.Nat.Basic.add_comm_verified"
        );
        assert_eq!(summary.decls[0].range, [58, 0, 102, 44]);
        assert_eq!(summary.decls[0].def_range, [65, 8, 65, 29]);
        assert_eq!(summary.references_count, 1);

        let hit = ILeanParser::find_decl_at(&summary, 65, 10);
        assert!(hit.is_some());
        assert_eq!(hit.unwrap().name, "Mathlib.Data.Nat.Basic.add_comm_verified");

        let miss = ILeanParser::find_decl_at(&summary, 105, 0);
        assert!(miss.is_none());

        let by_name = ILeanParser::find_decl_by_name(&summary, "Mathlib.Data.Nat.Basic.add_comm_verified");
        assert!(by_name.is_some());
        let decl = by_name.unwrap();

        // def_range is [65, 8, 65, 29]
        assert!(ILeanParser::is_in_def_range(decl, 65, 15));
        assert!(!ILeanParser::is_in_def_range(decl, 65, 5));
        assert!(!ILeanParser::is_in_def_range(decl, 64, 15));

        // range is [58, 0, 102, 44] => 102 - 58 + 1 = 45 lines
        assert_eq!(ILeanParser::range_line_count(decl), 45);
    }
}
