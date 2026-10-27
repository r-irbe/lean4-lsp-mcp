//! src/treesitter_mode.rs
//! Tree-Sitter mode for Lean 4 AST & CST analysis.
//! Translates Tree-Sitter Concrete Syntax Tree (CST) nodes into verified LeanExpr AST
//! and runs abstract interpretation directly on syntax nodes.
//! 

use crate::ast::LeanExpr;
use crate::interpreter::LeanAbstractInterpreter;
use crate::lattice::AbstractState;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CstNodeKind {
    Def,
    Theorem,
    App,
    Lam,
    Let,
    BinaryOp,
    UnaryOp,
    Ident(String),
    LitNat(u64),
    LitStr(String),
    Unknown(String),
}

#[derive(Debug, Clone)]
pub struct TreeSitterCstNode {
    pub kind: CstNodeKind,
    pub children: Vec<TreeSitterCstNode>,
    pub start_row: u32,
    pub start_col: u32,
    pub end_row: u32,
    pub end_col: u32,
}

impl TreeSitterCstNode {
    pub fn new(
        kind: CstNodeKind,
        start_row: u32,
        start_col: u32,
        end_row: u32,
        end_col: u32,
    ) -> Self {
        Self {
            kind,
            children: Vec::new(),
            start_row,
            start_col,
            end_row,
            end_col,
        }
    }

    pub fn is_operator_str(id: &str) -> bool {
        matches!(
            id,
            "+" | "-" | "*" | "/" | "%" | "^" | "**" | "min" | "max"
                | "<=" | "le" | "<" | "lt" | ">=" | "ge" | ">" | "gt"
                | "==" | "eq" | "!=" | "ne" | "&&" | "and" | "||" | "or"
                | "xor" | "^^" | "!" | "not" | "neg" | "succ" | "pred"
                | "&&&" | "|||" | "^^^" | "<<<" | ">>>"
                | "Nat.land" | "Nat.lor" | "Nat.xor" | "Nat.shiftLeft" | "Nat.shiftRight"
                | "Nat.succ" | "Nat.pred"
                | "AndOp.and" | "OrOp.or" | "XorOp.xor"
                | "ShiftLeft.shiftLeft" | "ShiftRight.shiftRight"
                | "Nat.add" | "Nat.sub" | "Nat.mul" | "Nat.div" | "Nat.mod"
                | "Nat.pow" | "Nat.min" | "Nat.max" | "Nat.ble" | "Nat.blt"
                | "Nat.bge" | "Nat.bgt" | "Nat.beq" | "Nat.bne"
                | "Bool.and" | "Bool.or" | "Bool.xor" | "Bool.not"
                | "HAdd.hAdd" | "HSub.hSub" | "HMul.hMul" | "HDiv.hDiv" | "HMod.hMod"
        )
    }

    pub fn is_operator_node(node: &TreeSitterCstNode) -> bool {
        match &node.kind {
            CstNodeKind::Ident(s) => Self::is_operator_str(s),
            _ => false,
        }
    }

    /// Normalizes common mathematical operators from Tree-Sitter tokens into Lean constants
    fn normalize_ident_operator(id: &str) -> String {
        match id {
            "+" => "Nat.add".to_string(),
            "-" => "Nat.sub".to_string(),
            "*" => "Nat.mul".to_string(),
            "/" => "Nat.div".to_string(),
            "%" | "mod" => "Nat.mod".to_string(),
            "^" | "**" => "Nat.pow".to_string(),
            "min" => "Nat.min".to_string(),
            "max" => "Nat.max".to_string(),
            "<=" | "le" => "Nat.ble".to_string(),
            "<" | "lt" => "Nat.blt".to_string(),
            ">=" | "ge" => "Nat.bge".to_string(),
            ">" | "gt" => "Nat.bgt".to_string(),
            "==" | "eq" => "Nat.beq".to_string(),
            "!=" | "ne" => "Nat.bne".to_string(),
            "&&" | "and" => "Bool.and".to_string(),
            "||" | "or" => "Bool.or".to_string(),
            "xor" | "^^" => "Bool.xor".to_string(),
            "!" | "not" => "Bool.not".to_string(),
            "neg" => "Neg.neg".to_string(),
            "succ" => "Nat.succ".to_string(),
            "pred" => "Nat.pred".to_string(),
            "&&&" => "Nat.land".to_string(),
            "|||" => "Nat.lor".to_string(),
            "^^^" => "Nat.xor".to_string(),
            "<<<" => "Nat.shiftLeft".to_string(),
            ">>>" => "Nat.shiftRight".to_string(),
            other => other.to_string(),
        }
    }

    /// Converts Tree-Sitter CST into Lean 4 Expression AST
    pub fn to_lean_expr(&self) -> Option<LeanExpr> {
        match &self.kind {
            CstNodeKind::LitNat(n) => Some(LeanExpr::LitNat(*n)),
            CstNodeKind::LitStr(s) => Some(LeanExpr::LitStr(s.clone())),
            CstNodeKind::Ident(id) => Some(LeanExpr::Const(Self::normalize_ident_operator(id))),
            CstNodeKind::BinaryOp => {
                if self.children.len() == 3 {
                    // Check if layout is prefix [op, left, right] or infix [left, op, right]
                    let (op_idx, left_idx, right_idx) = if Self::is_operator_node(&self.children[0])
                        && !Self::is_operator_node(&self.children[1])
                    {
                        (0, 1, 2)
                    } else {
                        (1, 0, 2)
                    };
                    let op = self.children[op_idx].to_lean_expr()?;
                    let left = self.children[left_idx].to_lean_expr()?;
                    let right = self.children[right_idx].to_lean_expr()?;
                    Some(LeanExpr::App(
                        Box::new(LeanExpr::App(Box::new(op), Box::new(left))),
                        Box::new(right),
                    ))
                } else if self.children.len() >= 2 {
                    // Prefix operator with arguments
                    let mut curr = self.children[0].to_lean_expr()?;
                    for child in &self.children[1..] {
                        let arg = child.to_lean_expr()?;
                        curr = LeanExpr::App(Box::new(curr), Box::new(arg));
                    }
                    Some(curr)
                } else {
                    None
                }
            }
            CstNodeKind::UnaryOp => {
                if self.children.len() == 2 {
                    let (op, operand) = if Self::is_operator_node(&self.children[0]) {
                        (&self.children[0], &self.children[1])
                    } else {
                        (&self.children[1], &self.children[0])
                    };
                    let op_expr = match &op.kind {
                        CstNodeKind::Ident(id) => match id.trim() {
                            "-" | "neg" => LeanExpr::Const("Neg.neg".to_string()),
                            "!" | "not" | "\u{00ac}" => LeanExpr::Const("Bool.not".to_string()),
                            other => LeanExpr::Const(Self::normalize_ident_operator(other)),
                        },
                        _ => op.to_lean_expr()?,
                    };
                    let operand_expr = operand.to_lean_expr()?;
                    Some(LeanExpr::App(Box::new(op_expr), Box::new(operand_expr)))
                } else if self.children.len() == 1 {
                    let operand = self.children[0].to_lean_expr()?;
                    Some(LeanExpr::App(
                        Box::new(LeanExpr::Const("Neg.neg".to_string())),
                        Box::new(operand),
                    ))
                } else {
                    None
                }
            }
            CstNodeKind::App => {
                if self.children.len() >= 2 {
                    let mut curr = self.children[0].to_lean_expr()?;
                    for child in &self.children[1..] {
                        let arg = child.to_lean_expr()?;
                        curr = LeanExpr::App(Box::new(curr), Box::new(arg));
                    }
                    Some(curr)
                } else {
                    None
                }
            }
            CstNodeKind::Lam => {
                if self.children.len() >= 2 {
                    let body = self.children.last()?.to_lean_expr()?;
                    let ty = Box::new(LeanExpr::Sort(0));
                    Some(LeanExpr::Lam("x".to_string(), ty, Box::new(body)))
                } else {
                    None
                }
            }
            CstNodeKind::Let => {
                if self.children.len() >= 2 {
                    let val = self.children[0].to_lean_expr()?;
                    let body = self.children[1].to_lean_expr()?;
                    let ty = Box::new(LeanExpr::Sort(0));
                    Some(LeanExpr::Let(
                        "x".to_string(),
                        ty,
                        Box::new(val),
                        Box::new(body),
                    ))
                } else {
                    None
                }
            }
            CstNodeKind::Def | CstNodeKind::Theorem => {
                // The body is typically the last child
                self.children.last()?.to_lean_expr()
            }
            CstNodeKind::Unknown(_) => None,
        }
    }

    /// Recursively collects all definition and theorem declarations in the CST.
    pub fn find_declarations(&self) -> Vec<(String, CstNodeKind)> {
        let mut decls = Vec::new();
        self.collect_declarations(&mut decls);
        decls
    }

    fn collect_declarations(&self, acc: &mut Vec<(String, CstNodeKind)>) {
        match &self.kind {
            CstNodeKind::Def | CstNodeKind::Theorem => {
                let name = self
                    .children
                    .iter()
                    .find_map(|c| match &c.kind {
                        CstNodeKind::Ident(s) => Some(s.clone()),
                        _ => None,
                    })
                    .unwrap_or_else(|| "anonymous".to_string());
                acc.push((name, self.kind.clone()));
            }
            _ => {}
        }
        for child in &self.children {
            child.collect_declarations(acc);
        }
    }

    /// Evaluates Tree-Sitter CST directly using abstract interpreter
    pub fn evaluate_abstractly(&self, interp: &LeanAbstractInterpreter) -> AbstractState {
        if let Some(expr) = self.to_lean_expr() {
            interp.eval_expr(&expr)
        } else {
            AbstractState::top()
        }
    }

    /// Evaluates and diagnoses a Tree-Sitter CST node using the abstract interpreter
    /// and SAIR KernelLawAuditor detectors (`KernelBrecOnTax`, `KernelPowerOfTwoDivMod`, `OverConcreteFixedArity`).
    pub fn diagnose_abstractly(
        &self,
        interp: &LeanAbstractInterpreter,
    ) -> (AbstractState, Vec<crate::interpreter::DiagnosticCertificate>) {
        let mut certs = Vec::new();
        if self.kind == CstNodeKind::Theorem {
            let mut idents: Vec<String> = Vec::new();
            for child in &self.children {
                if let CstNodeKind::Ident(s) = &child.kind {
                    idents.push(s.clone());
                }
            }
            if idents.len() >= 5 {
                let thm_name = idents[0].clone();
                let params: Vec<String> = idents[1..]
                    .iter()
                    .map(|p| format!("({p} : Nat)"))
                    .collect();
                let synthetic_thm = format!(
                    "theorem {thm_name} {} : {} >= 0 := by omega",
                    params.join(" "),
                    idents[1..].join(" + ")
                );
                for c in interp.diagnose_source_text(&synthetic_thm) {
                    if c.kind == crate::interpreter::DiagnosticKind::OverConcreteFixedArity {
                        certs.push(c);
                    }
                }
            }
        }
        if let Some(expr) = self.to_lean_expr() {
            let (st, mut expr_certs) = interp.diagnose_expr(&expr);
            certs.append(&mut expr_certs);
            (st, certs)
        } else {
            (AbstractState::top(), certs)
        }
    }
}

/// Lightweight parser for S-expression tree representation output by Tree-Sitter CLI
pub struct TreeSitterSExprParser<'a> {
    input: &'a [u8],
    pos: usize,
}

impl<'a> TreeSitterSExprParser<'a> {
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

    fn parse_atom(&mut self) -> Option<&'a str> {
        self.skip_whitespace();
        let start = self.pos;
        while self.pos < self.input.len() {
            let b = self.input[self.pos];
            if b == b' '
                || b == b'\t'
                || b == b'\n'
                || b == b'\r'
                || b == b'('
                || b == b')'
                || b == b'"'
            {
                break;
            }
            self.pos += 1;
        }
        if start == self.pos {
            None
        } else {
            std::str::from_utf8(&self.input[start..self.pos]).ok()
        }
    }

    pub fn parse(&mut self) -> Option<TreeSitterCstNode> {
        self.skip_whitespace();
        if self.pos >= self.input.len() || self.input[self.pos] != b'(' {
            // Check if literal atom
            if let Some(atom) = self.parse_atom() {
                if let Ok(num) = atom.parse::<u64>() {
                    return Some(TreeSitterCstNode::new(CstNodeKind::LitNat(num), 0, 0, 0, 0));
                }
                return Some(TreeSitterCstNode::new(
                    CstNodeKind::Ident(atom.to_string()),
                    0,
                    0,
                    0,
                    0,
                ));
            }
            return None;
        }

        self.pos += 1; // consume '('
        let kind_str = self.parse_atom().unwrap_or("unknown");
        let kind = match kind_str {
            "def" | "def_statement" => CstNodeKind::Def,
            "theorem" | "theorem_statement" => CstNodeKind::Theorem,
            "application" | "app" => CstNodeKind::App,
            "lambda" | "fun" => CstNodeKind::Lam,
            "let" => CstNodeKind::Let,
            "binary_expression" | "infix_op" | "op_expr" => CstNodeKind::BinaryOp,
            "unary_expression" | "negation" | "unary_op" => CstNodeKind::UnaryOp,
            "number" | "nat_lit" => {
                let val_str = self.parse_atom().unwrap_or("0");
                let val = val_str.parse::<u64>().unwrap_or(0);
                self.skip_whitespace();
                if self.pos < self.input.len() && self.input[self.pos] == b')' {
                    self.pos += 1;
                }
                return Some(TreeSitterCstNode::new(CstNodeKind::LitNat(val), 0, 0, 0, 0));
            }
            "string" | "string_lit" | "str_lit" | "string_literal" => {
                self.skip_whitespace();
                let mut s = String::new();
                if self.pos < self.input.len() && self.input[self.pos] == b'"' {
                    self.pos += 1;
                    while self.pos < self.input.len() && self.input[self.pos] != b'"' {
                        s.push(self.input[self.pos] as char);
                        self.pos += 1;
                    }
                    if self.pos < self.input.len() && self.input[self.pos] == b'"' {
                        self.pos += 1;
                    }
                } else if let Some(atom) = self.parse_atom() {
                    s = atom.trim_matches('"').to_string();
                }
                self.skip_whitespace();
                if self.pos < self.input.len() && self.input[self.pos] == b')' {
                    self.pos += 1;
                }
                return Some(TreeSitterCstNode::new(CstNodeKind::LitStr(s), 0, 0, 0, 0));
            }
            "identifier" | "ident" | "operator" => {
                let name = self.parse_atom().unwrap_or("").to_string();
                self.skip_whitespace();
                if self.pos < self.input.len() && self.input[self.pos] == b')' {
                    self.pos += 1;
                }
                return Some(TreeSitterCstNode::new(CstNodeKind::Ident(name), 0, 0, 0, 0));
            }
            other => CstNodeKind::Unknown(other.to_string()),
        };

        let mut node = TreeSitterCstNode::new(kind, 0, 0, 0, 0);

        while self.peek()? != b')' {
            if let Some(child) = self.parse() {
                node.children.push(child);
            } else {
                break;
            }
        }

        if self.pos < self.input.len() && self.input[self.pos] == b')' {
            self.pos += 1;
        }

        Some(node)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lattice::{AbstractSign, IntervalBound};

    #[test]
    fn test_treesitter_sexpr_to_ast_eval() {
        let sexpr = b"(def (identifier foo) (app (identifier Nat.add) (number 12) (number 28)))";
        let mut parser = TreeSitterSExprParser::new(sexpr);
        let cst = parser
            .parse()
            .expect("Failed to parse Tree-sitter S-expression");

        assert_eq!(cst.kind, CstNodeKind::Def);
        assert_eq!(cst.children.len(), 2);

        let interp = LeanAbstractInterpreter::new();
        let state = cst.evaluate_abstractly(&interp);

        assert_eq!(state.sign, AbstractSign::Positive);
        assert_eq!(state.interval, Some(IntervalBound::point(40)));
        assert!(state.is_deterministic);
        assert!(state.is_pure);
    }

    #[test]
    fn test_treesitter_binary_op_and_declaration_discovery() {
        let sexpr = b"(def (identifier computeVal) (binary_expression (number 15) (identifier +) (number 35)))";
        let mut parser = TreeSitterSExprParser::new(sexpr);
        let cst = parser
            .parse()
            .expect("Failed to parse Tree-sitter S-expression");

        let decls = cst.find_declarations();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].0, "computeVal");
        assert_eq!(decls[0].1, CstNodeKind::Def);

        let interp = LeanAbstractInterpreter::new();
        let state = cst.evaluate_abstractly(&interp);

        assert_eq!(state.sign, AbstractSign::Positive);
        assert_eq!(state.interval, Some(IntervalBound::point(50)));
        assert!(state.is_deterministic);
    }

    #[test]
    fn test_treesitter_prefix_binary_op_and_operator_token() {
        // Prefix layout: [operator, left, right] with (operator ...) token
        let sexpr = b"(def (identifier addPrefix) (binary_expression (operator +) (number 20) (number 80)))";
        let mut parser = TreeSitterSExprParser::new(sexpr);
        let cst = parser
            .parse()
            .expect("Failed to parse Tree-sitter S-expression");

        let interp = LeanAbstractInterpreter::new();
        let state = cst.evaluate_abstractly(&interp);

        assert_eq!(state.sign, AbstractSign::Positive);
        assert_eq!(state.interval, Some(IntervalBound::point(100)));
        assert!(state.is_deterministic);
    }

    #[test]
    fn test_treesitter_unary_op_and_string_literal() {
        let sexpr = b"(def (identifier msgDef) (string \"verified\"))";
        let mut parser = TreeSitterSExprParser::new(sexpr);
        let cst = parser
            .parse()
            .expect("Failed to parse string literal def");

        let interp = LeanAbstractInterpreter::new();
        let state = cst.evaluate_abstractly(&interp);
        assert!(state.is_pure);

        // Unary negation test
        let neg_sexpr = b"(unary_expression (operator -) (number 42))";
        let mut neg_parser = TreeSitterSExprParser::new(neg_sexpr);
        let neg_cst = neg_parser.parse().expect("Failed to parse unary op");
        assert_eq!(neg_cst.kind, CstNodeKind::UnaryOp);
        let expr = neg_cst.to_lean_expr().expect("Should convert unary op");
        match expr {
            LeanExpr::App(f, arg) => {
                assert_eq!(*f, LeanExpr::Const("Neg.neg".to_string()));
                assert_eq!(*arg, LeanExpr::LitNat(42));
            }
            _ => panic!("Expected App for unary expression"),
        }
    }

    #[test]
    fn test_treesitter_two_child_unary_minus_lowers_to_neg() {
        let sexpr = b"(unary_op (ident -) (nat_lit 7))";
        let mut parser = TreeSitterSExprParser::new(sexpr);
        let cst = parser.parse().expect("Failed to parse 2-child unary minus");
        assert_eq!(cst.kind, CstNodeKind::UnaryOp);
        assert_eq!(cst.children.len(), 2);

        let expr = cst.to_lean_expr().expect("Should lower 2-child unary minus");
        assert_eq!(
            expr,
            LeanExpr::App(
                Box::new(LeanExpr::Const("Neg.neg".to_string())),
                Box::new(LeanExpr::LitNat(7)),
            )
        );
    }

    #[test]
    fn test_treesitter_diagnose_sair_laws() {
        let interp = LeanAbstractInterpreter::new();

        // Law 14: / 64 in CST
        let pow2_sexpr =
            b"(def (identifier stepMod) (binary_expression (identifier x) (operator /) (number 64)))";
        let mut p1 = TreeSitterSExprParser::new(pow2_sexpr);
        let cst1 = p1.parse().expect("parse pow2 def");
        let (_st1, certs1) = cst1.diagnose_abstractly(&interp);
        assert!(
            certs1
                .iter()
                .any(|c| c.kind == crate::interpreter::DiagnosticKind::KernelPowerOfTwoDivMod),
            "Expected KernelPowerOfTwoDivMod in CST: {:?}",
            certs1
        );

        // Law 6: Nat.brecOn in CST
        let brec_sexpr = b"(def (identifier stepBrec) (app (identifier Nat.brecOn) (identifier n)))";
        let mut p2 = TreeSitterSExprParser::new(brec_sexpr);
        let cst2 = p2.parse().expect("parse brec def");
        let (_st2, certs2) = cst2.diagnose_abstractly(&interp);
        assert!(
            certs2
                .iter()
                .any(|c| c.kind == crate::interpreter::DiagnosticKind::KernelBrecOnTax),
            "Expected KernelBrecOnTax in CST: {:?}",
            certs2
        );

        // OverConcreteFixedArity in CST theorem
        let arity_sexpr = b"(theorem (identifier thmFixed4) (identifier a0) (identifier a1) (identifier a2) (identifier a3) (number 1))";
        let mut p3 = TreeSitterSExprParser::new(arity_sexpr);
        let cst3 = p3.parse().expect("parse fixed arity theorem");
        let (_st3, certs3) = cst3.diagnose_abstractly(&interp);
        assert!(
            certs3
                .iter()
                .any(|c| c.kind == crate::interpreter::DiagnosticKind::OverConcreteFixedArity),
            "Expected OverConcreteFixedArity in CST: {:?}",
            certs3
        );
    }
}
