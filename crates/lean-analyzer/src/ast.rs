//! src/ast.rs
//! Core Lean 4 expression representation for in-process abstract interpretation.
//! 

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LeanExpr {
    /// de Bruijn variable index
    BVar(u32),
    /// Free variable identifier
    FVar(String),
    /// Constant declaration name
    Const(String),
    /// Sort / Universe level
    Sort(u32),
    /// Natural number literal
    LitNat(u64),
    /// String literal
    LitStr(String),
    /// Function application: `(f a)`
    App(Box<LeanExpr>, Box<LeanExpr>),
    /// Lambda abstraction: `fun (x : T) => body`
    Lam(String, Box<LeanExpr>, Box<LeanExpr>),
    /// Dependent arrow / forall: `(x : T) -> body`
    Pi(String, Box<LeanExpr>, Box<LeanExpr>),
    /// Let binding: `let x : T := val; body`
    Let(String, Box<LeanExpr>, Box<LeanExpr>, Box<LeanExpr>),
    /// Structure projection: `struct.idx`
    Proj(String, u32, Box<LeanExpr>),
}

impl LeanExpr {
    pub fn is_atomic(&self) -> bool {
        matches!(
            self,
            LeanExpr::BVar(_)
                | LeanExpr::FVar(_)
                | LeanExpr::Const(_)
                | LeanExpr::LitNat(_)
                | LeanExpr::LitStr(_)
        )
    }

    pub fn depth(&self) -> usize {
        match self {
            LeanExpr::BVar(_)
            | LeanExpr::FVar(_)
            | LeanExpr::Const(_)
            | LeanExpr::Sort(_)
            | LeanExpr::LitNat(_)
            | LeanExpr::LitStr(_) => 1,
            LeanExpr::App(f, a) => 1 + std::cmp::max(f.depth(), a.depth()),
            LeanExpr::Lam(_, ty, body) | LeanExpr::Pi(_, ty, body) => {
                1 + std::cmp::max(ty.depth(), body.depth())
            }
            LeanExpr::Let(_, ty, val, body) => {
                1 + std::cmp::max(ty.depth(), std::cmp::max(val.depth(), body.depth()))
            }
            LeanExpr::Proj(_, _, inner) => 1 + inner.depth(),
        }
    }

    pub fn node_count(&self) -> usize {
        match self {
            LeanExpr::BVar(_)
            | LeanExpr::FVar(_)
            | LeanExpr::Const(_)
            | LeanExpr::Sort(_)
            | LeanExpr::LitNat(_)
            | LeanExpr::LitStr(_) => 1,
            LeanExpr::App(f, a) => 1 + f.node_count() + a.node_count(),
            LeanExpr::Lam(_, ty, body) | LeanExpr::Pi(_, ty, body) => {
                1 + ty.node_count() + body.node_count()
            }
            LeanExpr::Let(_, ty, val, body) => {
                1 + ty.node_count() + val.node_count() + body.node_count()
            }
            LeanExpr::Proj(_, _, inner) => 1 + inner.node_count(),
        }
    }

    pub fn collect_constants(&self, acc: &mut Vec<String>) {
        match self {
            LeanExpr::Const(c) => {
                if !acc.contains(c) {
                    acc.push(c.clone());
                }
            }
            LeanExpr::App(f, a) => {
                f.collect_constants(acc);
                a.collect_constants(acc);
            }
            LeanExpr::Lam(_, ty, body) | LeanExpr::Pi(_, ty, body) => {
                ty.collect_constants(acc);
                body.collect_constants(acc);
            }
            LeanExpr::Let(_, ty, val, body) => {
                ty.collect_constants(acc);
                val.collect_constants(acc);
                body.collect_constants(acc);
            }
            LeanExpr::Proj(_, _, inner) => {
                inner.collect_constants(acc);
            }
            _ => {}
        }
    }

    /// Recursively collects all `LitNat` literals appearing in the expression into `acc`.
    pub fn collect_nat_literals(&self, acc: &mut Vec<i64>) {
        match self {
            LeanExpr::LitNat(v) => {
                let s = if *v >= i64::MAX as u64 {
                    i64::MAX - 1
                } else {
                    *v as i64
                };
                if !acc.contains(&s) {
                    acc.push(s);
                }
            }
            LeanExpr::App(f, a) => {
                f.collect_nat_literals(acc);
                a.collect_nat_literals(acc);
            }
            LeanExpr::Lam(_, ty, body) | LeanExpr::Pi(_, ty, body) => {
                ty.collect_nat_literals(acc);
                body.collect_nat_literals(acc);
            }
            LeanExpr::Let(_, ty, val, body) => {
                ty.collect_nat_literals(acc);
                val.collect_nat_literals(acc);
                body.collect_nat_literals(acc);
            }
            LeanExpr::Proj(_, _, inner) => {
                inner.collect_nat_literals(acc);
            }
            _ => {}
        }
    }

    /// Harvests sorted threshold checkpoints from an expression (literal constants `c`, `c - 1`, `c + 1`
    /// plus standard scaled-integer checkpoints `{0, 1, 100, 10000}`) for threshold widening
    /// (`Moller & Schwartzbach 2018`, `Rival & Yi 2020`).
    pub fn collect_nat_thresholds(&self) -> Vec<i64> {
        let mut lits = vec![0i64, 1, 100, 10_000];
        self.collect_nat_literals(&mut lits);
        let base = lits.clone();
        for c in base {
            if c > 0 {
                lits.push(c - 1);
            }
            if c < i64::MAX - 1 {
                lits.push(c + 1);
            }
        }
        lits.sort_unstable();
        lits.dedup();
        lits
    }

    pub fn subst_bvar(&self, target_idx: u32, repl: &LeanExpr) -> LeanExpr {
        match self {
            LeanExpr::BVar(idx) => {
                if *idx == target_idx {
                    repl.clone()
                } else {
                    self.clone()
                }
            }
            LeanExpr::App(f, a) => LeanExpr::App(
                Box::new(f.subst_bvar(target_idx, repl)),
                Box::new(a.subst_bvar(target_idx, repl)),
            ),
            LeanExpr::Lam(id, ty, body) => LeanExpr::Lam(
                id.clone(),
                Box::new(ty.subst_bvar(target_idx, repl)),
                Box::new(body.subst_bvar(target_idx + 1, repl)),
            ),
            LeanExpr::Pi(id, ty, body) => LeanExpr::Pi(
                id.clone(),
                Box::new(ty.subst_bvar(target_idx, repl)),
                Box::new(body.subst_bvar(target_idx + 1, repl)),
            ),
            LeanExpr::Let(id, ty, val, body) => LeanExpr::Let(
                id.clone(),
                Box::new(ty.subst_bvar(target_idx, repl)),
                Box::new(val.subst_bvar(target_idx, repl)),
                Box::new(body.subst_bvar(target_idx + 1, repl)),
            ),
            LeanExpr::Proj(name, idx, inner) => {
                LeanExpr::Proj(name.clone(), *idx, Box::new(inner.subst_bvar(target_idx, repl)))
            }
            _ => self.clone(),
        }
    }

    pub fn has_loose_bvar_above(&self, cutoff: u32) -> bool {
        match self {
            LeanExpr::BVar(idx) => *idx >= cutoff,
            LeanExpr::App(f, a) => {
                f.has_loose_bvar_above(cutoff) || a.has_loose_bvar_above(cutoff)
            }
            LeanExpr::Lam(_, ty, body) | LeanExpr::Pi(_, ty, body) => {
                ty.has_loose_bvar_above(cutoff) || body.has_loose_bvar_above(cutoff + 1)
            }
            LeanExpr::Let(_, ty, val, body) => {
                ty.has_loose_bvar_above(cutoff)
                    || val.has_loose_bvar_above(cutoff)
                    || body.has_loose_bvar_above(cutoff + 1)
            }
            LeanExpr::Proj(_, _, inner) => inner.has_loose_bvar_above(cutoff),
            _ => false,
        }
    }

    pub fn is_closed(&self) -> bool {
        !self.has_loose_bvar_above(0)
    }

    pub fn beta_reduce_once(&self) -> Option<LeanExpr> {
        if let LeanExpr::App(f, a) = self {
            if let LeanExpr::Lam(_, _ty, body) = f.as_ref() {
                return Some(body.subst_bvar(0, a.as_ref()));
            }
        }
        None
    }

    /// Alpha-equivalence: syntactic identity modulo binder identifier names.
    pub fn alpha_equiv(&self, other: &LeanExpr) -> bool {
        match (self, other) {
            (LeanExpr::BVar(i1), LeanExpr::BVar(i2)) => i1 == i2,
            (LeanExpr::FVar(n1), LeanExpr::FVar(n2)) => n1 == n2,
            (LeanExpr::Const(c1), LeanExpr::Const(c2)) => c1 == c2,
            (LeanExpr::Sort(u1), LeanExpr::Sort(u2)) => u1 == u2,
            (LeanExpr::LitNat(v1), LeanExpr::LitNat(v2)) => v1 == v2,
            (LeanExpr::LitStr(s1), LeanExpr::LitStr(s2)) => s1 == s2,
            (LeanExpr::App(f1, a1), LeanExpr::App(f2, a2)) => {
                f1.alpha_equiv(f2) && a1.alpha_equiv(a2)
            }
            (LeanExpr::Lam(_, ty1, b1), LeanExpr::Lam(_, ty2, b2)) => {
                ty1.alpha_equiv(ty2) && b1.alpha_equiv(b2)
            }
            (LeanExpr::Pi(_, ty1, b1), LeanExpr::Pi(_, ty2, b2)) => {
                ty1.alpha_equiv(ty2) && b1.alpha_equiv(b2)
            }
            (LeanExpr::Let(_, ty1, v1, b1), LeanExpr::Let(_, ty2, v2, b2)) => {
                ty1.alpha_equiv(ty2) && v1.alpha_equiv(v2) && b1.alpha_equiv(b2)
            }
            (LeanExpr::Proj(s1, idx1, e1), LeanExpr::Proj(s2, idx2, e2)) => {
                s1 == s2 && idx1 == idx2 && e1.alpha_equiv(e2)
            }
            _ => false,
        }
    }

    /// Weak head normal form (WHNF) bounded reduction.
    pub fn whnf(&self, max_steps: usize) -> LeanExpr {
        let mut curr = self.clone();
        for _ in 0..max_steps {
            match curr {
                LeanExpr::App(ref f, ref a) => {
                    let f_whnf = f.whnf(max_steps);
                    if let LeanExpr::Lam(_, _, body) = f_whnf {
                        curr = body.subst_bvar(0, a);
                        continue;
                    }
                    if let LeanExpr::Let(_, _, val, body) = f_whnf {
                        curr = LeanExpr::App(Box::new(body.subst_bvar(0, &val)), a.clone());
                        continue;
                    }
                    curr = LeanExpr::App(Box::new(f_whnf), a.clone());
                    break;
                }
                LeanExpr::Let(_, _, ref val, ref body) => {
                    curr = body.subst_bvar(0, val);
                }
                _ => break,
            }
        }
        curr
    }

    /// Deep multi-step beta reduction until a normal form is reached or max_steps exhausted.
    pub fn beta_reduce_all(&self, max_steps: usize) -> LeanExpr {
        let mut curr = self.clone();
        for _ in 0..max_steps {
            if let Some(next) = curr.beta_reduce_once() {
                curr = next;
            } else {
                break;
            }
        }
        curr
    }

    /// Substitutes named free variable (FVar) with a replacement expression.
    pub fn subst_free_var(&self, name: &str, replacement: &LeanExpr) -> LeanExpr {
        match self {
            LeanExpr::FVar(n) if n == name => replacement.clone(),
            LeanExpr::App(f, a) => LeanExpr::App(
                Box::new(f.subst_free_var(name, replacement)),
                Box::new(a.subst_free_var(name, replacement)),
            ),
            LeanExpr::Lam(id, ty, body) => LeanExpr::Lam(
                id.clone(),
                Box::new(ty.subst_free_var(name, replacement)),
                Box::new(body.subst_free_var(name, replacement)),
            ),
            LeanExpr::Pi(id, ty, body) => LeanExpr::Pi(
                id.clone(),
                Box::new(ty.subst_free_var(name, replacement)),
                Box::new(body.subst_free_var(name, replacement)),
            ),
            LeanExpr::Let(id, ty, val, body) => LeanExpr::Let(
                id.clone(),
                Box::new(ty.subst_free_var(name, replacement)),
                Box::new(val.subst_free_var(name, replacement)),
                Box::new(body.subst_free_var(name, replacement)),
            ),
            LeanExpr::Proj(pname, idx, inner) => LeanExpr::Proj(
                pname.clone(),
                *idx,
                Box::new(inner.subst_free_var(name, replacement)),
            ),
            _ => self.clone(),
        }
    }

    /// Formats the Lean expression as a readable pseudo-Lean syntax string.
    pub fn to_lean_syntax(&self) -> String {
        match self {
            LeanExpr::BVar(idx) => format!("#{idx}"),
            LeanExpr::FVar(name) => name.clone(),
            LeanExpr::Const(name) => name.clone(),
            LeanExpr::Sort(lvl) => format!("Type {lvl}"),
            LeanExpr::LitNat(val) => val.to_string(),
            LeanExpr::LitStr(val) => format!("\"{val}\""),
            LeanExpr::App(f, a) => format!("({} {})", f.to_lean_syntax(), a.to_lean_syntax()),
            LeanExpr::Lam(id, ty, body) => {
                format!("(fun ({id} : {}) => {})", ty.to_lean_syntax(), body.to_lean_syntax())
            }
            LeanExpr::Pi(id, ty, body) => {
                format!("(({id} : {}) -> {})", ty.to_lean_syntax(), body.to_lean_syntax())
            }
            LeanExpr::Let(id, ty, val, body) => {
                format!(
                    "(let {id} : {} := {}; {})",
                    ty.to_lean_syntax(),
                    val.to_lean_syntax(),
                    body.to_lean_syntax()
                )
            }
            LeanExpr::Proj(name, idx, inner) => {
                format!("{name}.{idx} ({})", inner.to_lean_syntax())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expr_depth_and_node_count() {
        let x = LeanExpr::BVar(0);
        assert_eq!(x.depth(), 1);
        assert_eq!(x.node_count(), 1);

        let app = LeanExpr::App(
            Box::new(LeanExpr::Const("Nat.succ".to_string())),
            Box::new(LeanExpr::LitNat(42)),
        );
        assert_eq!(app.depth(), 2);
        assert_eq!(app.node_count(), 3);

        let lam = LeanExpr::Lam(
            "x".to_string(),
            Box::new(LeanExpr::Const("Nat".to_string())),
            Box::new(app),
        );
        assert_eq!(lam.depth(), 3);
        assert_eq!(lam.node_count(), 5);
    }

    #[test]
    fn test_collect_constants() {
        let expr = LeanExpr::App(
            Box::new(LeanExpr::Const("Nat.add".to_string())),
            Box::new(LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.mul".to_string())),
                Box::new(LeanExpr::Const("Nat.add".to_string())),
            )),
        );
        let mut consts = Vec::new();
        expr.collect_constants(&mut consts);
        assert_eq!(consts, vec!["Nat.add".to_string(), "Nat.mul".to_string()]);
    }

    #[test]
    fn test_subst_bvar() {
        let body = LeanExpr::App(
            Box::new(LeanExpr::BVar(0)),
            Box::new(LeanExpr::BVar(1)),
        );
        let repl = LeanExpr::LitNat(100);
        let res = body.subst_bvar(0, &repl);
        assert_eq!(
            res,
            LeanExpr::App(
                Box::new(LeanExpr::LitNat(100)),
                Box::new(LeanExpr::BVar(1)),
            )
        );
    }

    #[test]
    fn test_is_closed_and_loose_bvars() {
        // Const is closed
        let c = LeanExpr::Const("Nat.zero".to_string());
        assert!(c.is_closed());

        // BVar 0 alone is open (loose bvar 0)
        let b0 = LeanExpr::BVar(0);
        assert!(!b0.is_closed());
        assert!(b0.has_loose_bvar_above(0));
        assert!(!b0.has_loose_bvar_above(1));

        // fun x : Nat => x is closed because BVar 0 is bound by Lam
        let lam_id = LeanExpr::Lam(
            "x".to_string(),
            Box::new(LeanExpr::Const("Nat".to_string())),
            Box::new(LeanExpr::BVar(0)),
        );
        assert!(lam_id.is_closed());

        // fun x : Nat => y (where y is BVar 1) is open
        let lam_open = LeanExpr::Lam(
            "x".to_string(),
            Box::new(LeanExpr::Const("Nat".to_string())),
            Box::new(LeanExpr::BVar(1)),
        );
        assert!(!lam_open.is_closed());
    }

    #[test]
    fn test_beta_reduce_once() {
        // (fun x : Nat => x) 42  -->  42
        let lam_id = LeanExpr::Lam(
            "x".to_string(),
            Box::new(LeanExpr::Const("Nat".to_string())),
            Box::new(LeanExpr::BVar(0)),
        );
        let app = LeanExpr::App(Box::new(lam_id), Box::new(LeanExpr::LitNat(42)));
        let reduced = app.beta_reduce_once();
        assert_eq!(reduced, Some(LeanExpr::LitNat(42)));

        // Non-application cannot beta-reduce
        assert_eq!(LeanExpr::LitNat(42).beta_reduce_once(), None);
    }

    #[test]
    fn test_alpha_equiv() {
        // fun x : Nat => x  alpha-equiv  fun y : Nat => y
        let lam_x = LeanExpr::Lam(
            "x".to_string(),
            Box::new(LeanExpr::Const("Nat".to_string())),
            Box::new(LeanExpr::BVar(0)),
        );
        let lam_y = LeanExpr::Lam(
            "y".to_string(),
            Box::new(LeanExpr::Const("Nat".to_string())),
            Box::new(LeanExpr::BVar(0)),
        );
        assert!(lam_x.alpha_equiv(&lam_y));

        let lam_diff = LeanExpr::Lam(
            "x".to_string(),
            Box::new(LeanExpr::Const("Int".to_string())),
            Box::new(LeanExpr::BVar(0)),
        );
        assert!(!lam_x.alpha_equiv(&lam_diff));
    }

    #[test]
    fn test_whnf_and_to_lean_syntax() {
        // ((fun x : Nat => x) 100) -> 100
        let lam_id = LeanExpr::Lam(
            "x".to_string(),
            Box::new(LeanExpr::Const("Nat".to_string())),
            Box::new(LeanExpr::BVar(0)),
        );
        let app = LeanExpr::App(Box::new(lam_id), Box::new(LeanExpr::LitNat(100)));
        assert_eq!(app.to_lean_syntax(), "((fun (x : Nat) => #0) 100)");

        let norm = app.whnf(10);
        assert_eq!(norm, LeanExpr::LitNat(100));
        assert_eq!(norm.to_lean_syntax(), "100");
    }

    #[test]
    fn test_beta_reduce_all_and_subst_free_var() {
        // (fun x => x) 50
        let lam = LeanExpr::Lam(
            "x".to_string(),
            Box::new(LeanExpr::Const("Nat".to_string())),
            Box::new(LeanExpr::BVar(0)),
        );
        let app = LeanExpr::App(Box::new(lam), Box::new(LeanExpr::LitNat(50)));
        assert_eq!(app.beta_reduce_all(5), LeanExpr::LitNat(50));

        // Subst free var "alpha" with 99
        let fvar_expr = LeanExpr::App(
            Box::new(LeanExpr::Const("Nat.succ".to_string())),
            Box::new(LeanExpr::FVar("alpha".to_string())),
        );
        let substituted = fvar_expr.subst_free_var("alpha", &LeanExpr::LitNat(99));
        assert_eq!(
            substituted,
            LeanExpr::App(
                Box::new(LeanExpr::Const("Nat.succ".to_string())),
                Box::new(LeanExpr::LitNat(99)),
            )
        );
    }
}
