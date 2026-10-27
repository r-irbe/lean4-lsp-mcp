/-
  Oracle generator for the lean-analyzer differential tests.

  Evaluates every operator the abstract interpreter claims to model, on a grid of concrete
  inputs, using Lean core itself. The output is committed as
  tests/fixtures/lean_oracle.tsv; the Rust tests then check the analyzer against it.

  Run: bash tools/regen_oracle.sh
-/

def dense : List Nat := List.range 10

def sparse : List Nat :=
  [15, 16, 17, 31, 32, 33, 63, 64, 65, 100, 255, 256, 1000, 65535, 65536,
   4294967295, 4294967296, 4611686018427387903, 4611686018427387904,
   9223372036854775807, 9223372036854775808]

def values : List Nat := dense ++ sparse

def b2s (b : Bool) : String := if b then "true" else "false"

def row (op : String) (a b r : String) : IO Unit :=
  IO.println s!"{op}\t{a}\t{b}\t{r}"

/-- Binary Nat -> Nat -> Nat operators. Exponent/shift amounts are capped to keep results small. -/
def natOps : List (Prod String (Prod (Nat -> Nat -> Nat) Nat)) :=
  [ ("add", (fun a b => a + b), 0), ("sub", (fun a b => a - b), 0), ("mul", (fun a b => a * b), 0),
    ("div", (fun a b => a / b), 0), ("mod", (fun a b => a % b), 0), ("min", min, 0), ("max", max, 0),
    ("land", (fun a b => a &&& b), 0), ("lor", (fun a b => a ||| b), 0), ("lxor", (fun a b => a ^^^ b), 0),
    ("pow", (fun a b => a ^ b), 70), ("shl", (fun a b => a <<< b), 70), ("shr", (fun a b => a >>> b), 70) ]

/-- Binary Nat -> Nat -> Bool relations. -/
def relOps : List (Prod String (Nat -> Nat -> Bool)) :=
  [ ("le", fun a b => decide (a <= b)), ("lt", fun a b => decide (a < b)),
    ("ge", fun a b => decide (a >= b)), ("gt", fun a b => decide (a > b)),
    ("eq", fun a b => decide (a = b)), ("ne", fun a b => bne a b),
    ("ble", Nat.ble), ("blt", Nat.blt), ("beq", Nat.beq) ]

def main : IO Unit := do
  IO.println s!"#lean-oracle\t{Lean.versionString}"
  for (name, f, cap) in natOps do
    for a in values do
      for b in values do
        if cap == 0 || b <= cap then
          row name (toString a) (toString b) (toString (f a b))
  for a in values do
    row "succ" (toString a) "-" (toString (Nat.succ a))
    row "pred" (toString a) "-" (toString (Nat.pred a))
  for (name, f) in relOps do
    for a in values do
      for b in values do
        row name (toString a) (toString b) (b2s (f a b))
  for a in [true, false] do
    for b in [true, false] do
      row "band" (b2s a) (b2s b) (b2s (a && b))
      row "bor" (b2s a) (b2s b) (b2s (a || b))
      row "bxor" (b2s a) (b2s b) (b2s (xor a b))
      row "b_eq" (b2s a) (b2s b) (b2s (a == b))
      row "b_ne" (b2s a) (b2s b) (b2s (a != b))
  for a in [true, false] do
    row "bnot" (b2s a) "-" (b2s (!a))
  for c in [true, false] do
    for t in dense do
      for e in dense do
        row "cond" (b2s c) s!"{t},{e}" (toString (cond c t e))
