import Lean

open Lean

/-- Follow the declaration types and values available in this imported environment. -/
partial def reachable (env : Environment) (root : Name) : Array Name := Id.run do
  let rec visit (todo : List Name) (seen : NameHashSet) (order : Array Name) : Array Name :=
    match todo with
    | [] => order
    | name :: rest =>
      if seen.contains name then visit rest seen order
      else
        match env.find? name with
        | none => visit rest seen order
        | some info =>
          let deps := info.type.getUsedConstants ++
            (match info with
             | .defnInfo decl => decl.value.getUsedConstants
             | .thmInfo decl => decl.value.getUsedConstants
             | .opaqueInfo decl => decl.value.getUsedConstants
             | _ => #[])
          visit (deps.toList ++ rest) (seen.insert name) (order.push name)
  return visit [root] {} #[]

def coneReport (env : Environment) (root : Name) : IO Json := do
  unless (env.find? root).isSome do
    throw (IO.userError s!"declaration unavailable in imported module: {root}")
  let names := reachable env root
  let axioms ← (Lean.collectAxioms (m := CoreM) root).run'
    { fileName := "<compiled cone>", fileMap := FileMap.ofString "" } { env } |>.toIO fun _ =>
      IO.userError "Lean axiom collection failed"
  return Json.mkObj [
    ("root", toJson root.toString),
    ("declarations", toJson (names.map Name.toString)),
    ("theorems", toJson ((names.filter fun name =>
      match env.find? name with | some (.thmInfo _) => true | _ => false).map Name.toString)),
    ("axioms", toJson (axioms.map Name.toString))
  ]

unsafe def main (args : List String) : IO Unit := do
  let moduleName :: runtimeName :: roots := args
    | throw (IO.userError "usage: CompiledCone.lean module runtimeRoot [proofRoot]")
  unless roots.length ≤ 1 do
    throw (IO.userError "expected at most one proof root")
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := moduleName.toName }] {}
  let runtime ← coneReport env runtimeName.toName
  let proof ← roots.head?.mapM fun name => coneReport env name.toName
  IO.println (Json.mkObj [("module", toJson moduleName), ("runtime", runtime), ("proof", toJson proof)]).compress
