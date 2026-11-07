------------------------- MODULE NavigationLifecycle -------------------------
(***************************************************************************)
(* Formal lifecycle model for `FileWorkerManager.navigate()` and           *)
(* `Lean4IleanIndex` currency in `lean4-lsp-mcp` (`src/index.ts`,          *)
(* `src/navigation.ts`).                                                   *)
(*                                                                         *)
(* Instantiated from the `pi-lens` `NavigationLifecycle.tla` packet for    *)
(* P1 (`P1-MCP-LIVE-NAV.md` section 8):                                    *)
(*                                                                         *)
(*   Idle -> AdmissionChecked -> RouteBound -> SessionEnsured              *)
(*        -> Requested -> Served | Refused                                 *)
(*                                                                         *)
(* Recorded architectural delta from `pi-lens`:                            *)
(*   The `pi-lens` model included `mcpPending` / `McpBootstrapStart` /     *)
(*   `McpReset` / `McpBootstrapFinish` (`pending bootstrap reset`) to      *)
(*   model `pi-lens`'s async `loadBootstrapClients()` host wrapper.        *)
(*   `lean4-lsp-mcp` IS the MCP server itself and constructs/registers     *)
(*   sessions synchronously inside `FileWorkerManager.ensureSession`       *)
(*   (`this.sessions.set(leanRoot, session)`), so there is no separate     *)
(*   async pending-bootstrap publication window. Instead, session          *)
(*   replacement during `sendRequest` is checked directly via              *)
(*   `this.sessions.get(session.leanRoot) !== session` and index           *)
(*   currency is checked via `Lean4IleanIndex.getGeneration()`.            *)
(*                                                                         *)
(* Switches and mutant overrides (`<-` in `*.cfg`):                        *)
(*  - `NavGateBeforeSpawn` (`MutNavSpawnBeforeAdmission`):                 *)
(*      When TRUE (as-built), `ensureSession` (broker discovery, lock/     *)
(*      analyzer probe, child `spawn`) cannot run until `CheckAdmission`   *)
(*      and `BindWarmRoute` succeed on an admitted/valid context.          *)
(*      When FALSE, `MutSpawnBeforeAdmission` enters `SessionEnsured`      *)
(*      from `Idle` before checking admission, violating                   *)
(*      `NoSpawnBeforeAdmission`.                                          *)
(*  - `NavEntryCapture` (`MutNavLateCapture`):                             *)
(*      When TRUE (as-built), `CheckAdmission` captures `navAdm`,          *)
(*      `navMgrGen`, and `navIleanGen` (`gateGeneration`) before the       *)
(*      first async boundary. When FALSE, capture is deferred until        *)
(*      `ResolveRequest`, violating `NoStaleNavigationServe`.              *)
(*  - `NavBeforeReset` (`MutNavNoBeforeReset`):                            *)
(*      When TRUE (as-built), `ManagerReset` (`setLeanContext` / manager   *)
(*      session reset) atomically bumps `ileanGen` alongside `mgrGen`.     *)
(*      When FALSE, `ileanGen` is left unbumped across reset so an         *)
(*      offline/fallback lookup checking index generation alone serves     *)
(*      stale artifacts, violating `NoStaleNavigationServe`.               *)
(*  - `NavNoDropSurvivor` (`MutNavDropSurvivor`):                          *)
(*      When TRUE (as-built), a post-reset `SurvivorNavigate` under a      *)
(*      valid current admission completes and serves. When FALSE, the      *)
(*      gate unconditionally refuses survivor requests, violating          *)
(*      `NoDropSurvivorNavigation`.                                        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

NavGateBeforeSpawn == TRUE
NavGateBeforeSpawnOff == FALSE

NavEntryCapture == TRUE
NavEntryCaptureOff == FALSE

NavBeforeReset == TRUE
NavBeforeResetOff == FALSE

NavNoDropSurvivor == TRUE
NavNoDropSurvivorOff == FALSE

MaxSteps == 2

VARIABLES
    admValid,           \* BOOLEAN: whether current host/context state satisfies admission
    admGen,             \* Admitted LeanContext / fingerprint generation (1..MaxSteps+1)
    mgrGen,             \* FileWorkerManager session-map generation (1..MaxSteps+1)
    ileanGen,           \* Lean4IleanIndex generation counter (1..2*MaxSteps+1)
    navPhase,           \* "Idle" | "AdmissionChecked" | "RouteBound" | "SessionEnsured" | "Requested" | "Served" | "Refused"
    navRouteKind,       \* "live" | "offline"
    navAdm,             \* admGen captured at CheckAdmission
    navMgrGen,          \* mgrGen captured at BindWarmRoute
    navIleanGen,        \* ileanGen captured at CheckAdmission (gateGeneration)
    navBoundarySeen,    \* TRUE if context/session/index changed while request was in flight
    spawnedBeforeGate,  \* TRUE if ensureSession/spawn ran before admission or on invalid context
    survPhase,          \* "Idle" | "Served" | "Refused"
    survDropped         \* TRUE if a valid current-context survivor request was falsely refused

vars == <<admValid, admGen, mgrGen, ileanGen,
          navPhase, navRouteKind, navAdm, navMgrGen, navIleanGen,
          navBoundarySeen, spawnedBeforeGate, survPhase, survDropped>>

Init ==
    /\ admValid \in {TRUE, FALSE}
    /\ admGen = 1
    /\ mgrGen = 1
    /\ ileanGen = 1
    /\ navPhase = "Idle"
    /\ navRouteKind \in {"live", "offline"}
    /\ navAdm = 1
    /\ navMgrGen = 1
    /\ navIleanGen = 1
    /\ navBoundarySeen = FALSE
    /\ spawnedBeforeGate = FALSE
    /\ survPhase = "Idle"
    /\ survDropped = FALSE

\* Step 1-3 of P1 gate: validate args, resolve mode, assertAdmissionCurrent. Zero spawn side effects.
CheckAdmission ==
    /\ navPhase = "Idle"
    /\ IF admValid
         THEN /\ navPhase' = "AdmissionChecked"
              /\ navAdm' = admGen
              /\ navIleanGen' = ileanGen
              /\ navBoundarySeen' = FALSE
         ELSE /\ navPhase' = "Refused"
              /\ UNCHANGED <<navAdm, navIleanGen, navBoundarySeen>>
    /\ UNCHANGED <<admValid, admGen, mgrGen, ileanGen, navRouteKind,
                   navMgrGen, spawnedBeforeGate, survPhase, survDropped>>

\* P1 mutant transition: ensureSession/broker/lock/analyzer runs from Idle before admission verdict.
MutSpawnBeforeAdmission ==
    /\ ~NavGateBeforeSpawn
    /\ navPhase = "Idle"
    /\ navPhase' = "SessionEnsured"
    /\ spawnedBeforeGate' = TRUE
    /\ navAdm' = admGen
    /\ navMgrGen' = mgrGen
    /\ navIleanGen' = ileanGen
    /\ navBoundarySeen' = FALSE
    /\ UNCHANGED <<admValid, admGen, mgrGen, ileanGen, navRouteKind, survPhase, survDropped>>

\* Step 4 of P1 gate: bind warm route against current session/environment fingerprint.
BindWarmRoute ==
    /\ navPhase = "AdmissionChecked"
    /\ IF admValid /\ navAdm = admGen
         THEN /\ navPhase' = "RouteBound"
              /\ navMgrGen' = mgrGen
         ELSE /\ navPhase' = "Refused"
              /\ UNCHANGED navMgrGen
    /\ UNCHANGED <<admValid, admGen, mgrGen, ileanGen, navRouteKind,
                   navAdm, navIleanGen, navBoundarySeen, spawnedBeforeGate, survPhase, survDropped>>

\* Step 5 of P1 gate: ensureSession (live route) or offline index preparation (offline route).
EnsureSession ==
    /\ navPhase = "RouteBound"
    /\ IF admValid /\ navAdm = admGen /\ navMgrGen = mgrGen
         THEN navPhase' = "SessionEnsured"
         ELSE navPhase' = "Refused"
    /\ UNCHANGED <<admValid, admGen, mgrGen, ileanGen, navRouteKind,
                   navAdm, navMgrGen, navIleanGen, navBoundarySeen,
                   spawnedBeforeGate, survPhase, survDropped>>

\* Dispatch LSP sendRequest or offline .ilean lookup.
SendRequest ==
    /\ navPhase = "SessionEnsured"
    /\ navPhase' = "Requested"
    /\ UNCHANGED <<admValid, admGen, mgrGen, ileanGen, navRouteKind,
                   navAdm, navMgrGen, navIleanGen, navBoundarySeen,
                   spawnedBeforeGate, survPhase, survDropped>>

\* Host mutates compiler binary / lake-manifest or calls setLeanContext mid-flight.
ReAdmitContext ==
    /\ admGen <= MaxSteps
    /\ admGen' = admGen + 1
    /\ mgrGen' = IF mgrGen <= MaxSteps THEN mgrGen + 1 ELSE mgrGen
    /\ ileanGen' = ileanGen + 1
    /\ admValid' \in {TRUE, FALSE}
    /\ navBoundarySeen' = IF navPhase \in {"AdmissionChecked", "RouteBound", "SessionEnsured", "Requested"}
                            THEN TRUE
                            ELSE navBoundarySeen
    /\ UNCHANGED <<navPhase, navRouteKind, navAdm, navMgrGen, navIleanGen,
                   spawnedBeforeGate, survPhase, survDropped>>

\* Whole-manager session reset / dispose: retires live sessions and (when NavBeforeReset) bumps ileanGen.
ManagerReset ==
    /\ mgrGen <= MaxSteps
    /\ mgrGen' = mgrGen + 1
    /\ ileanGen' = IF NavBeforeReset THEN ileanGen + 1 ELSE ileanGen
    /\ navBoundarySeen' = IF navPhase \in {"AdmissionChecked", "RouteBound", "SessionEnsured", "Requested"}
                            THEN TRUE
                            ELSE navBoundarySeen
    /\ UNCHANGED <<admValid, admGen, navPhase, navRouteKind,
                   navAdm, navMgrGen, navIleanGen,
                   spawnedBeforeGate, survPhase, survDropped>>

\* Complete in-flight request: live route checks session identity + admission; offline route checks ileanGen + admission.
ResolveRequest ==
    /\ navPhase = "Requested"
    /\ LET effAdm      == IF NavEntryCapture THEN navAdm ELSE admGen
           effMgrGen   == IF NavEntryCapture THEN navMgrGen ELSE mgrGen
           effIleanGen == IF NavEntryCapture THEN navIleanGen ELSE ileanGen
           routeCurrent == IF navRouteKind = "live"
                             THEN (effMgrGen = mgrGen /\ effIleanGen = ileanGen)
                             ELSE (effIleanGen = ileanGen)
           isCurrent   == admValid /\ (effAdm = admGen) /\ routeCurrent
       IN IF isCurrent
            THEN navPhase' = "Served"
            ELSE navPhase' = "Refused"
    /\ UNCHANGED <<admValid, admGen, mgrGen, ileanGen, navRouteKind,
                   navAdm, navMgrGen, navIleanGen, navBoundarySeen,
                   spawnedBeforeGate, survPhase, survDropped>>

\* A fresh navigation started in a valid current context with no intervening reset must serve.
SurvivorNavigate ==
    /\ survPhase = "Idle"
    /\ admValid
    /\ IF NavNoDropSurvivor
         THEN /\ survPhase' = "Served"
              /\ survDropped' = FALSE
         ELSE /\ survPhase' = "Refused"
              /\ survDropped' = TRUE
    /\ UNCHANGED <<admValid, admGen, mgrGen, ileanGen,
                   navPhase, navRouteKind, navAdm, navMgrGen, navIleanGen,
                   navBoundarySeen, spawnedBeforeGate>>

Next ==
    \/ CheckAdmission
    \/ MutSpawnBeforeAdmission
    \/ BindWarmRoute
    \/ EnsureSession
    \/ SendRequest
    \/ ReAdmitContext
    \/ ManagerReset
    \/ ResolveRequest
    \/ SurvivorNavigate

Spec == Init /\ [][Next]_vars

(* Invariant 1: No process spawn, broker attach, lock probe, or analyzer selection
   occurs before the admission gate succeeds. *)
NoSpawnBeforeAdmission ==
    ~spawnedBeforeGate

(* Invariant 2: An in-flight live or offline navigation across a context change or
   manager reset never serves stale results; it refuses with context-changed. *)
NoStaleNavigationServe ==
    ~(navBoundarySeen /\ navPhase = "Served")

(* Invariant 3: A valid current-context survivor navigation with no intervening
   boundary is never falsely refused. *)
NoDropSurvivorNavigation ==
    ~survDropped
=============================================================================
