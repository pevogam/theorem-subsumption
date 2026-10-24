import Lean

open Lean Meta Elab

namespace TheoremSubsumption

inductive BinderRole where
  | sharedInput | requirement | witness | instanceRequirement
  deriving BEq, Repr, Inhabited

inductive ProofStatus where
  | proved | refuted | unknown
  deriving BEq, Repr, Inhabited

def ProofStatus.label : ProofStatus → String
  | .proved => "PROVED"
  | .refuted => "REFUTED"
  | .unknown => "UNKNOWN"

inductive ComparisonMode where
  | all | logical | contextual
  deriving BEq, Repr, Inhabited

structure Config where
  roles1 : Array BinderRole := #[]
  roles2 : Array BinderRole := #[]
  mode : ComparisonMode := .all
  heartbeat : Nat := 200000
  facts : Array Name := #[]
  verbose : Bool := false
  json : Bool := false
  deriving Inhabited

structure Attempt where
  status : ProofStatus := .unknown
  obligation : String := ""
  certificate? : Option Name := none
  dependencies : Array Name := #[]
  axioms : Array Name := #[]
  trace : String := "not attempted"
  wellFormed : Bool := true
  usesSourceResult : Bool := false
  usesTargetDecl : Bool := false
  deriving Inhabited

structure ComparisonReport where
  source : Name
  target : Name
  config : Config
  alignment : Array String := #[]
  roles : Array String := #[]
  diagnostic : String := ""
  req_2_to_1 : Attempt := {}
  req_1_to_2 : Attempt := {}
  guarantee_1_to_2 : Attempt := {}
  guarantee_2_to_1 : Attempt := {}
  contextual_1_to_2 : Attempt := {}
  contextual_2_to_1 : Attempt := {}
  adapter_1_to_2 : Attempt := {}
  adapter_2_to_1 : Attempt := {}
  deriving Inhabited

/-- All dependencies, including those hidden behind intermediate lemmas and definitions. -/
partial def dependencies (env : Environment) (roots : Array Name) : Array Name := Id.run do
  let env := env.setExporting false
  let mut seen : NameSet := {}
  let mut todo := roots.toList
  while let name :: rest := todo do
    todo := rest
    if seen.contains name then continue
    seen := seen.insert name
    if let some info := env.find? name then
      todo := info.getUsedConstantsAsSet.toList ++ todo
  return seen.toArray.qsort Name.lt

private def background : String :=
  "local assumptions and explicit facts; definitional equality; global typeclass instances; trivial; omega; grind only"

private def propositionText (e : Expr) : MetaM String := do
  let e ← Core.betaReduce (← instantiateMVars e)
  withOptions (fun opts => pp.funBinderTypes.set opts true) do
    return (← ppExpr e).pretty

private def proofSearch (goal : Expr) (cfg : Config) : TermElabM (Option Expr) := do
  let saved ← saveState
  try
    let mvar ← mkFreshExprSyntheticOpaqueMVar goal
    let remaining ← Tactic.run mvar.mvarId! do
      Tactic.evalTactic (← `(tactic| intros))
      for name in cfg.facts do
        Tactic.evalTactic (← `(tactic| have := @$(mkIdent name)))
      Tactic.evalTactic (← `(tactic| first | assumption | rfl | trivial | omega | grind only))
    let proof ← instantiateMVars mvar
    if !remaining.isEmpty || proof.hasMVar then
      saved.restore
      return none
    return some proof
  catch _ =>
    saved.restore
    return none

private def findTerm (type : Expr) (bi : BinderInfo) (cfg : Config) : TermElabM (Option Expr) := do
  for localDecl in ← getLCtx do
    if localDecl.isImplementationDetail then continue
    if ← isDefEq localDecl.type type then return some localDecl.toExpr
  if bi == .instImplicit then
    if let some inst ← synthInstance? type then return some inst
  if ← isProp type then return ← proofSearch type cfg
  return none

/-- A dependent requirement bundle stays in Prop, including data-valued witnesses. -/
private partial def requirementBundle (type : Expr) : MetaM Expr := do
  if let .forallE n domain body bi := type then
    return ← withLocalDecl n bi domain fun x => do
      let rest ← requirementBundle (body.instantiate1 x)
      mkAppM ``Exists #[← mkLambdaFVars #[x] rest]
  return mkConst ``True

private def certify (goal proof : Expr) (forbidden : Array Name)
    (trace : String) (usesSource := false) : TermElabM Attempt := do
  let obligation ← propositionText goal
  let env ← getEnv
  try
    check proof
    unless ← isDefEq (← inferType proof) goal do throwError "certificate type mismatch"
    let proof ← Term.levelMVarToParam (← instantiateMVars proof)
    let goal ← instantiateMVars goal
    if proof.hasMVar || proof.hasFVar || proof.hasLooseBVars || proof.hasLevelMVar ||
        goal.hasMVar || goal.hasFVar || goal.hasLooseBVars || goal.hasLevelMVar then
      throwError "certificate is not closed"
    unless ← isDefEq (← inferType proof) goal do throwError "certificate type mismatch"
    let deps := dependencies (← getEnv) (proof.getUsedConstants ++ goal.getUsedConstants)
    if deps.contains ``sorryAx then throwError "certificate depends on sorryAx"
    for name in forbidden do
      if deps.contains name then throwError "forbidden dependency: {name}"
    let certificatePrefix := (← getMainModule) ++ `subsumptionCertificate
    let mut index := 1
    let mut name := certificatePrefix.appendIndexAfter index
    while (← getEnv).contains name do
      index := index + 1
      name := certificatePrefix.appendIndexAfter index
    let levels := (collectLevelParams {} goal |>.collect proof).params.toList
    -- Disable asynchronous checking: PROVED is returned only after kernel acceptance.
    withOptions (fun opts => Elab.async.set opts false) do
      addDecl <| .thmDecl { name, levelParams := levels, type := goal, value := proof }
    return {
      status := .proved
      obligation := ← propositionText goal
      certificate? := some name
      dependencies := deps
      axioms := ← collectAxioms name
      trace
      usesSourceResult := usesSource
    }
  catch ex =>
    setEnv env
    return { obligation, trace := s!"certificate rejected: {← ex.toMessageData.toString}" }

private def candidates (type : Expr) : MetaM (Array Expr) := do
  if ← isDefEq type (mkConst ``Nat) then
    return #[0, 1, 2, 10, 11].map mkNatLit
  if ← isDefEq type (mkConst ``Int) then
    let positives ← #[0, 1, 2, 10, 11].mapM fun n => mkAppM ``Int.ofNat #[mkNatLit n]
    return positives ++ #[← mkAppM ``Int.neg #[← mkAppM ``Int.ofNat #[mkNatLit 1]]]
  if ← isDefEq type (mkConst ``Bool) then return #[mkConst ``Bool.false, mkConst ``Bool.true]
  if type == mkSort 0 then return #[mkConst ``False, mkConst ``True]
  return #[]

/-- Instantiate at most 64 concrete shared-input tuples, then ask for a contradiction. -/
private partial def refuteAt (hyp type : Expr) (remaining : Nat) (cfg : Config)
    (fuel : Nat) : TermElabM (Option Expr × Nat) := do
  if fuel == 0 then return (none, 0)
  if remaining == 0 then
    let result ← withLetDecl `counterexample type hyp fun fact => do
      let proof? ← proofSearch (mkConst ``False) cfg
      proof?.mapM fun proof => mkLetFVars #[fact] proof
    return (result, fuel - 1)
  if let .forallE _ domain body _ := type then
    let mut fuel := fuel
    for value in ← candidates domain do
      let (result, nextFuel) ← refuteAt (mkApp hyp value) (body.instantiate1 value)
        (remaining - 1) cfg fuel
      fuel := nextFuel
      if result.isSome then return (result, fuel)
  return (none, fuel)

private def usesLastInput (type proof : Expr) : MetaM Bool :=
  forallTelescope type fun xs _ => do
    let body ← Core.betaReduce (mkAppN proof xs)
    return xs.back?.any (fun x => body.containsFVar x.fvarId!)

private def attempt (goal : Expr) (sharedCount : Nat) (cfg : Config)
    (forbidden : Array Name) (candidate? : Option Expr := none)
    (trackSource := false) : TermElabM Attempt :=
  withOptions (fun opts => maxHeartbeats.set opts cfg.heartbeat) <| withCurrHeartbeats do
    let mut trace := "bounded search did not certify the obligation or its negation"
    try
      if let some proof ← (if candidate?.isSome then pure candidate? else proofSearch goal cfg) then
        let result ← certify goal proof forbidden "constructive transport / local, omega, grind-only portfolio"
        if result.status == .proved then
          let usesSource ← if trackSource then usesLastInput goal proof else pure false
          return { result with usesSourceResult := usesSource }
        trace := result.trace
      let negGoal := mkApp (mkConst ``Not) goal
      if let some proof ← proofSearch negGoal cfg then
        let result ← certify negGoal proof forbidden "negated obligation: local / omega / grind-only"
        if result.status == .proved then
          return { result with status := .refuted, obligation := ← propositionText goal }
        trace := result.trace
      let proof? ← withLocalDeclD `relation goal fun h => do
        let (some contradiction, _) ← refuteAt h goal sharedCount cfg 64 | return none
        return some (← mkLambdaFVars #[h] contradiction)
      if let some proof := proof? then
        let result ← certify negGoal proof forbidden "negated obligation: concrete shared-input witness"
        if result.status == .proved then
          return { result with status := .refuted, obligation := ← propositionText goal }
        trace := result.trace
    catch ex =>
      trace := s!"search exhausted or unsupported: {← ex.toMessageData.toString}"
    return { obligation := ← propositionText goal, trace }

private def roleLabel : BinderRole → String
  | .sharedInput => "sharedInput"
  | .requirement => "requirement"
  | .witness => "witness"
  | .instanceRequirement => "instanceRequirement"

private def classify (type : Expr) (overrides : Array BinderRole) : MetaM (Array BinderRole × Array String) :=
  forallTelescope type fun xs _ => do
    if !overrides.isEmpty && overrides.size != xs.size then
      throwError "role override count {overrides.size} does not match binder count {xs.size}"
    let mut roles := #[]
    let mut labels := #[]
    for i in [:xs.size] do
      let decl ← xs[i]!.fvarId!.getDecl
      let role ← if let some role := overrides[i]? then pure role else
        if decl.binderInfo == .instImplicit then pure .instanceRequirement else
        if ← isProp decl.type then pure .requirement else pure .sharedInput
      roles := roles.push role
      labels := labels.push s!"{decl.userName}={roleLabel role} : {(← ppExpr decl.type).pretty}"
    return (roles, labels)

private def applyRoles (type : Expr) (roles : Array BinderRole) : Expr :=
  go type roles.toList
where
  go (type : Expr) (roles : List BinderRole) : Expr :=
    match type, roles with
    | .forallE n domain body bi, role :: rest =>
      .forallE n domain (go body rest) (if role == .instanceRequirement then .instImplicit else bi)
    | _, _ => type

private partial def align (left right : Expr) (count : Nat)
    (shared : Array Expr) (labels : Array String)
    (k : Array Expr → Array String → Expr → Expr → TermElabM ComparisonReport) :
    TermElabM ComparisonReport := do
  if count == 0 then return ← k shared labels left right
  let .forallE n domain body bi := left | throwError "missing source shared input"
  let .forallE m domain' body' _ := right | throwError "missing target shared input"
  unless ← isDefEq domain domain' do
    throwError "shared input types differ: {domain} versus {domain'}"
  withLocalDecl n bi domain fun x => do
    align (body.instantiate1 x) (body'.instantiate1 x) (count - 1)
      (shared.push x) (labels.push s!"{n} <-> {m} : {(← ppExpr domain).pretty}") k

private def guaranteeGoal (shared : Array Expr) (left right : Expr) : MetaM (Option Expr) :=
  forallTelescope left fun req1 c1 => forallTelescope right fun req2 c2 => do
    let usesRequirement := (req1 ++ req2).any fun x =>
      c1.containsFVar x.fvarId! || c2.containsFVar x.fvarId!
    if usesRequirement then return none
    return some (← mkForallFVars shared (← mkArrow c1 c2))

private structure Transport where
  bundle : Expr
  sourceResult : Expr
  contextualType? : Option Expr := none
  contextual? : Option Expr := none

/-- Construct requirements in dependency order, keeping earlier witnesses available. -/
private partial def transport (sourceType targetConclusion source : Expr)
    (args : Array Expr) (cfg : Config) : TermElabM (Option Transport) := do
  if let .forallE n domain body bi := sourceType then
    let some witness ← findTerm domain bi cfg | return none
    return ← withLocalDecl n bi domain fun x => do
      let some rest ← transport (body.instantiate1 x) targetConclusion source (args.push x) cfg
        | return none
      let predicate ← mkLambdaFVars #[x] (← requirementBundle (body.instantiate1 x))
      let applyWitness := fun e => do pure <| mkApp (← mkLambdaFVars #[x] e) witness
      let restProof ← applyWitness rest.bundle
      let bundle ← mkAppOptM ``Exists.intro #[none, some predicate, some witness, some restProof]
      return some {
        bundle
        sourceResult := ← applyWitness rest.sourceResult
        contextualType? := ← rest.contextualType?.mapM applyWitness
        contextual? := ← rest.contextual?.mapM applyWitness
      }
  let sourceResult := mkAppN source args
  if cfg.mode == .logical then return some { bundle := mkConst ``True.intro, sourceResult }
  let contextType ← mkArrow sourceType targetConclusion
  let proof? ← proofSearch contextType cfg
  return some {
    bundle := mkConst ``True.intro
    sourceResult
    contextualType? := some contextType
    contextual? := proof?
  }

private def compareDirection (shared : Array Expr) (sourceType targetType source : Expr)
    (sourceName targetName : Name) (cfg : Config) : TermElabM (Attempt × Attempt × Attempt) := do
  let (reqGoal, transport?, contextGoal?) ← forallTelescope targetType fun targetReqs conclusion => do
    let reqGoal ← mkForallFVars (shared ++ targetReqs) (← requirementBundle sourceType)
    let result? ← withOptions (fun opts => maxHeartbeats.set opts cfg.heartbeat) <| withCurrHeartbeats do
      try transport sourceType conclusion source shared cfg
      catch _ => pure none
    let result? ← result?.mapM fun result => do
      return { result with
        bundle := ← mkLambdaFVars (shared ++ targetReqs) result.bundle
        sourceResult := ← mkLambdaFVars (shared ++ targetReqs) result.sourceResult
        contextualType? := ← result.contextualType?.mapM (fun e => mkForallFVars (shared ++ targetReqs) e)
        contextual? := ← result.contextual?.mapM (fun e => mkLambdaFVars (shared ++ targetReqs) e)
      }
    let contextGoal? := result?.bind (·.contextualType?)
    return (reqGoal, result?, contextGoal?)
  let req ← attempt reqGoal shared.size cfg #[sourceName, targetName] (transport?.map (·.bundle))
  if req.status != .proved || cfg.mode == .logical then return (req, {}, {})
  let some result := transport? | return (req, {}, {})
  let some contextGoal := contextGoal? | return (req, {}, {})
  let context ← attempt contextGoal shared.size cfg #[sourceName, targetName] result.contextual? true
  if context.status != .proved then return (req, context, {})
  let some contextName := context.certificate? | return (req, context, {})
  let adapterProof ← forallTelescope targetType fun reqs _ => do
    let inputs := shared ++ reqs
    let contextExpr ← mkAppOptM contextName (inputs.map some)
    let proof := mkApp contextExpr (mkAppN result.sourceResult inputs)
    mkLambdaFVars inputs proof
  let adapter ← certify (← inferType adapterProof) adapterProof #[targetName]
    "composition of constructed requirements, source theorem, and contextual guarantee" context.usesSourceResult
  return (req, context, adapter)

/-- Compare closed theorem declarations. Ambiguous/unsupported alignments stay UNKNOWN. -/
def compareTheorems (source target : Name) (cfg : Config := {}) : TermElabM ComparisonReport := do
  if cfg.heartbeat == 0 then throwError "heartbeat must be positive (zero disables Lean's limit)"
  let sourceInfo ← getConstInfo source
  let targetInfo ← getConstInfo target
  unless sourceInfo matches .thmInfo _ do throwError "source must be a theorem declaration"
  unless targetInfo matches .thmInfo _ do throwError "target must be a theorem declaration"
  let sourceExpr ← mkConstWithFreshMVarLevels source
  let targetExpr ← mkConstWithFreshMVarLevels target
  let sourceType ← inferType sourceExpr
  let targetType ← inferType targetExpr
  let (roles1, labels1) ← classify sourceType cfg.roles1
  let (roles2, labels2) ← classify targetType cfg.roles2
  let report : ComparisonReport := {
    source
    target
    config := cfg
    roles := (labels1.map (s!"source: {·}")) ++ (labels2.map (s!"target: {·}"))
  }
  let prefix1 := roles1.takeWhile (· == .sharedInput) |>.size
  let prefix2 := roles2.takeWhile (· == .sharedInput) |>.size
  if prefix1 != prefix2 || (roles1.extract prefix1 roles1.size).contains .sharedInput ||
      (roles2.extract prefix2 roles2.size).contains .sharedInput then
    return { report with diagnostic := "ambiguous shared-input prefix; provide explicit role overrides" }
  try
    align (applyRoles sourceType roles1) (applyRoles targetType roles2) prefix1 #[] #[] fun shared labels left right => do
      let (req21, ctx12, adapter12) ← compareDirection shared left right sourceExpr source target cfg
      let (req12, ctx21, adapter21) ← compareDirection shared right left targetExpr target source cfg
      let mut g12 : Attempt := { trace := "logical mode disabled" }
      let mut g21 : Attempt := g12
      if cfg.mode != .contextual then
        if let some goal ← guaranteeGoal shared left right then
          g12 ← attempt goal shared.size cfg #[source, target] (trackSource := true)
        else
          g12 := { wellFormed := false, trace := "NOT-WELL-FORMED: guarantee depends on requirement binders" }
        if let some goal ← guaranteeGoal shared right left then
          g21 ← attempt goal shared.size cfg #[source, target] (trackSource := true)
        else
          g21 := { wellFormed := false, trace := "NOT-WELL-FORMED: guarantee depends on requirement binders" }
      return { report with
        alignment := labels
        req_2_to_1 := req21
        req_1_to_2 := req12
        guarantee_1_to_2 := g12
        guarantee_2_to_1 := g21
        contextual_1_to_2 := ctx12
        contextual_2_to_1 := ctx21
        adapter_1_to_2 := adapter12
        adapter_2_to_1 := adapter21
      }
  catch ex =>
    return { report with diagnostic := s!"UNKNOWN: {← ex.toMessageData.toString}" }

def ComparisonReport.classification (r : ComparisonReport) : String := Id.run do
  if r.config.mode == .contextual then return "contextual mode; component-wise classification disabled"
  let forward := r.req_2_to_1.status == .proved && r.guarantee_1_to_2.status == .proved
  let reverse := r.req_1_to_2.status == .proved && r.guarantee_2_to_1.status == .proved
  let forwardRefuted := r.req_2_to_1.status == .refuted || r.guarantee_1_to_2.status == .refuted
  let reverseRefuted := r.req_1_to_2.status == .refuted || r.guarantee_2_to_1.status == .refuted
  if forward && reverse then return "equivalent under this alignment"
  if forward && reverseRefuted then return "source strictly subsumes target under this alignment"
  if reverse && forwardRefuted then return "target strictly subsumes source under this alignment"
  if forward then return "source subsumes target; strictness unknown"
  if reverse then return "target subsumes source; strictness unknown"
  if forwardRefuted && reverseRefuted then return "incomparable under this alignment"
  return "UNKNOWN"

private def strings (xs : Array Name) : Json := Lean.toJson (xs.map toString)

def Attempt.toJson (a : Attempt) : Json := Json.mkObj [
  ("status", Lean.toJson a.status.label), ("obligation", Lean.toJson a.obligation),
  ("certificate", Lean.toJson (a.certificate?.map toString)),
  ("certificationLevel", if a.certificate?.isSome then Lean.toJson "theoremLevel" else Json.null),
  ("closedKernelChecked", Lean.toJson a.certificate?.isSome),
  ("dependencies", strings a.dependencies), ("axioms", strings a.axioms),
  ("trace", Lean.toJson a.trace), ("wellFormed", Lean.toJson a.wellFormed),
  ("usesSourceResult", Lean.toJson a.usesSourceResult), ("usesTargetDecl", Lean.toJson a.usesTargetDecl)]

def ComparisonReport.toJson (r : ComparisonReport) : Json := Json.mkObj [
  ("schemaVersion", Lean.toJson (1 : Nat)), ("toolVersion", Lean.toJson "0.1.0"),
  ("leanVersion", Lean.toJson Lean.versionString),
  ("source", Lean.toJson r.source.toString), ("target", Lean.toJson r.target.toString),
  ("alignmentPolicy", Lean.toJson "positional shared-input prefix; definitional equality"),
  ("alignment", Lean.toJson r.alignment), ("roles", Lean.toJson r.roles),
  ("background", Lean.toJson background), ("explicitFacts", strings r.config.facts),
  ("heartbeatPerAttempt", Lean.toJson r.config.heartbeat),
  ("diagnostic", Lean.toJson r.diagnostic), ("classification", Lean.toJson r.classification),
  ("requirementsTargetToSource", r.req_2_to_1.toJson),
  ("requirementsSourceToTarget", r.req_1_to_2.toJson),
  ("guaranteeSourceToTarget", r.guarantee_1_to_2.toJson),
  ("guaranteeTargetToSource", r.guarantee_2_to_1.toJson),
  ("contextualSourceToTarget", r.contextual_1_to_2.toJson),
  ("contextualTargetToSource", r.contextual_2_to_1.toJson),
  ("adapterSourceToTarget", r.adapter_1_to_2.toJson),
  ("adapterTargetToSource", r.adapter_2_to_1.toJson),
  ("semanticComparisons", Lean.toJson (#[] : Array Json))]

def ComparisonReport.format (r : ComparisonReport) : String := Id.run do
  let mut lines := #[s!"{r.source} vs {r.target}", "ALIGNMENT (positional)"] ++ r.alignment ++ r.roles
  lines := lines.push s!"BACKGROUND: {background}; explicit facts: {r.config.facts}"
  if !r.diagnostic.isEmpty then lines := lines.push r.diagnostic
  for (label, edge) in #[
      ("requirements target => source", r.req_2_to_1),
      ("requirements source => target", r.req_1_to_2),
      ("context-free guarantee source => target", r.guarantee_1_to_2),
      ("context-free guarantee target => source", r.guarantee_2_to_1),
      ("contextual source => target", r.contextual_1_to_2),
      ("contextual target => source", r.contextual_2_to_1),
      ("derived adapter source => target", r.adapter_1_to_2),
      ("derived adapter target => source", r.adapter_2_to_1)] do
    lines := lines.push s!"{label}: {if edge.wellFormed then edge.status.label else "NOT-WELL-FORMED"}"
    if !edge.obligation.isEmpty then lines := lines.push s!"  obligation: {edge.obligation}"
    if let some name := edge.certificate? then
      lines := lines.push s!"  certificate: {name} (closed / kernel checked)"
      lines := lines.push s!"  dependencies: {edge.dependencies.size} declarations; axioms: {edge.axioms}"
      if r.config.verbose then lines := lines.push s!"  dependencies: {edge.dependencies}"
    if r.config.verbose then
      lines := lines.push s!"  {edge.trace}; uses source result: {edge.usesSourceResult}; uses target declaration: {edge.usesTargetDecl}"
  lines := lines.push s!"COMPONENT-WISE RESULT: {r.classification}"
  return String.intercalate "\n" lines.toList

declare_syntax_cat comparisonOption
syntax "(roles1" " := " "[" ident,* "]" ")" : comparisonOption
syntax "(roles2" " := " "[" ident,* "]" ")" : comparisonOption
syntax "(mode" " := " "." ident ")" : comparisonOption
syntax "(alignment" " := " "." ident ")" : comparisonOption
syntax "(heartbeat" " := " num ")" : comparisonOption
syntax "(using" " := " "[" ident,* "]" ")" : comparisonOption
syntax "(verbose" " := " ident ")" : comparisonOption
syntax "(json" " := " ident ")" : comparisonOption
syntax (name := compareCommand) "#compare_theorems " ident ident comparisonOption* : command

private def parseRole (stx : TSyntax `ident) : Command.CommandElabM BinderRole := do
  match stx.getId with
  | `sharedInput => return .sharedInput
  | `requirement => return .requirement
  | `witness => return .witness
  | `instanceRequirement => return .instanceRequirement
  | _ => throwErrorAt stx "expected sharedInput, requirement, witness, or instanceRequirement"

private def parseBool (stx : TSyntax `ident) : Command.CommandElabM Bool := do
  match stx.getId with
  | `true => return true
  | `false => return false
  | _ => throwErrorAt stx "expected true or false"

@[command_elab compareCommand] def elabCompare : Command.CommandElab := fun stx => do
  let `(#compare_theorems $left:ident $right:ident $options:comparisonOption*) := stx
    | throwUnsupportedSyntax
  let mut cfg : Config := {}
  for option in options do
    match option with
    | `(comparisonOption| (roles1 := [$roles:ident,*])) =>
      cfg := { cfg with roles1 := ← roles.getElems.mapM parseRole }
    | `(comparisonOption| (roles2 := [$roles:ident,*])) =>
      cfg := { cfg with roles2 := ← roles.getElems.mapM parseRole }
    | `(comparisonOption| (heartbeat := $n:num)) => cfg := { cfg with heartbeat := n.getNat }
    | `(comparisonOption| (using := [$facts,*])) =>
      cfg := { cfg with facts := ← facts.getElems.mapM fun fact => Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo fact }
    | `(comparisonOption| (verbose := $b:ident)) => cfg := { cfg with verbose := ← parseBool b }
    | `(comparisonOption| (json := $b:ident)) => cfg := { cfg with json := ← parseBool b }
    | `(comparisonOption| (alignment := .$mode:ident)) =>
      unless mode.getId == `positional do throwErrorAt mode "MVP supports positional alignment"
    | `(comparisonOption| (mode := .$mode:ident)) =>
      let mode ← match mode.getId with
        | `all => pure ComparisonMode.all
        | `logical => pure ComparisonMode.logical
        | `contextual => pure ComparisonMode.contextual
        | _ => throwErrorAt mode "expected all, logical, or contextual"
      cfg := { cfg with mode }
    | _ => throwUnsupportedSyntax
  let left ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo left
  let right ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo right
  let report ← Command.liftTermElabM <| compareTheorems left right cfg
  logInfo <| if cfg.json then report.toJson.compress else report.format

end TheoremSubsumption
