import Examples

open Lean Meta Elab TheoremSubsumption

namespace Tests

theorem tighter (x : Int) (h : x > 0) : x ≥ 1 := by omega
theorem looser (x : Int) (h : x > 10) : x ≥ 0 := by omega
theorem renamed (y : Int) (positive : y > 0) : y ≥ 1 := by omega

private def expect (condition : Bool) (message : String) : TermElabM Unit := do
  unless condition do throwError message

private def checkCertificates (r : ComparisonReport) : TermElabM Unit := do
  for edge in #[r.req_2_to_1, r.req_1_to_2, r.guarantee_1_to_2, r.guarantee_2_to_1,
      r.contextual_1_to_2, r.contextual_2_to_1, r.adapter_1_to_2, r.adapter_2_to_1] do
    if edge.status == .unknown then
      expect edge.certificate?.isNone "UNKNOWN edge has a certificate"
      continue
    let some cert := edge.certificate? | throwError "settled edge lacks a certificate"
    let .thmInfo info ← getConstInfo cert | throwError "certificate is not a theorem"
    expect (!info.value.hasMVar && !info.value.hasFVar && !info.value.hasLooseBVars)
      "certificate is not closed"
    checkWithKernel info.value
    let deps := dependencies (← getEnv) #[cert]
    expect (!deps.contains ``sorryAx) "certificate depends on sorryAx"
    expect (!edge.usesTargetDecl) "certificate uses target declaration"

run_cmd Command.liftTermElabM do
  let r ← compareTheorems ``tighter ``looser
  unless r.classification == "source strictly subsumes target under this alignment" do
    throwError "arithmetic comparison failed:\n{r.format}"
  expect (r.req_2_to_1.status == .proved) "forward requirements"
  expect (r.req_1_to_2.status == .refuted) "reverse requirements need a certified refutation"
  expect (r.guarantee_1_to_2.status == .proved) "forward guarantees"
  expect (r.guarantee_2_to_1.status == .refuted) "reverse guarantees need a certified refutation"
  expect (r.contextual_1_to_2.status == .proved && r.adapter_1_to_2.status == .proved)
    "derived contextual adapter"
  checkCertificates r
  let forward ← getConstInfo r.req_2_to_1.certificate?.get!
  let expectedForward ← Term.elabTerm (← `(∀ x : Int, x > 10 → ∃ h : x > 0, True)) none
  expect (← isDefEq forward.type expectedForward) "wrong forward requirement certificate type"
  let reverse ← getConstInfo r.req_1_to_2.certificate?.get!
  let expectedReverse ← Term.elabTerm (← `(¬ (∀ x : Int, x > 0 → ∃ h : x > 10, True))) none
  expect (← isDefEq reverse.type expectedReverse) "REFUTED certificate must prove negation"
  let .ok json := Json.parse r.toJson.compress | throwError "invalid report JSON"
  let .ok classification := json.getObjValAs? String "classification" | throwError "missing JSON classification"
  expect (classification == r.classification) "JSON classification disagrees with report"
  let equivalent ← compareTheorems ``tighter ``renamed
  expect (equivalent.classification == "equivalent under this alignment")
    "alpha-renaming must preserve the relation"
  checkCertificates equivalent

theorem negative (x : Int) (h : x < 0) : x ≤ -1 := by omega

run_cmd Command.liftTermElabM do
  let r ← compareTheorems ``tighter ``negative
  expect (r.classification == "incomparable under this alignment")
    s!"incomparability requires two refutations: {r.format}"
  checkCertificates r

opaque hidden : Int → Prop
theorem easy (x : Int) (_ : x > 0) : True := True.intro
theorem hard (x : Int) (_ : x > 0 ∧ hidden x) : True := True.intro

run_cmd Command.liftTermElabM do
  let r ← compareTheorems ``easy ``hard
  expect (r.req_1_to_2.status == .unknown) "an opaque predicate must preserve UNKNOWN"
  expect (r.classification == "source subsumes target; strictness unknown")
    s!"search failure is not strictness: {r.format}"
  checkCertificates r

theorem projection (P Q : Prop) (_ : P) (hQ : Q) : Q := hQ
theorem conjunction (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := ⟨hP, hQ⟩
theorem identity1 (P : Prop) (h : P) : P := h
theorem identity2 (Q : Prop) (h : Q) : Q := h

run_cmd Command.liftTermElabM do
  let r ← compareTheorems ``projection ``conjunction
  expect (r.guarantee_1_to_2.status == .refuted)
    s!"target requirements leaked into a context-free guarantee: {r.format}"
  expect (r.contextual_1_to_2.status == .proved && r.adapter_1_to_2.status == .proved)
    "the same guarantees should admit contextual adaptation"
  checkCertificates r
  let contextual ← compareTheorems ``projection ``conjunction { mode := .contextual }
  expect (contextual.guarantee_1_to_2.status == .unknown) "contextual mode ran logical comparison"
  expect (contextual.adapter_1_to_2.status == .proved) "contextual-only adapter"
  let logical ← compareTheorems ``projection ``conjunction { mode := .logical }
  expect (logical.contextual_1_to_2.status == .unknown) "logical mode ran contextual search"
  let identity ← compareTheorems ``identity1 ``identity2
  expect identity.guarantee_1_to_2.usesSourceResult "source-result use was not detected"

theorem witness1 (n : Nat) (_ : n = 0) : True := True.intro
theorem witness2 (m : Nat) (_ : m = 0) : True := True.intro

run_cmd Command.liftTermElabM do
  let roles := #[BinderRole.witness, .requirement]
  let r ← compareTheorems ``witness1 ``witness2 { roles1 := roles, roles2 := roles }
  expect (r.classification == "equivalent under this alignment")
    s!"dependent data-valued requirement transport failed: {r.format}"
  expect r.alignment.isEmpty "witness override should remove the shared input"
  checkCertificates r

class Base (α : Type u) where
  element : α

class Derived (α : Type u) extends Base α where
  mark : Bool

theorem baseResult (α : Type u) [Base α] : True := True.intro
theorem derivedResult (β : Type v) [Derived β] : True := True.intro
theorem dependent1 (α : Type u) [Base α] : (Base.element : α) = Base.element := rfl
theorem dependent2 (β : Type v) [Base β] : (Base.element : β) = Base.element := rfl
theorem explicitInstance (α : Type u) (_ : Base α) : True := True.intro

run_cmd Command.liftTermElabM do
  let r ← compareTheorems ``baseResult ``derivedResult
  expect (r.req_2_to_1.status == .proved) s!"parent instance transport failed: {r.format}"
  expect (r.req_1_to_2.status == .unknown) "missing data instance should be UNKNOWN"
  expect (r.adapter_1_to_2.status == .proved) "instance adapter failed"
  checkCertificates r
  let overrideInstance ← compareTheorems ``explicitInstance ``derivedResult {
    roles1 := #[.sharedInput, .instanceRequirement]
  }
  expect (overrideInstance.req_2_to_1.status == .proved)
    "instanceRequirement override must enable synthesis for an explicit binder"
  checkCertificates overrideInstance
  let dependent ← compareTheorems ``dependent1 ``dependent2 { verbose := true }
  expect (!dependent.guarantee_1_to_2.wellFormed)
    "a guarantee depending on a removed instance must be NOT-WELL-FORMED"
  expect (dependent.adapter_1_to_2.status == .proved)
    s!"dependent contextual adaptation failed: {dependent.format}"
  checkCertificates dependent

theorem poly1.{u} (α : Sort u) (x : α) : x = x := rfl
theorem poly2.{v} (β : Sort v) (y : β) : y = y := rfl
theorem natResult (n : Nat) : n = n := rfl

run_cmd Command.liftTermElabM do
  let poly ← compareTheorems ``poly1 ``poly2
  expect (poly.classification == "equivalent under this alignment")
    s!"universe-polymorphic alpha-renaming failed: {poly.format}"
  checkCertificates poly
  let mismatch ← compareTheorems ``tighter ``natResult
  expect (mismatch.classification == "UNKNOWN" && !mismatch.diagnostic.isEmpty)
    "mismatched positional types must be UNKNOWN"
  let imported ← compareTheorems ``Nat.add_comm ``Nat.add_comm { mode := .logical }
  expect (imported.classification == "equivalent under this alignment")
    s!"imported theorem comparison failed: {imported.format}"
  checkCertificates imported

theorem ambiguous1 (P : Prop) (_ : P) (n : Nat) : n = n := rfl
theorem ambiguous2 (Q : Prop) (_ : Q) (m : Nat) : m = m := rfl

run_cmd Command.liftTermElabM do
  let ambiguous ← compareTheorems ``ambiguous1 ``ambiguous2
  expect (ambiguous.classification == "UNKNOWN" && !ambiguous.diagnostic.isEmpty)
    "shared data after requirements must not be silently realigned"
  let roles := #[BinderRole.sharedInput, .requirement, .witness]
  let explicit ← compareTheorems ``ambiguous1 ``ambiguous2 { roles1 := roles, roles2 := roles }
  expect (explicit.req_2_to_1.status == .proved) "explicit roles did not resolve ambiguity"
  checkCertificates explicit

-- A known theorem can trivialize a component even through an intermediate lemma.
opaque secret : Prop
axiom secretProof : secret
theorem closedSource : True := True.intro
theorem closedTarget : secret := secretProof
theorem shortcut : secret := closedTarget

run_cmd Command.liftTermElabM do
  let baseline ← compareTheorems ``closedSource ``closedTarget
  expect (baseline.guarantee_1_to_2.status == .unknown)
    "unrestricted whole-theorem implication leaked into the classifier"
  let direct ← compareTheorems ``closedSource ``closedTarget { facts := #[``closedTarget] }
  expect (direct.guarantee_1_to_2.status == .unknown) "direct target declaration was accepted"
  let indirect ← compareTheorems ``closedSource ``closedTarget { facts := #[``shortcut] }
  expect (indirect.guarantee_1_to_2.status == .unknown) "transitive target declaration was accepted"
  let allowed ← compareTheorems ``closedSource ``closedTarget { facts := #[``secretProof], verbose := true }
  expect (allowed.guarantee_1_to_2.status == .proved) s!"explicit background fact was ignored: {allowed.format}"
  expect (allowed.guarantee_1_to_2.axioms.contains ``secretProof) "axiom dependency was not reported"
  checkCertificates allowed

-- A fabricated proof placeholder must never be promoted to a certificate.
set_option warningAsError false in
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem tainted : secret := by sorry

run_cmd Command.liftTermElabM do
  let r ← compareTheorems ``closedSource ``closedTarget { facts := #[``tainted] }
  expect (r.guarantee_1_to_2.status == .unknown) "sorryAx was accepted"
  let bounded ← compareTheorems ``easy ``hard { heartbeat := 1 }
  expect (bounded.req_1_to_2.status == .unknown) "budget exhaustion became a refutation"

#guard_msgs (drop info) in
#compare_theorems witness1 witness2
  (roles1 := [witness, requirement])
  (roles2 := [witness, requirement])
  (mode := .logical)
  (using := [])
  (verbose := true)
  (json := true)

/-- error: heartbeat must be positive (zero disables Lean's limit) -/
#guard_msgs in
#compare_theorems tighter looser (heartbeat := 0)

/-- error: role override count 1 does not match binder count 2 -/
#guard_msgs in
#compare_theorems tighter looser (roles1 := [sharedInput])

-- Phase 2: structural alignment must be unique before any relation is searched.
theorem mixed1 (n : Nat) (x : Int) (h : x > 0) : n = n ∧ x ≥ 1 := by omega
theorem mixed2 (y : Int) (m : Nat) (h : y > 10) : m = m ∧ y ≥ 0 := by omega

run_cmd Command.liftTermElabM do
  let positional ← compareTheorems ``mixed1 ``mixed2
  expect (positional.classification == "UNKNOWN") "positional mode silently reordered inputs"
  let structural ← compareTheorems ``mixed1 ``mixed2 { alignment := .structural }
  expect (structural.inputMap == #[2, 1]) s!"wrong structural map: {structural.format}"
  expect (structural.classification == "source strictly subsumes target under this alignment")
    s!"reordered arithmetic comparison failed: {structural.format}"
  checkCertificates structural
  let exhausted ← compareTheorems ``mixed1 ``mixed2 { alignment := .structural, maxAlignmentSteps := 1 }
  expect (exhausted.classification == "UNKNOWN" && exhausted.alignmentSearchSteps == 1)
    "exhausted alignment search must preserve UNKNOWN"

theorem twoNats1 (a b : Nat) : a + b = b + a := Nat.add_comm a b
theorem twoNats2 (c d : Nat) : c + d = d + c := Nat.add_comm c d
theorem dependentOrder1 (n _m : Nat) (i : Fin n) : i.val < n := i.isLt
theorem dependentOrder2 (_m n : Nat) (j : Fin n) : j.val < n := j.isLt

run_cmd Command.liftTermElabM do
  let ambiguous ← compareTheorems ``twoNats1 ``twoNats2 { alignment := .structural }
  expect (ambiguous.classification == "UNKNOWN" && ambiguous.diagnostic.startsWith "ambiguous")
    "same-type permutations must remain ambiguous even if their conclusions are provable"
  expect ambiguous.req_2_to_1.certificate?.isNone "ambiguous alignment emitted a certificate"
  let explicit ← compareTheorems ``twoNats1 ``twoNats2 { alignment := .explicit, mapping := #[2, 1] }
  expect (explicit.classification == "equivalent under this alignment") s!"explicit map failed: {explicit.format}"
  checkCertificates explicit
  let invalid ← compareTheorems ``twoNats1 ``twoNats2 { alignment := .explicit, mapping := #[1, 1] }
  expect (invalid.classification == "UNKNOWN") "non-bijective explicit map was accepted"
  let dependent ← compareTheorems ``dependentOrder1 ``dependentOrder2 { alignment := .structural }
  expect (dependent.inputMap == #[2, 1, 3]) s!"dependent matching did not backtrack: {dependent.format}"
  expect (dependent.classification == "equivalent under this alignment") "dependent alignment comparison"
  checkCertificates dependent

theorem interleaved1 (α : Type u) [Base α] (_f : α → α) : True := True.intro
theorem interleaved2 (β : Type v) (_g : β → β) [Derived β] : True := True.intro

class Dimension where
  size : Nat

theorem cannotMove1 [Dimension] (_i : Fin Dimension.size) : True := True.intro
theorem cannotMove2 [Dimension] (_j : Fin Dimension.size) : True := True.intro

run_cmd Command.liftTermElabM do
  let r ← compareTheorems ``interleaved1 ``interleaved2 { alignment := .structural }
  expect (r.req_2_to_1.status == .proved && r.adapter_1_to_2.status == .proved)
    s!"interleaved instance transport failed: {r.format}"
  checkCertificates r
  let unsupported ← compareTheorems ``cannotMove1 ``cannotMove2 { alignment := .structural }
  expect (unsupported.classification == "UNKNOWN" && !unsupported.diagnostic.isEmpty)
    "an input depending on a removed requirement was moved out of scope"
  let noSynthesis ← compareTheorems ``baseResult ``derivedResult { synthInstances := false }
  expect (noSynthesis.req_2_to_1.status == .unknown) "instance synthesis policy was ignored"

structure Box (α : Type u) where
  value : α

theorem needsSubtype (P : Nat → Prop) (s : Subtype P) : P s.val := s.property
theorem needsBox (P : Nat → Prop) (s : Box (Subtype P)) : P s.value.val := s.value.property
theorem hasPieces (P : Nat → Prop) (n : Nat) (h : P n) : P n := h
theorem hasFunction (P : Nat → Prop) (f : Nat → Subtype P) (n : Nat) : P (f n).val := (f n).property
def boxFromInstance {α : Type u} [Inhabited α] : Box α := ⟨default⟩
theorem needsNatBox (_s : Box Nat) : True := True.intro
theorem noRequirements : True := True.intro

run_cmd Command.liftTermElabM do
  let roles1 := #[BinderRole.sharedInput, .witness]
  let roles2 := #[BinderRole.sharedInput, .witness, .requirement]
  let r ← compareTheorems ``needsSubtype ``hasPieces {
    roles1, roles2, constructors := #[``Subtype.mk]
  }
  expect (r.req_2_to_1.status == .proved && r.adapter_1_to_2.status == .proved)
    s!"dependent constructor transport failed: {r.format}"
  checkCertificates r
  let nested ← compareTheorems ``needsBox ``hasPieces {
    roles1, roles2, constructors := #[``Box.mk, ``Subtype.mk], transportDepth := 2
  }
  expect (nested.req_2_to_1.status == .proved) s!"nested constructor search failed: {nested.format}"
  checkCertificates nested
  let bounded ← compareTheorems ``needsBox ``hasPieces {
    roles1, roles2, constructors := #[``Box.mk, ``Subtype.mk], transportDepth := 0
  }
  expect (bounded.req_2_to_1.status == .unknown) "constructor depth bound was ignored"
  let localFunction ← compareTheorems ``needsSubtype ``hasFunction {
    roles1, roles2 := #[.sharedInput, .witness, .witness]
  }
  expect (localFunction.req_2_to_1.status == .proved)
    s!"local function transport failed: {localFunction.format}"
  checkCertificates localFunction
  let instanceBuilder ← compareTheorems ``needsNatBox ``noRequirements {
    roles1 := #[.witness], constructors := #[``boxFromInstance]
  }
  expect (instanceBuilder.req_2_to_1.status == .proved) "builder instance synthesis failed"
  checkCertificates instanceBuilder
  let noBuilderSynthesis ← compareTheorems ``needsNatBox ``noRequirements {
    roles1 := #[.witness], constructors := #[``boxFromInstance], synthInstances := false
  }
  expect (noBuilderSynthesis.req_2_to_1.status == .unknown)
    "a builder bypassed the instance synthesis policy"

-- Cached certificates must never cross a background policy boundary.
run_cmd Command.liftTermElabM do
  let first ← compareTheorems ``mixed1 ``mixed2 { alignment := .structural }
  let repeated ← compareTheorems ``mixed1 ``mixed2 { alignment := .structural }
  expect (repeated.guarantee_1_to_2.cacheHit && repeated.req_1_to_2.cacheHit)
    "positive and negative certificate cache did not hit"
  expect (first.guarantee_1_to_2.certificate? == repeated.guarantee_1_to_2.certificate?)
    "a cache hit should reuse the existing certificate"
  checkCertificates repeated
  let disabled ← compareTheorems ``mixed1 ``mixed2 { alignment := .structural, cache := false }
  expect (!disabled.guarantee_1_to_2.cacheHit) "cache opt-out was ignored"
  let allowed ← compareTheorems ``closedSource ``closedTarget { facts := #[``secretProof] }
  expect (allowed.guarantee_1_to_2.status == .proved) "explicit background fact"
  let denied ← compareTheorems ``closedSource ``closedTarget {
    facts := #[``secretProof], forbiddenDecls := #[``secretProof]
  }
  expect (denied.guarantee_1_to_2.status == .unknown && !denied.guarantee_1_to_2.cacheHit)
    "cache bypassed a forbidden dependency"
  let noAxioms ← compareTheorems ``closedSource ``closedTarget {
    facts := #[``secretProof], allowedAxioms? := some #[]
  }
  expect (noAxioms.guarantee_1_to_2.status == .unknown) "cache bypassed the axiom allowlist"
  let permitted ← compareTheorems ``closedSource ``closedTarget {
    facts := #[``secretProof], allowedAxioms? := some #[``secretProof]
  }
  expect (permitted.guarantee_1_to_2.status == .proved) "allowed axiom was rejected"
  checkCertificates permitted
  let unknown1 ← compareTheorems ``easy ``hard
  let unknown2 ← compareTheorems ``easy ``hard
  expect (!unknown1.req_1_to_2.cacheHit && !unknown2.req_1_to_2.cacheHit) "UNKNOWN results were cached"
  let imported ← compareTheorems ``Examples.tighter ``Examples.looser
  expect (imported.req_2_to_1.cacheHit && imported.req_1_to_2.cacheHit)
    "certificate cache did not survive a module import"
  checkCertificates imported

#guard_msgs (drop info) in
#compare_theorems twoNats1 twoNats2
  (alignment := .explicit)
  (mapping := [2, 1])
  (maxAlignmentSteps := 32)
  (constructors := [])
  (transportDepth := 2)
  (forbidden := [])
  (allowedAxioms := [])
  (synthInstances := false)
  (cache := false)
  (json := true)

#guard_msgs (drop info) in
#compare_theorems mixed1 mixed2 (alignment := .structural)

end Tests
