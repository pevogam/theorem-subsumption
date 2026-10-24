# Certified Theorem Subsumption

A Lean 4 MVP implementation of [whitepaper.md](whitepaper.md). It compares theorem
requirements and guarantees independently, derives contextual adapters, and emits
closed, kernel-checked certificates. Lean is pinned to **4.31.0**; Mathlib and
external packages are not required.

## Run

With [elan](https://github.com/leanprover/elan) installed:

```sh
lake build
lake env lean Examples.lean
```

The default build includes the library, regression tests, runnable example, and
the original [check.lean](check.lean) validation of the whitepaper's logical
claims. The example certifies that `Examples.tighter` strictly subsumes
`Examples.looser` under positional alignment.

## Compare theorems

```lean
import TheoremSubsumption

theorem tighter (x : Int) (h : x > 0) : x ≥ 1 := by omega
theorem looser (x : Int) (h : x > 10) : x ≥ 0 := by omega

#compare_theorems tighter looser
  (alignment := .positional)
  (mode := .all)
  (heartbeat := 200000)
```

The report prints both requirement directions, both context-free guarantee
directions, contextual comparisons, composed adapters, and the component-wise
classification. Every settled edge includes its obligation, certificate name,
dependency count, and axiom set. A REFUTED edge's certificate proves the negation
of the printed obligation. Inspect certificates with `#print` and `#print axioms`.

Options:

| Option | Meaning |
| --- | --- |
| `(alignment := .positional)` | Match a common shared-input prefix by position; the default. |
| `(alignment := .structural)` | Bounded matching by dependent types and binder information; accept a unique mapping. |
| `(alignment := .explicit)` | Use the supplied shared-input permutation. |
| `(mapping := [2, 1])` | Map source shared input 1 to target shared input 2, and source input 2 to target input 1. |
| `(maxAlignmentSteps := 256)` | Maximum candidate pairings in structural search. |
| `(mode := .all)` | Logical comparison and contextual adapters; the default. |
| `(mode := .logical)` | Requirements and context-free guarantees. |
| `(mode := .contextual)` | Requirements and contextual adapters, without a logical strength label. |
| `(roles1 := [...])`, `(roles2 := [...])` | Complete positional binder-role overrides for each theorem. |
| `(using := [lemma1, lemma2])` | Explicit background facts, added as local hypotheses during search. |
| `(forbidden := [lemma])` | Additional declarations forbidden transitively in every certificate. |
| `(allowedAxioms := [])` | Require axiom-free certificates. Omit to record all axioms, or list those permitted. |
| `(synthInstances := false)` | Disable automatic instance synthesis during requirement and builder construction. |
| `(constructors := [Subtype.mk])` | Functions or constructors available for building data-valued requirements. |
| `(transportDepth := 4)` | Maximum nested builder applications; zero disables builder search. |
| `(cache := false)` | Disable reuse and recording of search certificates for this comparison. |
| `(heartbeat := 200000)` | Positive Lean heartbeat budget for each edge search and transport construction. |
| `(verbose := true)` | Include search diagnostics and complete transitive dependency lists. |
| `(json := true)` | Emit the report as JSON instead of readable text. |

Binder roles are `sharedInput`, `requirement`, `witness`, and
`instanceRequirement`. By default, proposition-valued and instance-implicit
binders are requirements, and other binders are shared inputs. Positional mode
requires a common prefix with definitionally equal types. Structural and explicit
modes can move independent shared inputs ahead of interleaved requirements and
reorder target inputs. The original theorem application is preserved through a
checked lambda term. Shared inputs whose types depend on removed requirements
remain unsupported; provide witness roles or keep those dependencies shared.

Input names never affect matching. Structural search substitutes earlier matches
into dependent types, checks binder information and definitional equality, and
backtracks within its budget. Multiple solutions or an exhausted search produce
UNKNOWN before any relation is searched. Explicit mappings are one-based
permutations of all shared inputs, counting only binders with role `sharedInput`.
They are still type-checked. Strictness remains relative to the selected mapping.

For example, to treat a data binder followed by its certificate as requirements:

```lean
theorem first (n : Nat) (h : n = 0) : True := True.intro
theorem second (m : Nat) (h : m = 0) : True := True.intro

#compare_theorems first second
  (roles1 := [witness, requirement])
  (roles2 := [witness, requirement])
```

Requirements are represented by nested dependent existential bundles ending in
`True`. For example, the requirement edge in the arithmetic example is
`∀ x : Int, x > 10 → ∃ h : x > 0, True`. Witness construction proceeds in
dependency order using matching locals, typeclass synthesis, and proof search.
For data requirements, bounded search can also apply local functions and the
configured builders recursively. For example, `Subtype.mk` constructs a subtype
witness from a target value and its target-side proof. All constructed arguments
are included in the emitted requirement and adapter certificates.
Adapters apply the source theorem to those constructed arguments and compose
with a separately certified contextual guarantee.

For reordered inputs:

```lean
theorem source (n : Nat) (x : Int) (h : x > 0) : x ≥ 1 := by omega
theorem target (y : Int) (m : Nat) (h : y > 10) : y ≥ 0 := by omega

#compare_theorems source target (alignment := .structural)
-- The inferred shared-input map is [2, 1].
```

For same-type inputs that admit multiple structural matches, specify
`(alignment := .explicit) (mapping := [2, 1])` instead.

## Certification and search

PROVED requires a closed proof accepted synchronously through Lean's declaration
checker. REFUTED requires the same for the negated obligation. Search failure,
resource exhaustion, and unsupported alignment remain UNKNOWN. Strictness
requires a proved forward relation and a refuted reverse component, and is always
scoped to the displayed alignment.

The fixed search portfolio uses local assumptions, definitional equality,
`trivial`, `omega`, and `grind only`. Explicit facts are introduced locally;
global typeclass instances remain available. Both compared theorem declarations
are forbidden transitively in component certificates. A composed adapter may use
its source theorem, and forbids its target. Every certificate rejects unsolved
metavariables, free variables, and transitive `sorryAx` dependencies. Other axioms
are reported, including any introduced by explicit facts, instances, or builders.
The optional axiom allowlist applies to all transitive axiom dependencies.
Disabling requirement-instance synthesis does not disable typeclass elaboration
inside the arithmetic and logical tactics; their dependencies remain audited.

Successful search certificates, including refutations, are cached in the Lean
environment and persist through module imports. Cache lookup checks the exact
proposition up to definitional equality, the explicit facts, forbidden
declarations, axiom policy, instance policy, builders, and depth. Dependencies
and axioms are audited again on a hit. UNKNOWN results are never cached.
An existing certificate can be reused with a smaller search budget; budgets
bound discovery, not already certified evidence. Composed adapters are emitted
anew from the certified components. Reports expose `cacheHit` on each edge.

Refutation first tries the negated obligation directly, then at most 64 concrete
shared-input tuples: natural numbers 0, 1, 2, 10, 11; those integers plus -1;
both booleans; and `False`/`True` for proposition inputs. This is deliberately
incomplete. Guarantees depending on removed requirement binders are reported as
NOT-WELL-FORMED; a contextual adapter can still succeed.

The public `TheoremSubsumption.compareTheorems` API returns a structured
`ComparisonReport` in `TermElabM`. `ComparisonReport.toJson` includes alignment,
roles, background, budget, obligations, statuses, certificate names, transitive
dependencies, axioms, cache hits, and source-use diagnostics. Schema version 2
also records the selected input map, structural search steps, and background
controls. To capture JSON command output
with Lean's diagnostic envelope, use `lake env lean --json YourComparisons.lean`
with `(json := true)` on the comparisons.

## Validation and scope

[Tests.lean](Tests.lean) checks arithmetic strictness, equivalence under
alpha-renaming, incomparability, UNKNOWN preservation, contextual versus
context-free reasoning, dependent witnesses, parent-instance synthesis,
universe polymorphism, alignment errors, background facts, target shortcuts,
placeholder rejection, and small search budgets. It independently kernel-checks
every settled edge in the principal test families.

Phase 2 regressions additionally cover reordered and dependent matching,
ambiguity and search exhaustion, explicit permutations, interleaved instance
requirements, nested data builders, local function transports, cache persistence,
and cache isolation under stricter background policies.

Semantic-domain plugins and bridges, corpus indexing, and library curation are
deferred to later phases of the whitepaper. JSON reports therefore contain an
empty `semanticComparisons` array.
