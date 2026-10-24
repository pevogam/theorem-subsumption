# Certified Theorem Subsumption

A Lean 4 MVP of Phase 1 in [whitepaper.md](whitepaper.md). It compares theorem
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
| `(mode := .all)` | Logical comparison and contextual adapters; the default. |
| `(mode := .logical)` | Requirements and context-free guarantees. |
| `(mode := .contextual)` | Requirements and contextual adapters, without a logical strength label. |
| `(roles1 := [...])`, `(roles2 := [...])` | Complete positional binder-role overrides for each theorem. |
| `(using := [lemma1, lemma2])` | Explicit background facts, added as local hypotheses during search. |
| `(heartbeat := 200000)` | Positive Lean heartbeat budget for each edge search and transport construction. |
| `(verbose := true)` | Include search diagnostics and complete transitive dependency lists. |
| `(json := true)` | Emit the report as JSON instead of readable text. |

Binder roles are `sharedInput`, `requirement`, `witness`, and
`instanceRequirement`. By default, proposition-valued and instance-implicit
binders are requirements, and other binders are shared inputs. Shared inputs
must form a common prefix with definitionally equal types. Input names do not
affect matching. A shared input appearing after a requirement is ambiguous and
returns UNKNOWN until roles are supplied explicitly.

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
Adapters apply the source theorem to those constructed arguments and compose
with a separately certified contextual guarantee.

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
are reported, including any introduced by explicit facts or instances.

Refutation first tries the negated obligation directly, then at most 64 concrete
shared-input tuples: natural numbers 0, 1, 2, 10, 11; those integers plus -1;
both booleans; and `False`/`True` for proposition inputs. This is deliberately
incomplete. Guarantees depending on removed requirement binders are reported as
NOT-WELL-FORMED; a contextual adapter can still succeed.

The public `TheoremSubsumption.compareTheorems` API returns a structured
`ComparisonReport` in `TermElabM`. `ComparisonReport.toJson` includes alignment,
roles, background, budget, obligations, statuses, certificate names, transitive
dependencies, axioms, and source-use diagnostics. To capture JSON command output
with Lean's diagnostic envelope, use `lake env lean --json YourComparisons.lean`
with `(json := true)` on the comparisons.

## Validation and scope

[Tests.lean](Tests.lean) checks arithmetic strictness, equivalence under
alpha-renaming, incomparability, UNKNOWN preservation, contextual versus
context-free reasoning, dependent witnesses, parent-instance synthesis,
universe polymorphism, alignment errors, background facts, target shortcuts,
placeholder rejection, and small search budgets. It independently kernel-checks
every settled edge in the principal test families.

This MVP implements positional alignment and role overrides. Structural or
reordered alignment, semantic-domain plugins and bridges, corpus indexing, and
library curation are deferred to later phases of the whitepaper. JSON reports
therefore contain an empty `semanticComparisons` array.
