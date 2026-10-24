import Lean

/-!
Small logical checks for the user-supplied theorem-subsumption whitepaper.
These are review evidence, not an implementation of #compare_theorems.
Checked against the repository's Lean 4.31.0 pin.
-/

namespace TheoremSubsumptionReview

theorem requirements_forward (x : Int) : x > 10 → x > 0 := by
  grind

theorem requirements_reverse_refuted :
    ¬ (∀ x : Int, x > 0 → x > 10) := by
  intro reverse
  have impossible := reverse 1 (by decide)
  omega

theorem guarantees_forward (x : Int) : x ≥ 1 → x ≥ 0 := by
  grind

theorem guarantees_reverse_refuted :
    ¬ (∀ x : Int, x ≥ 0 → x ≥ 1) := by
  intro reverse
  have impossible := reverse 0 (by decide)
  omega

theorem target_context_makes_guarantee_trivial
    (A C1 C2 : Prop) (target : A → C2) : A → C1 → C2 := by
  intro hA _
  exact target hA

theorem closed_target_makes_whole_implication_trivial
    (P Q : Prop) (target : Q) : P → Q := by
  intro _
  exact target

theorem unconditional_conclusion_comparison_trivial
    {α : Sort u} (C1 C2 : α → Prop) (target : ∀ x, C2 x) :
    ∀ x, C1 x → C2 x := by
  intro x _
  exact target x

theorem same_premise_can_strengthen_conclusion (P Q : Prop) :
    (P → Q) → P → P ∧ Q := by
  intro source hP
  exact ⟨hP, source hP⟩

theorem context_free_strengthening_refuted :
    ¬ (∀ P Q : Prop, Q → P ∧ Q) := by
  intro implication
  exact (implication False True True.intro).1

theorem bound_implication_iff_bound_order (upper1 upper2 : Nat) :
    (∀ h : Nat, h ≤ upper1 → h ≤ upper2) ↔ upper1 ≤ upper2 := by
  constructor
  · intro implication
    exact implication upper1 (Nat.le_refl upper1)
  · intro bounds h source
    exact Nat.le_trans source bounds

end TheoremSubsumptionReview

#print axioms TheoremSubsumptionReview.requirements_forward
#print axioms TheoremSubsumptionReview.requirements_reverse_refuted
#print axioms TheoremSubsumptionReview.guarantees_forward
#print axioms TheoremSubsumptionReview.guarantees_reverse_refuted
#print axioms TheoremSubsumptionReview.target_context_makes_guarantee_trivial
#print axioms TheoremSubsumptionReview.closed_target_makes_whole_implication_trivial
#print axioms TheoremSubsumptionReview.unconditional_conclusion_comparison_trivial
#print axioms TheoremSubsumptionReview.same_premise_can_strengthen_conclusion
#print axioms TheoremSubsumptionReview.context_free_strengthening_refuted
#print axioms TheoremSubsumptionReview.bound_implication_iff_bound_order
