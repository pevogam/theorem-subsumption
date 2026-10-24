import TheoremSubsumption

namespace Examples

theorem tighter (x : Int) (h : x > 0) : x ≥ 1 := by omega
theorem looser (x : Int) (h : x > 10) : x ≥ 0 := by omega

#compare_theorems tighter looser
  (alignment := .positional)
  (mode := .all)
  (heartbeat := 200000)
  (verbose := false)

theorem reorderedTighter (x : Int) (n : Nat) (h : x > 0) : x ≥ 1 ∧ n = n := by omega
theorem reorderedLooser (m : Nat) (y : Int) (h : y > 10) : y ≥ 0 ∧ m = m := by omega

#compare_theorems reorderedTighter reorderedLooser
  (alignment := .structural)
  (maxAlignmentSteps := 64)

end Examples
