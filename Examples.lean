import TheoremSubsumption

namespace Examples

theorem tighter (x : Int) (h : x > 0) : x ≥ 1 := by omega
theorem looser (x : Int) (h : x > 10) : x ≥ 0 := by omega

#compare_theorems tighter looser
  (alignment := .positional)
  (mode := .all)
  (heartbeat := 200000)
  (verbose := false)

end Examples
