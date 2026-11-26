import Mathlib

theorem solution : OpenProblems.QEDQ3.Claim := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring
