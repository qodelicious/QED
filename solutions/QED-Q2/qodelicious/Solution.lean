import Mathlib

theorem solution : OpenProblems.QEDQ2.Claim := fun n => by
  have h : n ^ 2 + n = n * (n + 1) := by ring
  rw [h, ← even_iff_two_dvd]
  exact Int.even_mul_succ_self n
