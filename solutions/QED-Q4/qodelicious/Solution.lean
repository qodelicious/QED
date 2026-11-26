import Mathlib

theorem twice_sum (n : ℕ) : 2 * ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

theorem four_sum_cubes (n : ℕ) : 4 * ∑ i ∈ Finset.range (n + 1), i ^ 3 = (n * (n + 1)) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; ring

theorem solution : OpenProblems.QEDQ4.Claim := by
  intro n
  have h1 := twice_sum n
  have h2 := four_sum_cubes n
  have h3 : 4 * ∑ i ∈ Finset.range (n + 1), i ^ 3 = 4 * (∑ i ∈ Finset.range (n + 1), i) ^ 2 := by
    rw [h2, ← h1]; ring
  omega
