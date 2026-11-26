import Mathlib

theorem solution : OpenProblems.QEDQ5.Claim := by
  intro n hn
  have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h with h | h | h
  · exact ⟨n / 3, 0, by omega⟩
  · exact ⟨(n - 10) / 3, 2, by omega⟩
  · exact ⟨(n - 5) / 3, 1, by omega⟩
