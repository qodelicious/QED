import Mathlib

/-- Three distinct vertices all adjacent to `0` give a triangle or an independent triple. -/
theorem party_adj (G : SimpleGraph (Fin 6)) (x y z : Fin 6) (h0x : (0 : Fin 6) ≠ x)
    (h0y : (0 : Fin 6) ≠ y) (h0z : (0 : Fin 6) ≠ z) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (ax : G.Adj 0 x) (ay : G.Adj 0 y) (az : G.Adj 0 z) :
    ∃ a b c : Fin 6, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      ((G.Adj a b ∧ G.Adj b c ∧ G.Adj a c) ∨ (¬ G.Adj a b ∧ ¬ G.Adj b c ∧ ¬ G.Adj a c)) := by
  by_cases e1 : G.Adj x y
  · exact ⟨0, x, y, h0x, hxy, h0y, Or.inl ⟨ax, e1, ay⟩⟩
  by_cases e2 : G.Adj y z
  · exact ⟨0, y, z, h0y, hyz, h0z, Or.inl ⟨ay, e2, az⟩⟩
  by_cases e3 : G.Adj x z
  · exact ⟨0, x, z, h0x, hxz, h0z, Or.inl ⟨ax, e3, az⟩⟩
  exact ⟨x, y, z, hxy, hyz, hxz, Or.inr ⟨e1, e2, e3⟩⟩

/-- Three distinct vertices all non-adjacent to `0` give an independent triple or a triangle. -/
theorem party_nadj (G : SimpleGraph (Fin 6)) (x y z : Fin 6) (h0x : (0 : Fin 6) ≠ x)
    (h0y : (0 : Fin 6) ≠ y) (h0z : (0 : Fin 6) ≠ z) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (ax : ¬ G.Adj 0 x) (ay : ¬ G.Adj 0 y) (az : ¬ G.Adj 0 z) :
    ∃ a b c : Fin 6, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      ((G.Adj a b ∧ G.Adj b c ∧ G.Adj a c) ∨ (¬ G.Adj a b ∧ ¬ G.Adj b c ∧ ¬ G.Adj a c)) := by
  by_cases e1 : G.Adj x y
  · by_cases e2 : G.Adj y z
    · by_cases e3 : G.Adj x z
      · exact ⟨x, y, z, hxy, hyz, hxz, Or.inl ⟨e1, e2, e3⟩⟩
      · exact ⟨0, x, z, h0x, hxz, h0z, Or.inr ⟨ax, e3, az⟩⟩
    · exact ⟨0, y, z, h0y, hyz, h0z, Or.inr ⟨ay, e2, az⟩⟩
  · exact ⟨0, x, y, h0x, hxy, h0y, Or.inr ⟨ax, e1, ay⟩⟩

theorem solution : OpenProblems.QEDQ6.Claim := by
  intro G
  by_cases h1 : G.Adj 0 1 <;> by_cases h2 : G.Adj 0 2 <;> by_cases h3 : G.Adj 0 3 <;>
    by_cases h4 : G.Adj 0 4 <;> by_cases h5 : G.Adj 0 5 <;>
    first
    | exact party_adj G 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1 h2 h3
    | exact party_nadj G 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1 h2 h3
    | exact party_adj G 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1 h2 h4
    | exact party_nadj G 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1 h2 h4
    | exact party_adj G 1 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1 h2 h5
    | exact party_nadj G 1 2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1 h2 h5
    | exact party_adj G 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1 h3 h4
    | exact party_nadj G 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1 h3 h4
    | exact party_adj G 1 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1 h3 h5
    | exact party_nadj G 1 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1 h3 h5
    | exact party_adj G 1 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1 h4 h5
    | exact party_nadj G 1 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h1 h4 h5
    | exact party_adj G 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h2 h3 h4
    | exact party_nadj G 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h2 h3 h4
    | exact party_adj G 2 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h2 h3 h5
    | exact party_nadj G 2 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h2 h3 h5
    | exact party_adj G 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h2 h4 h5
    | exact party_nadj G 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h2 h4 h5
    | exact party_adj G 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h3 h4 h5
    | exact party_nadj G 3 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h3 h4 h5
