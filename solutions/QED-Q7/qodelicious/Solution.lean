import Mathlib

namespace QEDQ7Proof

open Finset

/-- Index sets ending at `i` on which `g` is strictly increasing. -/
noncomputable def ending {n : ℕ} (g : Fin n → ℝ) (i : Fin n) : Finset (Finset (Fin n)) := by
  classical
  exact (univ : Finset (Fin n)).powerset.filter
    (fun t => t.max = (i : WithBot (Fin n)) ∧ StrictMonoOn g (t : Set (Fin n)))

theorem mem_ending {n : ℕ} (g : Fin n → ℝ) (i : Fin n) (t : Finset (Fin n)) :
    t ∈ ending g i ↔ t.max = (i : WithBot (Fin n)) ∧ StrictMonoOn g (t : Set (Fin n)) := by
  classical
  unfold ending
  simp

theorem singleton_mem {n : ℕ} (g : Fin n → ℝ) (i : Fin n) : {i} ∈ ending g i := by
  rw [mem_ending]
  refine ⟨Finset.max_singleton, ?_⟩
  simp

theorem lengths_nonempty {n : ℕ} (g : Fin n → ℝ) (i : Fin n) :
    ((ending g i).image card).Nonempty :=
  ⟨_, mem_image_of_mem _ (singleton_mem g i)⟩

/-- Length of the longest strictly increasing run of `g` ending at `i`. -/
noncomputable def len {n : ℕ} (g : Fin n → ℝ) (i : Fin n) : ℕ :=
  ((ending g i).image card).max' (lengths_nonempty g i)

theorem le_len {n : ℕ} (g : Fin n → ℝ) (i : Fin n) (t : Finset (Fin n)) (ht : t ∈ ending g i) :
    t.card ≤ len g i :=
  le_max' _ _ (mem_image_of_mem _ ht)

theorem len_spec {n : ℕ} (g : Fin n → ℝ) (i : Fin n) :
    ∃ t ∈ ending g i, t.card = len g i := by
  have h := max'_mem ((ending g i).image card) (lengths_nonempty g i)
  rw [mem_image] at h
  exact h

theorem one_le_len {n : ℕ} (g : Fin n → ℝ) (i : Fin n) : 1 ≤ len g i := by
  have := le_len g i {i} (singleton_mem g i)
  simpa using this

theorem len_lt {n : ℕ} (g : Fin n → ℝ) (i j : Fin n) (hij : i < j) (hg : g i < g j) :
    len g i < len g j := by
  obtain ⟨t, ht, hcard⟩ := len_spec g i
  rw [mem_ending] at ht
  obtain ⟨hmax, hmono⟩ := ht
  have hle : ∀ x ∈ t, x ≤ i := fun x hx => Finset.le_max_of_eq hx hmax
  have hi : i ∈ t := Finset.mem_of_max hmax
  have hj : j ∉ t := fun hj => absurd (hle j hj) (not_le.mpr hij)
  have hmem : insert j t ∈ ending g j := by
    rw [mem_ending]
    refine ⟨?_, ?_⟩
    · rw [Finset.max_insert, hmax]
      exact max_eq_left (WithBot.coe_le_coe.mpr hij.le)
    · intro x hx y hy hxy
      simp only [coe_insert, Set.mem_insert_iff, mem_coe] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact absurd hxy (lt_irrefl _)
      · exact absurd (lt_of_lt_of_le hxy (hle y hy)) (not_lt.mpr hij.le)
      · have hfx : g x ≤ g i := by
          rcases (hle x hx).lt_or_eq with h | h
          · exact (hmono hx hi h).le
          · rw [h]
        exact lt_of_le_of_lt hfx hg
      · exact hmono hx hy hxy
  have := le_len g j _ hmem
  rw [card_insert_of_notMem hj, hcard] at this
  omega

/-- The general form: more than `r * s` indices force a long monotone run. -/
theorem core {n r s : ℕ} (f : Fin n → ℝ) (hf : Function.Injective f) (hn : r * s < n) :
    (∃ t : Finset (Fin n), r < t.card ∧ StrictMonoOn f (t : Set (Fin n))) ∨
    (∃ t : Finset (Fin n), s < t.card ∧ StrictAntiOn f (t : Set (Fin n))) := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hA, hB⟩ := hcon
  let g : Fin n → ℝ := fun x => -f x
  have hr : ∀ i, len f i ≤ r := by
    intro i
    by_contra h
    obtain ⟨t, ht, hcard⟩ := len_spec f i
    rw [mem_ending] at ht
    exact hA ⟨t, by omega, ht.2⟩
  have hs : ∀ i, len g i ≤ s := by
    intro i
    by_contra h
    obtain ⟨t, ht, hcard⟩ := len_spec g i
    rw [mem_ending] at ht
    refine hB ⟨t, by omega, ?_⟩
    intro x hx y hy hxy
    have := ht.2 hx hy hxy
    simp only [g] at this
    linarith
  let p : Fin n → ℕ × ℕ := fun i => (len f i, len g i)
  have hp : Function.Injective p := by
    have key : ∀ i j, i < j → p i ≠ p j := by
      intro i j hij hpij
      simp only [p, Prod.mk.injEq] at hpij
      rcases lt_or_gt_of_ne (fun h => hij.ne (hf h)) with h | h
      · exact absurd hpij.1 (len_lt f i j hij h).ne
      · have : g i < g j := by simp only [g]; linarith
        exact absurd hpij.2 (len_lt g i j hij this).ne
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key i j h hij
    · exact key j i h hij.symm
  have hsub : (univ : Finset (Fin n)).image p ⊆ Icc 1 r ×ˢ Icc 1 s := by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    simp only [p, mem_product, mem_Icc]
    exact ⟨⟨one_le_len f i, hr i⟩, ⟨one_le_len g i, hs i⟩⟩
  have := card_le_card hsub
  rw [card_image_of_injective _ hp, card_product, Nat.card_Icc, Nat.card_Icc, card_univ,
    Fintype.card_fin, Nat.add_sub_cancel, Nat.add_sub_cancel] at this
  omega

end QEDQ7Proof

theorem solution : OpenProblems.QEDQ7.Claim := by
  intro r s f hf
  rcases QEDQ7Proof.core (r := r) (s := s) f hf (Nat.lt_succ_self _) with ⟨t, ht, hm⟩ | ⟨t, ht, hm⟩
  · left
    obtain ⟨u, hu, hcard⟩ := Finset.exists_subset_card_eq (show r + 1 ≤ t.card by omega)
    exact ⟨u, hcard, hm.mono (Finset.coe_subset.mpr hu)⟩
  · right
    obtain ⟨u, hu, hcard⟩ := Finset.exists_subset_card_eq (show s + 1 ≤ t.card by omega)
    exact ⟨u, hcard, hm.mono (Finset.coe_subset.mpr hu)⟩
