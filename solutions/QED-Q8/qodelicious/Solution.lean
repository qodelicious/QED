import Mathlib

/-!
Dilworth's theorem, following Galvin's proof (Amer. Math. Monthly 101 (1994)).
Induction on finite subsets `s` of a poset: we colour `s` with fewer than `width s` colours
so that each colour class is a chain, where `width s` is the size of a largest antichain in `s`.
-/
namespace QEDQ8Proof

open Finset

variable {α : Type} [PartialOrder α]

/-- Size of a largest antichain inside `s`. -/
noncomputable def width (s : Finset α) : ℕ := by
  classical
  exact (s.powerset.filter fun B : Finset α => IsAntichain (· ≤ ·) (B : Set α)).sup card

theorem le_width {s B : Finset α} (hB : B ⊆ s) (hA : IsAntichain (· ≤ ·) (B : Set α)) :
    B.card ≤ width s := by
  classical
  unfold width
  exact le_sup (f := card) (mem_filter.mpr ⟨mem_powerset.mpr hB, hA⟩)

theorem exists_width (s : Finset α) :
    ∃ B ⊆ s, IsAntichain (· ≤ ·) (B : Set α) ∧ B.card = width s := by
  classical
  unfold width
  have hne : (s.powerset.filter fun B : Finset α => IsAntichain (· ≤ ·) (B : Set α)).Nonempty :=
    ⟨∅, mem_filter.mpr ⟨empty_mem_powerset s, by simp⟩⟩
  obtain ⟨B, hB, h⟩ := exists_mem_eq_sup _ hne card
  rw [mem_filter, mem_powerset] at hB
  exact ⟨B, hB.1, hB.2, h.symm⟩

theorem width_mono {s t : Finset α} (h : t ⊆ s) : width t ≤ width s := by
  obtain ⟨B, hB, hA, hc⟩ := exists_width t
  rw [← hc]
  exact le_width (hB.trans h) hA

/-- `B` is a largest antichain of `s`. -/
def MaxAC (s B : Finset α) : Prop :=
  B ⊆ s ∧ IsAntichain (· ≤ ·) (B : Set α) ∧ B.card = width s

theorem exists_max_mem (s : Finset α) (hs : s.Nonempty) : ∃ m ∈ s, ∀ x ∈ s, ¬ m < x := by
  obtain ⟨m, hm⟩ := s.exists_maximal hs
  exact ⟨m, hm.1, fun x hx h => lt_irrefl _ (h.trans_le (hm.2 hx h.le))⟩

theorem dil [DecidableEq α] (s : Finset α) : ∃ c : α → ℕ, (∀ x ∈ s, c x < width s) ∧
    ∀ x ∈ s, ∀ y ∈ s, c x = c y → x ≤ y ∨ y ≤ x := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨fun _ => 0, by simp, by simp⟩
  obtain ⟨a, ha, amax⟩ := exists_max_mem s hs
  have : Nonempty α := ⟨a⟩
  obtain ⟨c', hc'lt, hc'ch⟩ := ih (s.erase a) (erase_ssubset ha)
  have hks : width (s.erase a) ≤ width s := width_mono (erase_subset a s)
  set s' := s.erase a with hs'
  set k := width s' with hk
  -- every largest antichain of `s'` meets every colour class of `c'`
  have hits : ∀ B, MaxAC s' B → ∀ i < k, ∃ y ∈ B, c' y = i := by
    intro B hB i hi
    obtain ⟨hBs, hBa, hBc⟩ := hB
    have hinj : Set.InjOn c' (B : Set α) := by
      intro x hx y hy hxy
      rcases hc'ch x (hBs hx) y (hBs hy) hxy with h | h
      · exact hBa.eq hx hy h
      · exact (hBa.eq hy hx h).symm
    have hsub : B.image c' ⊆ range k := by
      intro z hz
      rw [mem_image] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact mem_range.mpr (hc'lt y (hBs hy))
    have heq : B.image c' = range k :=
      eq_of_subset_of_card_le hsub (by rw [card_image_of_injOn hinj, card_range, hBc])
    have : i ∈ B.image c' := by rw [heq]; exact mem_range.mpr hi
    rw [mem_image] at this
    exact this
  obtain ⟨B0, hB0s, hB0a, hB0c⟩ := exists_width s'
  -- in colour class `i`, the top element lying in some largest antichain
  have hQ : ∀ i < k, ∃ y, y ∈ s' ∧ c' y = i ∧ (∃ B, MaxAC s' B ∧ y ∈ B) ∧
      ∀ z ∈ s', c' z = i → (∃ B, MaxAC s' B ∧ z ∈ B) → z ≤ y := by
    intro i hi
    let S := s'.filter fun z => c' z = i ∧ ∃ B, MaxAC s' B ∧ z ∈ B
    have hSne : S.Nonempty := by
      obtain ⟨y, hy, hcy⟩ := hits B0 ⟨hB0s, hB0a, hB0c⟩ i hi
      exact ⟨y, mem_filter.mpr ⟨hB0s hy, hcy, B0, ⟨hB0s, hB0a, hB0c⟩, hy⟩⟩
    obtain ⟨y, hyS, ymax⟩ := exists_max_mem S hSne
    rw [mem_filter] at hyS
    refine ⟨y, hyS.1, hyS.2.1, hyS.2.2, fun z hz hcz hzB => ?_⟩
    have hzS : z ∈ S := mem_filter.mpr ⟨hz, hcz, hzB⟩
    rcases hc'ch z hz y hyS.1 (hcz.trans hyS.2.1.symm) with h | h
    · exact h
    · rcases h.lt_or_eq with h | h
      · exact absurd h (ymax z hzS)
      · exact h.symm.le
  choose! x hx using hQ
  have xinj : ∀ i < k, ∀ j < k, x i = x j → i = j := by
    intro i hi j hj h
    rw [← (hx i hi).2.1, ← (hx j hj).2.1, h]
  have xanti : ∀ i < k, ∀ j < k, x i ≤ x j → i = j := by
    intro i hi j hj hle
    by_contra hij
    obtain ⟨_, hci, _, himax⟩ := hx i hi
    obtain ⟨_, hcj, ⟨B, hB, hxB⟩, _⟩ := hx j hj
    obtain ⟨y, hyB, hcy⟩ := hits B hB i hi
    have hyle : y ≤ x i := himax y (hB.1 hyB) hcy ⟨B, hB, hyB⟩
    have hyx : y = x j := hB.2.1.eq hyB hxB (hyle.trans hle)
    rw [hyx, hcj] at hcy
    exact hij hcy.symm
  have hxs : ∀ i < k, x i ∈ s := fun i hi => mem_of_mem_erase (hx i hi).1
  by_cases hcase : ∃ i < k, x i ≤ a
  · -- remove the chain of colour `i0` below `x i0`, together with `a`
    obtain ⟨i0, hi0, hxa⟩ := hcase
    let K := insert a (s'.filter fun z => c' z = i0 ∧ z ≤ x i0)
    let t := s.filter fun z => z ∉ K
    have ht : t ⊂ s := filter_ssubset.mpr ⟨a, ha, by simp [K]⟩
    obtain ⟨ct, hctlt, hctch⟩ := ih t ht
    have hts : ∀ z ∈ t, z ∈ s' := by
      intro z hz
      rw [mem_filter] at hz
      refine mem_erase.mpr ⟨fun h => hz.2 ?_, hz.1⟩
      rw [h]
      exact mem_insert_self a _
    have hwt : width t < k := by
      by_contra hge
      push Not at hge
      obtain ⟨B, hBt, hBa, hBc⟩ := exists_width t
      obtain ⟨B', hB'B, hB'c⟩ := exists_subset_card_eq (show k ≤ B.card by omega)
      have hB' : MaxAC s' B' :=
        ⟨fun z hz => hts z (hBt (hB'B hz)), hBa.subset (coe_subset.mpr hB'B), hB'c⟩
      obtain ⟨y, hyB', hcy⟩ := hits B' hB' i0 hi0
      have hys' := hB'.1 hyB'
      have hyle := (hx i0 hi0).2.2.2 y hys' hcy ⟨B', hB', hyB'⟩
      have hyt := hBt (hB'B hyB')
      rw [mem_filter] at hyt
      exact hyt.2 (mem_insert_of_mem (mem_filter.mpr ⟨hys', hcy, hyle⟩))
    have hKchain : ∀ y ∈ K, ∀ z ∈ K, y ≤ z ∨ z ≤ y := by
      intro y hy z hz
      rw [mem_insert, mem_filter] at hy hz
      rcases hy with rfl | ⟨hy, hcy, hyle⟩ <;> rcases hz with rfl | ⟨hz, hcz, hzle⟩
      · exact Or.inl le_rfl
      · exact Or.inr (hzle.trans hxa)
      · exact Or.inl (hyle.trans hxa)
      · exact hc'ch y hy z hz (hcy.trans hcz.symm)
    refine ⟨fun z => if z ∈ K then k - 1 else ct z, ?_, ?_⟩
    · intro z hz
      by_cases hzK : z ∈ K
      · simp only [hzK, ite_true]
        omega
      · simp only [hzK, ite_false]
        have := hctlt z (mem_filter.mpr ⟨hz, hzK⟩)
        omega
    · intro y hy z hz hc
      by_cases hyK : y ∈ K <;> by_cases hzK : z ∈ K <;> simp only [hyK, hzK, ite_true, ite_false] at hc
      · exact hKchain y hyK z hzK
      · have := hctlt z (mem_filter.mpr ⟨hz, hzK⟩)
        omega
      · have := hctlt y (mem_filter.mpr ⟨hy, hyK⟩)
        omega
      · exact hctch y (mem_filter.mpr ⟨hy, hyK⟩) z (mem_filter.mpr ⟨hz, hzK⟩) hc
  · -- the tops together with `a` form an antichain of size `k + 1`
    push Not at hcase
    have haA : a ∉ (range k).image x := by
      intro h
      rw [mem_image] at h
      obtain ⟨i, hi, hxi⟩ := h
      have := (hx i (mem_range.mp hi)).1
      rw [hxi] at this
      exact notMem_erase a s this
    have hAcard : (insert a ((range k).image x)).card = k + 1 := by
      rw [card_insert_of_notMem haA, card_image_of_injOn, card_range]
      intro i hi j hj h
      exact xinj i (mem_range.mp hi) j (mem_range.mp hj) h
    have hAanti : IsAntichain (· ≤ ·) ((insert a ((range k).image x) : Finset α) : Set α) := by
      intro u hu v hv huv h
      simp only [coe_insert, coe_image, coe_range, Set.mem_insert_iff, Set.mem_image,
        Set.mem_Iio] at hu hv
      rcases hu with hu | ⟨i, hi, hu⟩ <;> rcases hv with hv | ⟨j, hj, hv⟩ <;> subst hu hv
      · exact huv rfl
      · rcases h.lt_or_eq with h | h
        · exact amax _ (hxs j hj) h
        · exact haA (h ▸ mem_image_of_mem x (mem_range.mpr hj))
      · exact hcase i hi h
      · exact huv (congrArg x (xanti i hi j hj h))
    have hAs : insert a ((range k).image x) ⊆ s := by
      intro z hz
      rw [mem_insert, mem_image] at hz
      rcases hz with rfl | ⟨i, hi, rfl⟩
      · exact ha
      · exact hxs i (mem_range.mp hi)
    have hw := le_width hAs hAanti
    rw [hAcard] at hw
    refine ⟨fun z => if z = a then k else c' z, ?_, ?_⟩
    · intro z hz
      by_cases hza : z = a
      · simp only [hza, ite_true]
        omega
      · simp only [hza, ite_false]
        have := hc'lt z (mem_erase.mpr ⟨hza, hz⟩)
        omega
    · intro y hy z hz hc
      by_cases hya : y = a <;> by_cases hza : z = a <;> simp only [hya, hza, ite_true, ite_false] at hc
      · exact Or.inl (le_of_eq (hya.trans hza.symm))
      · have := hc'lt z (mem_erase.mpr ⟨hza, hz⟩)
        omega
      · have := hc'lt y (mem_erase.mpr ⟨hya, hy⟩)
        omega
      · exact hc'ch y (mem_erase.mpr ⟨hya, hy⟩) z (mem_erase.mpr ⟨hza, hz⟩) hc

end QEDQ8Proof

theorem solution : OpenProblems.QEDQ8.Claim := by
  intro α _ _
  classical
  obtain ⟨c, hclt, hcch⟩ := QEDQ8Proof.dil (Finset.univ : Finset α)
  obtain ⟨A, -, hA, hAc⟩ := QEDQ8Proof.exists_width (Finset.univ : Finset α)
  refine ⟨A.card, A, fun x => ⟨c x, by rw [hAc]; exact hclt x (Finset.mem_univ x)⟩, hA, rfl, ?_⟩
  intro x y hxy
  exact hcch x (Finset.mem_univ _) y (Finset.mem_univ _) (Fin.ext_iff.mp hxy)
