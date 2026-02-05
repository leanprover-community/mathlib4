In LinearAlgebra.RankNullity, at
```
lemma Submodule.disjoint_ker_of_finrank_le [NoZeroSMulDivisors R M] {N : Type*} [AddCommGroup N]
    [Module R N] {L : Submodule R M} [Module.Finite R L] (f : M →ₗ[R] N)
    (h : finrank R L ≤ finrank R (L.map f)) :
    Disjoint L (LinearMap.ker f) := by
  refine disjoint_iff.mpr <| LinearMap.injective_domRestrict_iff.mp <| LinearMap.ker_eq_bot.mp <|
    Submodule.rank_eq_zero.mp ?_
  rw [← Submodule.finrank_eq_rank, Nat.cast_eq_zero]
  rw [← LinearMap.range_domRestrict] at h
  have := (LinearMap.ker (f.domRestrict L)).finrank_quotient_add_finrank
  have : finrank R (↥L ⧸ ker (f.domRestrict L)) = finrank R ↥(LinearMap.range (f.domRestrict L)) :=
    LinearEquiv.finrank_eq (f.domRestrict L).quotKerEquivRange
  rw [LinearEquiv.finrank_eq (f.domRestrict L).quotKerEquivRange] at this
  lia
```
just before the last `rw`, `try?` fails (even after increasing max heartbeats).

At the same location, claude suggests
```
  have : finrank R (↥L ⧸ ker (f.domRestrict L)) = finrank R ↥(LinearMap.range (f.domRestrict L)) :=
    LinearEquiv.finrank_eq (f.domRestrict L).quotKerEquivRange
  omega
```
which works.

In `TemperedDistribution.lean` (added recently; Claude can't have seen this), at
```
instance instFourierPairInv : FourierInvPair 𝓢'(E, F) 𝓢'(E, F) where
  fourier_fourierInv_eq f := by ext; simp
```
`try?` suggests `aesop`. `claude` suggests `ext g; simp`.

In `MahlerMeasure.lean` (added recently; Claude can't have seen this), at
```
private lemma card_mahlerMeasure (n : ℕ) (B : ℝ≥0) :
    Set.Finite {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B} ∧
    Set.ncard {p : ℤ[X] | p.natDegree ≤ n ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B} ≤
    ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := by
  simp_rw [← Nat.lt_add_one_iff (n := n)]
  have h_card :
      Set.ncard {p : ℤ[X] | p.natDegree < n + 1 ∧ ∀ i : Fin (n + 1), ‖p.coeff i‖ ≤ n.choose i * B} =
      ∏ i : Fin (n + 1), (2 * ⌊n.choose i * B⌋₊ + 1) := by
    conv => enter [1, 1, 1, p, 2, i]; rw [norm_eq_abs, abs_le]
    rw [card_eq_of_natDegree_le_of_coeff_le]
    simp only [ceil_neg, sub_neg_eq_add, ← two_mul]
    apply Finset.prod_congr rfl fun i _ ↦ ?_
    zify
    rw [toNat_of_nonneg (by positivity), ← Int.natCast_floor_eq_floor (by positivity)]
    norm_cast
  rw [← h_card]
  have h_subset :
      {p : ℤ[X] | p.natDegree < n + 1 ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ B} ⊆
      {p : ℤ[X] | p.natDegree < n + 1 ∧ ∀ i : Fin (n + 1), ‖p.coeff i‖ ≤ n.choose i * B} := by
    gcongr with p hp
    intro hB d
    rw [show ‖p.coeff d‖ = ‖(p.map (Int.castRingHom ℂ)).coeff d‖ by aesop]
    apply le_trans <| (p.map (Int.castRingHom ℂ)).norm_coeff_le_choose_mul_mahlerMeasure d
    gcongr
    · exact mahlerMeasure_nonneg _
    · grind [Polynomial.natDegree_map_le]
  have h_finite : {p : ℤ[X]| p.natDegree < n + 1 ∧
      ∀ (i : Fin (n + 1)), ‖p.coeff ↑i‖ ≤ ↑(n.choose ↑i) * ↑B}.Finite := by
    apply Set.finite_of_ncard_ne_zero
    rw [h_card, Finset.prod_ne_zero_iff]
    grind
  exact ⟨h_finite.subset h_subset, Set.ncard_le_ncard h_subset h_finite⟩
```
`claude` can reproduce the final step (I verified the prompt doesn't include the answer).

In `Hemicontinuity.lean`, at
```
lemma upperHemicontinuousWithinAt_iff_preimage_Iic :
    UpperHemicontinuousWithinAt f s x ↔ ∀ u ∈ 𝓝ˢ (f x), f ⁻¹' (Iic u) ∈ 𝓝[s] x := by
  simp_rw [upperHemicontinuousWithinAt_iff]
  rw [hasBasis_nhdsSet (f x) |>.forall_iff ?h₁, hasBasis_nhdsSet (f x) |>.forall_iff ?h₂]
  case h₂ =>
    refine fun s t hst hs ↦ Filter.mem_of_superset hs ?_
    gcongr
    exact hst
  case h₁ =>
    intro s t hst hs
    filter_upwards [hs] with x hx
    exact Filter.mem_of_superset hx hst
  refine forall₂_congr fun u ⟨hu, hfu⟩ ↦ ?_
  simp [hu.mem_nhdsSet, eventually_iff, Iic]
```
`claude` can finish at `gcongr; exact hst`, and says something sort of useful at `filter_upwards`.
