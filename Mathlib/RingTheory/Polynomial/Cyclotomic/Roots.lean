/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.Minpoly

/-!
# Roots of cyclotomic polynomials.

We gather results about roots of cyclotomic polynomials. In particular we show in
`Polynomial.cyclotomic_eq_minpoly` that `cyclotomic n R` is the minimal polynomial of a primitive
root of unity.

## Main results

* `IsPrimitiveRoot.isRoot_cyclotomic` : Any `n`-th primitive root of unity is a root of
  `cyclotomic n R`.
* `isRoot_cyclotomic_iff` : if `NeZero (n : R)`, then `μ` is a root of `cyclotomic n R`
  if and only if `μ` is a primitive root of unity.
* `Polynomial.cyclotomic_eq_minpoly` : `cyclotomic n ℤ` is the minimal polynomial of a primitive
  `n`-th root of unity `μ`.
* `Polynomial.cyclotomic.irreducible` : `cyclotomic n ℤ` is irreducible.

## Implementation details

To prove `Polynomial.cyclotomic.irreducible`, the irreducibility of `cyclotomic n ℤ`, we show in
`Polynomial.cyclotomic_eq_minpoly` that `cyclotomic n ℤ` is the minimal polynomial of any `n`-th
primitive root of unity `μ : K`, where `K` is a field of characteristic `0`.
-/


namespace Polynomial

variable {R : Type*} [CommRing R] {n : ℕ}

theorem isRoot_of_unity_of_root_cyclotomic {ζ : R} {i : ℕ} (hi : i ∈ n.divisors)
    (h : (cyclotomic i R).IsRoot ζ) : ζ ^ n = 1 := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · exact pow_zero _
  have := congr_arg (eval ζ) (prod_cyclotomic_eq_X_pow_sub_one hn R).symm
  rw [eval_sub, eval_pow, eval_X, eval_one] at this
  convert eq_add_of_sub_eq' this
  convert (add_zero (M := R) _).symm
  apply eval_eq_zero_of_dvd_of_eval_eq_zero _ h
  exact Finset.dvd_prod_of_mem _ hi

section IsDomain

variable [IsDomain R]

theorem _root_.isRoot_of_unity_iff (h : 0 < n) (R : Type*) [CommRing R] [IsDomain R] {ζ : R} :
    ζ ^ n = 1 ↔ ∃ i ∈ n.divisors, (cyclotomic i R).IsRoot ζ := by
  rw [← mem_nthRoots h, nthRoots, mem_roots <| X_pow_sub_C_ne_zero h _, C_1, ←
      prod_cyclotomic_eq_X_pow_sub_one h, isRoot_prod]

/-- Any `n`-th primitive root of unity is a root of `cyclotomic n R`. -/
theorem _root_.IsPrimitiveRoot.isRoot_cyclotomic (hpos : 0 < n) {μ : R} (h : IsPrimitiveRoot μ n) :
    IsRoot (cyclotomic n R) μ := by
  rw [← mem_roots (cyclotomic_ne_zero n R), cyclotomic_eq_prod_X_sub_primitiveRoots h,
    roots_prod_X_sub_C, ← Finset.mem_def]
  rwa [← mem_primitiveRoots hpos] at h

private theorem isRoot_cyclotomic_iff' {n : ℕ} {K : Type*} [Field K] {μ : K} [NeZero (n : K)] :
    IsRoot (cyclotomic n K) μ ↔ IsPrimitiveRoot μ n := by
  -- in this proof, `o` stands for `orderOf μ`
  have hnpos : 0 < n := (NeZero.of_neZero_natCast K).out.bot_lt
  refine ⟨fun hμ => ?_, IsPrimitiveRoot.isRoot_cyclotomic hnpos⟩
  have hμn : μ ^ n = 1 := by
    rw [isRoot_of_unity_iff hnpos _]
    exact ⟨n, n.mem_divisors_self hnpos.ne', hμ⟩
  by_contra hnμ
  have ho : 0 < orderOf μ := (isOfFinOrder_iff_pow_eq_one.2 <| ⟨n, hnpos, hμn⟩).orderOf_pos
  have := pow_orderOf_eq_one μ
  rw [isRoot_of_unity_iff ho] at this
  obtain ⟨i, hio, hiμ⟩ := this
  replace hio := Nat.dvd_of_mem_divisors hio
  rw [IsPrimitiveRoot.not_iff] at hnμ
  rw [← orderOf_dvd_iff_pow_eq_one] at hμn
  have key : i < n := (Nat.le_of_dvd ho hio).trans_lt ((Nat.le_of_dvd hnpos hμn).lt_of_ne hnμ)
  have key' : i ∣ n := hio.trans hμn
  rw [← Polynomial.dvd_iff_isRoot] at hμ hiμ
  have hni : {i, n} ⊆ n.divisors := by simpa [Finset.insert_subset_iff, key'] using hnpos.ne'
  obtain ⟨k, hk⟩ := hiμ
  obtain ⟨j, hj⟩ := hμ
  have := prod_cyclotomic_eq_X_pow_sub_one hnpos K
  rw [← Finset.prod_sdiff hni, Finset.prod_pair key.ne, hk, hj] at this
  have hn := (X_pow_sub_one_separable_iff.mpr <| NeZero.natCast_ne n K).squarefree
  rw [← this, Squarefree] at hn
  specialize hn (X - C μ) ⟨(∏ x ∈ n.divisors \ {i, n}, cyclotomic x K) * k * j, by ring⟩
  simp [Polynomial.isUnit_iff_degree_eq_zero] at hn

theorem isRoot_cyclotomic_iff [NeZero (n : R)] {μ : R} :
    IsRoot (cyclotomic n R) μ ↔ IsPrimitiveRoot μ n := by
  have hf : Function.Injective _ := IsFractionRing.injective R (FractionRing R)
  haveI : NeZero (n : FractionRing R) := NeZero.nat_of_injective hf
  rw [← isRoot_map_iff hf, ← IsPrimitiveRoot.map_iff_of_injective hf, map_cyclotomic, ←
    isRoot_cyclotomic_iff']

theorem roots_cyclotomic_nodup [NeZero (n : R)] : (cyclotomic n R).roots.Nodup := by
  obtain h | ⟨ζ, hζ⟩ := (cyclotomic n R).roots.empty_or_exists_mem
  · exact h.symm ▸ Multiset.nodup_zero
  rw [mem_roots <| cyclotomic_ne_zero n R, isRoot_cyclotomic_iff] at hζ
  refine Multiset.nodup_of_le
    (roots.le_of_dvd (X_pow_sub_C_ne_zero (NeZero.pos_of_neZero_natCast R) 1) <|
      cyclotomic.dvd_X_pow_sub_one n R) hζ.nthRoots_one_nodup

theorem cyclotomic.roots_to_finset_eq_primitiveRoots [NeZero (n : R)] :
    (⟨(cyclotomic n R).roots, roots_cyclotomic_nodup⟩ : Finset _) = primitiveRoots n R := by
  ext a
  -- Porting note: was
  -- `simp [cyclotomic_ne_zero n R, isRoot_cyclotomic_iff, mem_primitiveRoots,`
  -- `  NeZero.pos_of_neZero_natCast R]`
  simp only [mem_primitiveRoots, NeZero.pos_of_neZero_natCast R]
  convert isRoot_cyclotomic_iff (n := n) (μ := a) using 0
  simp [cyclotomic_ne_zero n R]

theorem cyclotomic.roots_eq_primitiveRoots_val [NeZero (n : R)] :
    (cyclotomic n R).roots = (primitiveRoots n R).val := by
  rw [← cyclotomic.roots_to_finset_eq_primitiveRoots]

/-- If `R` is of characteristic zero, then `ζ` is a root of `cyclotomic n R` if and only if it is a
primitive `n`-th root of unity. -/
theorem isRoot_cyclotomic_iff_charZero {n : ℕ} {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {μ : R} (hn : 0 < n) : (Polynomial.cyclotomic n R).IsRoot μ ↔ IsPrimitiveRoot μ n :=
  letI := NeZero.of_gt hn
  isRoot_cyclotomic_iff

end IsDomain

/-- Over a ring `R` of characteristic zero, `fun n => cyclotomic n R` is injective. -/
theorem cyclotomic_injective [CharZero R] : Function.Injective fun n => cyclotomic n R := by
  intro n m hnm
  simp only at hnm
  rcases eq_or_ne n 0 with (rfl | hzero)
  · rw [cyclotomic_zero] at hnm
    replace hnm := congr_arg natDegree hnm
    rwa [natDegree_one, natDegree_cyclotomic, eq_comm, Nat.totient_eq_zero, eq_comm] at hnm
  · haveI := NeZero.mk hzero
    rw [← map_cyclotomic_int _ R, ← map_cyclotomic_int _ R] at hnm
    replace hnm := map_injective (Int.castRingHom R) Int.cast_injective hnm
    replace hnm := congr_arg (map (Int.castRingHom ℂ)) hnm
    rw [map_cyclotomic_int, map_cyclotomic_int] at hnm
    have hprim := Complex.isPrimitiveRoot_exp _ hzero
    have hroot := isRoot_cyclotomic_iff (R := ℂ).2 hprim
    rw [hnm] at hroot
    haveI hmzero : NeZero m := ⟨fun h => by simp [h] at hroot⟩
    rw [isRoot_cyclotomic_iff (R := ℂ)] at hroot
    replace hprim := hprim.eq_orderOf
    rwa [← IsPrimitiveRoot.eq_orderOf hroot] at hprim

/-- The minimal polynomial of a primitive `n`-th root of unity `μ` divides `cyclotomic n ℤ`. -/
theorem _root_.IsPrimitiveRoot.minpoly_dvd_cyclotomic {n : ℕ} {K : Type*} [Field K] {μ : K}
    (h : IsPrimitiveRoot μ n) (hpos : 0 < n) [CharZero K] : minpoly ℤ μ ∣ cyclotomic n ℤ := by
  apply minpoly.isIntegrallyClosed_dvd (h.isIntegral hpos)
  simpa [aeval_def, eval₂_eq_eval_map, IsRoot.def] using h.isRoot_cyclotomic hpos

section minpoly

open IsPrimitiveRoot Complex

theorem _root_.IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible {K : Type*} [Field K]
    {R : Type*} [CommRing R] [IsDomain R] {μ : R} {n : ℕ} [Algebra K R] (hμ : IsPrimitiveRoot μ n)
    (h : Irreducible <| cyclotomic n K) [NeZero (n : K)] : cyclotomic n K = minpoly K μ := by
  haveI := NeZero.of_faithfulSMul K R n
  refine minpoly.eq_of_irreducible_of_monic h ?_ (cyclotomic.monic n K)
  rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ← IsRoot.def, isRoot_cyclotomic_iff]

/-- `cyclotomic n ℤ` is the minimal polynomial of a primitive `n`-th root of unity `μ`. -/
theorem cyclotomic_eq_minpoly {n : ℕ} {K : Type*} [Field K] {μ : K} (h : IsPrimitiveRoot μ n)
    (hpos : 0 < n) [CharZero K] : cyclotomic n ℤ = minpoly ℤ μ := by
  refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (IsPrimitiveRoot.isIntegral h hpos))
    (cyclotomic.monic n ℤ) (h.minpoly_dvd_cyclotomic hpos) ?_
  simpa [natDegree_cyclotomic n ℤ] using totient_le_degree_minpoly h

/-- `cyclotomic n ℚ` is the minimal polynomial of a primitive `n`-th root of unity `μ`. -/
theorem cyclotomic_eq_minpoly_rat {n : ℕ} {K : Type*} [Field K] {μ : K} (h : IsPrimitiveRoot μ n)
    (hpos : 0 < n) [CharZero K] : cyclotomic n ℚ = minpoly ℚ μ := by
  rw [← map_cyclotomic_int, cyclotomic_eq_minpoly h hpos]
  exact (minpoly.isIntegrallyClosed_eq_field_fractions' _ (IsPrimitiveRoot.isIntegral h hpos)).symm

/-- `cyclotomic n ℤ` is irreducible. -/
theorem cyclotomic.irreducible {n : ℕ} (hpos : 0 < n) : Irreducible (cyclotomic n ℤ) := by
  rw [cyclotomic_eq_minpoly (isPrimitiveRoot_exp n hpos.ne') hpos]
  apply minpoly.irreducible
  exact (isPrimitiveRoot_exp n hpos.ne').isIntegral hpos

/-- `cyclotomic n ℚ` is irreducible. -/
theorem cyclotomic.irreducible_rat {n : ℕ} (hpos : 0 < n) : Irreducible (cyclotomic n ℚ) := by
  rw [← map_cyclotomic_int]
  exact (IsPrimitive.irreducible_iff_irreducible_map_fraction_map (cyclotomic.isPrimitive n ℤ)).1
    (cyclotomic.irreducible hpos)

/-- If `n ≠ m`, then `(cyclotomic n ℚ)` and `(cyclotomic m ℚ)` are coprime. -/
theorem cyclotomic.isCoprime_rat {n m : ℕ} (h : n ≠ m) :
    IsCoprime (cyclotomic n ℚ) (cyclotomic m ℚ) := by
  rcases n.eq_zero_or_pos with (rfl | hnzero)
  · exact isCoprime_one_left
  rcases m.eq_zero_or_pos with (rfl | hmzero)
  · exact isCoprime_one_right
  rw [Irreducible.coprime_iff_not_dvd <| cyclotomic.irreducible_rat <| hnzero]
  exact fun hdiv => h <| cyclotomic_injective <|
    eq_of_monic_of_associated (cyclotomic.monic n ℚ) (cyclotomic.monic m ℚ) <|
      Irreducible.associated_of_dvd (cyclotomic.irreducible_rat hnzero)
        (cyclotomic.irreducible_rat hmzero) hdiv

end minpoly

end Polynomial
