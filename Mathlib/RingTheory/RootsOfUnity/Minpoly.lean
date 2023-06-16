/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin

! This file was ported from Lean 3 source module ring_theory.roots_of_unity.minpoly
! leanprover-community/mathlib commit 7fdeecc0d03cd40f7a165e6cf00a4d2286db599f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Minimal polynomial of roots of unity

We gather several results about minimal polynomial of root of unity.

## Main results

* `is_primitive_root.totient_le_degree_minpoly`: The degree of the minimal polynomial of a `n`-th
  primitive root of unity is at least `totient n`.

-/


open minpoly Polynomial

open scoped Polynomial

namespace IsPrimitiveRoot

section CommRing

variable {n : ℕ} {K : Type _} [CommRing K] {μ : K} (h : IsPrimitiveRoot μ n) (hpos : 0 < n)

/-- `μ` is integral over `ℤ`. -/
theorem isIntegral : IsIntegral ℤ μ := by
  use X ^ n - 1
  constructor
  · exact monic_X_pow_sub_C 1 (ne_of_lt hpos).symm
  · simp only [((IsPrimitiveRoot.iff_def μ n).mp h).left, eval₂_one, eval₂_X_pow, eval₂_sub,
      sub_self]
#align is_primitive_root.is_integral IsPrimitiveRoot.isIntegral

section IsDomain

variable [IsDomain K] [CharZero K]

/-- The minimal polynomial of a root of unity `μ` divides `X ^ n - 1`. -/
theorem minpoly_dvd_x_pow_sub_one : minpoly ℤ μ ∣ X ^ n - 1 := by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp
  letI : IsIntegrallyClosed ℤ := GCDMonoid.toIsIntegrallyClosed
  apply minpoly.isIntegrallyClosed_dvd (isIntegral h hpos)
  simp only [((IsPrimitiveRoot.iff_def μ n).mp h).left, aeval_X_pow, eq_intCast, Int.cast_one,
    aeval_one, AlgHom.map_sub, sub_self]
set_option linter.uppercaseLean3 false in
#align is_primitive_root.minpoly_dvd_X_pow_sub_one IsPrimitiveRoot.minpoly_dvd_x_pow_sub_one

/-- The reduction modulo `p` of the minimal polynomial of a root of unity `μ` is separable. -/
theorem separable_minpoly_mod {p : ℕ} [Fact p.Prime] (hdiv : ¬p ∣ n) :
    Separable (map (Int.castRingHom (ZMod p)) (minpoly ℤ μ)) := by
  have hdvd : map (Int.castRingHom (ZMod p)) (minpoly ℤ μ) ∣ X ^ n - 1 := by
    simp [Polynomial.map_pow, map_X, Polynomial.map_one, Polynomial.map_sub]
    convert  RingHom.map_dvd (mapRingHom (Int.castRingHom (ZMod p)))
        (minpoly_dvd_x_pow_sub_one h hpos)
    simp only [map_sub, map_pow, coe_mapRingHom, map_X, map_one]
  refine' Separable.of_dvd (separable_X_pow_sub_C 1 _ one_ne_zero) hdvd
  by_contra hzero
  exact hdiv ((ZMod.nat_cast_zmod_eq_zero_iff_dvd n p).1 hzero)
#align is_primitive_root.separable_minpoly_mod IsPrimitiveRoot.separable_minpoly_mod

/-- The reduction modulo `p` of the minimal polynomial of a root of unity `μ` is squarefree. -/
theorem squarefree_minpoly_mod {p : ℕ} [Fact p.Prime] (hdiv : ¬p ∣ n) :
    Squarefree (map (Int.castRingHom (ZMod p)) (minpoly ℤ μ)) :=
  (separable_minpoly_mod h hdiv).Squarefree
#align is_primitive_root.squarefree_minpoly_mod IsPrimitiveRoot.squarefree_minpoly_mod

/- Let `P` be the minimal polynomial of a root of unity `μ` and `Q` be the minimal polynomial of
`μ ^ p`, where `p` is a natural number that does not divide `n`. Then `P` divides `expand ℤ p Q`. -/
theorem minpoly_dvd_expand {p : ℕ} (hdiv : ¬p ∣ n) : minpoly ℤ μ ∣ expand ℤ p (minpoly ℤ (μ ^ p)) :=
  by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp_all
  letI : IsIntegrallyClosed ℤ := GCDMonoid.toIsIntegrallyClosed
  refine' minpoly.isIntegrallyClosed_dvd (h.isIntegral hpos) _
  · rw [aeval_def, coe_expand, ← comp, eval₂_eq_eval_map, map_comp, Polynomial.map_pow, map_X,
      eval_comp, eval_pow, eval_X, ← eval₂_eq_eval_map, ← aeval_def]
    exact minpoly.aeval _ _
#align is_primitive_root.minpoly_dvd_expand IsPrimitiveRoot.minpoly_dvd_expand

/- Let `P` be the minimal polynomial of a root of unity `μ` and `Q` be the minimal polynomial of
`μ ^ p`, where `p` is a prime that does not divide `n`. Then `P` divides `Q ^ p` modulo `p`. -/
theorem minpoly_dvd_pow_mod {p : ℕ} [hprime : Fact p.Prime] (hdiv : ¬p ∣ n) :
    map (Int.castRingHom (ZMod p)) (minpoly ℤ μ) ∣
      map (Int.castRingHom (ZMod p)) (minpoly ℤ (μ ^ p)) ^ p := by
  set Q := minpoly ℤ (μ ^ p)
  have hfrob :
    map (Int.castRingHom (ZMod p)) Q ^ p = map (Int.castRingHom (ZMod p)) (expand ℤ p Q) := by
    rw [← ZMod.expand_card, map_expand]
  rw [hfrob]
  apply RingHom.map_dvd (mapRingHom (Int.castRingHom (ZMod p)))
  exact minpoly_dvd_expand h hdiv
#align is_primitive_root.minpoly_dvd_pow_mod IsPrimitiveRoot.minpoly_dvd_pow_mod

/- Let `P` be the minimal polynomial of a root of unity `μ` and `Q` be the minimal polynomial of
`μ ^ p`, where `p` is a prime that does not divide `n`. Then `P` divides `Q` modulo `p`. -/
theorem minpoly_dvd_mod_p {p : ℕ} [hprime : Fact p.Prime] (hdiv : ¬p ∣ n) :
    map (Int.castRingHom (ZMod p)) (minpoly ℤ μ) ∣
      map (Int.castRingHom (ZMod p)) (minpoly ℤ (μ ^ p)) :=
  (UniqueFactorizationMonoid.dvd_pow_iff_dvd_of_squarefree (squarefree_minpoly_mod h hdiv)
        hprime.1.ne_zero).1
    (minpoly_dvd_pow_mod h hdiv)
#align is_primitive_root.minpoly_dvd_mod_p IsPrimitiveRoot.minpoly_dvd_mod_p

/-- If `p` is a prime that does not divide `n`,
then the minimal polynomials of a primitive `n`-th root of unity `μ`
and of `μ ^ p` are the same. -/
theorem minpoly_eq_pow {p : ℕ} [hprime : Fact p.Prime] (hdiv : ¬p ∣ n) :
    minpoly ℤ μ = minpoly ℤ (μ ^ p) := by
  classical
  by_cases hn : n = 0
  · simp_all
  have hpos := Nat.pos_of_ne_zero hn
  by_contra hdiff
  set P := minpoly ℤ μ
  set Q := minpoly ℤ (μ ^ p)
  have Pmonic : P.monic := minpoly.monic (h.isIntegral hpos)
  have Qmonic : Q.monic := minpoly.monic ((h.pow_of_prime hprime.1 hdiv).IsIntegral hpos)
  have Pirr : Irreducible P := minpoly.irreducible (h.is_integral hpos)
  have Qirr : Irreducible Q := minpoly.irreducible ((h.pow_of_prime hprime.1 hdiv).IsIntegral hpos)
  have PQprim : is_primitive (P * Q) := Pmonic.is_primitive.mul Qmonic.is_primitive
  have prod : P * Q ∣ X ^ n - 1 := by
    rw [is_primitive.int.dvd_iff_map_cast_dvd_map_cast (P * Q) (X ^ n - 1) PQprim
        (monic_X_pow_sub_C (1 : ℤ) (ne_of_gt hpos)).IsPrimitive,
      Polynomial.map_mul]
    refine' IsCoprime.mul_dvd _ _ _
    · have aux := is_primitive.int.irreducible_iff_irreducible_map_cast Pmonic.is_primitive
      refine' (dvd_or_coprime _ _ (aux.1 Pirr)).resolve_left _
      rw [map_dvd_map (Int.castRingHom ℚ) Int.cast_injective Pmonic]
      intro hdiv
      refine' hdiff (eq_of_monic_of_associated Pmonic Qmonic _)
      exact associated_of_dvd_dvd hdiv (Pirr.dvd_symm Qirr hdiv)
    · apply (map_dvd_map (Int.castRingHom ℚ) Int.cast_injective Pmonic).2
      exact minpoly_dvd_X_pow_sub_one h
    · apply (map_dvd_map (Int.castRingHom ℚ) Int.cast_injective Qmonic).2
      exact minpoly_dvd_X_pow_sub_one (pow_of_prime h hprime.1 hdiv)
  replace prod := RingHom.map_dvd (map_ring_hom (Int.castRingHom (ZMod p))) Prod
  rw [coe_map_ring_hom, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow, map_X] at prod
  obtain ⟨R, hR⟩ := minpoly_dvd_mod_p h hdiv
  rw [hR, ← mul_assoc, ← Polynomial.map_mul, ← sq, Polynomial.map_pow] at prod
  have habs : map (Int.castRingHom (ZMod p)) P ^ 2 ∣ map (Int.castRingHom (ZMod p)) P ^ 2 * R := by
    use R
  replace habs :=
    lt_of_lt_of_le (PartENat.coe_lt_coe.2 one_lt_two)
      (multiplicity.le_multiplicity_of_pow_dvd (dvd_trans habs Prod))
  have hfree : Squarefree (X ^ n - 1 : (ZMod p)[X]) :=
    (separable_X_pow_sub_C 1 (fun h => hdiv <| (ZMod.nat_cast_zmod_eq_zero_iff_dvd n p).1 h)
        one_ne_zero).Squarefree
  cases'
    (multiplicity.squarefree_iff_multiplicity_le_one (X ^ n - 1)).1 hfree
      (map (Int.castRingHom (ZMod p)) P) with
    hle hunit
  · rw [Nat.cast_one] at habs ; exact hle.not_lt habs
  · replace hunit := degree_eq_zero_of_is_unit hunit
    rw [degree_map_eq_of_leading_coeff_ne_zero (Int.castRingHom (ZMod p)) _] at hunit
    · exact (minpoly.degree_pos (IsIntegral h hpos)).ne' hunit
    simp only [Pmonic, eq_intCast, monic.leading_coeff, Int.cast_one, Ne.def, not_false_iff,
      one_ne_zero]
#align is_primitive_root.minpoly_eq_pow IsPrimitiveRoot.minpoly_eq_pow

/-- If `m : ℕ` is coprime with `n`,
then the minimal polynomials of a primitive `n`-th root of unity `μ`
and of `μ ^ m` are the same. -/
theorem minpoly_eq_pow_coprime {m : ℕ} (hcop : Nat.coprime m n) : minpoly ℤ μ = minpoly ℤ (μ ^ m) :=
  by
  revert n hcop
  refine' UniqueFactorizationMonoid.induction_on_prime m _ _ _
  · intro n hn h
    congr
    simpa [(Nat.coprime_zero_left n).mp hn] using h
  · intro u hunit n hcop h
    congr
    simp [Nat.isUnit_iff.mp hunit]
  · intro a p ha hprime hind n hcop h
    rw [hind (Nat.coprime.coprime_mul_left hcop) h]; clear hind
    replace hprime := hprime.nat_prime
    have hdiv := (Nat.Prime.coprime_iff_not_dvd hprime).1 (Nat.coprime.coprime_mul_right hcop)
    haveI := Fact.mk hprime
    rw [minpoly_eq_pow (h.pow_of_coprime a (Nat.coprime.coprime_mul_left hcop)) hdiv]
    congr 1
    ring
#align is_primitive_root.minpoly_eq_pow_coprime IsPrimitiveRoot.minpoly_eq_pow_coprime

/-- If `m : ℕ` is coprime with `n`,
then the minimal polynomial of a primitive `n`-th root of unity `μ`
has `μ ^ m` as root. -/
theorem pow_isRoot_minpoly {m : ℕ} (hcop : Nat.coprime m n) :
    IsRoot (map (Int.castRingHom K) (minpoly ℤ μ)) (μ ^ m) := by
  simpa [minpoly_eq_pow_coprime h hcop, eval_map, aeval_def (μ ^ m) _] using minpoly.aeval ℤ (μ ^ m)
#align is_primitive_root.pow_is_root_minpoly IsPrimitiveRoot.pow_isRoot_minpoly

/-- `primitive_roots n K` is a subset of the roots of the minimal polynomial of a primitive
`n`-th root of unity `μ`. -/
theorem is_roots_of_minpoly [DecidableEq K] :
    primitiveRoots n K ⊆ (map (Int.castRingHom K) (minpoly ℤ μ)).roots.toFinset := by
  by_cases hn : n = 0; · simp_all
  have hpos := Nat.pos_of_ne_zero hn
  intro x hx
  obtain ⟨m, hle, hcop, rfl⟩ := (is_primitive_root_iff h hpos).1 ((mem_primitiveRoots hpos).1 hx)
  simpa [Multiset.mem_toFinset,
    mem_roots (map_monic_ne_zero <| minpoly.monic <| IsIntegral h hpos)] using
    pow_is_root_minpoly h hcop
#align is_primitive_root.is_roots_of_minpoly IsPrimitiveRoot.is_roots_of_minpoly

/-- The degree of the minimal polynomial of `μ` is at least `totient n`. -/
theorem totient_le_degree_minpoly : Nat.totient n ≤ (minpoly ℤ μ).natDegree := by
  classical
  let P : ℤ[X] := minpoly ℤ μ
  -- minimal polynomial of `μ`
  let P_K : K[X] := map (Int.castRingHom K) P
  -- minimal polynomial of `μ` sent to `K[X]`
  calc
    n.totient = (primitiveRoots n K).card := h.card_primitiveRoots.symm
    _ ≤ P_K.roots.toFinset.card := (Finset.card_le_of_subset (is_roots_of_minpoly h))
    _ ≤ P_K.roots.card := (Multiset.toFinset_card_le _)
    _ ≤ P_K.nat_degree := (card_roots' _)
    _ ≤ P.nat_degree := nat_degree_map_le _ _
#align is_primitive_root.totient_le_degree_minpoly IsPrimitiveRoot.totient_le_degree_minpoly

end IsDomain

end CommRing

end IsPrimitiveRoot
