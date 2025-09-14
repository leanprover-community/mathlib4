/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin
-/
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

/-!
# Minimal polynomial of roots of unity

We gather several results about minimal polynomial of root of unity.

## Main results

* `IsPrimitiveRoot.totient_le_degree_minpoly`: The degree of the minimal polynomial of an `n`-th
  primitive root of unity is at least `totient n`.

-/


open minpoly Polynomial

open scoped Polynomial

namespace IsPrimitiveRoot

section CommRing

variable {n : ℕ} {K : Type*} [CommRing K] {μ : K} (h : IsPrimitiveRoot μ n)
include h

/-- `μ` is integral over `ℤ`. -/
-- Porting note: `hpos` was in the `variable` line, with an `omit` in mathlib3 just after this
-- declaration. For some reason, in Lean4, `hpos` gets included also in the declarations below,
-- even if it is not used in the proof.
theorem isIntegral (hpos : 0 < n) : IsIntegral ℤ μ := by
  use X ^ n - 1
  constructor
  · exact monic_X_pow_sub_C 1 (ne_of_lt hpos).symm
  · simp only [((IsPrimitiveRoot.iff_def μ n).mp h).left, eval₂_one, eval₂_X_pow, eval₂_sub,
      sub_self]

section IsDomain

variable [IsDomain K] [CharZero K]

/-- The minimal polynomial of a root of unity `μ` divides `X ^ n - 1`. -/
theorem minpoly_dvd_x_pow_sub_one : minpoly ℤ μ ∣ X ^ n - 1 := by
  rcases n.eq_zero_or_pos with (rfl | h0)
  · simp
  apply minpoly.isIntegrallyClosed_dvd (isIntegral h h0)
  simp only [((IsPrimitiveRoot.iff_def μ n).mp h).left, aeval_X_pow,
    aeval_one, map_sub, sub_self]

/-- The reduction modulo `p` of the minimal polynomial of a root of unity `μ` is separable. -/
theorem separable_minpoly_mod {p : ℕ} [Fact p.Prime] (hdiv : ¬p ∣ n) :
    Separable (map (Int.castRingHom (ZMod p)) (minpoly ℤ μ)) := by
  have hdvd : map (Int.castRingHom (ZMod p)) (minpoly ℤ μ) ∣ X ^ n - 1 := by
    convert _root_.map_dvd (mapRingHom (Int.castRingHom (ZMod p)))
        (minpoly_dvd_x_pow_sub_one h)
    simp only [map_sub, map_pow, coe_mapRingHom, map_X, map_one]
  refine Separable.of_dvd (separable_X_pow_sub_C 1 ?_ one_ne_zero) hdvd
  by_contra hzero
  exact hdiv ((ZMod.natCast_eq_zero_iff n p).1 hzero)

/-- The reduction modulo `p` of the minimal polynomial of a root of unity `μ` is squarefree. -/
theorem squarefree_minpoly_mod {p : ℕ} [Fact p.Prime] (hdiv : ¬p ∣ n) :
    Squarefree (map (Int.castRingHom (ZMod p)) (minpoly ℤ μ)) :=
  (separable_minpoly_mod h hdiv).squarefree

/-- Let `P` be the minimal polynomial of a root of unity `μ` and `Q` be the minimal polynomial of
`μ ^ p`, where `p` is a natural number that does not divide `n`. Then `P` divides `expand ℤ p Q`. -/
theorem minpoly_dvd_expand {p : ℕ} (hdiv : ¬p ∣ n) :
    minpoly ℤ μ ∣ expand ℤ p (minpoly ℤ (μ ^ p)) := by
  rcases n.eq_zero_or_pos with (rfl | hpos)
  · simp_all
  letI : IsIntegrallyClosed ℤ := GCDMonoid.toIsIntegrallyClosed
  refine minpoly.isIntegrallyClosed_dvd (h.isIntegral hpos) ?_
  rw [aeval_def, coe_expand, ← comp, eval₂_eq_eval_map, map_comp, Polynomial.map_pow, map_X,
    eval_comp, eval_pow, eval_X, ← eval₂_eq_eval_map, ← aeval_def]
  exact minpoly.aeval _ _

/-- Let `P` be the minimal polynomial of a root of unity `μ` and `Q` be the minimal polynomial of
`μ ^ p`, where `p` is a prime that does not divide `n`. Then `P` divides `Q ^ p` modulo `p`. -/
theorem minpoly_dvd_pow_mod {p : ℕ} [hprime : Fact p.Prime] (hdiv : ¬p ∣ n) :
    map (Int.castRingHom (ZMod p)) (minpoly ℤ μ) ∣
      map (Int.castRingHom (ZMod p)) (minpoly ℤ (μ ^ p)) ^ p := by
  set Q := minpoly ℤ (μ ^ p)
  have hfrob :
    map (Int.castRingHom (ZMod p)) Q ^ p = map (Int.castRingHom (ZMod p)) (expand ℤ p Q) := by
    rw [← ZMod.expand_card, map_expand]
  rw [hfrob]
  apply _root_.map_dvd (mapRingHom (Int.castRingHom (ZMod p)))
  exact minpoly_dvd_expand h hdiv

/-- Let `P` be the minimal polynomial of a root of unity `μ` and `Q` be the minimal polynomial of
`μ ^ p`, where `p` is a prime that does not divide `n`. Then `P` divides `Q` modulo `p`. -/
theorem minpoly_dvd_mod_p {p : ℕ} [Fact p.Prime] (hdiv : ¬p ∣ n) :
    map (Int.castRingHom (ZMod p)) (minpoly ℤ μ) ∣
      map (Int.castRingHom (ZMod p)) (minpoly ℤ (μ ^ p)) :=
  (squarefree_minpoly_mod h hdiv).isRadical _ _ (minpoly_dvd_pow_mod h hdiv)

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
  have Pmonic : P.Monic := minpoly.monic (h.isIntegral hpos)
  have Qmonic : Q.Monic := minpoly.monic ((h.pow_of_prime hprime.1 hdiv).isIntegral hpos)
  have Pirr : Irreducible P := minpoly.irreducible (h.isIntegral hpos)
  have Qirr : Irreducible Q := minpoly.irreducible ((h.pow_of_prime hprime.1 hdiv).isIntegral hpos)
  have PQprim : IsPrimitive (P * Q) := Pmonic.isPrimitive.mul Qmonic.isPrimitive
  have prod : P * Q ∣ X ^ n - 1 := by
    rw [IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast (P * Q) (X ^ n - 1) PQprim
        (monic_X_pow_sub_C (1 : ℤ) (ne_of_gt hpos)).isPrimitive,
      Polynomial.map_mul]
    refine IsCoprime.mul_dvd ?_ ?_ ?_
    · have aux := IsPrimitive.Int.irreducible_iff_irreducible_map_cast Pmonic.isPrimitive
      refine (dvd_or_isCoprime _ _ (aux.1 Pirr)).resolve_left ?_
      rw [map_dvd_map (Int.castRingHom ℚ) Int.cast_injective Pmonic]
      intro hdiv
      refine hdiff (eq_of_monic_of_associated Pmonic Qmonic ?_)
      exact associated_of_dvd_dvd hdiv (Pirr.dvd_symm Qirr hdiv)
    · apply (map_dvd_map (Int.castRingHom ℚ) Int.cast_injective Pmonic).2
      exact minpoly_dvd_x_pow_sub_one h
    · apply (map_dvd_map (Int.castRingHom ℚ) Int.cast_injective Qmonic).2
      exact minpoly_dvd_x_pow_sub_one (pow_of_prime h hprime.1 hdiv)
  replace prod := _root_.map_dvd (mapRingHom (Int.castRingHom (ZMod p))) prod
  rw [coe_mapRingHom, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow, map_X] at prod
  obtain ⟨R, hR⟩ := minpoly_dvd_mod_p h hdiv
  rw [hR, ← mul_assoc, ← Polynomial.map_mul, ← sq, Polynomial.map_pow] at prod
  have habs : map (Int.castRingHom (ZMod p)) P ^ 2 ∣ map (Int.castRingHom (ZMod p)) P ^ 2 * R := by
    use R
  replace habs :=
    lt_of_lt_of_le (Nat.cast_lt.2 one_lt_two)
      (le_emultiplicity_of_pow_dvd (dvd_trans habs prod))
  have hfree : Squarefree (X ^ n - 1 : (ZMod p)[X]) :=
    (separable_X_pow_sub_C 1 (fun h => hdiv <| (ZMod.natCast_eq_zero_iff n p).1 h)
        one_ne_zero).squarefree
  rcases (squarefree_iff_emultiplicity_le_one (X ^ n - 1)).1 hfree
      (map (Int.castRingHom (ZMod p)) P) with hle | hunit
  · rw [Nat.cast_one] at habs; exact hle.not_gt habs
  · replace hunit := degree_eq_zero_of_isUnit hunit
    rw [degree_map_eq_of_leadingCoeff_ne_zero (Int.castRingHom (ZMod p)) _] at hunit
    · exact (minpoly.degree_pos (isIntegral h hpos)).ne' hunit
    simp only [Pmonic, eq_intCast, Monic.leadingCoeff, Int.cast_one, Ne, not_false_iff,
      one_ne_zero]

/-- If `m : ℕ` is coprime with `n`,
then the minimal polynomials of a primitive `n`-th root of unity `μ`
and of `μ ^ m` are the same. -/
theorem minpoly_eq_pow_coprime {m : ℕ} (hcop : Nat.Coprime m n) :
    minpoly ℤ μ = minpoly ℤ (μ ^ m) := by
  revert n hcop
  refine UniqueFactorizationMonoid.induction_on_prime m ?_ ?_ ?_
  · intro h hn
    congr
    simpa [(Nat.coprime_zero_left _).mp hn] using h
  · intro u hunit _ _
    congr
    simp [Nat.isUnit_iff.mp hunit]
  · intro a p _ hprime hind h hcop
    rw [hind h (Nat.Coprime.coprime_mul_left hcop)]; clear hind
    replace hprime := hprime.nat_prime
    have hdiv := (Nat.Prime.coprime_iff_not_dvd hprime).1 (Nat.Coprime.coprime_mul_right hcop)
    haveI := Fact.mk hprime
    rw [minpoly_eq_pow (h.pow_of_coprime a (Nat.Coprime.coprime_mul_left hcop)) hdiv]
    congr 1
    ring

/-- If `m : ℕ` is coprime with `n`,
then the minimal polynomial of a primitive `n`-th root of unity `μ`
has `μ ^ m` as root. -/
theorem pow_isRoot_minpoly {m : ℕ} (hcop : Nat.Coprime m n) :
    IsRoot (map (Int.castRingHom K) (minpoly ℤ μ)) (μ ^ m) := by
  simp only [minpoly_eq_pow_coprime h hcop, IsRoot.def, eval_map]
  exact minpoly.aeval ℤ (μ ^ m)

/-- `primitiveRoots n K` is a subset of the roots of the minimal polynomial of a primitive
`n`-th root of unity `μ`. -/
theorem is_roots_of_minpoly [DecidableEq K] :
    primitiveRoots n K ⊆ (map (Int.castRingHom K) (minpoly ℤ μ)).roots.toFinset := by
  by_cases hn : n = 0; · simp_all
  have : NeZero n := ⟨hn⟩
  have hpos := Nat.pos_of_ne_zero hn
  intro x hx
  obtain ⟨m, _, hcop, rfl⟩ := (isPrimitiveRoot_iff h).1 ((mem_primitiveRoots hpos).1 hx)
  simp only [Multiset.mem_toFinset]
  convert pow_isRoot_minpoly h hcop using 0
  rw [← mem_roots]
  exact map_monic_ne_zero <| minpoly.monic <| isIntegral h hpos

/-- The degree of the minimal polynomial of `μ` is at least `totient n`. -/
theorem totient_le_degree_minpoly : Nat.totient n ≤ (minpoly ℤ μ).natDegree := by
  classical
  let P : ℤ[X] := minpoly ℤ μ
  -- minimal polynomial of `μ`
  let P_K : K[X] := map (Int.castRingHom K) P
  -- minimal polynomial of `μ` sent to `K[X]`
  calc
    n.totient = (primitiveRoots n K).card := h.card_primitiveRoots.symm
    _ ≤ P_K.roots.toFinset.card := Finset.card_le_card (is_roots_of_minpoly h)
    _ ≤ Multiset.card P_K.roots := Multiset.toFinset_card_le _
    _ ≤ P_K.natDegree := card_roots' _
    _ ≤ P.natDegree := natDegree_map_le

end IsDomain

end CommRing

end IsPrimitiveRoot
