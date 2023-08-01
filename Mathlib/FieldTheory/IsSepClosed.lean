/-
Copyright (c) 2020 Kenny Lau, 2023 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Jz Pan
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Separably Closed Field

In this file we define the typeclass for separably closed fields and separable closures,
and prove some of their properties.

## Main Definitions

- `IsSepClosed k` is the typeclass saying `k` is a separably closed field, i.e. every separable
polynomial in `k` splits.

- `IsSepClosure R K` is the typeclass saying `K` is a separable closure of `R`, where `R` is a
  commutative ring. This means that the map from `R` to `K` is injective, and `K` is
  separably closed and separable over `R`

## Tags

separable closure, separably closed

-/

universe u v w

open scoped Classical BigOperators Polynomial

open Polynomial

variable (k : Type u) [Field k]

/-- Typeclass for separably closed fields.

To show `Polynomial.Splits p f` for an arbitrary ring homomorphism `f`,
see `IsSepClosed.splits_codomain` and `IsSepClosed.splits_domain`.
-/
class IsSepClosed : Prop where
  splits_of_separable : ∀ p : k[X], p.Separable → (p.Splits <| RingHom.id k)

/-- Every separable polynomial splits in the field extension `f : K →+* k` if `k` is
separably closed.

See also `IsSepClosed.splits_domain` for the case where `K` is separably closed.
-/
theorem IsSepClosed.splits_codomain {k K : Type _} [Field k] [IsSepClosed k] [Field K] {f : K →+* k}
    (p : K[X]) (h : p.Separable) : p.Splits f := by
  convert IsSepClosed.splits_of_separable (p.map f) (Separable.map h); simp [splits_map_iff]

/-- Every separable polynomial splits in the field extension `f : K →+* k` if `K` is
separably closed.

See also `IsSepClosed.splits_codomain` for the case where `k` is separably closed.
-/
theorem IsSepClosed.splits_domain {k K : Type _} [Field k] [IsSepClosed k] [Field K] {f : k →+* K}
    (p : k[X]) (h : p.Separable) : p.Splits f :=
  Polynomial.splits_of_splits_id _ <| IsSepClosed.splits_of_separable _ h

namespace IsSepClosed

variable {k}

theorem exists_root [IsSepClosed k] (p : k[X]) (hp : p.degree ≠ 0) (hsep : p.Separable) :
    ∃ x, IsRoot p x :=
  exists_root_of_splits _ (IsSepClosed.splits_of_separable p hsep) hp

theorem exists_pow_nat_eq [IsSepClosed k] (x : k) {n : ℕ} (hn : (n : k) ≠ 0) : ∃ z, z ^ n = x := by
  have hn' : 0 < n := Nat.pos_of_ne_zero <| fun h => by
    rw [h, Nat.cast_zero] at hn
    exact hn rfl
  have : degree (X ^ n - C x) ≠ 0 := by
    rw [degree_X_pow_sub_C hn' x]
    exact ne_of_gt (WithBot.coe_lt_coe.2 hn')
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, pow_eq_zero_iff hn']⟩
  · obtain ⟨z, hz⟩ := exists_root _ this <| separable_X_pow_sub_C x hn hx
    use z
    simp only [eval_C, eval_X, eval_pow, eval_sub, IsRoot.def] at hz
    exact sub_eq_zero.1 hz

theorem exists_eq_mul_self [IsSepClosed k] (x : k) (h2 : (2 : k) ≠ 0) : ∃ z, x = z * z := by
  rcases exists_pow_nat_eq x h2 with ⟨z, rfl⟩
  exact ⟨z, sq z⟩

theorem roots_eq_zero_iff [IsSepClosed k] {p : k[X]} (hsep : p.Separable) :
    p.roots = 0 ↔ p = Polynomial.C (p.coeff 0) := by
  refine' ⟨fun h => _, fun hp => by rw [hp, roots_C]⟩
  cases' le_or_lt (degree p) 0 with hd hd
  · exact eq_C_of_degree_le_zero hd
  · obtain ⟨z, hz⟩ := IsSepClosed.exists_root p hd.ne' hsep
    rw [← mem_roots (ne_zero_of_degree_gt hd), h] at hz
    simp at hz

theorem exists_eval₂_eq_zero_of_injective {R : Type _} [CommRing R] [IsSepClosed k] (f : R →+* k)
    (hf : Function.Injective f) (p : R[X]) (hp : p.degree ≠ 0) (hsep : p.Separable) :
    ∃ x, p.eval₂ f x = 0 :=
  let ⟨x, hx⟩ := exists_root (p.map f) (by rwa [degree_map_eq_of_injective hf]) (Separable.map hsep)
  ⟨x, by rwa [eval₂_eq_eval_map, ← IsRoot]⟩

theorem exists_eval₂_eq_zero {R : Type _} [Field R] [IsSepClosed k] (f : R →+* k) (p : R[X])
    (hp : p.degree ≠ 0) (hsep : p.Separable) : ∃ x, p.eval₂ f x = 0 :=
  exists_eval₂_eq_zero_of_injective f f.injective p hp hsep

variable (k)

theorem exists_aeval_eq_zero_of_injective {R : Type _} [CommRing R] [IsSepClosed k] [Algebra R k]
    (hinj : Function.Injective (algebraMap R k)) (p : R[X]) (hp : p.degree ≠ 0)
    (hsep : p.Separable) : ∃ x : k, aeval x p = 0 :=
  exists_eval₂_eq_zero_of_injective (algebraMap R k) hinj p hp hsep

theorem exists_aeval_eq_zero {R : Type _} [Field R] [IsSepClosed k] [Algebra R k] (p : R[X])
    (hp : p.degree ≠ 0) (hsep : p.Separable) : ∃ x : k, aeval x p = 0 :=
  exists_eval₂_eq_zero (algebraMap R k) p hp hsep

theorem of_exists_root (H : ∀ p : k[X], p.Monic → Irreducible p → Separable p → ∃ x, p.eval x = 0) :
    IsSepClosed k := by
  refine ⟨fun p ↦ (fun hsep ↦ Or.inr ?_)⟩
  intro q hq hdvd
  simp only [map_id] at hdvd 
  have hlc : IsUnit (leadingCoeff q)⁻¹ := IsUnit.inv <| Ne.isUnit <|
    leadingCoeff_ne_zero.2 <| Irreducible.ne_zero hq
  have hsep' : Separable (q * C (leadingCoeff q)⁻¹) :=
    Separable.mul (Separable.of_dvd hsep hdvd) ((separable_C _).2 hlc)
    (by simpa only [← isCoprime_mul_unit_right_right (isUnit_C.2 hlc) q 1, one_mul]
      using isCoprime_one_right (x := q))
  have hirr' := hq
  rw [← irreducible_mul_isUnit (isUnit_C.2 hlc)] at hirr'
  obtain ⟨x, hx⟩ := H (q * C (leadingCoeff q)⁻¹) (monic_mul_leadingCoeff_inv hq.ne_zero) hirr' hsep'
  exact degree_mul_leadingCoeff_inv q hq.ne_zero ▸ degree_eq_one_of_irreducible_of_root hirr' hx

theorem degree_eq_one_of_irreducible [IsSepClosed k] {p : k[X]}
    (hp : Irreducible p) (hsep : p.Separable) : p.degree = 1 :=
  degree_eq_one_of_irreducible_of_splits hp (IsSepClosed.splits_codomain p hsep)

theorem algebraMap_surjective_of_isIntegral {k K : Type _} [Field k] [Ring K] [IsDomain K]
    [hk : IsSepClosed k] [Algebra k K] [IsSeparable k K] (hf : Algebra.IsIntegral k K) :
    Function.Surjective (algebraMap k K) := by
  refine' fun x => ⟨-(minpoly k x).coeff 0, _⟩
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic (hf x)
  have hsep : (minpoly k x).Separable := IsSeparable.separable k x
  have h : (minpoly k x).degree = 1 :=
    degree_eq_one_of_irreducible k (minpoly.irreducible (hf x)) hsep
  have : aeval x (minpoly k x) = 0 := minpoly.aeval k x
  rw [eq_X_add_C_of_degree_eq_one h, hq, C_1, one_mul, aeval_add, aeval_X, aeval_C,
    add_eq_zero_iff_eq_neg] at this
  exact (RingHom.map_neg (algebraMap k K) ((minpoly k x).coeff 0)).symm ▸ this.symm

theorem algebraMap_surjective_of_isAlgebraic {k K : Type _} [Field k] [Ring K] [IsDomain K]
    [IsSepClosed k] [Algebra k K] [IsSeparable k K] (hf : Algebra.IsAlgebraic k K) :
    Function.Surjective (algebraMap k K) :=
  algebraMap_surjective_of_isIntegral (Algebra.isAlgebraic_iff_isIntegral.mp hf)

end IsSepClosed

/-- Typeclass for an extension being a separable closure. -/
class IsSepClosure (R : Type u) (K : Type v) [CommRing R] [Field K] [Algebra R K]
    [NoZeroSMulDivisors R K] : Prop where
  sep_closed : IsSepClosed K
  separable : IsSeparable R K

theorem isSepClosure_iff (K : Type v) [Field K] [Algebra k K] :
    IsSepClosure k K ↔ IsSepClosed K ∧ IsSeparable k K :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

instance (priority := 100) IsSepClosure.normal (R K : Type _) [Field R] [Field K] [Algebra R K]
    [IsSepClosure R K] : Normal R K :=
  ⟨fun x => by apply IsIntegral.isAlgebraic; exact IsSepClosure.separable.isIntegral' x,
    fun x => @IsSepClosed.splits_codomain _ _ _ (IsSepClosure.sep_closed R) _ _ _ (by
      have : IsSeparable R K := IsSepClosure.separable
      exact IsSeparable.separable R x)⟩
