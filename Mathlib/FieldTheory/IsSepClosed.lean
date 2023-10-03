/-
Copyright (c) 2023 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Separably Closed Field

In this file we define the typeclass for separably closed fields and separable closures,
and prove some of their properties.

## Main Definitions

- `IsSepClosed k` is the typeclass saying `k` is a separably closed field, i.e. every separable
  polynomial in `k` splits.

- `IsSepClosure k K` is the typeclass saying `K` is a separable closure of `k`, where `k` is a
  field. This means that `K` is separably closed and separable over `k`.

- `IsSepClosed.lift` is a map from a separable extension `L` of `K`, into any separably
  closed extension `M` of `K`.

- `IsSepClosure.equiv` is a proof that any two separable closures of the
  same field are isomorphic.

## Tags

separable closure, separably closed

## TODO

- Maximal separable subextension of `K/k`, consisting of all elements of `K` which are separable
  over `k`.

- If `K` is a separably closed field containing `k`, then the maximal separable subextension
  of `K/k` is a separable closure of `k`.

- In particular, a separable closure exists.

- If `k` is a perfect field, then its separable closure coincides with its algebraic closure.

- An algebraic extension of a separably closed field is purely inseparable.

-/

universe u v w

open scoped Classical BigOperators Polynomial

open Polynomial

variable (k : Type u) [Field k] (K : Type v) [Field K]

/-- Typeclass for separably closed fields.

To show `Polynomial.Splits p f` for an arbitrary ring homomorphism `f`,
see `IsSepClosed.splits_codomain` and `IsSepClosed.splits_domain`.
-/
class IsSepClosed : Prop where
  splits_of_separable : ∀ p : k[X], p.Separable → (p.Splits <| RingHom.id k)

/-- An algebraically closed field is also separably closed. -/
instance IsSepClosed.of_isAlgClosed [IsAlgClosed k] : IsSepClosed k :=
  ⟨fun p _ => IsAlgClosed.splits p⟩

variable {k} {K}

/-- Every separable polynomial splits in the field extension `f : k →+* K` if `K` is
separably closed.

See also `IsSepClosed.splits_domain` for the case where `k` is separably closed.
-/
theorem IsSepClosed.splits_codomain [IsSepClosed K] {f : k →+* K}
    (p : k[X]) (h : p.Separable) : p.Splits f := by
  convert IsSepClosed.splits_of_separable (p.map f) (Separable.map h); simp [splits_map_iff]

/-- Every separable polynomial splits in the field extension `f : k →+* K` if `k` is
separably closed.

See also `IsSepClosed.splits_codomain` for the case where `k` is separably closed.
-/
theorem IsSepClosed.splits_domain [IsSepClosed k] {f : k →+* K}
    (p : k[X]) (h : p.Separable) : p.Splits f :=
  Polynomial.splits_of_splits_id _ <| IsSepClosed.splits_of_separable _ h

namespace IsSepClosed

theorem exists_root [IsSepClosed k] (p : k[X]) (hp : p.degree ≠ 0) (hsep : p.Separable) :
    ∃ x, IsRoot p x :=
  exists_root_of_splits _ (IsSepClosed.splits_of_separable p hsep) hp

theorem exists_pow_nat_eq [IsSepClosed k] (x : k) (n : ℕ) [hn : NeZero (n : k)] :
    ∃ z, z ^ n = x := by
  have hn' : 0 < n := Nat.pos_of_ne_zero <| fun h => by
    rw [h, Nat.cast_zero] at hn
    exact hn.out rfl
  have : degree (X ^ n - C x) ≠ 0 := by
    rw [degree_X_pow_sub_C hn' x]
    exact (WithBot.coe_lt_coe.2 hn').ne'
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, pow_eq_zero_iff hn']⟩
  · obtain ⟨z, hz⟩ := exists_root _ this <| separable_X_pow_sub_C x hn.out hx
    use z
    simpa [eval_C, eval_X, eval_pow, eval_sub, IsRoot.def, sub_eq_zero] using hz

theorem exists_eq_mul_self [IsSepClosed k] (x : k) [h2 : NeZero (2 : k)] : ∃ z, x = z * z := by
  rcases exists_pow_nat_eq x 2 with ⟨z, rfl⟩
  exact ⟨z, sq z⟩

theorem roots_eq_zero_iff [IsSepClosed k] {p : k[X]} (hsep : p.Separable) :
    p.roots = 0 ↔ p = Polynomial.C (p.coeff 0) := by
  refine' ⟨fun h => _, fun hp => by rw [hp, roots_C]⟩
  cases' le_or_lt (degree p) 0 with hd hd
  · exact eq_C_of_degree_le_zero hd
  · obtain ⟨z, hz⟩ := IsSepClosed.exists_root p hd.ne' hsep
    rw [← mem_roots (ne_zero_of_degree_gt hd), h] at hz
    simp at hz

theorem exists_eval₂_eq_zero [IsSepClosed K] (f : k →+* K)
    (p : k[X]) (hp : p.degree ≠ 0) (hsep : p.Separable) :
    ∃ x, p.eval₂ f x = 0 :=
  let ⟨x, hx⟩ := exists_root (p.map f) (by rwa [degree_map_eq_of_injective f.injective])
    (Separable.map hsep)
  ⟨x, by rwa [eval₂_eq_eval_map, ← IsRoot]⟩

variable (K)

theorem exists_aeval_eq_zero [IsSepClosed K] [Algebra k K] (p : k[X])
    (hp : p.degree ≠ 0) (hsep : p.Separable) : ∃ x : K, aeval x p = 0 :=
  exists_eval₂_eq_zero (algebraMap k K) p hp hsep

variable (k) {K}

theorem of_exists_root (H : ∀ p : k[X], p.Monic → Irreducible p → Separable p → ∃ x, p.eval x = 0) :
    IsSepClosed k := by
  refine ⟨fun p hsep ↦ Or.inr ?_⟩
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

variable {k}

theorem algebraMap_surjective
    [IsSepClosed k] [Algebra k K] [IsSeparable k K] :
    Function.Surjective (algebraMap k K) := by
  refine fun x => ⟨-(minpoly k x).coeff 0, ?_⟩
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic (IsSeparable.isIntegral k x)
  have hsep : (minpoly k x).Separable := IsSeparable.separable k x
  have h : (minpoly k x).degree = 1 :=
    degree_eq_one_of_irreducible k (minpoly.irreducible (IsSeparable.isIntegral k x)) hsep
  have : aeval x (minpoly k x) = 0 := minpoly.aeval k x
  rw [eq_X_add_C_of_degree_eq_one h, hq, C_1, one_mul, aeval_add, aeval_X, aeval_C,
    add_eq_zero_iff_eq_neg] at this
  exact (RingHom.map_neg (algebraMap k K) ((minpoly k x).coeff 0)).symm ▸ this.symm

end IsSepClosed

variable (k) (K)

/-- Typeclass for an extension being a separable closure. -/
class IsSepClosure [Algebra k K] : Prop where
  sep_closed : IsSepClosed K
  separable : IsSeparable k K

/-- A separably closed field is its separable closure. -/
instance IsSepClosure.self_of_isSepClosed [IsSepClosed k] : IsSepClosure k k :=
  ⟨by assumption, isSeparable_self k⟩

variable {k} {K}

theorem isSepClosure_iff [Algebra k K] :
    IsSepClosure k K ↔ IsSepClosed K ∧ IsSeparable k K :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

-- TODO: move to suitable file
instance IsSeparable.isAlgebraic [Algebra k K] [IsSeparable k K] : Algebra.IsAlgebraic k K :=
  fun x => IsIntegral.isAlgebraic k <| IsSeparable.isIntegral' x

namespace IsSepClosure

instance isSeparable [Algebra k K] [IsSepClosure k K] : IsSeparable k K :=
  IsSepClosure.separable

instance isAlgebraic [Algebra k K] [IsSepClosure k K] : Algebra.IsAlgebraic k K :=
  IsSeparable.isAlgebraic

instance (priority := 100) normal [Algebra k K] [IsSepClosure k K] : Normal k K :=
  ⟨isAlgebraic,
    fun x => @IsSepClosed.splits_codomain _ _ _ _ (IsSepClosure.sep_closed k) _ _
      (have : IsSeparable k K := IsSepClosure.separable; IsSeparable.separable k x)⟩

end IsSepClosure

namespace IsSepClosed

open IsAlgClosed lift SubfieldWithHom

variable {K : Type u} {L : Type v} {M : Type w} [Field K] [Field L] [Algebra K L] [Field M]
  [Algebra K M] [IsSepClosed M] [IsSeparable K L]

-- porting note: this was much faster in lean 3
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem maximalSubfieldWithHom_eq_top : (maximalSubfieldWithHom K L M).carrier = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hL : Algebra.IsAlgebraic K L := IsSeparable.isAlgebraic
  let N : Subalgebra K L := (maximalSubfieldWithHom K L M).carrier
  letI : Field N := (Subalgebra.isField_of_algebraic N IsSeparable.isAlgebraic).toField
  letI : Algebra N M := (maximalSubfieldWithHom K L M).emb.toRingHom.toAlgebra
  haveI : IsSeparable N L := isSeparable_tower_top_of_isSeparable K N L
  obtain ⟨y, hy⟩ := IsSepClosed.exists_aeval_eq_zero M (minpoly N x)
    (minpoly.degree_pos
      (isAlgebraic_iff_isIntegral.1 (Algebra.isAlgebraic_of_larger_base _ hL x))).ne'
    (IsSeparable.separable N x)
  let O : Subalgebra N L := Algebra.adjoin N {(x : L)}
  letI : Algebra N O := Subalgebra.algebra O
  -- Porting note: there are some tricky unfolds going on here:
  -- (O.restrictScalars K : Type*) is identified with (O : Type*) in a few places
  let larger_emb : O →ₐ[N] M := Algebra.adjoin.liftSingleton N x y hy
  let larger_emb' : O →ₐ[K] M := AlgHom.restrictScalars K (S := N) (A := O) (B := M) larger_emb
  have hNO : N ≤ O.restrictScalars K := by
    intro z hz
    show algebraMap N L ⟨z, hz⟩ ∈ O
    exact O.algebraMap_mem _
  let O' : SubfieldWithHom K L M :=
    ⟨O.restrictScalars K, larger_emb'⟩
  have hO' : maximalSubfieldWithHom K L M ≤ O' := by
    refine' ⟨hNO, _⟩
    intro z
    -- Porting note: have to help Lean unfold even more here
    show Algebra.adjoin.liftSingleton N x y hy (@algebraMap N O _ _ (Subalgebra.algebra O) z) =
        algebraMap N M z
    exact AlgHom.commutes _ _
  refine' (maximalSubfieldWithHom_is_maximal K L M O' hO').fst _
  show x ∈ Algebra.adjoin N {(x : L)}
  exact Algebra.subset_adjoin (Set.mem_singleton x)

/-- A (random) homomorphism from a separable extension L of K into a separably
  closed extension M of K. -/
noncomputable irreducible_def lift : L →ₐ[K] M := by
  exact (maximalSubfieldWithHom K L M).emb.comp <|
    (maximalSubfieldWithHom_eq_top (K := K) (L := L) (M := M)).symm
      ▸ Algebra.toTop

end IsSepClosed

namespace IsSepClosure

variable (K : Type u) [Field K] (L : Type v) (M : Type w) [Field L] [Field M]
variable [Algebra K M] [IsSepClosure K M]
variable [Algebra K L] [IsSepClosure K L]

/-- A (random) isomorphism between two separable closures of `K`. -/
noncomputable def equiv : L ≃ₐ[K] M :=
  -- Porting note: added to replace local instance above
  haveI : IsSepClosed M := IsSepClosure.sep_closed K
  haveI : IsSeparable K L := IsSepClosure.separable
  let f : L →ₐ[K] M := IsSepClosed.lift
  AlgEquiv.ofBijective f
    ⟨RingHom.injective f.toRingHom, by
      letI : Algebra L M := RingHom.toAlgebra f
      haveI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq <| by
        simp only [RingHom.algebraMap_toAlgebra, RingHom.coe_coe, AlgHom.commutes, forall_const]
      haveI : IsSepClosed L := IsSepClosure.sep_closed K
      haveI : IsSeparable K M := IsSepClosure.separable
      haveI : IsSeparable L M := isSeparable_tower_top_of_isSeparable K L M
      show Function.Surjective (algebraMap L M)
      exact IsSepClosed.algebraMap_surjective⟩

end IsSepClosure
