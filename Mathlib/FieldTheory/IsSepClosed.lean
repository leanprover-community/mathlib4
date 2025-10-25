/-
Copyright (c) 2023 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.Galois.Basic

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

- `IsSepClosure.isAlgClosure_of_perfectField`, `IsSepClosure.of_isAlgClosure_of_perfectField`:
  if `k` is a perfect field, then its separable closure coincides with its algebraic closure.

## Tags

separable closure, separably closed

## Related

- `separableClosure`: maximal separable subextension of `K/k`, consisting of all elements of `K`
  which are separable over `k`.

- `separableClosure.isSepClosure`: if `K` is a separably closed field containing `k`, then the
  maximal separable subextension of `K/k` is a separable closure of `k`.

- In particular, a separable closure (`SeparableClosure`) exists.

- `Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed`: an algebraic extension of a separably
  closed field is purely inseparable.

-/

universe u v w

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
  ⟨fun p _ ↦ IsAlgClosed.splits p⟩

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

/-- If `n ≥ 2` equals zero in a separably closed field `k`, `b ≠ 0`,
then there exists `x` in `k` such that `a * x ^ n + b * x + c = 0`. -/
theorem exists_root_C_mul_X_pow_add_C_mul_X_add_C
    [IsSepClosed k] {n : ℕ} (a b c : k) (hn : (n : k) = 0) (hn' : 2 ≤ n) (hb : b ≠ 0) :
    ∃ x, a * x ^ n + b * x + c = 0 := by
  let f : k[X] := C a * X ^ n + C b * X + C c
  have hdeg : f.degree ≠ 0 := degree_ne_of_natDegree_ne <| by
    by_cases ha : a = 0
    · suffices f.natDegree = 1 from this ▸ one_ne_zero
      simp_rw [f, ha, map_zero, zero_mul, zero_add]
      compute_degree!
    · suffices f.natDegree = n from this ▸ (lt_of_lt_of_le zero_lt_two hn').ne'
      simp_rw [f]
      have h0 : n ≠ 0 := by linarith only [hn']
      have h1 : n ≠ 1 := by linarith only [hn']
      have : 1 ≤ n := le_trans one_le_two hn'
      compute_degree!
      simp [h0, h1, ha]
  have hsep : f.Separable := separable_C_mul_X_pow_add_C_mul_X_add_C a b c hn hb.isUnit
  obtain ⟨x, hx⟩ := exists_root f hdeg hsep
  exact ⟨x, by simpa [f] using hx⟩

/-- If a separably closed field `k` is of characteristic `p`, `n ≥ 2` is such that `p ∣ n`, `b ≠ 0`,
then there exists `x` in `k` such that `a * x ^ n + b * x + c = 0`. -/
theorem exists_root_C_mul_X_pow_add_C_mul_X_add_C'
    [IsSepClosed k] (p n : ℕ) (a b c : k) [CharP k p] (hn : p ∣ n) (hn' : 2 ≤ n) (hb : b ≠ 0) :
    ∃ x, a * x ^ n + b * x + c = 0 :=
  exists_root_C_mul_X_pow_add_C_mul_X_add_C a b c ((CharP.cast_eq_zero_iff k p n).2 hn) hn' hb

variable (k) in
/-- A separably closed perfect field is also algebraically closed. -/
instance (priority := 100) isAlgClosed_of_perfectField [IsSepClosed k] [PerfectField k] :
    IsAlgClosed k :=
  IsAlgClosed.of_exists_root k fun p _ h ↦ exists_root p ((degree_pos_of_irreducible h).ne')
    (PerfectField.separable_of_irreducible h)

theorem exists_pow_nat_eq [IsSepClosed k] (x : k) (n : ℕ) [hn : NeZero (n : k)] :
    ∃ z, z ^ n = x := by
  have hn' : 0 < n := Nat.pos_of_ne_zero fun h => by
    rw [h, Nat.cast_zero] at hn
    exact hn.out rfl
  have : degree (X ^ n - C x) ≠ 0 := by
    rw [degree_X_pow_sub_C hn' x]
    exact (WithBot.coe_lt_coe.2 hn').ne'
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, pow_eq_zero_iff hn'.ne']⟩
  · obtain ⟨z, hz⟩ := exists_root _ this <| separable_X_pow_sub_C x hn.out hx
    use z
    simpa [eval_C, eval_X, eval_pow, eval_sub, IsRoot.def, sub_eq_zero] using hz

theorem exists_eq_mul_self [IsSepClosed k] (x : k) [h2 : NeZero (2 : k)] : ∃ z, x = z * z := by
  rcases exists_pow_nat_eq x 2 with ⟨z, rfl⟩
  exact ⟨z, sq z⟩

theorem roots_eq_zero_iff [IsSepClosed k] {p : k[X]} (hsep : p.Separable) :
    p.roots = 0 ↔ p = Polynomial.C (p.coeff 0) := by
  refine ⟨fun h => ?_, fun hp => by rw [hp, roots_C]⟩
  rcases le_or_gt (degree p) 0 with hd | hd
  · exact eq_C_of_degree_le_zero hd
  · obtain ⟨z, hz⟩ := IsSepClosed.exists_root p hd.ne' hsep
    rw [← mem_roots (ne_zero_of_degree_gt hd), h] at hz
    simp at hz

theorem exists_eval₂_eq_zero_of_injective {k : Type*} [CommSemiring k] [IsSepClosed K] (f : k →+* K)
    (hf : Function.Injective f) (p : k[X]) (hp : p.degree ≠ 0) (hsep : p.Separable) :
    ∃ x, p.eval₂ f x = 0 :=
  let ⟨x, hx⟩ := exists_root (p.map f) (by rwa [degree_map_eq_of_injective hf])
    (Separable.map hsep)
  ⟨x, by rwa [eval₂_eq_eval_map, ← IsRoot]⟩

theorem exists_eval₂_eq_zero {k : Type*} [CommRing k] [IsSimpleRing k] [IsSepClosed K] (f : k →+* K)
    (p : k[X]) (hp : p.degree ≠ 0) (hsep : p.Separable) : ∃ x, p.eval₂ f x = 0 :=
  exists_eval₂_eq_zero_of_injective _ f.injective _ hp hsep

variable (K)

theorem exists_aeval_eq_zero {k : Type*} [CommSemiring k] [IsSepClosed K] [Algebra k K]
    [FaithfulSMul k K] (p : k[X]) (hp : p.degree ≠ 0) (hsep : p.Separable) :
    ∃ x : K, p.aeval x = 0 :=
  exists_eval₂_eq_zero_of_injective _ (FaithfulSMul.algebraMap_injective _ _) p hp hsep

variable (k) {K}

theorem of_exists_root (H : ∀ p : k[X], p.Monic → Irreducible p → Separable p → ∃ x, p.eval x = 0) :
    IsSepClosed k := by
  refine ⟨fun p hsep ↦ factors_iff_splits.mpr <| Or.inr ?_⟩
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

variable (K)

theorem algebraMap_surjective
    [IsSepClosed k] [Algebra k K] [Algebra.IsSeparable k K] :
    Function.Surjective (algebraMap k K) := by
  refine fun x => ⟨-(minpoly k x).coeff 0, ?_⟩
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic (Algebra.IsSeparable.isIntegral k x)
  have hsep : IsSeparable k x := Algebra.IsSeparable.isSeparable k x
  have h : (minpoly k x).degree = 1 :=
    degree_eq_one_of_irreducible k (minpoly.irreducible (Algebra.IsSeparable.isIntegral k x)) hsep
  have : aeval x (minpoly k x) = 0 := minpoly.aeval k x
  rw [eq_X_add_C_of_degree_eq_one h, hq, C_1, one_mul, aeval_add, aeval_X, aeval_C,
    add_eq_zero_iff_eq_neg] at this
  exact (RingHom.map_neg (algebraMap k K) ((minpoly k x).coeff 0)).symm ▸ this.symm

end IsSepClosed

/-- If `k` is separably closed, `K / k` is a field extension, `L / k` is an intermediate field
which is separable, then `L` is equal to `k`. A corollary of `IsSepClosed.algebraMap_surjective`. -/
theorem IntermediateField.eq_bot_of_isSepClosed_of_isSeparable [IsSepClosed k] [Algebra k K]
    (L : IntermediateField k K) [Algebra.IsSeparable k L] : L = ⊥ := bot_unique fun x hx ↦ by
  obtain ⟨y, hy⟩ := IsSepClosed.algebraMap_surjective k L ⟨x, hx⟩
  exact ⟨y, congr_arg (algebraMap L K) hy⟩

variable (k) (K)

/-- Typeclass for an extension being a separable closure. -/
class IsSepClosure [Algebra k K] : Prop where
  sep_closed : IsSepClosed K
  separable : Algebra.IsSeparable k K

/-- A separably closed field is its separable closure. -/
instance IsSepClosure.self_of_isSepClosed [IsSepClosed k] : IsSepClosure k k :=
  ⟨by assumption, Algebra.isSeparable_self k⟩

/-- If `K` is perfect and is a separable closure of `k`,
then it is also an algebraic closure of `k`. -/
instance (priority := 100) IsSepClosure.isAlgClosure_of_perfectField_top
    [Algebra k K] [IsSepClosure k K] [PerfectField K] : IsAlgClosure k K :=
  haveI : IsSepClosed K := IsSepClosure.sep_closed k
  ⟨inferInstance, IsSepClosure.separable.isAlgebraic⟩

/-- If `k` is perfect, `K` is a separable closure of `k`,
then it is also an algebraic closure of `k`. -/
instance (priority := 100) IsSepClosure.isAlgClosure_of_perfectField
    [Algebra k K] [IsSepClosure k K] [PerfectField k] : IsAlgClosure k K :=
  have halg : Algebra.IsAlgebraic k K := IsSepClosure.separable.isAlgebraic
  haveI := halg.perfectField; inferInstance

/-- If `k` is perfect, `K` is an algebraic closure of `k`,
then it is also a separable closure of `k`. -/
instance (priority := 100) IsSepClosure.of_isAlgClosure_of_perfectField
    [Algebra k K] [IsAlgClosure k K] [PerfectField k] : IsSepClosure k K :=
  ⟨haveI := IsAlgClosure.isAlgClosed (R := k) (K := K); inferInstance,
    (IsAlgClosure.isAlgebraic (R := k) (K := K)).isSeparable_of_perfectField⟩

variable {k} {K}

theorem isSepClosure_iff [Algebra k K] :
    IsSepClosure k K ↔ IsSepClosed K ∧ Algebra.IsSeparable k K :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

namespace IsSepClosure

instance isSeparable [Algebra k K] [IsSepClosure k K] : Algebra.IsSeparable k K :=
  IsSepClosure.separable

instance (priority := 100) isGalois [Algebra k K] [IsSepClosure k K] : IsGalois k K where
  to_isSeparable := IsSepClosure.separable
  to_normal.toIsAlgebraic :=  inferInstance
  to_normal.splits' x := (IsSepClosure.sep_closed k).splits_codomain _
    (Algebra.IsSeparable.isSeparable k x)

end IsSepClosure

namespace IsSepClosed

variable {K : Type u} (L : Type v) {M : Type w} [Field K] [Field L] [Algebra K L] [Field M]
  [Algebra K M] [IsSepClosed M]

theorem surjective_restrictDomain_of_isSeparable {E : Type*}
    [Field E] [Algebra K E] [Algebra L E] [IsScalarTower K L E] [Algebra.IsSeparable L E] :
    Function.Surjective fun φ : E →ₐ[K] M ↦ φ.restrictDomain L :=
  fun f ↦ IntermediateField.exists_algHom_of_splits' (E := E) f
    fun s ↦ ⟨Algebra.IsSeparable.isIntegral L s,
      IsSepClosed.splits_codomain _ <| Algebra.IsSeparable.isSeparable L s⟩

variable [Algebra.IsSeparable K L] {L}

/-- A (random) homomorphism from a separable extension L of K into a separably
  closed extension M of K. -/
noncomputable irreducible_def lift : L →ₐ[K] M :=
  Classical.choice <| IntermediateField.nonempty_algHom_of_adjoin_splits
    (fun x _ ↦ ⟨Algebra.IsSeparable.isIntegral K x,
      splits_codomain _ (Algebra.IsSeparable.isSeparable K x)⟩)
    (IntermediateField.adjoin_univ K L)

end IsSepClosed

namespace IsSepClosure

variable (K : Type u) [Field K] (L : Type v) (M : Type w) [Field L] [Field M]
variable [Algebra K M] [IsSepClosure K M]
variable [Algebra K L] [IsSepClosure K L]

attribute [local instance] IsSepClosure.sep_closed in
/-- A (random) isomorphism between two separable closures of `K`. -/
noncomputable def equiv : L ≃ₐ[K] M :=
  AlgEquiv.ofBijective _ (Normal.toIsAlgebraic.algHom_bijective₂
    (IsSepClosed.lift : L →ₐ[K] M) (IsSepClosed.lift : M →ₐ[K] L)).1

end IsSepClosure
