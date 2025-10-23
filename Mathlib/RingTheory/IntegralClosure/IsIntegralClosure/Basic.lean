/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs
import Mathlib.RingTheory.Polynomial.IntegralNormalization
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# # Integral closure as a characteristic predicate

We prove basic properties of `IsIntegralClosure`.

-/

open Polynomial Submodule

section inv

open Algebra

variable {R S : Type*}

/-- A nonzero element in a domain integral over a field is a unit. -/
theorem IsIntegral.isUnit [Field R] [Ring S] [IsDomain S] [Algebra R S] {x : S}
    (int : IsIntegral R x) (h0 : x ≠ 0) : IsUnit x :=
  have : FiniteDimensional R (adjoin R {x}) := ⟨(Submodule.fg_top _).mpr int.fg_adjoin_singleton⟩
  (FiniteDimensional.isUnit R (K := adjoin R {x})
    (x := ⟨x, subset_adjoin rfl⟩) <| mt Subtype.ext_iff.mp h0).map (adjoin R {x}).val

/-- A commutative domain that is an integral algebra over a field is a field. -/
theorem isField_of_isIntegral_of_isField' [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [Algebra.IsIntegral R S] (hR : IsField R) : IsField S where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel {x} hx := by
    letI := hR.toField
    obtain ⟨y, rfl⟩ := (Algebra.IsIntegral.isIntegral (R := R) x).isUnit hx
    exact ⟨y.inv, y.val_inv⟩

variable [Field R] [DivisionRing S] [Algebra R S] {x : S} {A : Subalgebra R S}

theorem IsIntegral.inv_mem_adjoin (int : IsIntegral R x) : x⁻¹ ∈ adjoin R {x} := by
  obtain rfl | h0 := eq_or_ne x 0
  · rw [inv_zero]; exact Subalgebra.zero_mem _
  have : FiniteDimensional R (adjoin R {x}) := ⟨(Submodule.fg_top _).mpr int.fg_adjoin_singleton⟩
  obtain ⟨⟨y, hy⟩, h1⟩ := FiniteDimensional.exists_mul_eq_one R
    (K := adjoin R {x}) (x := ⟨x, subset_adjoin rfl⟩) (mt Subtype.ext_iff.mp h0)
  rwa [← mul_left_cancel₀ h0 ((Subtype.ext_iff.mp h1).trans (mul_inv_cancel₀ h0).symm)]

/-- The inverse of an integral element in a subalgebra of a division ring over a field
  also lies in that subalgebra. -/
theorem IsIntegral.inv_mem (int : IsIntegral R x) (hx : x ∈ A) : x⁻¹ ∈ A :=
  adjoin_le (Set.singleton_subset_iff.mpr hx) int.inv_mem_adjoin

/-- An integral subalgebra of a division ring over a field is closed under inverses. -/
theorem Algebra.IsIntegral.inv_mem [Algebra.IsIntegral R A] (hx : x ∈ A) : x⁻¹ ∈ A :=
  ((isIntegral_algHom_iff A.val Subtype.val_injective).mpr <|
    Algebra.IsIntegral.isIntegral (⟨x, hx⟩ : A)).inv_mem hx

/-- The inverse of an integral element in a division ring over a field is also integral. -/
theorem IsIntegral.inv (int : IsIntegral R x) : IsIntegral R x⁻¹ :=
  .of_mem_of_fg _ int.fg_adjoin_singleton _ int.inv_mem_adjoin

theorem IsIntegral.mem_of_inv_mem (int : IsIntegral R x) (inv_mem : x⁻¹ ∈ A) : x ∈ A := by
  rw [← inv_inv x]; exact int.inv.inv_mem inv_mem

end inv

section

variable {R A B S : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S]
variable [Algebra R A] [Algebra R B] {f : R →+* S}

/-- The [Kurosh problem](https://en.wikipedia.org/wiki/Kurosh_problem) asks to show that
  this is still true when `A` is not necessarily commutative and `R` is a field, but it has
  been solved in the negative. See https://arxiv.org/pdf/1706.02383.pdf for criteria for a
  finitely generated algebraic (= integral) algebra over a field to be finite dimensional.

This could be an `instance`, but we tend to go from `Module.Finite` to `IsIntegral`/`IsAlgebraic`,
and making it an instance will cause the search to be complicated a lot.
-/
theorem Algebra.IsIntegral.finite [Algebra.IsIntegral R A] [h' : Algebra.FiniteType R A] :
    Module.Finite R A :=
  have ⟨s, hs⟩ := h'
  ⟨by apply hs ▸ fg_adjoin_of_finite s.finite_toSet fun x _ ↦ Algebra.IsIntegral.isIntegral x⟩

/-- finite = integral + finite type -/
theorem Algebra.finite_iff_isIntegral_and_finiteType :
    Module.Finite R A ↔ Algebra.IsIntegral R A ∧ Algebra.FiniteType R A :=
  ⟨fun _ ↦ ⟨⟨.of_finite R⟩, inferInstance⟩, fun ⟨h, _⟩ ↦ h.finite⟩

theorem RingHom.IsIntegral.to_finite (h : f.IsIntegral) (h' : f.FiniteType) : f.Finite :=
  let _ := f.toAlgebra
  let _ : Algebra.IsIntegral R S := ⟨h⟩
  Algebra.IsIntegral.finite (h' := h')

alias RingHom.Finite.of_isIntegral_of_finiteType := RingHom.IsIntegral.to_finite

/-- finite = integral + finite type -/
theorem RingHom.finite_iff_isIntegral_and_finiteType : f.Finite ↔ f.IsIntegral ∧ f.FiniteType :=
  ⟨fun h ↦ ⟨h.to_isIntegral, h.to_finiteType⟩, fun ⟨h, h'⟩ ↦ h.to_finite h'⟩

variable (f : R →+* S) (R A)

theorem mem_integralClosure_iff_mem_fg {r : A} :
    r ∈ integralClosure R A ↔ ∃ M : Subalgebra R A, M.toSubmodule.FG ∧ r ∈ M :=
  ⟨fun hr =>
    ⟨Algebra.adjoin R {r}, hr.fg_adjoin_singleton, Algebra.subset_adjoin rfl⟩,
    fun ⟨M, Hf, hrM⟩ => .of_mem_of_fg M Hf _ hrM⟩

variable {R A}

theorem adjoin_le_integralClosure {x : A} (hx : IsIntegral R x) :
    Algebra.adjoin R {x} ≤ integralClosure R A := by
  rw [Algebra.adjoin_le_iff]
  simp only [SetLike.mem_coe, Set.singleton_subset_iff]
  exact hx

theorem le_integralClosure_iff_isIntegral {S : Subalgebra R A} :
    S ≤ integralClosure R A ↔ Algebra.IsIntegral R S :=
  SetLike.forall.symm.trans <|
    (forall_congr' fun x =>
      show IsIntegral R (algebraMap S A x) ↔ IsIntegral R x from
        isIntegral_algebraMap_iff Subtype.coe_injective).trans
      Algebra.isIntegral_def.symm

theorem Algebra.IsIntegral.adjoin {S : Set A} (hS : ∀ x ∈ S, IsIntegral R x) :
    Algebra.IsIntegral R (adjoin R S) :=
  le_integralClosure_iff_isIntegral.mp <| adjoin_le hS

theorem integralClosure_eq_top_iff : integralClosure R A = ⊤ ↔ Algebra.IsIntegral R A := by
  rw [← top_le_iff, le_integralClosure_iff_isIntegral,
      (Subalgebra.topEquiv (R := R) (A := A)).isIntegral_iff] -- explicit arguments for speedup

theorem Algebra.isIntegral_sup {S T : Subalgebra R A} :
    Algebra.IsIntegral R (S ⊔ T : Subalgebra R A) ↔
      Algebra.IsIntegral R S ∧ Algebra.IsIntegral R T := by
  simp_rw [← le_integralClosure_iff_isIntegral, sup_le_iff]

theorem Algebra.isIntegral_iSup {ι} (S : ι → Subalgebra R A) :
    Algebra.IsIntegral R ↑(iSup S) ↔ ∀ i, Algebra.IsIntegral R (S i) := by
  simp_rw [← le_integralClosure_iff_isIntegral, iSup_le_iff]

/-- Mapping an integral closure along an `AlgEquiv` gives the integral closure. -/
theorem integralClosure_map_algEquiv [Algebra R S] (f : A ≃ₐ[R] S) :
    (integralClosure R A).map (f : A →ₐ[R] S) = integralClosure R S := by
  ext y
  rw [Subalgebra.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.map f
  · intro hy
    use f.symm y, hy.map (f.symm : S →ₐ[R] A)
    simp

/-- An `AlgHom` between two rings restrict to an `AlgHom` between the integral closures inside
them. -/
def AlgHom.mapIntegralClosure [Algebra R S] (f : A →ₐ[R] S) :
    integralClosure R A →ₐ[R] integralClosure R S :=
  (f.restrictDomain (integralClosure R A)).codRestrict (integralClosure R S) (fun ⟨_, h⟩ => h.map f)

@[simp]
theorem AlgHom.coe_mapIntegralClosure [Algebra R S] (f : A →ₐ[R] S)
    (x : integralClosure R A) : (f.mapIntegralClosure x : S) = f (x : A) := rfl

/-- An `AlgEquiv` between two rings restrict to an `AlgEquiv` between the integral closures inside
them. -/
def AlgEquiv.mapIntegralClosure [Algebra R S] (f : A ≃ₐ[R] S) :
    integralClosure R A ≃ₐ[R] integralClosure R S :=
  AlgEquiv.ofAlgHom (f : A →ₐ[R] S).mapIntegralClosure (f.symm : S →ₐ[R] A).mapIntegralClosure
    (AlgHom.ext fun _ ↦ Subtype.ext (f.right_inv _))
    (AlgHom.ext fun _ ↦ Subtype.ext (f.left_inv _))

@[simp]
theorem AlgEquiv.coe_mapIntegralClosure [Algebra R S] (f : A ≃ₐ[R] S)
    (x : integralClosure R A) : (f.mapIntegralClosure x : S) = f (x : A) := rfl

theorem integralClosure.isIntegral (x : integralClosure R A) : IsIntegral R x :=
  let ⟨p, hpm, hpx⟩ := x.2
  ⟨p, hpm,
    Subtype.eq <| by
      rwa [← aeval_def, ← Subalgebra.val_apply, aeval_algHom_apply] at hpx⟩

instance integralClosure.AlgebraIsIntegral : Algebra.IsIntegral R (integralClosure R A) :=
  ⟨integralClosure.isIntegral⟩

theorem IsIntegral.of_mul_unit {x y : B} {r : R} (hr : algebraMap R B r * y = 1)
    (hx : IsIntegral R (x * y)) : IsIntegral R x := by
  obtain ⟨p, p_monic, hp⟩ := hx
  refine ⟨scaleRoots p r, (monic_scaleRoots_iff r).2 p_monic, ?_⟩
  convert scaleRoots_aeval_eq_zero hp
  rw [Algebra.commutes] at hr ⊢
  rw [mul_assoc, hr, mul_one]; rfl

theorem RingHom.IsIntegralElem.of_mul_unit (x y : S) (r : R) (hr : f r * y = 1)
    (hx : f.IsIntegralElem (x * y)) : f.IsIntegralElem x :=
  letI : Algebra R S := f.toAlgebra
  IsIntegral.of_mul_unit hr hx

/-- Generalization of `IsIntegral.of_mem_closure` bootstrapped up from that lemma -/
theorem IsIntegral.of_mem_closure' (G : Set A) (hG : ∀ x ∈ G, IsIntegral R x) :
    ∀ x ∈ Subring.closure G, IsIntegral R x := fun _ hx ↦
  Subring.closure_induction hG isIntegral_zero isIntegral_one (fun _ _ _ _ ↦ IsIntegral.add)
    (fun _ _ ↦ IsIntegral.neg) (fun _ _ _ _ ↦ IsIntegral.mul) hx

theorem IsIntegral.of_mem_closure'' {S : Type*} [CommRing S] {f : R →+* S} (G : Set S)
    (hG : ∀ x ∈ G, f.IsIntegralElem x) : ∀ x ∈ Subring.closure G, f.IsIntegralElem x := fun x hx =>
  @IsIntegral.of_mem_closure' R S _ _ f.toAlgebra G hG x hx

theorem IsIntegral.pow {x : B} (h : IsIntegral R x) (n : ℕ) : IsIntegral R (x ^ n) :=
  .of_mem_of_fg _ h.fg_adjoin_singleton _ <|
    Subalgebra.pow_mem _ (by exact Algebra.subset_adjoin rfl) _

theorem IsIntegral.nsmul {x : B} (h : IsIntegral R x) (n : ℕ) : IsIntegral R (n • x) :=
  h.smul n

theorem IsIntegral.zsmul {x : B} (h : IsIntegral R x) (n : ℤ) : IsIntegral R (n • x) :=
  h.smul n

theorem IsIntegral.multiset_prod {s : Multiset A} (h : ∀ x ∈ s, IsIntegral R x) :
    IsIntegral R s.prod :=
  (integralClosure R A).multiset_prod_mem h

theorem IsIntegral.multiset_sum {s : Multiset A} (h : ∀ x ∈ s, IsIntegral R x) :
    IsIntegral R s.sum :=
  (integralClosure R A).multiset_sum_mem h

theorem IsIntegral.prod {α : Type*} {s : Finset α} (f : α → A) (h : ∀ x ∈ s, IsIntegral R (f x)) :
    IsIntegral R (∏ x ∈ s, f x) :=
  (integralClosure R A).prod_mem h

theorem IsIntegral.sum {α : Type*} {s : Finset α} (f : α → A) (h : ∀ x ∈ s, IsIntegral R (f x)) :
    IsIntegral R (∑ x ∈ s, f x) :=
  (integralClosure R A).sum_mem h

theorem IsIntegral.det {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n A}
    (h : ∀ i j, IsIntegral R (M i j)) : IsIntegral R M.det := by
  rw [Matrix.det_apply]
  exact IsIntegral.sum _ fun σ _hσ ↦ (IsIntegral.prod _ fun i _hi => h _ _).zsmul _

@[simp]
theorem IsIntegral.pow_iff {x : A} {n : ℕ} (hn : 0 < n) : IsIntegral R (x ^ n) ↔ IsIntegral R x :=
  ⟨IsIntegral.of_pow hn, fun hx ↦ hx.pow n⟩

section Pushout

variable (R S A) [Algebra R S] [int : Algebra.IsIntegral R S]
variable (SA : Type*) [CommRing SA] [Algebra R SA] [Algebra S SA] [Algebra A SA]
  [IsScalarTower R S SA] [IsScalarTower R A SA]

theorem Algebra.IsPushout.isIntegral' [IsPushout R A S SA] : Algebra.IsIntegral A SA :=
  (equiv R A S SA).isIntegral_iff.mp inferInstance

theorem Algebra.IsPushout.isIntegral [h : IsPushout R S A SA] : Algebra.IsIntegral A SA :=
  h.symm.isIntegral'

attribute [local instance] Polynomial.algebra in
instance : Algebra.IsIntegral R[X] S[X] := Algebra.IsPushout.isIntegral R _ S _

attribute [local instance] MvPolynomial.algebraMvPolynomial in
instance {σ} : Algebra.IsIntegral (MvPolynomial σ R) (MvPolynomial σ S) :=
  Algebra.IsPushout.isIntegral R _ S _

end Pushout

section

variable (p : R[X]) (x : S)

/-- Given a `p : R[X]` and a `x : S` such that `p.eval₂ f x = 0`,
`f p.leadingCoeff * x` is integral. -/
theorem RingHom.isIntegralElem_leadingCoeff_mul (h : p.eval₂ f x = 0) :
    f.IsIntegralElem (f p.leadingCoeff * x) := by
  by_cases h' : 1 ≤ p.natDegree
  · use integralNormalization p
    have : p ≠ 0 := fun h'' => by
      rw [h'', natDegree_zero] at h'
      exact Nat.not_succ_le_zero 0 h'
    use monic_integralNormalization this
    rw [integralNormalization_eval₂_leadingCoeff_mul h' f x, h, mul_zero]
  · by_cases hp : p.map f = 0
    · apply_fun fun q => coeff q p.natDegree at hp
      rw [coeff_map, coeff_zero, coeff_natDegree] at hp
      rw [hp, zero_mul]
      exact f.isIntegralElem_zero
    · rw [Nat.one_le_iff_ne_zero, Classical.not_not] at h'
      rw [eq_C_of_natDegree_eq_zero h', eval₂_C] at h
      suffices p.map f = 0 by exact (hp this).elim
      rw [eq_C_of_natDegree_eq_zero h', map_C, h, C_eq_zero]

/-- Given a `p : R[X]` and a root `x : S`,
then `p.leadingCoeff • x : S` is integral over `R`. -/
theorem isIntegral_leadingCoeff_smul [Algebra R S] (h : aeval x p = 0) :
    IsIntegral R (p.leadingCoeff • x) := by
  rw [aeval_def] at h
  rw [Algebra.smul_def]
  exact (algebraMap R S).isIntegralElem_leadingCoeff_mul p x h

end

lemma Polynomial.Monic.quotient_isIntegralElem {g : S[X]} (mon : g.Monic) {I : Ideal S[X]}
    (h : g ∈ I) :
    ((Ideal.Quotient.mk I).comp (algebraMap S S[X])).IsIntegralElem (Ideal.Quotient.mk I X) := by
  exact ⟨g, mon, by
  rw [← (Ideal.Quotient.eq_zero_iff_mem.mpr h), eval₂_eq_sum_range]
  nth_rw 3 [(as_sum_range_C_mul_X_pow g)]
  simp only [map_sum, algebraMap_eq, RingHom.coe_comp, Function.comp_apply, map_mul, map_pow]⟩

/- If `I` is an ideal of the polynomial ring `S[X]` and contains a monic polynomial `f`,
then `S[X]/I` is integral over `S`. -/
lemma Polynomial.Monic.quotient_isIntegral {g : S[X]} (mon : g.Monic) {I : Ideal S[X]} (h : g ∈ I) :
    ((Ideal.Quotient.mkₐ S I).comp (Algebra.ofId S S[X])).IsIntegral := by
  have eq_top : Algebra.adjoin S {(Ideal.Quotient.mkₐ S I) X} = ⊤ := by
    ext g
    constructor
    · simp only [Algebra.mem_top, implies_true]
    · intro _
      obtain ⟨g', hg⟩ := Ideal.Quotient.mkₐ_surjective S I g
      have : g = (Polynomial.aeval ((Ideal.Quotient.mkₐ S I) X)) g' := by
        nth_rw 1 [← hg, aeval_eq_sum_range' (lt_add_one _),
          as_sum_range_C_mul_X_pow g', map_sum]
        simp only [Polynomial.C_mul', ← map_pow, map_smul]
      exact this ▸ (aeval_mem_adjoin_singleton S ((Ideal.Quotient.mk I) Polynomial.X))
  exact fun a ↦ (eq_top ▸ adjoin_le_integralClosure <| mon.quotient_isIntegralElem h)
    Algebra.mem_top

end

section IsIntegralClosure

instance integralClosure.isIntegralClosure (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] :
    IsIntegralClosure (integralClosure R A) R A where
  algebraMap_injective := Subtype.coe_injective
  isIntegral_iff {x} := ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨⟨_, h⟩, rfl⟩; exact h⟩

namespace IsIntegralClosure

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R B] [Algebra A B] [IsIntegralClosure A R B]
variable (R B)

protected theorem isIntegral [Algebra R A] [IsScalarTower R A B] (x : A) : IsIntegral R x :=
  (isIntegral_algebraMap_iff (algebraMap_injective A R B)).mp <|
    show IsIntegral R (algebraMap A B x) from isIntegral_iff.mpr ⟨x, rfl⟩

theorem isIntegral_algebra [Algebra R A] [IsScalarTower R A B] : Algebra.IsIntegral R A :=
  ⟨fun x => IsIntegralClosure.isIntegral R B x⟩

theorem noZeroSMulDivisors [SMul R A] [IsScalarTower R A B] [NoZeroSMulDivisors R B] :
    NoZeroSMulDivisors R A := by
  refine
    Function.Injective.noZeroSMulDivisors _ (IsIntegralClosure.algebraMap_injective A R B)
      (map_zero _) fun _ _ => ?_
  simp only [Algebra.algebraMap_eq_smul_one, IsScalarTower.smul_assoc]

variable {R} (A) {B}

/-- If `x : B` is integral over `R`, then it is an element of the integral closure of `R` in `B`. -/
noncomputable def mk' (x : B) (hx : IsIntegral R x) : A :=
  Classical.choose (isIntegral_iff.mp hx)

@[simp]
theorem algebraMap_mk' (x : B) (hx : IsIntegral R x) : algebraMap A B (mk' A x hx) = x :=
  Classical.choose_spec (isIntegral_iff.mp hx)

@[simp]
theorem mk'_one (h : IsIntegral R (1 : B) := isIntegral_one) : mk' A 1 h = 1 :=
  algebraMap_injective A R B <| by rw [algebraMap_mk', RingHom.map_one]

@[simp]
theorem mk'_zero (h : IsIntegral R (0 : B) := isIntegral_zero) : mk' A 0 h = 0 :=
  algebraMap_injective A R B <| by rw [algebraMap_mk', RingHom.map_zero]

@[simp]
theorem mk'_add (x y : B) (hx : IsIntegral R x) (hy : IsIntegral R y) :
    mk' A (x + y) (hx.add hy) = mk' A x hx + mk' A y hy :=
  algebraMap_injective A R B <| by simp only [algebraMap_mk', RingHom.map_add]

@[simp]
theorem mk'_mul (x y : B) (hx : IsIntegral R x) (hy : IsIntegral R y) :
    mk' A (x * y) (hx.mul hy) = mk' A x hx * mk' A y hy :=
  algebraMap_injective A R B <| by simp only [algebraMap_mk', RingHom.map_mul]

@[simp]
theorem mk'_algebraMap [Algebra R A] [IsScalarTower R A B] (x : R)
    (h : IsIntegral R (algebraMap R B x) := isIntegral_algebraMap) :
    IsIntegralClosure.mk' A (algebraMap R B x) h = algebraMap R A x :=
  algebraMap_injective A R B <| by rw [algebraMap_mk', ← IsScalarTower.algebraMap_apply]

/-- The integral closure of a field in a commutative domain is always a field. -/
theorem isField [Algebra R A] [IsScalarTower R A B] [IsDomain A] (hR : IsField R) :
    IsField A :=
  have := IsIntegralClosure.isIntegral_algebra R (A := A) B
  isField_of_isIntegral_of_isField' hR

section lift

variable (B) {S : Type*} [CommRing S] [Algebra R S]
-- split from above, since otherwise it does not synthesize `Semiring S`
variable [Algebra S B] [IsScalarTower R S B]
variable [Algebra R A] [IsScalarTower R A B] [isIntegral : Algebra.IsIntegral R S]
variable (R)

/-- If `B / S / R` is a tower of ring extensions where `S` is integral over `R`,
then `S` maps (uniquely) into an integral closure `B / A / R`. -/
noncomputable def lift : S →ₐ[R] A where
  toFun x := mk' A (algebraMap S B x) (IsIntegral.algebraMap
    (Algebra.IsIntegral.isIntegral (R := R) x))
  map_one' := by simp only [RingHom.map_one, mk'_one]
  map_zero' := by simp only [RingHom.map_zero, mk'_zero]
  map_add' x y := by simp_rw [← mk'_add, map_add]
  map_mul' x y := by simp_rw [← mk'_mul, RingHom.map_mul]
  commutes' x := by simp_rw [← IsScalarTower.algebraMap_apply, mk'_algebraMap]

@[simp]
theorem algebraMap_lift (x : S) : algebraMap A B (lift R A B x) = algebraMap S B x :=
  algebraMap_mk' A (algebraMap S B x) (IsIntegral.algebraMap
    (Algebra.IsIntegral.isIntegral (R := R) x))

end lift

section Equiv

variable (R B) (A' : Type*) [CommRing A']
variable [Algebra A' B] [IsIntegralClosure A' R B]
variable [Algebra R A] [Algebra R A'] [IsScalarTower R A B] [IsScalarTower R A' B]

/-- Integral closures are all isomorphic to each other. -/
noncomputable def equiv : A ≃ₐ[R] A' :=
  AlgEquiv.ofAlgHom
    (lift R A' B (isIntegral := isIntegral_algebra R B))
    (lift R A B (isIntegral := isIntegral_algebra R B))
    (by ext x; apply algebraMap_injective A' R B; simp)
    (by ext x; apply algebraMap_injective A R B; simp)

@[simp]
theorem algebraMap_equiv (x : A) : algebraMap A' B (equiv R A B A' x) = algebraMap A B x :=
  algebraMap_lift R A' B (isIntegral := isIntegral_algebra R B) x

end Equiv

end IsIntegralClosure

end IsIntegralClosure

section Algebra

open Algebra

variable {R A B S T : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S] [CommRing T]
variable [Algebra A B] [Algebra R B] (f : R →+* S) (g : S →+* T)
variable [Algebra R A] [IsScalarTower R A B]

/-- If A is an R-algebra all of whose elements are integral over R,
and x is an element of an A-algebra that is integral over A, then x is integral over R. -/
theorem isIntegral_trans [Algebra.IsIntegral R A] (x : B) (hx : IsIntegral A x) :
    IsIntegral R x := by
  rcases hx with ⟨p, pmonic, hp⟩
  let S := adjoin R (p.coeffs : Set A)
  have : Module.Finite R S := ⟨(Subalgebra.toSubmodule S).fg_top.mpr <|
    fg_adjoin_of_finite p.coeffs.finite_toSet fun a _ ↦ Algebra.IsIntegral.isIntegral a⟩
  let p' : S[X] := p.toSubring S.toSubring subset_adjoin
  have hSx : IsIntegral S x := ⟨p', (p.monic_toSubring _ _).mpr pmonic, by
    rw [IsScalarTower.algebraMap_eq S A B, ← eval₂_map]
    convert hp; apply p.map_toSubring S.toSubring⟩
  let Sx := Subalgebra.toSubmodule (adjoin S {x})
  let MSx : Module S Sx := SMulMemClass.toModule _ -- the next line times out without this
  have : Module.Finite S Sx := ⟨(Submodule.fg_top _).mpr hSx.fg_adjoin_singleton⟩
  refine .of_mem_of_fg ((adjoin S {x}).restrictScalars R) ?_ _
    ((Subalgebra.mem_restrictScalars R).mpr <| subset_adjoin rfl)
  rw [← Submodule.fg_top, ← Module.finite_def]
  letI : SMul S Sx := { MSx with } -- need this even though MSx is there
  have : IsScalarTower R S Sx :=
    Submodule.isScalarTower Sx -- Lean looks for `Module A Sx` without this
  exact Module.Finite.trans S Sx

variable (A) in
/-- If A is an R-algebra all of whose elements are integral over R,
and B is an A-algebra all of whose elements are integral over A,
then all elements of B are integral over R. -/
protected theorem Algebra.IsIntegral.trans
    [Algebra.IsIntegral R A] [Algebra.IsIntegral A B] : Algebra.IsIntegral R B :=
  ⟨fun x ↦ isIntegral_trans x (Algebra.IsIntegral.isIntegral (R := A) x)⟩

protected theorem RingHom.IsIntegral.trans
    (hf : f.IsIntegral) (hg : g.IsIntegral) : (g.comp f).IsIntegral :=
  let _ := f.toAlgebra; let _ := g.toAlgebra; let _ := (g.comp f).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsIntegral R S := ⟨hf⟩
  have : Algebra.IsIntegral S T := ⟨hg⟩
  have : Algebra.IsIntegral R T := Algebra.IsIntegral.trans S
  Algebra.IsIntegral.isIntegral

/-- If `R → A → B` is an algebra tower, `C` is the integral closure of `R` in `B`
and `A` is integral over `R`, then `C` is the integral closure of `A` in `B`. -/
lemma IsIntegralClosure.tower_top {B C : Type*} [CommSemiring C] [CommRing B]
    [Algebra R B] [Algebra A B] [Algebra C B] [IsScalarTower R A B]
    [IsIntegralClosure C R B] [Algebra.IsIntegral R A] :
    IsIntegralClosure C A B :=
  ⟨IsIntegralClosure.algebraMap_injective _ R _,
   fun hx => (IsIntegralClosure.isIntegral_iff).mp (isIntegral_trans (R := R) _ hx),
   fun hx => ((IsIntegralClosure.isIntegral_iff (R := R)).mpr hx).tower_top⟩

theorem RingHom.isIntegral_of_surjective (hf : Function.Surjective f) : f.IsIntegral :=
  fun x ↦ (hf x).recOn fun _y hy ↦ hy ▸ f.isIntegralElem_map

/-- If `R → A → B` is an algebra tower with `A → B` injective,
then if the entire tower is an integral extension so is `R → A` -/
theorem IsIntegral.tower_bot (H : Function.Injective (algebraMap A B)) {x : A}
    (h : IsIntegral R (algebraMap A B x)) : IsIntegral R x :=
  (isIntegral_algHom_iff (IsScalarTower.toAlgHom R A B) H).mp h

nonrec theorem RingHom.IsIntegral.tower_bot (hg : Function.Injective g)
    (hfg : (g.comp f).IsIntegral) : f.IsIntegral :=
  letI := f.toAlgebra; letI := g.toAlgebra; letI := (g.comp f).toAlgebra
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  fun x ↦ IsIntegral.tower_bot hg (hfg (g x))

variable (T) in
/-- Let `T / S / R` be a tower of algebras, `T` is non-trivial and is a torsion free `S`-module,
  then if `T` is an integral `R`-algebra, then `S` is an integral `R`-algebra. -/
theorem Algebra.IsIntegral.tower_bot [Algebra R S] [Algebra R T] [Algebra S T]
    [NoZeroSMulDivisors S T] [Nontrivial T] [IsScalarTower R S T]
    [h : Algebra.IsIntegral R T] : Algebra.IsIntegral R S where
  isIntegral := by
    apply RingHom.IsIntegral.tower_bot (algebraMap R S) (algebraMap S T)
      (FaithfulSMul.algebraMap_injective S T)
    rw [← IsScalarTower.algebraMap_eq R S T]
    exact h.isIntegral

theorem IsIntegral.tower_bot_of_field {R A B : Type*} [CommRing R] [Field A]
    [Ring B] [Nontrivial B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    {x : A} (h : IsIntegral R (algebraMap A B x)) : IsIntegral R x :=
  h.tower_bot (algebraMap A B).injective

theorem RingHom.isIntegralElem.of_comp {x : T} (h : (g.comp f).IsIntegralElem x) :
    g.IsIntegralElem x :=
  let ⟨p, hp, hp'⟩ := h
  ⟨p.map f, hp.map f, by rwa [← eval₂_map] at hp'⟩

theorem RingHom.IsIntegral.tower_top (h : (g.comp f).IsIntegral) : g.IsIntegral :=
  fun x ↦ RingHom.isIntegralElem.of_comp f g (h x)

variable (R) in
/-- Let `T / S / R` be a tower of algebras, `T` is an integral `R`-algebra, then it is integral
  as an `S`-algebra. -/
theorem Algebra.IsIntegral.tower_top [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [h : Algebra.IsIntegral R T] : Algebra.IsIntegral S T where
  isIntegral := by
    apply RingHom.IsIntegral.tower_top (algebraMap R S) (algebraMap S T)
    rw [← IsScalarTower.algebraMap_eq R S T]
    exact h.isIntegral

theorem RingHom.IsIntegral.quotient {I : Ideal S} (hf : f.IsIntegral) :
    (Ideal.quotientMap I f le_rfl).IsIntegral := by
  rintro ⟨x⟩
  obtain ⟨p, p_monic, hpx⟩ := hf x
  refine ⟨p.map (Ideal.Quotient.mk _), p_monic.map _, ?_⟩
  simpa only [hom_eval₂, eval₂_map] using congr_arg (Ideal.Quotient.mk I) hpx

instance {I : Ideal A} [Algebra.IsIntegral R A] : Algebra.IsIntegral R (A ⧸ I) :=
  Algebra.IsIntegral.trans A

instance Algebra.IsIntegral.quotient {I : Ideal A} [Algebra.IsIntegral R A] :
    Algebra.IsIntegral (R ⧸ I.comap (algebraMap R A)) (A ⧸ I) :=
  ⟨RingHom.IsIntegral.quotient (algebraMap R A) Algebra.IsIntegral.isIntegral⟩

theorem isIntegral_quotientMap_iff {I : Ideal S} :
    (Ideal.quotientMap I f le_rfl).IsIntegral ↔
      ((Ideal.Quotient.mk I).comp f : R →+* S ⧸ I).IsIntegral := by
  let g := Ideal.Quotient.mk (I.comap f)
  -- Porting note: added type ascription
  have : (Ideal.quotientMap I f le_rfl).comp g = (Ideal.Quotient.mk I).comp f :=
    Ideal.quotientMap_comp_mk le_rfl
  refine ⟨fun h => ?_, fun h => RingHom.IsIntegral.tower_top g _ (this ▸ h)⟩
  refine this ▸ RingHom.IsIntegral.trans g (Ideal.quotientMap I f le_rfl) ?_ h
  exact g.isIntegral_of_surjective Ideal.Quotient.mk_surjective

variable {R S : Type*} [CommRing R] [CommRing S]

theorem RingHom.IsIntegral.isLocalHom {f : R →+* S} (hf : f.IsIntegral)
    (inj : Function.Injective f) : IsLocalHom f where
  map_nonunit a ha := by
    -- `f a` is invertible in `S`, and we need to show that `(f a)⁻¹` is of the form `f b`.
    -- Let `p : R[X]` be monic with root `(f a)⁻¹`,
    obtain ⟨p, p_monic, hp⟩ := hf (ha.unit⁻¹ : _)
    -- and `q` be `p` with coefficients reversed (so `q(a) = q'(a) * a + 1`).
    -- We have `q(a) = 0`, so `-q'(a)` is the inverse of `a`.
    refine isUnit_of_mul_eq_one _ (-p.reverse.divX.eval a) ?_
    nth_rewrite 1 [mul_neg, ← eval_X (x := a), ← eval_mul, ← p_monic, ← coeff_zero_reverse,
      ← add_eq_zero_iff_neg_eq, ← eval_C (a := p.reverse.coeff 0), ← eval_add, X_mul_divX_add,
      ← (injective_iff_map_eq_zero' _).mp inj, ← eval₂_hom]
    rwa [← eval₂_reverse_eq_zero_iff] at hp

variable [Algebra R S] [Algebra.IsIntegral R S]

variable (R S) in
instance Algebra.IsIntegral.isLocalHom [FaithfulSMul R S] : IsLocalHom (algebraMap R S) :=
  (algebraMap_isIntegral_iff.mpr ‹_›).isLocalHom (FaithfulSMul.algebraMap_injective R S)

/-- If the integral extension `R → S` is injective, and `S` is a field, then `R` is also a field. -/
theorem isField_of_isIntegral_of_isField (hRS : Function.Injective (algebraMap R S))
    (hS : IsField S) : IsField R :=
  have := (faithfulSMul_iff_algebraMap_injective R S).mpr hRS
  IsLocalHom.isField hRS hS

theorem Algebra.IsIntegral.isField_iff_isField [IsDomain S]
    (hRS : Function.Injective (algebraMap R S)) : IsField R ↔ IsField S :=
  ⟨isField_of_isIntegral_of_isField', isField_of_isIntegral_of_isField hRS⟩

end Algebra

theorem integralClosure_idem {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] :
    integralClosure (integralClosure R A) A = ⊥ :=
  letI := (integralClosure R A).algebra
  eq_bot_iff.2 fun x hx ↦ Algebra.mem_bot.2
    ⟨⟨x, isIntegral_trans (A := integralClosure R A) x hx⟩, rfl⟩

section IsDomain

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]

instance : IsDomain (integralClosure R S) :=
  inferInstance

theorem roots_mem_integralClosure {f : R[X]} (hf : f.Monic) {a : S}
    (ha : a ∈ f.aroots S) : a ∈ integralClosure R S :=
  ⟨f, hf, (eval₂_eq_eval_map _).trans <| (mem_roots <| (hf.map _).ne_zero).1 ha⟩

end IsDomain
