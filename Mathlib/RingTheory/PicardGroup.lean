/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalRing.Module

/-!
# The Picard group of a commutative ring

This file defines the Picard group `CommRing.Pic R` of a commutative ring `R` as the type of
invertible `R`-modules (in the sense that `M` is invertible if there exists another `R`-module
`N` such that `M ⊗[R] N ≃ₗ[R] R`) up to isomorphism, equipped with tensor product as multiplication.

## Main definitions

- `Module.Invertible R M` says that the canonical map `Mᵛ ⊗[R] M → R` is an isomorphism.
  To show that `M` is invertible, it suffices to provide an arbitrary `R`-module `N`
  and an isomorphism `N ⊗[R] M ≃ₗ[R] R`, see `Module.Invertible.right`.

## Main results

- An invertible module is finite and projective (provided as instances).

## References

- https://qchu.wordpress.com/2014/10/19/the-picard-groups/
- https://mathoverflow.net/questions/13768/what-is-the-right-definition-of-the-picard-group-of-a-commutative-ring
- https://mathoverflow.net/questions/375725/picard-group-vs-class-group
- [Weibel2013], https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.I.pdf, Proposition 3.5.
- [Stacks: Picard groups of rings](https://stacks.math.columbia.edu/tag/0AFW)

## TODO

Show:
- The Picard group of a commutative domain is isomorphic to its ideal class group.
- All commutative semi-local rings, in particular Artinian rings, has trivial Picard group.
- All unique factorization domains have trivial Picard group.

- Establish other characterizations of invertible modules, e.g. they are modules that
  becomes free of rank one when localized at every prime ideal.
  See [Stacks: Finite projective modules](https://stacks.math.columbia.edu/tag/00NX).
- Connect to invertible sheaves on `Spec R`. More generally, connect projective `R`-modules of
  constant finite rank to locally free sheaves on `Spec R`.
- Exhibit isomorphism with sheaf cohomology `H¹(Spec R, Oˣ_R)`.

-/

open TensorProduct

universe u v

namespace Module

variable (R : Type u) (M : Type v) (N P Q A : Type*) [CommSemiring R] [CommSemiring A]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [Algebra R A]
variable [Module R M] [Module R N] [Module R P] [Module R Q]

/-- An `R`-module `M` is invertible if the canonical map `Mᵛ ⊗[R] M → R` is an isomorphism,
where `Mᵛ` is the `R`-dual of `M`. -/
protected class Invertible : Prop where
  bijective : Function.Bijective (contractLeft R M)

namespace Invertible

/-- Promote the canonical map `Mᵛ ⊗[R] M → R` to a linear equivalence for invertible `M`. -/
noncomputable def linearEquiv [Module.Invertible R M] : Module.Dual R M ⊗[R] M ≃ₗ[R] R :=
  .ofBijective _ Invertible.bijective

variable {R M N}

section LinearEquiv

variable (e : M ⊗[R] N ≃ₗ[R] R)

open TensorProduct (assoc rid) in
/-- If M is invertible, `rTensorHom M` admits an inverse. -/
noncomputable def rTensorInv : (P ⊗[R] M →ₗ[R] Q ⊗[R] M) →ₗ[R] (P →ₗ[R] Q) :=
  ((assoc R Q M N ≪≫ₗ e.lTensor Q ≪≫ₗ rid R Q).congrRight ≪≫ₗ
    (assoc R P M N ≪≫ₗ e.lTensor P ≪≫ₗ rid R P).congrLeft _ R) ∘ₗ LinearMap.rTensorHom N

theorem rTensorInv_leftInverse : Function.LeftInverse (rTensorInv P Q e) (.rTensorHom M) :=
  fun _ ↦ by
    simp_rw [rTensorInv, LinearEquiv.coe_trans, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [← LinearEquiv.eq_symm_apply]
    ext; simp [LinearEquiv.congrLeft, LinearEquiv.congrRight, LinearEquiv.arrowCongrAddEquiv]

theorem rTensorInv_injective : Function.Injective (rTensorInv P Q e) := by
  simpa [rTensorInv] using (rTensorInv_leftInverse _ _ <| TensorProduct.comm R N M ≪≫ₗ e).injective

/-- If `M` is an invertible `R`-module, `(· ⊗[R] M)` is an auto-equivalence of the category
of `R`-modules. -/
@[simps!] noncomputable def rTensorEquiv : (P →ₗ[R] Q) ≃ₗ[R] (P ⊗[R] M →ₗ[R] Q ⊗[R] M) where
  __ := LinearMap.rTensorHom M
  invFun := rTensorInv P Q e
  left_inv := rTensorInv_leftInverse P Q e
  right_inv _ := rTensorInv_injective P Q e <| by
    rw [LinearMap.toFun_eq_coe, rTensorInv_leftInverse]

open LinearMap in
/-- If there is an `R`-isomorphism between `M ⊗[R] N` and `R`, where `M` is not assumed to be
the dual of `N`, we show the induced map `M → Nᵛ` is in fact an isomorphism, so `M` is
isomorphic to the dual of `N` after all. -/
theorem bijective_curry : Function.Bijective (curry e.toLinearMap) := by
  have : curry e.toLinearMap = ((TensorProduct.lid R N).congrLeft _ R ≪≫ₗ e.congrRight) ∘ₗ
      rTensorHom N ∘ₗ (ringLmapEquivSelf R R M).symm.toLinearMap := by
    rw [← LinearEquiv.toLinearMap_symm_comp_eq]; ext
    simp [LinearEquiv.congrLeft, LinearEquiv.congrRight, LinearEquiv.arrowCongrAddEquiv]
  simpa [this] using (rTensorEquiv R M <| TensorProduct.comm R N M ≪≫ₗ e).bijective

/-- Given `M ⊗[R] N ≃ₗ[R] R`, this is the induced isomorphism `M ≃ₗ[R] Nᵛ`. -/
noncomputable def linearEquivDual : M ≃ₗ[R] Dual R N := .ofBijective _ (bijective_curry e)

include e

protected theorem right : Module.Invertible R N where
  bijective := by
    rw [show contractLeft R N = .symm (.rTensor N (linearEquivDual e)) ≪≫ₗ e by
      rw [LinearEquiv.coe_trans, LinearEquiv.eq_comp_toLinearMap_symm]; ext; rfl]
    apply LinearEquiv.bijective

protected theorem left : Module.Invertible R M := .right (TensorProduct.comm R N M ≪≫ₗ e)

instance : Module.Invertible R R := .left (TensorProduct.lid R R)

end LinearEquiv

variable [Module.Invertible R M]

protected theorem congr (e : M ≃ₗ[R] N) : Module.Invertible R N :=
  .right (e.symm.lTensor _ ≪≫ₗ linearEquiv R M)

variable (R M N)

instance : Module.Invertible R (Dual R M) := .left (linearEquiv R M)

instance [Module.Invertible R N] : Module.Invertible R (M ⊗[R] N) :=
  .right (M := Dual R M ⊗[R] Dual R N) <| tensorTensorTensorComm .. ≪≫ₗ
    congr (linearEquiv R M) (linearEquiv R N) ≪≫ₗ TensorProduct.lid R R

private theorem finite_projective : Module.Finite R M ∧ Projective R M := by
  let N := Dual R M
  let e : M ⊗[R] N ≃ₗ[R] R := TensorProduct.comm .. ≪≫ₗ linearEquiv R M
  have ⟨S, hS⟩ := TensorProduct.exists_finset (e.symm 1)
  let f : (S →₀ N) →ₗ[R] R := Finsupp.lsum R fun i ↦ e.toLinearMap ∘ₗ TensorProduct.mk R M N i.1.1
  have : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Ideal.eq_top_iff_one]
    use Finsupp.equivFunOnFinite.symm fun i ↦ i.1.2
    simp_rw [f, Finsupp.coe_lsum]
    rw [Finsupp.sum_fintype _ _ fun _ ↦ map_zero _]
    rwa [e.symm_apply_eq, map_sum, ← Finset.sum_coe_sort, eq_comm] at hS
  have ⟨g, hg⟩ := projective_lifting_property f .id this
  classical
  let aux := finsuppRight R M N S ≪≫ₗ Finsupp.mapRange.linearEquiv e
  let f' : (S →₀ R) →ₗ[R] M := TensorProduct.rid R M ∘ₗ f.lTensor M ∘ₗ aux.symm
  let g' : M →ₗ[R] S →₀ R := aux ∘ₗ g.lTensor M ∘ₗ (TensorProduct.rid R M).symm
  have : Function.Surjective f' := by simpa [f'] using LinearMap.lTensor_surjective _ this
  refine ⟨.of_surjective f' this, .of_split g' f' <| LinearMap.ext fun m ↦ ?_⟩
  simp [f', g', show f (g 1) = 1 from DFunLike.congr_fun hg 1]

instance : Module.Finite R M := (finite_projective R M).1
instance : Projective R M := (finite_projective R M).2
example : IsReflexive R M := inferInstance

open Finsupp in
variable {R M} in
theorem free_iff_linearEquiv : Free R M ↔ Nonempty (M ≃ₗ[R] R) := by
  refine ⟨fun _ ↦ ?_, fun ⟨e⟩ ↦ .of_equiv e.symm⟩
  nontriviality R
  have := card_eq_of_linearEquiv R <|
    (finsuppTensorFinsupp' .. ≪≫ₗ linearEquivFunOnFinite R R _).symm ≪≫ₗ TensorProduct.congr
      (linearEquivFunOnFinite R R _ ≪≫ₗ llift R R R _ ≪≫ₗ (Free.repr R M).dualMap)
      (Free.repr R M).symm ≪≫ₗ linearEquiv R M ≪≫ₗ (.symm <| .funUnique Unit R R)
  have : Unique (Free.ChooseBasisIndex R M) :=
    (Fintype.card_eq_one_iff_nonempty_unique.mp (by simpa using this)).some
  exact ⟨Free.repr R M ≪≫ₗ LinearEquiv.finsuppUnique R R _⟩

theorem finrank_eq_one [StrongRankCondition R] [Free R M] : finrank R M = 1 := by
  cases subsingleton_or_nontrivial R
  · rw [← rank_eq_one_iff_finrank_eq_one, rank_subsingleton]
  · rw [(free_iff_linearEquiv.mp ‹_›).some.finrank_eq, finrank_self]

theorem rank_eq_one [StrongRankCondition R] [Free R M] : Module.rank R M = 1 :=
  rank_eq_one_iff_finrank_eq_one.mpr (finrank_eq_one R M)

open TensorProduct (comm lid) in
theorem toModuleEnd_bijective : Function.Bijective (toModuleEnd R (S := R) M) := by
  have : toModuleEnd R (S := R) M = (lid R M).conj ∘ rTensorEquiv R R
      (comm .. ≪≫ₗ linearEquiv R M) ∘ RingEquiv.moduleEndSelf R ∘ MulOpposite.opEquiv := by
    ext; simp [LinearEquiv.conj, liftAux]
  simpa [this] using MulOpposite.opEquiv.bijective

section Algebra

instance : Module.Invertible A (A ⊗[R] M) :=
  .right (M := A ⊗[R] Dual R M) <| (AlgebraTensorModule.distribBaseChange ..).symm ≪≫ₗ
    AlgebraTensorModule.congr (.refl A A) (linearEquiv R M) ≪≫ₗ AlgebraTensorModule.rid ..

instance (L) [AddCommMonoid L] [Module R L] [Module A L] [IsScalarTower R A L]
    [Module.Invertible A L] : Module.Invertible A (L ⊗[R] M) :=
  .congr (AlgebraTensorModule.cancelBaseChange R A A L M)

variable [FaithfulSMul R A] [Free A (A ⊗[R] M)]

/-- An invertible `R`-module embeds into an `R`-algebra that `R` injects into,
provided `A ⊗[R] M` is a free `A`-module. -/
noncomputable def embAlgebra : M →ₗ[R] A :=
  (free_iff_linearEquiv.mp ‹_›).some.restrictScalars R ∘ₗ
    (Algebra.ofId R A).toLinearMap.rTensor M ∘ₗ (TensorProduct.lid R M).symm

theorem embAlgebra_injective : Function.Injective (embAlgebra R M A) := by
  simpa [embAlgebra] using
    Flat.rTensor_preserves_injective_linearMap _ (FaithfulSMul.algebraMap_injective R A)

/-- An invertible `R`-module as a `R`-submodule of an `R`-algebra. -/
noncomputable def toSubmodule : Submodule R A := LinearMap.range (embAlgebra R M A)

end Algebra

end Invertible

end Module

section PicardGroup

open CategoryTheory Module

variable (R : Type u) [CommRing R]

instance (M : (Skeleton <| ModuleCat.{u} R)ˣ) : Module.Invertible R M :=
  .right (Quotient.eq.mp M.inv_mul).some.toLinearEquiv

instance : Small.{u} (Skeleton <| ModuleCat.{u} R)ˣ :=
  let sf := Σ n, Submodule R (Fin n → R)
  have {M N : sf} : M = N → (_ ⧸ M.2) ≃ₗ[R] _ ⧸ N.2 := by rintro rfl; exact .refl ..
  let f (M : (Skeleton <| ModuleCat.{u} R)ˣ) : sf := ⟨_, Finite.kerRepr R M⟩
  small_of_injective (f := f) fun M N eq ↦ Units.ext <| Quotient.out_equiv_out.mp
    ⟨((Finite.reprEquiv R M).symm ≪≫ₗ this eq ≪≫ₗ Finite.reprEquiv R N).toModuleIso⟩

/-- The Picard group of a commutative ring R consists of the invertible R-modules,
up to isomorphism. -/
def CommRing.Pic (R : Type u) [CommRing R] : Type u :=
  Shrink (Skeleton <| ModuleCat.{u} R)ˣ

open CommRing (Pic)

noncomputable instance : CommGroup (Pic R) := (equivShrink _).symm.commGroup

variable {R} in
/-- A representative of an element in the Picard group. -/
abbrev CommRing.Pic.AsModule (M : Pic R) : Type u := ((equivShrink _).symm M).val

noncomputable instance : CoeSort (Pic R) (Type u) := ⟨Pic.AsModule⟩

private noncomputable def equivShrinkLinearEquiv (M : (Skeleton <| ModuleCat.{u} R)ˣ) :
    (id <| equivShrink _ M : Pic R) ≃ₗ[R] M :=
  have {M N : Skeleton (ModuleCat.{u} R)} : M = N → M ≃ₗ[R] N := by rintro rfl; exact .refl ..
  this (by simp)

section CommRing

variable (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module.Invertible R M] [Module.Invertible R N]

instance : Module.Invertible R (Finite.repr R M) := .congr (Finite.reprEquiv R M).symm

namespace CommRing.Pic

/-- The class of an invertible module in the Picard group. -/
protected noncomputable def mk : Pic R := equivShrink _ <|
  letI M' := Finite.repr R M
  .mkOfMulEqOne ⟦.of R M'⟧ ⟦.of R (Dual R M')⟧ <| by
    rw [← toSkeleton, ← toSkeleton, mul_comm, ← Skeleton.toSkeleton_tensorObj]
    exact Quotient.sound ⟨(Invertible.linearEquiv R _).toModuleIso⟩

/-- `mk R M` is indeed the class of `M`. -/
noncomputable def mk.linearEquiv : Pic.mk R M ≃ₗ[R] M :=
  equivShrinkLinearEquiv R _ ≪≫ₗ (Quotient.mk_out (s := isIsomorphicSetoid _)
    (ModuleCat.of R (Finite.repr R M))).some.toLinearEquiv ≪≫ₗ Finite.reprEquiv R M

variable {R M N}

theorem mk_eq_iff {N : Pic R} : Pic.mk R M = N ↔ Nonempty (M ≃ₗ[R] N) where
  mp := (· ▸ ⟨(mk.linearEquiv R M).symm⟩)
  mpr := fun ⟨e⟩ ↦ ((equivShrink _).apply_eq_iff_eq_symm_apply).mpr <|
    Units.ext <| Quotient.mk_eq_iff_out.mpr ⟨(Finite.reprEquiv R M ≪≫ₗ e).toModuleIso⟩

theorem mk_eq_self {M : Pic R} : Pic.mk R M = M := mk_eq_iff.mpr ⟨.refl ..⟩

theorem ext_iff {M N : Pic R} : M = N ↔ Nonempty (M ≃ₗ[R] N) := by
  rw [← mk_eq_iff, mk_eq_self]

theorem mk_eq_mk_iff : Pic.mk R M = Pic.mk R N ↔ Nonempty (M ≃ₗ[R] N) :=
  let eN := mk.linearEquiv R N
  mk_eq_iff.trans ⟨fun ⟨e⟩ ↦ ⟨e ≪≫ₗ eN⟩, fun ⟨e⟩ ↦ ⟨e ≪≫ₗ eN.symm⟩⟩

theorem mk_self : Pic.mk R R = 1 :=
  congr_arg (equivShrink _) <| Units.ext <| Quotient.sound ⟨(Finite.reprEquiv R R).toModuleIso⟩

theorem mk_eq_one_iff : Pic.mk R M = 1 ↔ Nonempty (M ≃ₗ[R] R) := by
  rw [← mk_self, mk_eq_mk_iff]

theorem mk_eq_one [Free R M] : Pic.mk R M = 1 :=
  mk_eq_one_iff.mpr (Invertible.free_iff_linearEquiv.mp ‹_›)

theorem mk_tensor : Pic.mk R (M ⊗[R] N) = Pic.mk R M * Pic.mk R N :=
  congr_arg (equivShrink _) <| Units.ext <| by
    simp_rw [Pic.mk, Equiv.symm_apply_apply]
    refine (Quotient.sound ?_).trans (Skeleton.toSkeleton_tensorObj ..)
    exact ⟨(Finite.reprEquiv R _ ≪≫ₗ TensorProduct.congr
      (Finite.reprEquiv R M).symm (Finite.reprEquiv R N).symm).toModuleIso⟩

theorem mk_dual : Pic.mk R (Dual R M) = (Pic.mk R M)⁻¹ :=
  congr_arg (equivShrink _) <| Units.ext <| by
    rw [Pic.mk, Equiv.symm_apply_apply]
    exact Quotient.sound ⟨(Finite.reprEquiv R _ ≪≫ₗ (Finite.reprEquiv R _).dualMap).toModuleIso⟩

theorem inv_eq_dual (M : Pic R) : M⁻¹ = Pic.mk R (Dual R M) := by
  rw [mk_dual, mk_eq_self]

theorem mul_eq_tensor (M N : Pic R) : M * N = Pic.mk R (M ⊗[R] N) := by
  rw [mk_tensor, mk_eq_self, mk_eq_self]

theorem subsingleton_iff : Subsingleton (Pic R) ↔
    ∀ (M : Type u) [AddCommGroup M] [Module R M], Module.Invertible R M → Free R M :=
  .trans ⟨fun _ M _ _ _ ↦ Subsingleton.elim ..,
      fun h ↦ ⟨fun M N ↦ by rw [← mk_eq_self (M := M), ← mk_eq_self (M := N), h, h]⟩⟩ <|
    forall₄_congr fun _ _ _ _ ↦ mk_eq_one_iff.trans Invertible.free_iff_linearEquiv.symm

instance [Subsingleton (Pic R)] : Free R M :=
  have := subsingleton_iff.mp ‹_› (Finite.repr R M) inferInstance
  .of_equiv (Finite.reprEquiv R M)

/- TODO: it's still true that an invertible module over a (commutative) local semiring is free;
  in fact invertible modules over a semiring is Zariski-locally free.
  See [BorgerJun2024], Theorem 11.7. -/
instance [IsLocalRing R] : Subsingleton (Pic R) :=
  subsingleton_iff.mpr fun _ _ _ _ ↦ free_of_flat_of_isLocalRing

end CommRing.Pic

end CommRing

end PicardGroup

namespace Submodule

open Module Invertible

variable {R A : Type*} [CommSemiring R]

section Semiring

variable [Semiring A] [Algebra R A] [FaithfulSMul R A]

open LinearMap in
instance projective_unit (I : (Submodule R A)ˣ) : Projective R I := by
  obtain ⟨T, T', hT, hT', one_mem⟩ := mem_span_mul_finite_of_mem_mul (I.inv_mul ▸ one_le.mp le_rfl)
  classical
  rw [← Set.image2_mul, ← Finset.coe_image₂, mem_span_finset] at one_mem
  set S := T.image₂ (· * ·) T'
  obtain ⟨r, hr⟩ := one_mem
  choose a ha b hb eq using fun i : S ↦ Finset.mem_image₂.mp i.2
  let f : I →ₗ[R] S → R := .pi fun i ↦ (LinearEquiv.ofInjective
      (Algebra.linearMap R A) (FaithfulSMul.algebraMap_injective R A)).symm.comp <|
    restrict (mulRight R (r i • a i)) fun x hx ↦ by
      rw [← one_eq_range, ← I.mul_inv]; exact mul_mem_mul hx (I⁻¹.1.smul_mem _ <| hT <| ha i)
  let g : (S → R) →ₗ[R] I := .lsum _ _ ℕ fun i ↦ .toSpanSingleton _ _ ⟨b i, hT' <| hb i⟩
  refine .of_split f g (LinearMap.ext fun x ↦ Subtype.ext ?_)
  simp only [f, g, lsum_apply, comp_apply, sum_apply, toSpanSingleton_apply, proj_apply, pi_apply]
  simp_rw [restrict_apply, mulRight_apply, id_apply, coe_sum, coe_smul, Algebra.smul_def,
    ← Algebra.coe_linearMap, LinearEquiv.coe_toLinearMap, LinearEquiv.ofInjective_symm_apply,
    mul_assoc, Algebra.coe_linearMap, ← Algebra.smul_def, ← Finset.mul_sum, eq,
    (Finset.sum_coe_sort ..).trans hr.2, mul_one]

theorem projective_of_isUnit {I : Submodule R A} (hI : IsUnit I) : Projective R I :=
  projective_unit hI.unit

end Semiring

section CommSemiring

variable [CommSemiring A] [Algebra R A] [FaithfulSMul R A]
  (S : Submonoid R) [IsLocalization S A] (I J : (Submodule R A)ˣ)

/-- Given two invertible `R`-submodules in an `R`-algebra `A`, the `R`-linear map from
`I ⊗[R] J` to `I * J` induced by multiplication is an isomorphism. -/
noncomputable def tensorEquivMul : I ⊗[R] J ≃ₗ[R] I * J :=
  .ofBijective (mulMap' ..) ⟨by
    have := IsLocalization.flat A S
    simpa [mulMap', mulMap_eq_mul'_comp_mapIncl] using
      (IsLocalization.bijective_linearMap_mul' S A).1.comp
        (Flat.tensorProduct_mapIncl_injective_of_left ..),
    mulMap'_surjective _ _⟩

/-- Given an invertible `R`-submodule `I` in an `R`-algebra `A`, the `R`-linear map
from `I ⊗[R] I⁻¹` to `R` induced by multiplication is an isomorphism. -/
noncomputable def tensorInvEquiv : I ⊗[R] ↑I⁻¹ ≃ₗ[R] R :=
  tensorEquivMul S I _ ≪≫ₗ .ofEq _ _ (I.mul_inv.trans one_eq_range) ≪≫ₗ
    .symm (.ofInjective _ (FaithfulSMul.algebraMap_injective R A))

include S in
theorem _root_.Units.submodule_invertible : Module.Invertible R I := .left (tensorInvEquiv S I)

end CommSemiring

section CommRing

open CommRing Pic

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] [FaithfulSMul R A]
  (S : Submonoid R) [IsLocalization S A]

/-- The group homomorphism from the invertible submodules
in a localization of `R` to the Picard group of `R`. -/
@[simps] noncomputable def unitsToPic : (Submodule R A)ˣ →* Pic R :=
  haveI := Units.submodule_invertible S (A := A)
{ toFun I := Pic.mk R I
  map_one' := mk_eq_one_iff.mpr
    ⟨.ofEq _ _ one_eq_range ≪≫ₗ .symm (.ofInjective _ (FaithfulSMul.algebraMap_injective R A))⟩
  map_mul' I J := by rw [← mk_tensor, mk_eq_mk_iff]; exact ⟨(tensorEquivMul S I J).symm⟩ }

end CommRing

end Submodule
