/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Module.FiniteProjective
import Mathlib.Algebra.Module.Submodule.Localization
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalRing.Module

/-!
# The Picard group of a commutative ring

This file defines the Picard group `CommRing.Pic R` of a commutative ring `R` as the type of
invertible `R`-modules (in the sense that `M` is invertible if there exists another `R`-module
`N` such that `M ⊗[R] N ≃ₗ[R] R`) up to isomorphism, equipped with tensor product as multiplication.

## Main definitions

 - `CommRing.Pic R` is the type of invertible `R`-modules

## Main results

 - `CommRing.Pic.equivClassGroup` shows that if `R` is a commutative domain, then its Picard
   group is isomorphic to its ideal class group.

## References

 - https://qchu.wordpress.com/2014/10/19/the-picard-groups/
 - https://arxiv.org/pdf/2210.02951
 - https://mathoverflow.net/questions/13768/what-is-the-right-definition-of-the-picard-group-of-a-commutative-ring
 - https://mathoverflow.net/questions/375725/picard-group-vs-class-group
 - Charles A. Weibel, *The K-book: an introduction to algebraic K-theory*,
   https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.I.pdf, Proposition 3.5.
 - [Stacks: Picard groups of rings](https://stacks.math.columbia.edu/tag/0AFW)

## TODO

 - Establish other characterizations of invertible modules, e.g. they are modules that
   becomes free of rank one when localized at every prime ideal.
 - Connect to invertible sheaves on `Spec R`. More generally, connect projective `R`-modules of
   constant finite rank to locally free sheaves on `Spec R`.
   [Stacks: Finite projective modules](https://stacks.math.columbia.edu/tag/00NX)
 - Exhibit isomorphism with sheaf cohomology `H¹(Spec R, Oˣ_R)`.

-/

open TensorProduct

namespace Submodule

variable {R A} [CommSemiring R] [Semiring A] [Algebra R A]
variable (inj : Function.Injective (algebraMap R A))
include inj

open LinearMap in
theorem projective_unit (I : (Submodule R A)ˣ) : Module.Projective R I := by
  obtain ⟨T, T', hT, hT', one_mem⟩ := mem_span_mul_finite_of_mem_mul (I.inv_mul ▸ one_le.mp le_rfl)
  classical
  rw [← Set.image2_mul, ← Finset.coe_image₂, mem_span_finset] at one_mem
  set S := T.image₂ (· * ·) T'
  obtain ⟨r, hr⟩ := one_mem
  choose a ha b hb eq using fun i : S ↦ Finset.mem_image₂.mp i.2
  let f : I →ₗ[R] S → R := .pi fun i ↦
    (LinearEquiv.ofInjective (Algebra.linearMap R A) inj).symm.comp <|
    restrict (mulRight R (r i • a i)) fun x hx ↦ by
      rw [← one_eq_range, ← I.mul_inv]; exact mul_mem_mul hx (I⁻¹.1.smul_mem _ <| hT <| ha i)
  let g : (S → R) →ₗ[R] I := .lsum _ _ ℕ fun i ↦ .toSpanSingleton _ _ ⟨b i, hT' <| hb i⟩
  refine .of_split f g (LinearMap.ext fun x ↦ Subtype.ext ?_)
  simp only [f, g, lsum_apply, comp_apply, sum_apply, toSpanSingleton_apply, proj_apply, pi_apply]
  simp_rw [restrict_apply, mulRight_apply, id_apply, coe_sum, coe_smul, Algebra.smul_def,
    ← Algebra.coe_linearMap, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_ofInjective_symm,
    mul_assoc, Algebra.coe_linearMap, ← Algebra.smul_def, ← Finset.mul_sum, eq,
    (Finset.sum_coe_sort _ _).trans hr, mul_one]

theorem projective_of_isUnit {I : Submodule R A} (hI : IsUnit I) : Module.Projective R I :=
  projective_unit inj hI.unit

variable {R A : Type*} [CommRing R] (S : Submonoid R) (le : S ≤ nonZeroDivisors R)
variable [CommRing A] [Algebra R A] [IsLocalization S A]

/-- Given a unit in `Submodule R A`, the `R`-linear map from `I ⊗[R] I⁻¹` to `R`
induced by multiplication is an isomorphism. -/
noncomputable def linearEquivOfUnits (I : (Submodule R A)ˣ) : I ⊗[R] ↑I⁻¹ ≃ₗ[R] R :=
  have inj := IsLocalization.injective A le
  .ofBijective ((LinearEquiv.ofInjective (Algebra.linearMap R A) inj).symm.comp <|
    (LinearEquiv.ofEq _ _ <| I.mul_inv.trans one_eq_range).comp <| mulMap' _ _) ⟨by
      have := projective_unit inj I
      have := IsLocalization.flat A S
      simpa [mulMap', mulMap_eq_mul'_comp_mapIncl] using
        (IsLocalization.bijective_linearMap_mul' S A).1.comp
          (Module.Flat.tensorProduct_mapIncl_injective' _ _),
    by simpa using mulMap'_surjective _ _⟩

noncomputable def linearEquivOfUnitsMul (I J : (Submodule R A)ˣ) : I ⊗[R] J ≃ₗ[R] I * J :=
  .ofBijective (mulMap' _ _) ⟨by
    have := projective_unit (IsLocalization.injective A le) I
    have := IsLocalization.flat A S
    simpa [mulMap', mulMap_eq_mul'_comp_mapIncl] using
      (IsLocalization.bijective_linearMap_mul' S A).1.comp
        (Module.Flat.tensorProduct_mapIncl_injective' _ _),
    mulMap'_surjective _ _⟩

end Submodule

-- Picard group of UFD is trivial. somewhat nontrivial
-- local rings and artinian rings have trivial Picard group. Doable now.

-- functoriality of Picard group .. need Skeleton.map .. ? just compose with skeletonEquivalence ..
-- is a monoid hom ..
-- Quotient.map, Quotient.recOnSubsingleton ..
-- CategoryTheory.ThinSkeleton.map

-- define CommRing.Pic, and functoriality at the beginning .. require monoidal functor ..
-- Module.IsInvertible API..
-- make use of [Subsingleton (CommRing.Pic R)] class ..
-- iff all IsInvertible submodule is free, has rank 1.


-- Construct the induced functor of a monoidal functor between the skeleta,
-- to produce the base change homomorphism between Picard groups.
-- show that toSkeletonEquivalence is actually monoidal functor .. both ways?
-- inverse of a monoidal is also monoidal?

universe u v

/-- The Picard group of a commutative ring R consists of the invertible R-modules. -/
abbrev CommRing.Pic (R : Type u) [CommRing R] : Type (u + 1) :=
  (CategoryTheory.Skeleton <| ModuleCat.{u} R)ˣ

open CommRing (Pic)

/-- Gives an arbitrarily chosen `R`-module that is a representative of
a class in the Picard group of `R`. -/
instance (R) [CommRing R] : CoeSort (Pic R) (Type u) := ⟨fun M ↦ M.val⟩

namespace Module

variable (R : Type u) (M : Type v) (N P Q : Type*) [CommRing R]
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]

/-- An `R`-module `M` is invertible if the canonical map `Mᵛ ⊗[R] M → R` is an isomorphism,
where `Mᵛ` is the `R`-dual of `M`. -/
class Invertible : Prop where
  bijective : Function.Bijective (lift <| dualPairing R M)

namespace Invertible

/-- Promote the canonical map `Mᵛ ⊗[R] M → R` to a linear equivalence for invertible `M`. -/
noncomputable def linearEquiv [Invertible R M] : Module.Dual R M ⊗[R] M ≃ₗ[R] R :=
  .ofBijective _ Invertible.bijective

variable {R M N} (e : M ⊗[R] N ≃ₗ[R] R)

open TensorProduct (assoc rid) in
/-- If M is invertible, `rTensorHom M` admits an inverse. -/
noncomputable def rTensorInv : (P ⊗[R] M →ₗ[R] Q ⊗[R] M) →ₗ[R] (P →ₗ[R] Q) :=
  ((assoc R Q M N ≪≫ₗ e.lTensor Q ≪≫ₗ rid R Q).congrRight ≪≫ₗ
    (assoc R P M N ≪≫ₗ e.lTensor P ≪≫ₗ rid R P).congrLeft _ R) ∘ₗ LinearMap.rTensorHom N

theorem rTensorInv_leftInverse : Function.LeftInverse (rTensorInv P Q e) (.rTensorHom M) :=
  fun _ ↦ by
    simp_rw [rTensorInv, LinearEquiv.coe_trans, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [← LinearEquiv.eq_symm_apply]
    ext; simp [LinearEquiv.congrLeft, LinearEquiv.congrRight]

theorem rTensorInv_injective : Function.Injective (rTensorInv P Q e) := by
  simpa [rTensorInv] using (rTensorInv_leftInverse _ _ <| TensorProduct.comm R N M ≪≫ₗ e).injective

/-- If `M` is an invertible `R`-module, `(· ⊗[R] M)` is an auto-equivalence of the category
of `R`-modules. In particular the  -/
@[simps!] noncomputable def rTensorEquiv : (P →ₗ[R] Q) ≃ₗ[R] (P ⊗[R] M →ₗ[R] Q ⊗[R] M) where
  __ := LinearMap.rTensorHom M
  invFun := rTensorInv P Q e
  left_inv := rTensorInv_leftInverse P Q e
  right_inv _ := rTensorInv_injective P Q e <| by
    dsimp only; rw [LinearMap.toFun_eq_coe, rTensorInv_leftInverse]

open LinearMap in
/-- If there is an `R`-isomorphism between `M ⊗[R] N` and `R`, where `M` is not assumed to be
the dual of `N`, we show the induced map `M → Nᵛ` is in fact an isomorphism, so `M` is
isomorphic to `Nᵛ` after all. -/
theorem bijective_curry : Function.Bijective (curry e.toLinearMap) := by
  have : curry e.toLinearMap = ((TensorProduct.lid R N).congrLeft _ R ≪≫ₗ e.congrRight) ∘ₗ
      rTensorHom N ∘ₗ (ringLmapEquivSelf R R M).symm.toLinearMap := by
    rw [← LinearEquiv.toLinearMap_symm_comp_eq]; ext
    simp [LinearEquiv.congrLeft, LinearEquiv.congrRight]
  simpa [this] using (rTensorEquiv R M <| TensorProduct.comm R N M ≪≫ₗ e).bijective

include e

protected theorem right : Invertible R N where
  bijective := by
    have : lift (dualPairing R N) =
        ((LinearEquiv.ofBijective _ <| bijective_curry e).rTensor N).symm ≪≫ₗ e := by
      rw [LinearEquiv.coe_trans, LinearEquiv.eq_comp_toLinearMap_symm]; ext; rfl
    rw [this]; apply LinearEquiv.bijective

protected theorem left : Invertible R M := .right (TensorProduct.comm R N M ≪≫ₗ e)

instance (M : Pic R) : Invertible R M := .right (Quotient.eq.mp M.inv_mul).some.toLinearEquiv

instance : Invertible R R := .left (TensorProduct.lid R R)

omit e

variable [Invertible R M]

protected theorem congr (e : M ≃ₗ[R] N) : Invertible R N :=
  .right (e.symm.lTensor _ ≪≫ₗ linearEquiv R M)

variable (R M N)

instance : Invertible R (Dual R M) := .left (linearEquiv R M)

instance [Invertible R N] : Invertible R (M ⊗[R] N) :=
  .right (M := Dual R M ⊗[R] Dual R N) <| tensorTensorTensorComm _ _ _ _ _ ≪≫ₗ
    congr (linearEquiv R M) (linearEquiv R N) ≪≫ₗ TensorProduct.lid R R

instance (A) [CommRing A] [Algebra R A] : Invertible A (A ⊗[R] M) :=
  .right (M := A ⊗[R] Dual R M) <| (AlgebraTensorModule.distribBaseChange _ _ _ _).symm ≪≫ₗ
    AlgebraTensorModule.congr (.refl A A) (linearEquiv R M) ≪≫ₗ AlgebraTensorModule.rid _ _ _

private theorem finite_projective : Module.Finite R M ∧ Projective R M := by
  let N := Dual R M
  let e : M ⊗[R] N ≃ₗ[R] R := TensorProduct.comm _ _ _ ≪≫ₗ linearEquiv R M
  have ⟨S, hS⟩ := TensorProduct.exists_finset (e.symm 1)
  let f : (S →₀ N) →ₗ[R] R := Finsupp.lsum R fun i ↦ e.toLinearMap ∘ₗ TensorProduct.mk R M N i.1.1
  have : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← Ideal.span_one, Ideal.span_le, ← Set.singleton_one,
      Set.singleton_subset_iff]
    use Finsupp.equivFunOnFinite.symm fun i ↦ i.1.2
    simp_rw [f, Finsupp.coe_lsum, Finsupp.sum_fintype _ _ fun _ ↦ map_zero _]
    rwa [e.symm_apply_eq, map_sum, ← Finset.sum_coe_sort, eq_comm] at hS
  have ⟨g, hg⟩ := projective_lifting_property f .id this
  classical
  let aux := finsuppRight R M N S ≪≫ₗ Finsupp.mapRange.linearEquiv e
  let f' : (S →₀ R) →ₗ[R] M := TensorProduct.rid R M ∘ₗ f.lTensor M ∘ₗ aux.symm
  let g' : M →ₗ[R] S →₀ R := aux ∘ₗ g.lTensor M ∘ₗ (TensorProduct.rid R M).symm
  have : Function.Surjective f' := by simpa [f'] using LinearMap.lTensor_surjective _ this
  refine ⟨.of_surjective f' this, .of_split g' f' <| LinearMap.ext fun m ↦ ?_⟩
  simp [f', g', show f (g 1) = 1 from DFunLike.congr_fun hg 1]

instance : Projective R M := (finite_projective R M).2
instance : Module.Finite R M := (finite_projective R M).1
example : IsReflexive R M := inferInstance

-- TODO (?): generalize to any finite module and move to Mathlib.RingTheory.Finiteness
/-- A representative of an invertible module in the same universe as the ring. -/
protected abbrev repr : Type u := _ ⧸ LinearMap.ker (Finite.exists_fin' R M).choose_spec.choose

/-- The representative is isomorphic to the original module. -/
noncomputable def reprEquiv : Invertible.repr R M ≃ₗ[R] M :=
  LinearMap.quotKerEquivOfSurjective _ (Finite.exists_fin' R M).choose_spec.choose_spec

instance : Invertible R (Invertible.repr R M) := .congr (reprEquiv R M).symm

theorem finrank_eq_one [Free R M] : finrank R M = 1 := by
  cases subsingleton_or_nontrivial R
  · rw [← rank_eq_one_iff_finrank_eq_one, rank_subsingleton]
  refine (mul_eq_one (a := finrank R (Dual R M)).mp ?_).2
  rw [← finrank_tensorProduct, (linearEquiv R M).finrank_eq, finrank_self]

theorem rank_eq_one [Free R M] : Module.rank R M = 1 :=
  rank_eq_one_iff_finrank_eq_one.mpr (finrank_eq_one R M)

theorem free_iff_equiv : Free R M ↔ Nonempty (M ≃ₗ[R] R) := by
  refine ⟨fun _ ↦ ?_, fun ⟨e⟩ ↦ .of_equiv e.symm⟩
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R M; exact ⟨.ofSubsingleton _ _⟩
  exact ⟨finDimVectorspaceEquiv 1 (rank_eq_one R M) ≪≫ₗ LinearEquiv.funUnique _ _ _⟩

open TensorProduct (comm lid) in
theorem toModuleEnd_bijective : Function.Bijective (toModuleEnd R (S := R) M) := by
  have : toModuleEnd R (S := R) M = (lid R M).conj ∘ rTensorEquiv R R
      (comm _ _ _ ≪≫ₗ linearEquiv R M) ∘ moduleEndSelf R ∘ MulOpposite.opEquiv := by
    ext; simp [LinearEquiv.conj, liftAux]
  simpa [this] using MulOpposite.opEquiv.bijective

open Cardinal in
theorem cardinal_lift_mk : lift.{u} #M = lift.{v} #R := by
  sorry -- need Artinian ring result

open CategoryTheory

section same_universe

variable (M : Type u) [AddCommGroup M] [Module R M]

variable [Invertible R M]

open Cardinal in
theorem cardinal_mk [Invertible R M] : #M = #R := by
  sorry

/-- The class in the Picard group of an invertible module in the same universe as the ring,
with better defeq than the universe polymorphic version `toPic`. -/
@[simps!] def toPic' : Pic R :=
  .mkOfMulEqOne ⟦.of R M⟧ ⟦.of R (Dual R M)⟧ <| by
    rw [← toSkeleton, ← toSkeleton, mul_comm, ← Skeleton.toSkeleton_tensorObj]
    exact Quotient.sound ⟨(linearEquiv R M).toModuleIso⟩

/-- `toPic' R M` is indeed the class of `M`. -/
noncomputable def toPic'.linearEquiv : toPic' R M ≃ₗ[R] M :=
  (Quotient.eq_mk_iff_out.mp <| val_toPic' R M).some.toLinearEquiv

variable {R M}

-- toPic' = 1 iff Free iff iso to R
-- toPic' P = toPic' M * toPic' N iff P iso to M ⊗[R] N
-- toPic' P = (toPic' M)⁻¹ iff P iso to Dual R M

theorem toPic'_eq_iff (N : Pic R) : toPic' R M = N ↔ Nonempty (M ≃ₗ[R] N) := by
  sorry

theorem _root_.CommRing.Pic.one_eq : (1 : Pic R) = toPic' R R := _

theorem _root_.CommRing.Pic.inv_eq_dual (M : Pic R) :
    M⁻¹ = toPic' R (Dual R M):=
  sorry

theorem _root_.CommRing.Pic.mul_eq_tensor (M N : Pic R) :
    M * N = toPic' R (M ⊗[R] N):=
  sorry

theorem subsingleton_Pic_iff : Subsingleton (Pic R) ↔
    ∀ (M : Type u) [AddCommGroup M] [Module R M], Invertible R M → Free R M := by
  refine ⟨fun _ M _ _ _ ↦ ?_, fun h ↦ ⟨fun M N ↦ ?_⟩⟩
  · have := Quotient.eq.mp (congr_arg (·.val) <| Subsingleton.elim (toPic' R M) 1)
    exact (free_iff_equiv R M).mpr (this.map Iso.toLinearEquiv)
  · have ⟨eM⟩ := (free_iff_equiv R _).mp (h M inferInstance)
    have ⟨eN⟩ := (free_iff_equiv R _).mp (h N inferInstance)
    exact Units.ext (Quotient.out_equiv_out.mp ⟨(eM.trans eN.symm).toModuleIso⟩)

end same_universe

instance [Subsingleton (Pic R)] : Free R M :=
  have := subsingleton_Pic_iff.mp ‹_› (Invertible.repr R M) inferInstance
  .of_equiv (reprEquiv R M)

/-- The class of an invertible module (not necessarily in the same universe as the ring)
in the Picard group. -/
noncomputable def toPic : Pic R := toPic' R (Invertible.repr R M)

/-- `toPic R M` is indeed the class of `M`. -/
noncomputable def toPic.linearEquiv : toPic R M ≃ₗ[R] M :=
  (toPic'.linearEquiv R _).trans (reprEquiv R M)

theorem toPic'_eq_toPic (M : Type u) [AddCommGroup M] [Module R M] [Invertible R M] :
    toPic' R M = toPic R M :=
  Units.ext <| Quotient.sound ⟨(reprEquiv R M).toModuleIso.symm⟩

theorem toPic_self : toPic R R = 1 := sorry

theorem toPic_tensor [Invertible R N] : toPic R (M ⊗[R] N) = toPic R M * toPic R N := sorry

theorem toPic_dual : toPic R (Dual R M) = (toPic R M)⁻¹ := sorry

instance [LocalRing R] : Subsingleton (Pic R) :=
  subsingleton_Pic_iff.mpr fun M _ _ _ ↦
    have := Projective.finite_iff_finitePresentation.mp (Invertible.instFinite R M)
    free_of_flat_of_localRing

/- TODO: show that all commutative semi-local rings,
  in particular Artinian rings, has trivial Picard group.

instance [IsSemilocalRing R] : Subsingleton (Pic R) := sorry

-- move these; define IsSemilocalRing in Jacobson file .. after IsTwoSided is introduced
instance [LocalRing R] : IsSemilocalRing R := sorry
instance [CommRing R] [Finite {M : Ideal R | I.IsMaximal}] : IsSemilocalRing R := sorry

TODO: show every comm. Artinian ring is a product of finitely many local rings
+ Show that over an Artinian ring, or more generally semi-local ring, a finite flat module is free
  deduce that Picard group is trivial
+ for artinian rings, make finiteness of maximal ideals / primes / minimal primes global instances
+ reduced artinian ring / modulo nilradical -> product of fields (quotient by max ideals)
+ semi-local ring = IsSemisimpleRing (R ⧸ jacobson R) => fin many left/right max ideal
+ commutative + finitely many maximal ideals -> semi-local
+ fin many max ideals + intersection = nilradical => map into the product of localization at max
  ideals is surjective (always injective)
+ perfect ring / semiperfect ring (idempotents lift)
-/

end Invertible

end Module


namespace Module.Invertible

variable {R K M N M' N' : Type*} [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ⊗[R] N ≃ₗ[R] R)
include e

section

variable (K) [IsDomain R]

-- TODO: generalize to arbitrary localization at a prime, which is free of rank 1
theorem finrank_fractionRing_tensor : finrank K (K ⊗[R] M) = 1 := by
  refine (mul_eq_one (b := finrank K (K ⊗[R] N)).mp ?_).1
  let e' := (AlgebraTensorModule.distribBaseChange _ _ _ _).symm ≪≫ₗ
    AlgebraTensorModule.congr (.refl K K) e ≪≫ₗ AlgebraTensorModule.rid _ _ _
  letI : Field K := IsFractionRing.toField R
  rw [← finrank_tensorProduct, e'.finrank_eq, finrank_self]

theorem rank_fractionRing_tensor : Module.rank K (K ⊗[R] M) = 1 :=
  rank_eq_one_iff_finrank_eq_one.mpr <| finrank_fractionRing_tensor K e

/-- An arbitrarily chosen isomorphism over the fraction field K between the base change of an
invertible module M over a domain R to K and the free K-module of rank 1. -/
noncomputable def fractionRingTensorEquiv : K ⊗[R] M ≃ₗ[K] K :=
  letI : Field K := IsFractionRing.toField R
  finDimVectorspaceEquiv (R := K) 1 (rank_fractionRing_tensor K e) ≪≫ₗ LinearEquiv.funUnique _ _ _

/-- An invertible module over a domain embeds into the fraction field. -/
noncomputable def embFractionRing : M →ₗ[R] K :=
  (fractionRingTensorEquiv K e).restrictScalars R ∘ₗ
    (Algebra.ofId R K).toLinearMap.rTensor M ∘ₗ (TensorProduct.lid R M).symm

theorem embFractionRing_injective : Function.Injective (embFractionRing K e) := by
  have := left_projective e
  simpa [embFractionRing] using
    Flat.rTensor_preserves_injective_linearMap (R := R) _ (IsFractionRing.injective R K)

/-- An invertible module as a submodule of the fraction field. -/
noncomputable def toSubmodule : Submodule R K := LinearMap.range (embFractionRing K e)


/- variable [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
(e' : M' ⊗[R] N' ≃ₗ[R] R)
include e'

lift_mul_bijective {R A} [CommSemiring R] [CommSemiring A]
    [Algebra R A] {S : Submonoid R} [IsLocalization S A] :
    Function.Bijective (lift (.mul R A)) := by
  _ -/


end

end Module.Invertible


namespace CommRing

variable (R : Type u) [CommRing R]

open CategoryTheory

/-- The Picard group of a commutative ring R consists of the invertible R-modules. -/
abbrev Pic : Type (u + 1) := (Skeleton <| ModuleCat.{u} R)ˣ

namespace Pic


-- ClassGroup.toPic always multiplicative ..

-- invertible module must have the same cardinality as R and K .. over arbitrary CommRing ..?
-- then we can use the same universe
-- over a finite ring, cardinality must be equal? yes. Pic of artinian ring is trivial
-- also trivial for UFD ...

-- Any submodule isomorphic to the invertible module is in the same class as the image of the
-- invertible module (automatically an invertible submodule? yes if in a field.)
-- because you can take product with the inverse of the invertible module, and it will be isomorphic
-- to 1 and therefore differ by a scalar from 1 (i.e. principal).

-- inverse is isomorphic to Module.Dual ..

-- over commutative ring, rank is always well defined ..
-- projective module over local ring must be free (easier to prove when finite?)
-- can reduce over residue field and take dimension..
-- show that the rank when localized at every prime ideal is 1 (stronger than finite projective ..)

-- being invertible / being an isomorphism is local property


/-- Given an class `M` in the Picard group of `R`, `M.linearEquiv` is an arbitrarily chosen
`R`-isomorphism between `M ⊗[R] M⁻¹` and `R`. -/
noncomputable def linearEquiv (M : Pic R) : M ⊗[R] ↥M⁻¹ ≃ₗ[R] R :=
  (Nonempty.some <| Quotient.eq.mp M.mul_inv).toLinearEquiv

variable (S : Submonoid R) (le : S ≤ nonZeroDivisors R)
variable (A : Type u) [CommRing A] [Algebra R A] [IsLocalization S A]

/-- The group homomorphism from the invertible submodules
in a localization of R to the Picard group of R. -/
def _root_.Submodule.unitsToPic : (Submodule R A)ˣ →* Pic R where
  toFun I := .mkOfMulEqOne ⟦.of R I⟧ ⟦.of R ↑I⁻¹⟧ <| by
    rw [← toSkeleton, ← toSkeleton, ← Skeleton.toSkeleton_tensorObj]
    exact Quotient.sound ⟨(Submodule.linearEquivOfUnits S le I).toModuleIso⟩
  map_one' := Units.ext <| Quotient.sound ⟨LinearEquiv.toModuleIso <| .trans
    (.ofEq _ _ Submodule.one_eq_range) <| .symm <|
    .ofInjective (Algebra.linearMap R A) <| IsLocalization.injective A le⟩
  map_mul' I J := Units.ext <| by
    dsimp only [Units.val_mul, Units.val_mkOfMulEqOne]
    rw [← toSkeleton, ← toSkeleton, ← Skeleton.toSkeleton_tensorObj]
    exact Quotient.sound ⟨(Submodule.linearEquivOfUnitsMul S le I J).symm.toModuleIso⟩

-- theorem _root_.Submodule.unitsToPic_bijective :
#check Submodule.spanSingleton


variable (K) [CommRing K] [Algebra R K] [IsFractionRing R K]

def toUnitsSubmodule : Pic R →* (Submodule R K)ˣ where
  toFun := _
  map_one' := _
  map_mul' := _


variable [IsDomain R]


end Pic

end CommRing
