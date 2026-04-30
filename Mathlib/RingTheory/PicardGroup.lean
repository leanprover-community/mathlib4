/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.LinearDisjoint
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.UniqueFactorizationDomain.ClassGroup

/-!
# The Picard group of a commutative ring

This file defines the Picard group `CommRing.Pic R` of a commutative ring `R` as the type of
invertible `R`-modules (in the sense that `M` is invertible if there exists another `R`-module
`N` such that `M ⊗[R] N ≃ₗ[R] R`) up to isomorphism, equipped with tensor product as multiplication.

## Main definition

- `Module.Invertible R M` says that the canonical map `Mᵛ ⊗[R] M → R` is an isomorphism.
  To show that `M` is invertible, it suffices to provide an arbitrary `R`-module `N`
  and an isomorphism `N ⊗[R] M ≃ₗ[R] R`, see `Module.Invertible.right`.

- `ClassGroup.equivPic`: the class group of a domain is isomorphic to the Picard group.

## Main results

- An invertible module is finite and projective (provided as instances).

- `Module.Invertible.free_iff_linearEquiv`: an invertible module is free iff it is isomorphic to
  the ring, i.e. its class is trivial in the Picard group.

- `Submodule.ker_unitsToPic`, `Submodule.range_unitsToPic`: exactness of the sequence
  `1 → Rˣ → Aˣ → (Submodule R A)ˣ → Pic R → Pic A` at the last two spots.
  See Theorem 2.4 in [RobertsSingh1993] or Exercise I.3.7(iv) and Proposition I.3.5 in [Weibel2013].

## References

- https://qchu.wordpress.com/2014/10/19/the-picard-groups/
- https://mathoverflow.net/questions/13768/what-is-the-right-definition-of-the-picard-group-of-a-commutative-ring
- https://mathoverflow.net/questions/375725/picard-group-vs-class-group
- [Weibel2013], https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.I.pdf
- [Stacks: Picard groups of rings](https://stacks.math.columbia.edu/tag/0AFW)

## TODO

Show:
- Invertible modules over a commutative ring have the same cardinality as the ring.

- Establish other characterizations of invertible modules, e.g. they are modules that
  become free of rank one when localized at every prime ideal.
  See [Stacks: Finite projective modules](https://stacks.math.columbia.edu/tag/00NX).
- Connect to invertible sheaves on `Spec R`. More generally, connect projective `R`-modules of
  constant finite rank to locally free sheaves on `Spec R`.
- Exhibit isomorphism with sheaf cohomology `H¹(Spec R, 𝓞ˣ)`.
-/

@[expose] public section

open TensorProduct

universe u v

variable (R : Type u) (M : Type v) (N P Q A : Type*) [CommSemiring R]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]

namespace Module

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

/-- The canonical isomorphism between a module and the result of tensoring it
from the left by two mutually dual invertible modules. -/
noncomputable abbrev leftCancelEquiv : M ⊗[R] (N ⊗[R] P) ≃ₗ[R] P :=
  (TensorProduct.assoc R M N P).symm ≪≫ₗ e.rTensor P ≪≫ₗ TensorProduct.lid R P

/-- The canonical isomorphism between a module and the result of tensoring it
from the right by two mutually dual invertible modules. -/
noncomputable abbrev rightCancelEquiv : (P ⊗[R] M) ⊗[R] N ≃ₗ[R] P :=
  TensorProduct.assoc R P M N ≪≫ₗ e.lTensor P ≪≫ₗ TensorProduct.rid R P

variable {P Q} in
theorem leftCancelEquiv_comp_lTensor_comp_symm (f : P →ₗ[R] Q) :
    leftCancelEquiv Q e ∘ₗ (f.lTensor N).lTensor M ∘ₗ (leftCancelEquiv P e).symm = f := by
  rw [← LinearMap.comp_assoc, LinearEquiv.comp_toLinearMap_symm_eq]; ext; simp

variable {P Q} in
theorem rightCancelEquiv_comp_rTensor_comp_symm (f : P →ₗ[R] Q) :
    rightCancelEquiv Q e ∘ₗ (f.rTensor M).rTensor N ∘ₗ (rightCancelEquiv P e).symm = f := by
  rw [← LinearMap.comp_assoc, LinearEquiv.comp_toLinearMap_symm_eq]; ext; simp

/-- If M is invertible, `rTensorHom M` admits an inverse. -/
noncomputable def rTensorInv : (P ⊗[R] M →ₗ[R] Q ⊗[R] M) →ₗ[R] (P →ₗ[R] Q) :=
  ((rightCancelEquiv Q e).congrRight ≪≫ₗ (rightCancelEquiv P e).congrLeft _ R) ∘ₗ
    LinearMap.rTensorHom N

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
  right_inv _ := rTensorInv_injective P Q e (by rw [LinearMap.toFun_eq_coe, rTensorInv_leftInverse])

open LinearMap in
/-- If there is an `R`-isomorphism between `M ⊗[R] N` and `R`,
the induced map `M → Nᵛ` is an isomorphism. -/
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
    rw [show contractLeft R N = ((linearEquivDual e).rTensor N).symm ≪≫ₗ e by
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
  let aux := finsuppRight R _ M N S ≪≫ₗ Finsupp.mapRange.linearEquiv e
  let f' : (S →₀ R) →ₗ[R] M := TensorProduct.rid R M ∘ₗ f.lTensor M ∘ₗ aux.symm
  let g' : M →ₗ[R] S →₀ R := aux ∘ₗ g.lTensor M ∘ₗ (TensorProduct.rid R M).symm
  have : Function.Surjective f' := by simpa [f'] using LinearMap.lTensor_surjective _ this
  refine ⟨.of_surjective f' this, .of_split g' f' <| LinearMap.ext fun m ↦ ?_⟩
  simp [f', g', show f (g 1) = 1 from DFunLike.congr_fun hg 1]

instance : Module.Finite R M := (finite_projective R M).1
instance : Projective R M := (finite_projective R M).2
example : IsReflexive R M := inferInstance

section inj_surj_bij

variable {R N P}

theorem lTensor_injective_iff {f : N →ₗ[R] P} :
    Function.Injective (f.lTensor M) ↔ Function.Injective f := by
  refine ⟨fun h ↦ ?_, Flat.lTensor_preserves_injective_linearMap _⟩
  rw [← leftCancelEquiv_comp_lTensor_comp_symm (linearEquiv R M) f]
  simpa using Flat.lTensor_preserves_injective_linearMap _ h

theorem rTensor_injective_iff {f : N →ₗ[R] P} :
    Function.Injective (f.rTensor M) ↔ Function.Injective f := by
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj, lTensor_injective_iff]

theorem lTensor_surjective_iff {f : N →ₗ[R] P} :
    Function.Surjective (f.lTensor M) ↔ Function.Surjective f := by
  refine ⟨fun h ↦ ?_, LinearMap.lTensor_surjective _⟩
  rw [← leftCancelEquiv_comp_lTensor_comp_symm (linearEquiv R M) f]
  simpa using LinearMap.lTensor_surjective _ h

theorem rTensor_surjective_iff {f : N →ₗ[R] P} :
    Function.Surjective (f.rTensor M) ↔ Function.Surjective f := by
  rw [← LinearMap.lTensor_surj_iff_rTensor_surj, lTensor_surjective_iff]

theorem lTensor_bijective_iff {f : N →ₗ[R] P} :
    Function.Bijective (f.lTensor M) ↔ Function.Bijective f := by
  simp_rw [Function.Bijective, lTensor_injective_iff, lTensor_surjective_iff]

theorem rTensor_bijective_iff {f : N →ₗ[R] P} :
    Function.Bijective (f.rTensor M) ↔ Function.Bijective f := by
  simp_rw [Function.Bijective, rTensor_injective_iff, rTensor_surjective_iff]

end inj_surj_bij

open Finsupp in
variable {R M} in
/-- An invertible module is free iff it is isomorphic to the ring, i.e. its class is trivial in
the Picard group. -/
theorem free_iff_linearEquiv : Free R M ↔ Nonempty (M ≃ₗ[R] R) := by
  refine ⟨fun _ ↦ ?_, fun ⟨e⟩ ↦ .of_equiv e.symm⟩
  nontriviality R
  have e := (Free.chooseBasis R M).repr
  have := card_eq_of_linearEquiv R <|
    (finsuppTensorFinsupp' .. ≪≫ₗ linearEquivFunOnFinite R R _).symm ≪≫ₗ TensorProduct.congr
      (linearEquivFunOnFinite R R _ ≪≫ₗ llift R R R _ ≪≫ₗ e.dualMap)
      e.symm ≪≫ₗ linearEquiv R M ≪≫ₗ (.symm <| .funUnique Unit R R)
  have : Unique (Free.ChooseBasisIndex R M) :=
    (Fintype.card_eq_one_iff_nonempty_unique.mp (by simpa using this)).some
  exact ⟨e ≪≫ₗ LinearEquiv.finsuppUnique R R _⟩

/- TODO: The ≤ direction holds for arbitrary invertible modules over any commutative **ring** by
considering the localization at a prime (which is free of rank 1) using the strong rank condition.
The ≥ direction fails in general but holds for domains and Noetherian rings,
see https://math.stackexchange.com/q/5089900 and https://mathoverflow.net/a/499611. -/
protected theorem finrank_eq_one [StrongRankCondition R] [Free R M] : finrank R M = 1 := by
  cases subsingleton_or_nontrivial R
  · rw [← rank_eq_one_iff_finrank_eq_one, rank_subsingleton]
  · rw [(free_iff_linearEquiv.mp ‹_›).some.finrank_eq, finrank_self]

theorem rank_eq_one [StrongRankCondition R] [Free R M] : Module.rank R M = 1 :=
  rank_eq_one_iff_finrank_eq_one.mpr (Invertible.finrank_eq_one R M)

open TensorProduct (comm lid) in
theorem toModuleEnd_bijective : Function.Bijective (toModuleEnd R (S := R) M) := by
  have : toModuleEnd R (S := R) M = (lid R M).conj ∘ rTensorEquiv R R
      (comm .. ≪≫ₗ linearEquiv R M) ∘ RingEquiv.moduleEndSelf R ∘ MulOpposite.opEquiv := by
    ext; simp [LinearEquiv.conj, liftAux]
  simpa [this] using MulOpposite.opEquiv.bijective

instance : FaithfulSMul R M where
  eq_of_smul_eq_smul {_ _} h := (toModuleEnd_bijective R M).injective <| LinearMap.ext h

variable {R M N} in
private theorem bijective_self_of_surjective (f : R →ₗ[R] M) (hf : Function.Surjective f) :
    Function.Bijective f where
  left {r₁ r₂} eq := smul_left_injective' (α := M) <| funext fun m ↦ by
    obtain ⟨r, rfl⟩ := hf m
    simp_rw [← map_smul, smul_eq_mul, mul_comm _ r, ← smul_eq_mul, map_smul, eq]
  right := hf

variable {R M N} in
/- Not true if `surjective` is replaced by `injective`: any nonzero element in an invertible
module over a domain generates a submodule isomorphic to the domain, which is not the whole
module unless the module is free. -/
theorem bijective_of_surjective [Module.Invertible R N] {f : M →ₗ[R] N}
    (hf : Function.Surjective f) : Function.Bijective f := by
  simpa [lTensor_bijective_iff] using bijective_self_of_surjective
    (f.lTensor _ ∘ₗ (linearEquiv R M).symm.toLinearMap) (by simpa [lTensor_surjective_iff] using hf)

section LinearEquiv
variable {R M N} [Module.Invertible R N] {f : M →ₗ[R] N} {g : N →ₗ[R] M}

theorem rightInverse_of_leftInverse (hfg : Function.LeftInverse f g) :
    Function.RightInverse f g :=
  Function.rightInverse_of_injective_of_leftInverse
    (bijective_of_surjective hfg.surjective).injective hfg

theorem leftInverse_of_rightInverse (hfg : Function.RightInverse f g) :
    Function.LeftInverse f g :=
  rightInverse_of_leftInverse hfg

variable (f g) in
theorem leftInverse_iff_rightInverse :
    Function.LeftInverse f g ↔ Function.RightInverse f g :=
  ⟨rightInverse_of_leftInverse, leftInverse_of_rightInverse⟩

/-- If `f : M →ₗ[R] N` and `g : N →ₗ[R] M` where `M` and `N` are invertible `R`-modules, and `f` is
a left inverse of `g`, then in fact `f` is also the right inverse of `g`, and we promote this to
an `R`-module isomorphism. -/
def linearEquivOfLeftInverse (hfg : Function.LeftInverse f g) : M ≃ₗ[R] N :=
  .ofLinear f g (LinearMap.ext hfg) (LinearMap.ext <| rightInverse_of_leftInverse hfg)

@[simp] lemma linearEquivOfLeftInverse_apply (hfg : Function.LeftInverse f g) (x : M) :
    linearEquivOfLeftInverse hfg x = f x := rfl

@[simp] lemma linearEquivOfLeftInverse_symm_apply (hfg : Function.LeftInverse f g) (x : N) :
    (linearEquivOfLeftInverse hfg).symm x = g x := rfl

/-- If `f : M →ₗ[R] N` and `g : N →ₗ[R] M` where `M` and `N` are invertible `R`-modules, and `f` is
a right inverse of `g`, then in fact `f` is also the left inverse of `g`, and we promote this to
an `R`-module isomorphism. -/
def linearEquivOfRightInverse (hfg : Function.RightInverse f g) : M ≃ₗ[R] N :=
  .ofLinear f g (LinearMap.ext <| leftInverse_of_rightInverse hfg) (LinearMap.ext hfg)

@[simp] lemma linearEquivOfRightInverse_apply (hfg : Function.RightInverse f g) (x : M) :
    linearEquivOfRightInverse hfg x = f x := rfl

@[simp] lemma linearEquivOfRightInverse_symm_apply (hfg : Function.RightInverse f g) (x : N) :
    (linearEquivOfRightInverse hfg).symm x = g x := rfl

end LinearEquiv

section Algebra

section algEquivOfRing

variable [Semiring A] [Algebra R A] [Module.Invertible R A]

/-- If an `R`-algebra `A` is also an invertible `R`-module, then it is in fact isomorphic to the
base ring `R`. The algebra structure gives us a map `A ⊗ A → A`, which after tensoring by `Aᵛ`
becomes a map `A → R`, which is the inverse map we seek. -/
noncomputable def algEquivOfRing : R ≃ₐ[R] A :=
  let inv : A →ₗ[R] R :=
    linearEquiv R A ∘ₗ
      (LinearMap.mul' R A).lTensor (Dual R A) ∘ₗ
      (leftCancelEquiv A (linearEquiv R A)).symm
  have right : inv ∘ₗ Algebra.linearMap R A = LinearMap.id :=
    let ⟨s, hs⟩ := exists_finset ((linearEquiv R A).symm 1)
    LinearMap.ext_ring <| by simp [inv, hs, sum_tmul, map_sum, ← (LinearEquiv.symm_apply_eq _).1 hs]
  { linearEquivOfRightInverse (f := Algebra.linearMap R A) (g := inv) (LinearMap.ext_iff.1 right),
    Algebra.ofId R A with }

variable {A} in
@[simp] lemma algEquivOfRing_apply (x : R) : algEquivOfRing R A x = algebraMap R A x := rfl

end algEquivOfRing

section CommSemiring

variable [CommSemiring A] [Algebra R A]

instance : Module.Invertible A (A ⊗[R] M) :=
  .right (M := A ⊗[R] Dual R M) <| (AlgebraTensorModule.distribBaseChange ..).symm ≪≫ₗ
    AlgebraTensorModule.congr (.refl A A) (linearEquiv R M) ≪≫ₗ AlgebraTensorModule.rid ..

variable {R M N A} in
theorem of_isLocalization (S : Submonoid R) [IsLocalization S A]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] [Module A N] [IsScalarTower R A N] :
    Module.Invertible A N :=
  .congr (IsLocalizedModule.isBaseChange S A f).equiv

instance (S : Submonoid R) : Module.Invertible (Localization S) (LocalizedModule S M) :=
  of_isLocalization S (LocalizedModule.mkLinearMap S M)

instance (L) [AddCommMonoid L] [Module R L] [Module A L] [IsScalarTower R A L]
    [Module.Invertible A L] : Module.Invertible A (L ⊗[R] M) :=
  .congr (AlgebraTensorModule.cancelBaseChange R A A L M)

end CommSemiring

end Algebra

end Invertible

end Module

section PicardGroup

open CategoryTheory Module

instance (M : (Skeleton <| SemimoduleCat.{u} R)ˣ) : Module.Invertible R M :=
  .right (Quotient.eq.mp M.inv_mul).some.toLinearEquivₛ

instance (R : Type u) [CommRing R] (M : (Skeleton <| ModuleCat.{u} R)ˣ) : Module.Invertible R M :=
  .right (Quotient.eq.mp M.inv_mul).some.toLinearEquiv

instance : Small.{u} (Skeleton <| SemimoduleCat.{u} R)ˣ :=
  let sf := Σ n, ModuleCon R (Fin n → R)
  have {c₁ c₂ : sf} : c₁ = c₂ → c₁.2.Quotient ≃ₗ[R] c₂.2.Quotient := by rintro rfl; exact .refl ..
  let f (M : (Skeleton <| SemimoduleCat.{u} R)ˣ) : sf := ⟨_, Finite.kerReprₛ R M⟩
  small_of_injective (f := f) fun M N eq ↦ Units.ext <| Quotient.out_equiv_out.mp
    ⟨((Finite.reprEquivₛ R M).symm ≪≫ₗ this eq ≪≫ₗ Finite.reprEquivₛ R N).toModuleIsoₛ⟩

instance (R : Type u) [CommRing R] : Small.{u} (Skeleton <| ModuleCat.{u} R)ˣ :=
  small_map (Units.mapEquiv <| Skeleton.mulEquiv ModuleCat.equivalenceSemimoduleCat).toEquiv

/-- The Picard group of a commutative semiring R consists of the invertible R-modules,
up to isomorphism. -/
def CommRing.Pic (R : Type u) [CommSemiring R] : Type u :=
  Shrink (Skeleton <| SemimoduleCat.{u} R)ˣ

open CommRing (Pic)

noncomputable instance : CommGroup (Pic R) := fast_instance% (equivShrink _).symm.commGroup

variable (M N : Type*) [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [Module.Invertible R M] [Module.Invertible R N]

instance : Module.Invertible R (Finite.reprₛ R M) := .congr (Finite.reprEquivₛ R M).symm

namespace CommRing.Pic

variable {R} in
/-- A representative of an element in the Picard group. -/
abbrev AsModule (M : Pic R) : Type u := ((equivShrink _).symm M).val

noncomputable instance : CoeSort (Pic R) (Type u) := ⟨AsModule⟩

noncomputable instance (R) [CommRing R] (M : Pic R) : AddCommGroup M :=
  Module.addCommMonoidToAddCommGroup R

set_option backward.privateInPublic true in
private noncomputable def equivShrinkLinearEquiv (M : (Skeleton <| SemimoduleCat.{u} R)ˣ) :
    (id <| equivShrink _ M : Pic R) ≃ₗ[R] M :=
  have {M N : Skeleton (SemimoduleCat.{u} R)} : M = N → M ≃ₗ[R] N := by rintro rfl; exact .refl ..
  this (by simp)

/-- The class of an invertible module in the Picard group. -/
protected noncomputable def mk : Pic R := equivShrink _ <|
  letI M' := Finite.reprₛ R M
  .mkOfMulEqOne ⟦.of R M'⟧ ⟦.of R (Dual R M')⟧ <| by
    rw [← toSkeleton, ← toSkeleton, mul_comm, ← Skeleton.toSkeleton_tensorObj]
    exact Quotient.sound ⟨(Invertible.linearEquiv R _).toModuleIsoₛ⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `mk R M` is indeed the class of `M`. -/
noncomputable def mk.linearEquiv : Pic.mk R M ≃ₗ[R] M :=
  equivShrinkLinearEquiv R _ ≪≫ₗ (Quotient.mk_out (s := isIsomorphicSetoid _)
    (SemimoduleCat.of R (Finite.reprₛ R M))).some.toLinearEquivₛ ≪≫ₗ Finite.reprEquivₛ R M

variable {R M N}

theorem mk_eq_iff {N : Pic R} : Pic.mk R M = N ↔ Nonempty (M ≃ₗ[R] N) where
  mp := (· ▸ ⟨(mk.linearEquiv R M).symm⟩)
  mpr := fun ⟨e⟩ ↦ ((equivShrink _).apply_eq_iff_eq_symm_apply).mpr <|
    Units.ext <| Quotient.mk_eq_iff_out.mpr ⟨(Finite.reprEquivₛ R M ≪≫ₗ e).toModuleIsoₛ⟩

theorem mk_eq_self {M : Pic R} : Pic.mk R M = M := mk_eq_iff.mpr ⟨.refl ..⟩

theorem ext_iff {M N : Pic R} : M = N ↔ Nonempty (M ≃ₗ[R] N) := by
  rw [← mk_eq_iff, mk_eq_self]

theorem mk_eq_mk_iff : Pic.mk R M = Pic.mk R N ↔ Nonempty (M ≃ₗ[R] N) :=
  let eN := mk.linearEquiv R N
  mk_eq_iff.trans ⟨fun ⟨e⟩ ↦ ⟨e ≪≫ₗ eN⟩, fun ⟨e⟩ ↦ ⟨e ≪≫ₗ eN.symm⟩⟩

theorem mk_self : Pic.mk R R = 1 :=
  congr_arg (equivShrink _) <| Units.ext <| Quotient.sound ⟨(Finite.reprEquivₛ R R).toModuleIsoₛ⟩

theorem mk_eq_one_iff : Pic.mk R M = 1 ↔ Nonempty (M ≃ₗ[R] R) := by
  rw [← mk_self, mk_eq_mk_iff]

theorem mk_eq_one_iff_free : Pic.mk R M = 1 ↔ Free R M :=
  mk_eq_one_iff.trans Invertible.free_iff_linearEquiv.symm

variable (R M) in
theorem mk_eq_one [Free R M] : Pic.mk R M = 1 := mk_eq_one_iff_free.mpr ‹_›

instance : Free R (1 : Pic R) := mk_eq_one_iff_free.mp mk_eq_self

theorem mk_tensor : Pic.mk R (M ⊗[R] N) = Pic.mk R M * Pic.mk R N :=
  congr_arg (equivShrink _) <| Units.ext <| by
    simp_rw [Pic.mk, Equiv.symm_apply_apply]
    refine (Quotient.sound ?_).trans (Skeleton.toSkeleton_tensorObj ..)
    exact ⟨(Finite.reprEquivₛ R _ ≪≫ₗ TensorProduct.congr
      (Finite.reprEquivₛ R M).symm (Finite.reprEquivₛ R N).symm).toModuleIsoₛ⟩

theorem mk_dual : Pic.mk R (Dual R M) = (Pic.mk R M)⁻¹ :=
  congr_arg (equivShrink _) <| Units.ext <| by
    rw [Pic.mk, Equiv.symm_apply_apply]
    exact Quotient.sound ⟨(Finite.reprEquivₛ R _ ≪≫ₗ (Finite.reprEquivₛ R _).dualMap).toModuleIsoₛ⟩

theorem inv_eq_dual (M : Pic R) : M⁻¹ = Pic.mk R (Dual R M) := by
  rw [mk_dual, mk_eq_self]

theorem mul_eq_tensor (M N : Pic R) : M * N = Pic.mk R (M ⊗[R] N) := by
  rw [mk_tensor, mk_eq_self, mk_eq_self]

theorem subsingleton_iffₛ : Subsingleton (Pic R) ↔
    ∀ (M : Type u) [AddCommMonoid M] [Module R M], Module.Invertible R M → Free R M :=
  .trans ⟨fun _ M _ _ _ ↦ Subsingleton.elim ..,
      fun h ↦ ⟨fun M N ↦ by rw [← mk_eq_self (M := M), ← mk_eq_self (M := N), h, h]⟩⟩ <|
    forall₄_congr fun _ _ _ _ ↦ mk_eq_one_iff_free

theorem subsingleton_iff {R : Type u} [CommRing R] : Subsingleton (Pic R) ↔
    ∀ (M : Type u) [AddCommGroup M] [Module R M], Module.Invertible R M → Free R M :=
  subsingleton_iffₛ.trans
    ⟨fun h M ↦ h M, fun h M ↦ let _ := @Module.addCommMonoidToAddCommGroup R; h M⟩

instance [Subsingleton (Pic R)] : Free R M :=
  have := subsingleton_iffₛ.mp ‹_› (Finite.reprₛ R M) inferInstance
  .of_equiv (Finite.reprEquivₛ R M)

/- TODO: it's still true that the Picard group of a (commutative) local semiring is trivial;
in fact invertible modules over a semiring are Zariski-locally free (but projective module may
not be). See Remark 7.10, Example 9.6 and 9.8, and Theorem 11.7 in [BorgerJun2024]. -/
instance (R) [CommRing R] [IsLocalRing R] : Subsingleton (Pic R) :=
  subsingleton_iff.mpr fun _ _ _ _ ↦ free_of_flat_of_isLocalRing

/-- The Picard group of a semilocal ring is trivial. -/
instance (R) [CommRing R] [Finite (MaximalSpectrum R)] : Subsingleton (Pic R) :=
  subsingleton_iff.mpr fun _ _ _ _ ↦ free_of_flat_of_finrank_eq _ _ 1
    fun _ ↦ let _ := @Ideal.Quotient.field; Invertible.finrank_eq_one ..

variable (R) (A B : Type*) [CommSemiring A] [CommSemiring B] [Algebra R A]

open AlgebraTensorModule in
/-- Every `R`-algebra `A` gives rise to a homomorphism between Picard groups of `R` and `A`. -/
@[simps] noncomputable def mapAlgebra : Pic R →* Pic A where
  toFun M := .mk A (A ⊗[R] M)
  map_one' := mk_eq_one_iff.mpr (Invertible.free_iff_linearEquiv.mp inferInstance)
  map_mul' _ _ := by
    rw [← mk_tensor, mk_eq_mk_iff]
    refine ⟨congr (.refl ..) (.symm (mk_eq_iff.mp ?_).some) ≪≫ₗ distribBaseChange R A ..⟩
    simp_rw [mk_tensor, mk_eq_self]

variable {R A B} [Algebra R B] [Algebra A B] [IsScalarTower R A B]

theorem mapAlgebra_mapAlgebra {M : Pic R} : mapAlgebra A B (mapAlgebra R A M) = mapAlgebra R B M :=
  mk_eq_mk_iff.mpr ⟨AlgebraTensorModule.congr (.refl ..) (mk.linearEquiv ..) ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange ..⟩

theorem mapAlgebra_comp_mapAlgebra : (mapAlgebra A B).comp (mapAlgebra R A) = mapAlgebra R B := by
  ext; rw [MonoidHom.comp_apply, mapAlgebra_mapAlgebra]

theorem mapAlgebra_self_apply {M : Pic R} : mapAlgebra R R M = M :=
  mk_eq_iff.mpr ⟨TensorProduct.lid ..⟩

theorem mapAlgebra_self : mapAlgebra R R = .id _ := by ext; exact mapAlgebra_self_apply

variable {S T : Type*} [CommSemiring S] [CommSemiring T] (f : R →+* S) (g : S →+* T)

/-- Every ring homomorphism between commutative semirings induces a homomorphism between
Picard groups. -/
noncomputable def mapRingHom : Pic R →* Pic S :=
  let := f.toAlgebra; mapAlgebra R S

theorem mapRingHom_algebraMap : mapRingHom (algebraMap R A) = mapAlgebra R A := by
  rw [mapRingHom, toAlgebra_algebraMap]

variable {f g}

theorem mapRingHom_comp_mapRingHom :
    (mapRingHom g).comp (mapRingHom f) = mapRingHom (g.comp f) := by
  algebraize [f, g, g.comp f]
  simp_rw [mapRingHom, mapAlgebra_comp_mapAlgebra]

theorem mapRingHom_mapRingHom {M : Pic R} :
    mapRingHom g (mapRingHom f M) = mapRingHom (g.comp f) M :=
  congr($mapRingHom_comp_mapRingHom M)

set_option backward.isDefEq.respectTransparency false in
theorem mapRingHom_id : mapRingHom (.id R) = .id _ := by
  rw [mapRingHom, mapAlgebra_self]

theorem mapRingHom_id_apply {M : Pic R} : mapRingHom (.id R) M = M :=
  congr($mapRingHom_id M)

/-- Picard group as a functor from the category of commutative semirings to
the category of abelian groups. -/
noncomputable def functor : CommSemiRingCat.{u} ⥤ CommGrpCat.{u} where
  obj R := .of (Pic R)
  map f := CommGrpCat.ofHom (mapRingHom f.hom)
  map_id _ := CommGrpCat.Hom.ext mapRingHom_id
  map_comp _ _ := CommGrpCat.Hom.ext mapRingHom_comp_mapRingHom.symm

end Pic

variable (A : Type*) [CommSemiring A] [Algebra R A]

/-- The relative Picard group of an `R`-algebra `A`, denoted `Pic(A/R)`,
defined to be the kernel of `Pic.mapAlgebra R A`. -/
noncomputable def relPic : Subgroup (Pic R) := (Pic.mapAlgebra R A).ker

theorem relPic_eq_top [Subsingleton (Pic A)] : relPic R A = ⊤ :=
  top_unique fun _ _ ↦ Subsingleton.elim ..

end CommRing

end PicardGroup

namespace Module.Invertible

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Module.Invertible R M]

-- TODO: generalize to CommSemiring by generalizing `CommRing.Pic.instSubsingletonOfIsLocalRing`
theorem tensorProductComm_eq_refl : TensorProduct.comm R M M = .refl .. := by
  let f (P : Ideal R) [P.IsMaximal] := LocalizedModule.mkLinearMap P.primeCompl M
  let ff (P : Ideal R) [P.IsMaximal] := TensorProduct.map (f P) (f P)
  refine LinearEquiv.toLinearMap_injective <| LinearMap.eq_of_localization_maximal _ ff _ ff _ _
    fun P _ ↦ .trans (b := (TensorProduct.comm ..).toLinearMap) ?_ ?_
  · apply IsLocalizedModule.linearMap_ext P.primeCompl (ff P) (ff P)
    ext; dsimp
    apply IsLocalizedModule.map_apply
  let Rp := Localization P.primeCompl
  have ⟨e⟩ := free_iff_linearEquiv.mp (inferInstance : Free Rp (LocalizedModule P.primeCompl M))
  have e := e.restrictScalars R
  ext x y
  refine (congr e e ≪≫ₗ equivOfCompatibleSMul Rp ..).injective ?_
  suffices e y ⊗ₜ[Rp] e x = e x ⊗ₜ e y by simpa [equivOfCompatibleSMul]
  conv_lhs => rw [← mul_one (e y), ← smul_eq_mul, smul_tmul, smul_eq_mul,
    mul_comm, ← smul_eq_mul, ← smul_tmul, smul_eq_mul, mul_one]

variable {R M} in
theorem tmul_comm {m₁ m₂ : M} : m₁ ⊗ₜ[R] m₂ = m₂ ⊗ₜ m₁ :=
  DFunLike.congr_fun (tensorProductComm_eq_refl ..) (m₂ ⊗ₜ m₁)

end Module.Invertible

namespace Submodule

open Module Invertible

variable {R M A}

section Semiring

variable [Semiring A] [Algebra R A] [FaithfulSMul R A]

open LinearMap in
set_option backward.privateInPublic true in
private theorem projective_units_and_mul'_comp_lTensor_bijective (I : (Submodule R A)ˣ) :
    Projective R I ∧ Function.Bijective (mul' R A ∘ₗ I.1.subtype.lTensor A) := by
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
  have hf (x : I.1) (i : S) : algebraMap R A (f x i) = x * r i • a i := by
    dsimp [f, ← Algebra.linearMap_apply]
    exact LinearEquiv.ofInjective_symm_apply ..
  let g : (S → R) →ₗ[R] I := .lsum _ _ ℕ fun i ↦ .toSpanSingleton _ _ ⟨b i, hT' <| hb i⟩
  have hgf : g ∘ₗ f = .id := LinearMap.ext fun x ↦ Subtype.ext <| by
    simp only [g, lsum_apply, comp_apply, sum_apply, toSpanSingleton_apply, proj_apply]
    simp_rw [coe_sum, coe_smul, Algebra.smul_def, hf, mul_assoc, ← Finset.mul_sum,
      Algebra.smul_mul_assoc, eq, (Finset.sum_coe_sort ..).trans hr.2, mul_one, id_apply]
  set m := mul' R A ∘ₗ I.1.subtype.lTensor A
  have eq : (piScalarRight R R A S).toLinearMap ∘ₗ f.lTensor A =
      (.pi fun i : S ↦ mulRight R (r i • a i)) ∘ₗ m := by
    ext; simp [(Algebra.smul_def ..).trans (Algebra.commutes ..), hf, m, mul_assoc]
  have := (piScalarRight R R A S).injective.comp <| injective_of_comp_eq_id
    (f.lTensor A) (g.lTensor A) <| by rw [← lTensor_comp, hgf, lTensor_id]
  rw [← LinearEquiv.coe_toLinearMap, ← coe_comp, eq, coe_comp] at this
  refine ⟨.of_split f g hgf, .of_comp this, range_eq_top.mp ?_⟩
  rw [show m = mulMap ⊤ I ∘ₗ (topEquiv.symm.rTensor I.1).toLinearMap by ext; rfl, range_comp,
    LinearEquiv.range, map_top, mulMap_range, top_mul_eq_top_of_mul_eq_one I.inv_mul]

open LinearMap in
instance projective_units (I : (Submodule R A)ˣ) : Projective R I :=
  (projective_units_and_mul'_comp_lTensor_bijective I).1

theorem projective_of_isUnit {I : Submodule R A} (hI : IsUnit I) : Projective R I :=
  projective_units hI.unit

variable (I J : (Submodule R A)ˣ)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Given two invertible `R`-submodules in an `R`-algebra `A`, the `R`-linear map from
`I ⊗[R] J` to `I * J` induced by multiplication is an isomorphism. -/
noncomputable def tensorEquivMul : I ⊗[R] J ≃ₗ[R] I * J := by
  refine .ofBijective _ ⟨.of_comp (f := Submodule.subtype _) ?_, mulMap'_surjective _ _⟩
  convert (projective_units_and_mul'_comp_lTensor_bijective J).2.1.comp
    (Flat.rTensor_preserves_injective_linearMap _ I.1.subtype_injective)
  simp_rw [← LinearMap.coe_comp]
  congr 1; ext; rfl

/-- Given an invertible `R`-submodule `I` in an `R`-algebra `A`, the `R`-linear map
from `I ⊗[R] I⁻¹` to `R` induced by multiplication is an isomorphism. -/
noncomputable def tensorInvEquiv : I ⊗[R] ↑I⁻¹ ≃ₗ[R] R :=
  tensorEquivMul I _ ≪≫ₗ .ofEq _ _ (I.mul_inv.trans one_eq_range) ≪≫ₗ
    .symm (.ofInjective _ (FaithfulSMul.algebraMap_injective R A))

instance : Module.Invertible R I := .left (tensorInvEquiv I)

open CommRing Pic

variable (R A) in
/-- The group homomorphism from the invertible submodules in a faithful algebra over `R` to
the Picard group of `R`. See Lemma 2.2 in [RobertsSingh1993]. -/
@[simps] noncomputable def unitsToPic : (Submodule R A)ˣ →* Pic R where
  toFun I := Pic.mk R I
  map_one' := mk_eq_one_iff.mpr
    ⟨.ofEq _ _ one_eq_range ≪≫ₗ .symm (.ofInjective _ (FaithfulSMul.algebraMap_injective R A))⟩
  map_mul' I J := by rw [← mk_tensor, mk_eq_mk_iff]; exact ⟨(tensorEquivMul I J).symm⟩

/-- The image of an invertible `R`-submodule `I ⊆ A` under `unitsToPic` is isomorphic to `I`. -/
noncomputable def unitsToPicEquiv (I : (Submodule R A)ˣ) : unitsToPic R A I ≃ₗ[R] I :=
  (mk_eq_iff.mp rfl).some.symm

variable (R A)

theorem ker_unitsToPic :
    (unitsToPic R A).ker = (Units.map (spanSingleton R).toMonoidHom).range := by
  ext I; constructor <;> intro h
  · have e := (mk_eq_one_iff.mp h).some.symm
    have e' := (mk_eq_one_iff.mp (inv_mem h)).some.symm
    have h := eq_span_singleton_of_surjective e.surjective
    have h' := eq_span_singleton_of_surjective e'.surjective
    refine ⟨(isUnit_iff_exists_and_exists.mpr ⟨?_, ?_⟩).unit, Units.ext h.symm⟩
    · have : span R {(e 1).1 * e' 1} = 1 := by simpa [span_mul_span] using congr($h * $h').symm
      have ⟨r, hr⟩ := span_singleton_eq_one_iff.mp this
      exact ⟨e' 1 * algebraMap R A r.inv, by simp [← mul_assoc, hr, ← map_mul]⟩
    · have : span R {(e' 1).1 * e 1} = 1 := by simpa [span_mul_span] using congr($h' * $h).symm
      have ⟨r, hr⟩ := span_singleton_eq_one_iff.mp this
      exact ⟨algebraMap R A r.inv * e' 1, by simp [mul_assoc, hr, ← map_mul]⟩
  · obtain ⟨x, rfl⟩ := h
    exact mk_eq_one_iff.mpr ⟨.symm <| (.ofInjective (LinearMap.toSpanSingleton R A x) fun _ _ eq ↦
      (faithfulSMul_iff_injective_smul_one R A).mp ‹_› <| by simpa using congr($eq * x.inv)) ≪≫ₗ
      .ofEq _ _ (by ext; simp [mem_span_singleton])⟩

/-- Exactness of the sequence `1 → Rˣ → Aˣ → (Submodule R A)ˣ → Pic R → Pic A`
at `(Submodule R A)ˣ`. -/
theorem mulExact_unitsMap_spanSingleton_unitsToPic :
    Function.MulExact (Units.map (spanSingleton R).toMonoidHom) (unitsToPic R A) :=
  MonoidHom.mulExact_iff.mpr (ker_unitsToPic R A)

end Semiring

end Submodule

namespace Module.Flat

variable {R M A} [Semiring A] [Algebra R A] (e : A ⊗[R] M ≃ₗ[A] A)

/-- If a flat `R`-module becomes free of rank 1 after base-changing to a faithful `R`-algebra `A`,
then it embeds into `A`. -/
noncomputable def toAlgebra : M →ₗ[R] A :=
  e.restrictScalars R ∘ₗ (Algebra.ofId R A).toLinearMap.rTensor M ∘ₗ (TensorProduct.lid R M).symm

variable [Flat R M] [FaithfulSMul R A]

theorem toAlgebra_injective : Function.Injective (toAlgebra e) := by
  simpa [toAlgebra] using
    Flat.rTensor_preserves_injective_linearMap _ (FaithfulSMul.algebraMap_injective R A)

/-- A flat `R`-module as a `R`-submodule of a faithful `R`-algebra. -/
noncomputable abbrev submoduleAlgebra : Submodule R A := LinearMap.range (toAlgebra e)

/-- An isomorphism between a flat `R`-module and its realization as a submodule in
a faithful `R`-algebra. -/
noncomputable def submoduleAlgebraEquiv : submoduleAlgebra e ≃ₗ[R] M :=
  .symm <| .ofInjective _ (toAlgebra_injective e)

instance : Flat R (submoduleAlgebra e) := .of_linearEquiv (submoduleAlgebraEquiv e)

instance [Module.Invertible R M] : Module.Invertible R (submoduleAlgebra e) :=
  .congr (submoduleAlgebraEquiv e).symm

/-- When a flat `R`-module `M` is embedded as a submodule of a faithful `R`-algebra `A`,
the multiplication map induces an isomorphism `A ⊗[R] M ≃ₗ[A] A`. -/
noncomputable def tensorSubmoduleAlgebraEquiv : A ⊗[R] submoduleAlgebra e ≃ₗ[A] A :=
  .ofBijective (.mul'' R A ∘ₗ AlgebraTensorModule.lTensor A A (Submodule.subtype _)) <| by
    convert (AlgebraTensorModule.congr (.refl ..) (submoduleAlgebraEquiv e) ≪≫ₗ e).bijective
    ext x
    refine x.induction_on (by simp) ?_ (by simp +contextual)
    intro a x
    obtain ⟨m, rfl⟩ := (submoduleAlgebraEquiv e).symm.surjective x
    suffices a * toAlgebra e m = e (a ⊗ₜ[R] m) by simpa using this
    dsimp [toAlgebra]
    rw [map_one, ← smul_eq_mul, ← map_smul, smul_tmul', smul_eq_mul, mul_one]

theorem top_mul_submoduleAlgebra : ⊤ * submoduleAlgebra e = ⊤ := by
  rw [← Submodule.mulMap_range]
  convert (Submodule.topEquiv.rTensor _ ≪≫ₗ (tensorSubmoduleAlgebraEquiv e).restrictScalars R).range
  ext; rfl

/-- When a flat `R`-module `M` is embedded as a submodule of a faithful `R`-algebra `A`,
we have `I ⊗[R] M ≃ₗ[R] I * M` for any `R`-submodule `I` of `A`. -/
noncomputable def tensorSubmoduleAlgebraEquivMul (I : Submodule R A) :
    I ⊗[R] submoduleAlgebra e ≃ₗ[R] I * submoduleAlgebra e := by
  refine .ofBijective _ ⟨.of_comp (f := Submodule.subtype _) ?_, Submodule.mulMap'_surjective _ _⟩
  convert ((tensorSubmoduleAlgebraEquiv e).restrictScalars R).injective.comp
    (Flat.rTensor_preserves_injective_linearMap _ I.subtype_injective)
  simp_rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp]
  congr 1; ext; rfl

end Module.Flat

namespace Module.Invertible

@[deprecated (since := "2025-11-23")] alias embAlgebra := Flat.toAlgebra
@[deprecated (since := "2025-11-23")] alias embAlgebra_injective := Flat.toAlgebra_injective
@[deprecated (since := "2025-11-23")] alias toSubmodule := Flat.submoduleAlgebra

end Module.Invertible

section PicardGroup

variable [CommSemiring A] [Algebra R A] [FaithfulSMul R A]

open CommRing Pic LinearMap Module.Flat

theorem Submodule.range_unitsToPic : (unitsToPic R A).range = relPic R A := by
  ext M; constructor <;> intro h
  · obtain ⟨I, rfl⟩ := h
    exact mk_eq_one_iff.mpr ⟨AlgebraTensorModule.congr (.refl ..) (unitsToPicEquiv I) ≪≫ₗ
      .ofBijective ((Algebra.TensorProduct.lmul'' R).toLinearMap ∘ₗ AlgebraTensorModule.lTensor A A
        I.1.subtype) (projective_units_and_mul'_comp_lTensor_bijective I).2⟩
  have e := (mk_eq_one_iff.mp h).some
  have f := (mk_eq_one_iff.mp (inv_mem h)).some
  refine ⟨(isUnit_of_mul_isUnit_left (x := submoduleAlgebra e) (y := submoduleAlgebra f) ?_).unit,
    mk_eq_iff.mpr ⟨submoduleAlgebraEquiv e⟩⟩
  have := eq_span_singleton_of_surjective <| LinearEquiv.surjective <|
    (congr (submoduleAlgebraEquiv e) (submoduleAlgebraEquiv f) ≪≫ₗ
    (mk_eq_one_iff.mp <| by simp_rw [mk_tensor, mk_eq_self, mul_inv_cancel]).some).symm ≪≫ₗ
    tensorSubmoduleAlgebraEquivMul f (submoduleAlgebra e)
  rw [this]
  apply_fun (⊤ * ·) at this
  simp_rw [← mul_assoc, top_mul_submoduleAlgebra] at this
  obtain ⟨a, -, eq⟩ := mem_mul_span_singleton.mp (this ▸ mem_top (x := 1))
  exact .map (spanSingleton R).toMonoidHom (.of_mul_eq_one_right _ eq)

/-- Exactness of the sequence `1 → Rˣ → Aˣ → (Submodule R A)ˣ → Pic R → Pic A` at `Pic R`. -/
theorem Submodule.mulExact_unitsToPic_mapAlgebra :
    Function.MulExact (unitsToPic R A) (mapAlgebra R A) :=
  MonoidHom.mulExact_iff.mpr (range_unitsToPic R A).symm

open QuotientGroup in
/-- If `A` is a faithful `R`-algebra, the relative Picard group Pic(A/R) is isomorphic to
the group of the invertible `R`-submodules in `A` modulo the principal submodules. -/
@[simps!] noncomputable def Submodule.unitsQuotEquivRelPic :
    (Submodule R A)ˣ ⧸ (Units.map (spanSingleton R).toMonoidHom).range ≃* relPic R A :=
  (QuotientGroup.congr _ _ (.refl _) ((Subgroup.map_id _).trans (ker_unitsToPic R A).symm)).trans <|
  (quotientKerEquivRange _).trans <| .subgroupCongr (range_unitsToPic R A)

/-- The class group of a domain is isomorphic to the Picard group. -/
@[simps!] noncomputable def ClassGroup.equivPic (R) [CommRing R] [IsDomain R] :
    ClassGroup R ≃* Pic R :=
  (mulEquivUnitsSubmoduleQuotRange R).trans <| .trans (Submodule.unitsQuotEquivRelPic R _) <|
    .trans (.subgroupCongr <| relPic_eq_top R _) Subgroup.topEquiv

/-- The Picard group of a domain with normalizable gcd is trivial.
This includes unique factorization domains. -/
@[stacks 0BCH]
instance (R) [CommRing R] [IsDomain R] [Nonempty (NormalizedGCDMonoid R)] : Subsingleton (Pic R) :=
  Equiv.subsingleton (ClassGroup.equivPic R).toEquiv.symm

end PicardGroup

open CommRing Pic

section Ideal

variable (R M N : Type*) [CommRing R]
variable [AddCommGroup M] [Module R M] [Module.Invertible R M]
variable [AddCommGroup N] [Module R N] [Module.Invertible R N]

/-- If `FractionRing R` has trivial Picard group,
every invertible `R`-module is isomorphic to an ideal. -/
theorem Module.Invertible.exists_linearEquiv_ideal [Subsingleton (Pic (FractionRing R))] :
    ∃ I : Ideal R, Nonempty (M ≃ₗ[R] I) :=
  have : Pic.mk R M ∈ relPic R (FractionRing R) := Subsingleton.elim ..
  have ⟨I, eq⟩ := Submodule.range_unitsToPic R (FractionRing R) ▸ this
  have ⟨e⟩ := mk_eq_mk_iff.mp eq.symm
  ⟨_, ⟨e ≪≫ₗ FractionalIdeal.equivNumOfIsLocalization
    ⟨_, I.submodule_isFractional (S := nonZeroDivisors R)⟩⟩⟩

/- Every invertible module over a domain is isomorphic to an ideal. -/
example [IsDomain R] : ∃ I : Ideal R, Nonempty (M ≃ₗ[R] I) :=
  Module.Invertible.exists_linearEquiv_ideal R M

/- Every invertible module over a Noetherian ring is isomorphic to an ideal.
See https://mathoverflow.net/a/499611. -/
example [IsNoetherianRing R] : ∃ I : Ideal R, Nonempty (M ≃ₗ[R] I) :=
  Module.Invertible.exists_linearEquiv_ideal R M

variable {R} in
/-- In a total ring of fractions, if two ideals are inverse to each other in the Picard group,
the only possibility is that they are both the whole ring. -/
theorem Ideal.eq_top_of_mk_tensor_eq_one [IsFractionRing R R] (I J : Ideal R)
    [Module.Invertible R I] [Module.Invertible R J] (h : Pic.mk R (I ⊗[R] J) = 1) :
    I = ⊤ ∧ J = ⊤ := by
  have ⟨e⟩ := mk_eq_one_iff.mp h
  have e := e.symm ≪≫ₗ Submodule.LinearDisjoint.mulMap
    (.of_left_le_one_of_flat I J <| le_top.trans one_eq_top.ge)
  have : IsUnit (e 1 : R) := IsFractionRing.self_iff_nonZeroDivisors_le_isUnit.mp ‹_› <|
      IsRegular.mem_nonZeroDivisors <| isRightRegular_iff_isRegular.mp <| by
    rw [IsRightRegular]
    convert Subtype.val_injective.comp e.injective using 2
    rw [← smul_eq_mul, ← Submodule.coe_smul, ← map_smul, smul_eq_mul, mul_one, Function.comp_apply]
  constructor <;> refine eq_top_of_isUnit_mem _ ?_ this
  exacts [mul_le_right (e 1).2, mul_le_left (e 1).2]

end Ideal
