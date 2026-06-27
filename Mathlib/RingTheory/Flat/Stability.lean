/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Flatness is stable under composition and base change

We show that flatness is stable under composition and base change.

## Main theorems

* `Module.Flat.trans`: if `S` is a flat `R`-algebra and `M` is a flat `S`-module,
                      then `M` is a flat `R`-module
* `Module.Flat.baseChange`: if `M` is a flat `R`-module and `S` is any `R`-algebra,
                            then `S ⊗[R] M` is `S`-flat.
* `Module.Flat.of_isLocalizedModule`: if `M` is a flat `R`-module and `S` is a submonoid of `R`
                                          then the localization of `M` at `S` is flat as a module
                                          for the localization of `R` at `S`.
-/

public section

universe u v w t t'

open Function (Injective Surjective)

open LinearMap (lsmul rTensor lTensor)

open TensorProduct

namespace Module.Flat

section Composition

/-! ### Composition

Let `R` be a ring, `S` a flat `R`-algebra and `M` a flat `S`-module. To show that `M` is flat
as an `R`-module, we show that the inclusion of an `R`-submodule `N` into an `R`-module `P`
tensored on the left with `M` is injective. For this consider the composition of natural maps

`M ⊗[R] N ≃ M ⊗[S] (S ⊗[R] N) → M ⊗[S] (S ⊗[R] P) ≃ M ⊗[R] P`;

`S ⊗[R] N → S ⊗[R] P` is injective by `R`-flatness of `S`,
so the middle map is injective by `S`-flatness of `M`.
-/

variable (R : Type u) (S : Type v) (M : Type w)
  [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]

open AlgebraTensorModule in
/-- If `S` is a flat `R`-algebra, then any flat `S`-Module is also `R`-flat. -/
theorem trans [Flat R S] [Flat S M] : Flat R M := by
  rw [Flat.iff_lTensor_injectiveₛ]
  introv
  rw [← coe_lTensor (A := S), ← EquivLike.injective_comp (cancelBaseChange R S S _ _),
    ← LinearEquiv.coe_coe, ← LinearMap.coe_comp, lTensor_comp_cancelBaseChange,
    LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_injective]
  iterate 2 apply Flat.lTensor_preserves_injective_linearMap
  exact Subtype.val_injective

variable {R M} in
@[simp]
lemma ulift_left_iff : Flat (ULift.{t} R) M ↔ Flat R M := by
  refine ⟨fun h ↦ .trans _ (ULift R) _, fun h ↦ ?_⟩
  have : Module.Flat (ULift.{t} R) R := .of_ulift
  let _ := ULift.algebra'
  exact .trans _ R _

variable {R M} in
@[simp]
lemma ulift_right_iff : Flat R (ULift.{t} M) ↔ Flat R M :=
  Flat.equiv_iff ULift.moduleEquiv

end Composition

section BaseChange

/-! ### Base change

Let `R` be a ring, `M` a flat `R`-module and `S` an `R`-algebra, then
`S ⊗[R] M` is a flat `S`-module. This is a special case of `Module.Flat.instTensorProduct`.

-/

variable (R : Type u) (S : Type v) (M : Type w)
  [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- If `M` is a flat `R`-module and `S` is any `R`-algebra, `S ⊗[R] M` is `S`-flat. -/
instance baseChange [Flat R M] : Flat S (S ⊗[R] M) := inferInstance

/-- A base change of a flat module is flat. -/
theorem isBaseChange [Flat R M] (N : Type t) [AddCommMonoid N] [Module R N] [Module S N]
    [IsScalarTower R S N] {f : M →ₗ[R] N} (h : IsBaseChange S f) :
    Flat S N :=
  of_linearEquiv (IsBaseChange.equiv h).symm

end BaseChange

section Localization

variable {R : Type u} {M Mp : Type*} (Rp : Type v)
  [CommSemiring R] [AddCommMonoid M] [Module R M] [CommSemiring Rp] [Algebra R Rp]
  [AddCommMonoid Mp] [Module R Mp] [Module Rp Mp] [IsScalarTower R Rp Mp]

instance localizedModule [Flat R M] (S : Submonoid R) :
    Flat (Localization S) (LocalizedModule S M) := by
  apply Flat.isBaseChange (R := R) (S := Localization S)
    (f := LocalizedModule.mkLinearMap S M)
  rw [← isLocalizedModule_iff_isBaseChange S]
  exact localizedModuleIsLocalizedModule S

theorem of_isLocalizedModule [Flat R M] (S : Submonoid R) [IsLocalization S Rp]
    (f : M →ₗ[R] Mp) [h : IsLocalizedModule S f] : Flat Rp Mp := by
  fapply Flat.isBaseChange (R := R) (M := M) (S := Rp) (N := Mp)
  exact (isLocalizedModule_iff_isBaseChange S Rp f).mp h

instance {A : Type*} [CommSemiring A] [Algebra R A] [Flat R A] (S : Submonoid R) :
    Flat (Localization S) (Localization (Algebra.algebraMapSubmonoid A S)) :=
  of_isLocalizedModule _ S (IsScalarTower.toAlgHom R A _).toLinearMap

end Localization

section TensorTower

/-- **Flatness of a tensor product over a tower.** If `A` is a flat `S`-algebra and `M` is a flat
`R`-module (where `R → S → A` is a tower), then `A ⊗[S] M` is a flat `R`-module. -/
theorem tensor_tower {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (A : Type*) [CommRing A] [Algebra S A] [Algebra R A] [IsScalarTower R S A] [Flat S A]
    (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Flat R M] :
    Flat R (A ⊗[S] M) := by
  rw [iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  let g : M ⊗[R] N →ₗ[S] M ⊗[R] N' := TensorProduct.AlgebraTensorModule.lTensor S M f
  have hg : Function.Injective g := by
    have hcoe : (g : M ⊗[R] N → M ⊗[R] N') = LinearMap.lTensor M f := by ext x; rfl
    rw [hcoe]
    exact lTensor_preserves_injective_linearMap (M := M) f hf
  have hbot : Function.Injective (LinearMap.lTensor A g) :=
    lTensor_preserves_injective_linearMap (M := A) g hg
  let eN := TensorProduct.AlgebraTensorModule.assoc R S S A M N
  let eN' := TensorProduct.AlgebraTensorModule.assoc R S S A M N'
  have hsqL : eN'.toLinearMap.restrictScalars R ∘ₗ LinearMap.lTensor (A ⊗[S] M) f
      = (LinearMap.lTensor A g).restrictScalars R ∘ₗ eN.toLinearMap.restrictScalars R := by
    apply TensorProduct.ext'
    intro w n
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [eN, eN', g, TensorProduct.AlgebraTensorModule.assoc_tmul,
        TensorProduct.AlgebraTensorModule.lTensor_tmul]
    | add a b ha hb => simp [TensorProduct.add_tmul, map_add, ha, hb]
  have hsq : (eN' : _ → _) ∘ LinearMap.lTensor (A ⊗[S] M) f
      = LinearMap.lTensor A g ∘ (eN : _ → _) := by
    simpa using congrArg (fun L : _ →ₗ[R] _ ↦ (L : _ → _)) hsqL
  have hcomp : Function.Injective ((eN' : _ → _) ∘ LinearMap.lTensor (A ⊗[S] M) f) := by
    rw [hsq]; exact hbot.comp eN.injective
  exact hcomp.of_comp

end TensorTower

end Module.Flat
