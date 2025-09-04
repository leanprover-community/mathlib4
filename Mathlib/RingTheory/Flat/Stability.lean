/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Flatness is stable under composition and base change

We show that flatness is stable under composition and base change.

## Main theorems

* `Module.Flat.comp`: if `S` is a flat `R`-algebra and `M` is a flat `S`-module,
                      then `M` is a flat `R`-module
* `Module.Flat.baseChange`: if `M` is a flat `R`-module and `S` is any `R`-algebra,
                            then `S ⊗[R] M` is `S`-flat.
* `Module.Flat.of_isLocalizedModule`: if `M` is a flat `R`-module and `S` is a submonoid of `R`
                                          then the localization of `M` at `S` is flat as a module
                                          for the localization of `R` at `S`.
-/

universe u v w t

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

end Localization

end Module.Flat
