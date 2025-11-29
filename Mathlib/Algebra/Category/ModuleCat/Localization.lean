/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Localization.Module

/-!

# Localized Module in ModuleCat

For `ModuleCat.{v} R` and `R` being `Small.{v} R`, localized module can be canonically constructed
within `ModuleCat.{v} (Localization S)`.

-/

@[expose] public section

universe v u

variable (R : Type u) [CommRing R]

open CategoryTheory

local instance [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M] (S : Submonoid R) :
    Small.{v} (LocalizedModule S M) :=
  small_of_surjective (IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M))

variable {R}

/-- Shrink of `LocalizedModule S M` in category which `M` belongs. -/
noncomputable def ModuleCat.localizedModule [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    ModuleCat.{v} (Localization S) :=
  ModuleCat.of.{v} _ (Shrink.{v} (LocalizedModule S M))

/-- The `R` module structure on `M.localizedModule S` given by the
`R` module structure on (Shrink.{v} (LocalizedModule S M)) -/
noncomputable instance [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    Module R (M.localizedModule S) :=
  inferInstanceAs (Module R (Shrink.{v} (LocalizedModule S M)))

/-- The corresponding linear map to make `M.localizedModule` is localized module of `M`. -/
noncomputable def ModuleCat.localizedModule_mkLinearMap [Small.{v} R] (M : ModuleCat.{v} R)
    (S : Submonoid R) : M →ₗ[R] (M.localizedModule S) :=
  (Shrink.linearEquiv.{v} R _).symm.toLinearMap.comp (LocalizedModule.mkLinearMap S M)

instance ModuleCat.localizedModule_isLocalizedModule [Small.{v} R] (M : ModuleCat.{v} R)
    (S : Submonoid R) : IsLocalizedModule S (M.localizedModule_mkLinearMap S) := by
  simpa [ModuleCat.localizedModule_mkLinearMap] using IsLocalizedModule.of_linearEquiv _ _ _

instance [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    IsScalarTower R (Localization S) (M.localizedModule S) :=
  (equivShrink (LocalizedModule S M)).symm.isScalarTower R (Localization S)

/-- The category version of `IsLocalizedModule.mapExtendScalars`. -/
noncomputable def ModuleCat.localizedModule_map [Small.{v} R] {M N : ModuleCat.{v} R}
    (S : Submonoid R) (f : M ⟶ N) : (M.localizedModule S) ⟶ (N.localizedModule S) :=
  ModuleCat.ofHom.{v} <| IsLocalizedModule.mapExtendScalars S (M.localizedModule_mkLinearMap S)
    (N.localizedModule_mkLinearMap S) (Localization S) (ModuleCat.homLinearEquiv (S := R) f)
