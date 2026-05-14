/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Module.Shrink
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Logic.Small.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.SetLike

/-!

# Localized Module in ModuleCat

For a ring `R` satisfying `[Small.{v} R]` and a submonoid `S` of `R`,
this file defines an exact functor `ModuleCat.{v} R ⥤ ModuleCat.{v} (Localization S)`,
see `ModuleCat.localizedModuleFunctor`.

-/

@[expose] public section

universe v u

variable (R : Type u) [CommRing R]

open CategoryTheory

local instance [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M] (S : Submonoid R) :
    Small.{v} (LocalizedModule S M) :=
  small_of_surjective (IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M))

variable {R}

namespace ModuleCat

/-- Shrink of `LocalizedModule S M` in category which `M` belongs. -/
noncomputable def localizedModule [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    ModuleCat.{v} (Localization S) :=
  ModuleCat.of.{v} _ (Shrink.{v} (LocalizedModule S M))

/-- The `R` module structure on `M.localizedModule S` given by the
`R` module structure on `Shrink.{v} (LocalizedModule S M)` -/
noncomputable instance [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    Module R (M.localizedModule S) :=
  inferInstanceAs (Module R (Shrink.{v} (LocalizedModule S M)))

instance [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    IsScalarTower R (Localization S) (M.localizedModule S) :=
  (equivShrink (LocalizedModule S M)).symm.isScalarTower R (Localization S)

/-- The linear map `M →ₗ[R] (M.localizedModule S)` which
exhibits `M.localizedModule S` as a localized module of `M`. -/
noncomputable def localizedModuleMkLinearMap [Small.{v} R] (M : ModuleCat.{v} R)
    (S : Submonoid R) : M →ₗ[R] (M.localizedModule S) :=
  (Shrink.linearEquiv.{v} R _).symm.toLinearMap.comp (LocalizedModule.mkLinearMap S M)

set_option backward.isDefEq.respectTransparency false in
instance localizedModule_isLocalizedModule [Small.{v} R] (M : ModuleCat.{v} R)
    (S : Submonoid R) : IsLocalizedModule S (M.localizedModuleMkLinearMap S) := by
  dsimp only [localizedModuleMkLinearMap]
  infer_instance

/-- `IsLocalizedModule.mapExtendScalars` as a morphism in `ModuleCat`. -/
@[simps!]
noncomputable def localizedModuleMap [Small.{v} R] {M N : ModuleCat.{v} R}
    (S : Submonoid R) (f : M ⟶ N) : (M.localizedModule S) ⟶ (N.localizedModule S) :=
  ModuleCat.ofHom.{v} <| IsLocalizedModule.mapExtendScalars S (M.localizedModuleMkLinearMap S)
    (N.localizedModuleMkLinearMap S) (Localization S) f.hom

/-- The functor `ModuleCat.{v} R ⥤ ModuleCat.{v} (Localization S)` sending
`M` to `M.localizedModule S` and `f : M1 ⟶ M2` to
`IsLocalizedModule.mapExtendScalars S _ _ (Localization S) f.hom`. -/
@[simps]
noncomputable def localizedModuleFunctor [Small.{v} R] (S : Submonoid R) :
    ModuleCat.{v} R ⥤ ModuleCat.{v} (Localization S) where
  obj M := M.localizedModule S
  map := ModuleCat.localizedModuleMap S
  map_comp {X Y Z} f g := by
    ext
    simp [IsLocalizedModule.map_comp' S _ (Y.localizedModuleMkLinearMap S)]

instance [Small.{v} R] (S : Submonoid R) : (ModuleCat.localizedModuleFunctor S).Additive where

lemma localizedModuleFunctor_map_exact [Small.{v} R] (S : Submonoid R)
    (T : ShortComplex (ModuleCat.{v} R)) (h : T.Exact) :
    (T.map (ModuleCat.localizedModuleFunctor S)).Exact := by
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact IsLocalizedModule.map_exact S (T.X₁.localizedModuleMkLinearMap S)
    (T.X₂.localizedModuleMkLinearMap S) (T.X₃.localizedModuleMkLinearMap S) _ _ h

instance [Small.{v} R] (S : Submonoid R) :
    Limits.PreservesFiniteLimits (ModuleCat.localizedModuleFunctor.{v} S) := by
  have := ((Functor.exact_tfae _).out 1 3).mp (ModuleCat.localizedModuleFunctor_map_exact S)
  exact this.1

instance [Small.{v} R] (S : Submonoid R) :
    Limits.PreservesFiniteColimits (ModuleCat.localizedModuleFunctor.{v} S) := by
  have := ((Functor.exact_tfae _).out 1 3).mp (ModuleCat.localizedModuleFunctor_map_exact S)
  exact this.2

end ModuleCat
