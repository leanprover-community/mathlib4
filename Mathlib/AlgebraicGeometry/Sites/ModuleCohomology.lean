/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The module structure on the cohomology of a sheaf of modules

The cohomology groups of a sheaf of modules `F : X.Modules` carry an intrinsic action of the
global sections `Γ(X, ⊤)`: a global section acts on `F` by multiplication, and `Ext` is additive
in its second variable. No morphism to an affine scheme is involved; see
`AlgebraicGeometry.Scheme.Modules.globalSectionsModule`.

If `X` is a scheme over `R` via `f : X ⟶ Spec R`, an `R`-module structure is obtained from this by
restriction of scalars along `globalSectionsRingHom f : R →+* Γ(X, ⊤)`; see `cohomologyModule`.

## TODO

The action should ultimately come from a presheaf of `𝒪_X`-modules structure on
`Sheaf.cohomologyPresheaf`, with `Γ(X, U)` acting on `Hⁿ(U, F)` and the action here being
restriction of scalars along `Γ(X, ⊤) →+* Γ(X, U)`. That is blocked on the two open items in the
`TODO` of `Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean`, in particular on the
isomorphism `(F.cohomologyPresheaf n).obj (op U) ≃+ Sheaf.H (F.over U) n`: a section `r : Γ(X, U)`
is an endomorphism of `F` restricted to `U`, not of `F`, so it is invisible to the second-variable
action on `Ext (ℤ[U]) F n`. The action defined here, being uniform in the first `Ext` variable,
applies to `Sheaf.H` and to every value of `Sheaf.cohomologyPresheaf` at once.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/--
The cohomology of a sheaf of modules in degree `n`
-/
abbrev H := ((SheafOfModules.toSheaf _).obj F).H

/-- The intrinsic `Γ(X, ⊤)`-module structure on the degree-`n` cohomology of the abelian sheaf
underlying an `𝒪_X`-module `F`: a global section acts by multiplication on `F`, and `Ext` is
additive in its second variable.

This is not made a global instance because its head `Ext _ _ _` is far too general an instance
key; make it a local instance where it is needed. -/
@[reducible] noncomputable def globalSectionsModule (n : ℕ) : Module Γ(X, ⊤) (F.H n) :=
  Abelian.Ext.moduleOfRingHom (smulEnd F) n

lemma globalSectionsModule_smul_def (n : ℕ) (r : Γ(X, ⊤)) (x : F.H n) :
    letI := F.globalSectionsModule n
    r • x = x.comp (Abelian.Ext.mk₀ (smulEnd F r)) (add_zero n) := rfl

variable {R : CommRingCat} (f : X ⟶ Spec R)

/-- The `R`-module structure on the degree-`n` cohomology of the abelian sheaf underlying an
`𝒪_X`-module `F`, for `X` a scheme over `R` via `f : X ⟶ Spec R`. It is restriction of scalars of
the intrinsic `Γ(X, ⊤)`-action along `globalSectionsRingHom f`. -/
@[reducible] noncomputable def cohomologyModule (n : ℕ) : Module R (F.H n) :=
  letI := F.globalSectionsModule n
  Module.compHom _ (globalSectionsRingHom f)

lemma cohomologyModule_smul_def (n : ℕ) (r : R) (x : F.H n) :
    letI := F.cohomologyModule f n
    letI := F.globalSectionsModule n
    r • x = globalSectionsRingHom f r • x := rfl

/--
For a morphism `f : X ⟶ Spec R` and a sheaf of modules `F : X.Modules`, `F.h f n` gives the finrank
of the `n`th cohomology group of `F` as an `R`-module.
-/
noncomputable def h (n : ℕ) :=
  letI := F.cohomologyModule f n
  Module.finrank R (F.H n)

end AlgebraicGeometry.Scheme.Modules
