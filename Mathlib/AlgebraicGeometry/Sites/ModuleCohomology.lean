/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The module structure on the cohomology of a sheaf of modules

In this file we provide some interface for working with the cohomology of sheaves of modules on
schemes.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.H`: the cohomology `Hⁿ(X, F)` of an `𝒪ₓ`-module, that is,
  the cohomology of the underlying abelian sheaf. This is just a thin wrapper around
  `CategoryTheory.Sheaf.H`.
* `AlgebraicGeometry.Scheme.Modules.h`: the `Module.finrank` of `F.H n` over `R`.

## TODO

The action should ultimately come from a presheaf of `𝒪ₓ`-modules structure on
`Sheaf.cohomologyPresheaf`, with `Γ(X, U)` acting on `Hⁿ(U, F)`. That is blocked by the `TODO`s of
`Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean`, in particular on the
isomorphism `(F.cohomologyPresheaf n).obj (op U) ≃+ Sheaf.H (F.over U) n`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/--
The cohomology of a sheaf of modules in degree `n`.

Note this is the cohomology of the abelian sheaf underlying `F`. That is, `Ext` taken in the
category of abelian sheaves on `X` rather than in `X.Modules`.
-/
abbrev H (n : ℕ) := ((SheafOfModules.toSheaf _).obj F).H n

noncomputable instance globalModule (n : ℕ) : Module Γ(X, ⊤) (F.H n) :=
  Module.compHom (F.H n) (smulEnd F)

lemma globalModule_smul (n : ℕ) (r : Γ(X, ⊤)) (x : F.H n) : r • x = smulEnd F r • x := rfl

variable {R : CommRingCat} (f : X ⟶ Spec R)

/-- The `R`-module structure on the degree-`n` cohomology of the abelian sheaf underlying an
`𝒪ₓ`-module `F`, for `X` a scheme over `R` via `f : X ⟶ Spec R`: `Scheme.Modules.moduleOfBase`
applied to `Scheme.Modules.globalModule`. -/
@[instance_reducible]
noncomputable def cohomologyModule (n : ℕ) : Module R (F.H n) :=
  moduleOfBase f (F.H n)

lemma cohomologyModule_smul (n : ℕ) (r : R) (x : F.H n) :
    letI := F.cohomologyModule f n
    r • x = ((Scheme.ΓSpecIso R).inv ≫ f.appTop) r • x :=
  moduleOfBase_smul f _ r x

section Map

variable {F}

/-- The map on cohomology induced by a morphism of `𝒪ₓ`-modules, that is, `Sheaf.H.map` of the
underlying morphism of abelian sheaves. It is `Γ(X, ⊤)`-linear, and hence `R`-linear;
see `H.map_smul_global` and `H.map_smul`. -/
noncomputable abbrev H.map {F G : X.Modules} (φ : F ⟶ G) (n : ℕ) : F.H n →+ G.H n :=
  Sheaf.H.map ((SheafOfModules.toSheaf _).map φ) n

/-- `H.map φ n` is `Γ(X, ⊤)`-linear: `φ` is `𝒪ₓ`-linear, so it commutes with multiplication by a
global section (`Scheme.Modules.smulEnd`), and the action on cohomology is postcomposition with
that. -/
lemma H.map_smul_global {F G : X.Modules} (φ : F ⟶ G) (n : ℕ) (r : Γ(X, ⊤)) (x : F.H n) :
    H.map φ n (r • x) = r • H.map φ n x :=
  Abelian.Ext.smul_comp_mk₀_of_comm _ _ _ (toSheaf_map_comp_smulEnd φ r).symm x

/-- `H.map φ n` is `R`-linear, by restriction of scalars from `H.map_smul_global`. -/
lemma H.map_smul {F G : X.Modules} (φ : F ⟶ G) (n : ℕ) (r : R) (x : F.H n) :
    letI := F.cohomologyModule f n
    letI := G.cohomologyModule f n
    H.map φ n (r • x) = r • H.map φ n x :=
  H.map_smul_global φ n _ x

/-- `H.map φ n` packaged as an `R`-linear map, for use with the `LinearMap` API (kernels,
ranges, rank-nullity). The underlying function is `H.map φ n`; see `H.coe_mapₗ`. -/
noncomputable def H.mapₗ {F G : X.Modules} (φ : F ⟶ G) (n : ℕ) :
    letI := F.cohomologyModule f n
    letI := G.cohomologyModule f n
    F.H n →ₗ[R] G.H n :=
  letI := F.cohomologyModule f n
  letI := G.cohomologyModule f n
  { toFun := H.map φ n
    map_add' := map_add _
    map_smul' := fun r x => H.map_smul f φ n r x }

@[simp] lemma H.coe_mapₗ {F G : X.Modules} (φ : F ⟶ G) (n : ℕ) :
    letI := F.cohomologyModule f n
    letI := G.cohomologyModule f n
    ⇑(H.mapₗ f φ n) = H.map φ n := rfl

/-- An isomorphism of `𝒪ₓ`-modules induces an `R`-linear equivalence on cohomology in every
degree. -/
noncomputable def H.mapLinearEquiv {F G : X.Modules} (e : F ≅ G) (n : ℕ) :
    letI := F.cohomologyModule f n
    letI := G.cohomologyModule f n
    F.H n ≃ₗ[R] G.H n :=
  letI := F.cohomologyModule f n
  letI := G.cohomologyModule f n
  { toFun := Sheaf.H.map ((SheafOfModules.toSheaf _).mapIso e).hom n
    map_add' := map_add _
    map_smul' := fun r x => H.map_smul f e.hom n r x
    invFun := Sheaf.H.map ((SheafOfModules.toSheaf _).mapIso e).inv n
    left_inv := fun x => by
      rw [← Sheaf.H.map_comp_apply, Iso.hom_inv_id, Sheaf.H.map_id_apply]
    right_inv := fun x => by
      rw [← Sheaf.H.map_comp_apply, Iso.inv_hom_id, Sheaf.H.map_id_apply] }

@[simp] lemma H.coe_mapLinearEquiv {F G : X.Modules} (e : F ≅ G) (n : ℕ) :
    letI := F.cohomologyModule f n
    letI := G.cohomologyModule f n
    ⇑(H.mapLinearEquiv f e n) = H.map e.hom n := rfl

@[simp] lemma H.coe_mapLinearEquiv_symm {F G : X.Modules} (e : F ≅ G) (n : ℕ) :
    letI := F.cohomologyModule f n
    letI := G.cohomologyModule f n
    ⇑(H.mapLinearEquiv f e n).symm = H.map e.inv n := rfl

end Map

/--
For a morphism `f : X ⟶ Spec R` and a sheaf of modules `F : X.Modules`, `F.h f n` gives the finrank
of the `n`th cohomology group of `F` as an `R`-module. Note that this has the junk value `0` when
the rank of this module is infinite.
-/
protected noncomputable def h (n : ℕ) : ℕ :=
  letI := F.cohomologyModule f n
  Module.finrank R (F.H n)

variable {F}

lemma h_eq_of_iso {G : X.Modules} (e : F ≅ G) (n : ℕ) : F.h f n = G.h f n := by
  let := F.cohomologyModule f n
  let := G.cohomologyModule f n
  exact LinearEquiv.finrank_eq (H.mapLinearEquiv f e n)

variable (F)

lemma h_eq_zero_of_subsingleton [Nontrivial R] (n : ℕ) [Subsingleton (F.H n)] :
    F.h f n = 0 := by
  let := F.cohomologyModule f n
  exact Module.finrank_zero_of_subsingleton

lemma h_zero :
    letI := moduleOfBase f Γ(F, ⊤)
    F.h f 0 = Module.finrank R Γ(F, ⊤) := by
  let := F.cohomologyModule f 0
  let := moduleOfBase f Γ(F, ⊤)
  refine LinearEquiv.finrank_eq
    (AddEquiv.toLinearEquiv (R := R)
      (Sheaf.H.equiv₀ ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
        Limits.isTerminalTop : F.H 0 ≃+ Γ(F, ⊤)) fun r x => ?_)
  exact (Sheaf.H.equiv₀_naturality (f := smulEnd F _) Limits.isTerminalTop x).symm.trans
    (smulEnd_hom_app_top F _ _)

end AlgebraicGeometry.Scheme.Modules
