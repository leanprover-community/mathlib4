/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Category instance for smooth manifolds

We introduce the category `MfldCat 𝕜 n` of `C^n` manifolds over a field `𝕜`. Each object bundles the
underlying manifold together with its model space `E`, chart space `H`, and
`I : ModelWithCorners 𝕜 E H`. Thus, `MfldCat 𝕜 n` also includes manifolds with boundary and corners.

We define a forgetful functor `forget₂ (MfldCat 𝕜 n) TopCat` taking smooth manifolds to topological
spaces. We also define `MfldCat.ofNormedSpace` turning any `NormedSpace 𝕜 E` into a manifold. In the
future, we plan to define a functor `FGModuleCat 𝕜 ⥤ MfldCat 𝕜 n` from the category of
finite-dimensional vector spaces over `𝕜`.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory
open scoped Manifold

universe u

/-- The category of `C^n` 𝕜-manifolds. -/
structure MfldCat (𝕜 : Type u) [NontriviallyNormedField 𝕜] (n : WithTop ℕ∞) where
  /-- The object in `MfldCat` associated to a type equipped with the appropriate typeclasses. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  /-- The model normed space. -/
  E : Type u
  /-- The chart space. -/
  H : Type u
  [instNAG : NormedAddCommGroup E]
  [instNS : NormedSpace 𝕜 E]
  [instTopH : TopologicalSpace H]
  /-- The model with corners. -/
  I : ModelWithCorners 𝕜 E H
  [instTop : TopologicalSpace carrier]
  [instCharted : ChartedSpace H carrier]
  [instManifold : IsManifold I n carrier]

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `MfldCat.of M E H I` being printed as `{ carrier := M, ... }` by
`delabStructureInstance`. -/
@[app_delab MfldCat.of]
meta def MfldCat.delabOf : Delab := delabApp

end Notation

attribute [instance] MfldCat.instNAG MfldCat.instNS MfldCat.instTopH MfldCat.instTop
  MfldCat.instCharted MfldCat.instManifold

initialize_simps_projections MfldCat
  (-instNAG, -instNS, -instTopH, -instTop, -instCharted, -instManifold)

namespace MfldCat

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}

instance : CoeSort (MfldCat 𝕜 n) (Type u) := ⟨MfldCat.carrier⟩

attribute [coe] MfldCat.carrier

lemma coe_of (M : Type u) (E : Type u) (H : Type u)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I n M] : (of (n := n) M E H I : Type u) = M := rfl

lemma of_carrier (M : MfldCat.{u} 𝕜 n) : of (n := n) M.carrier M.E M.H M.I = M := rfl

/-- The type of morphisms in `MfldCat`. -/
@[ext]
structure Hom (M N : MfldCat 𝕜 n) where
  /-- The underlying `C^n` map. -/
  hom' : ContMDiffMap M.I N.I M N n

instance : Category (MfldCat 𝕜 n) where
  Hom M N := Hom M N
  id M := ⟨ContMDiffMap.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory.{u} (MfldCat 𝕜 n)
    (fun M N => ContMDiffMap M.I N.I M N n) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `MfldCat` back into a `ContMDiffMap`. -/
abbrev Hom.hom {M N : MfldCat.{u} 𝕜 n} (f : Hom M N) :=
  ConcreteCategory.hom (C := MfldCat 𝕜 n) f

/-- Typecheck a `ContMDiffMap` as a morphism in `MfldCat`. -/
abbrev ofHom {M N : Type u} {E E' : Type u} {H H' : Type u}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
    {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' n N]
    (f : ContMDiffMap I I' M N n) :
    of (n := n) M E H I ⟶ of (n := n) N E' H' I' :=
  ConcreteCategory.ofHom (C := MfldCat 𝕜 n) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (M N : MfldCat.{u} 𝕜 n) (f : Hom M N) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
lemma hom_id {M : MfldCat 𝕜 n} :
    (𝟙 M : M ⟶ M).hom = ContMDiffMap.id := rfl

@[simp]
theorem id_app (M : MfldCat 𝕜 n) (x : ↑M) : (𝟙 M : M ⟶ M) x = x := rfl

@[simp]
theorem coe_id (M : MfldCat 𝕜 n) : (𝟙 M : M → M) = _root_.id := rfl

@[simp]
lemma hom_comp {M N P : MfldCat 𝕜 n} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp]
theorem comp_app {M N P : MfldCat 𝕜 n} (f : M ⟶ N) (g : N ⟶ P) (x : M) :
    (f ≫ g : M → P) x = g (f x) := rfl

@[simp]
theorem coe_comp {M N P : MfldCat 𝕜 n} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g : M → P) = g ∘ f := rfl

@[ext]
lemma hom_ext {M N : MfldCat 𝕜 n} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[ext]
lemma ext {M N : MfldCat 𝕜 n} {f g : M ⟶ N} (w : ∀ x : M, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

section ofHom

variable {X Y Z : Type u} {E E' E'' : Type u} {H H' H'' : Type u}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
    [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [TopologicalSpace H'']
    {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
    {I'' : ModelWithCorners 𝕜 E'' H''}
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' n Y]
    [TopologicalSpace Z] [ChartedSpace H'' Z] [IsManifold I'' n Z]

@[simp]
lemma hom_ofHom (f : ContMDiffMap I I' X Y n) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {M N : MfldCat 𝕜 n} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id :
    ofHom (ContMDiffMap.id : ContMDiffMap I I X X n) = 𝟙 (of (n := n) X E H I) := rfl

@[simp]
lemma ofHom_comp (f : ContMDiffMap I I' X Y n) (g : ContMDiffMap I' I'' Y Z n) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

lemma ofHom_apply (f : ContMDiffMap I I' X Y n) (x : X) : (ofHom f) x = f x := rfl

lemma hom_inv_id_apply {M N : MfldCat 𝕜 n} (f : M ≅ N) (x : M) : f.inv (f.hom x) = x := by
  simp

lemma inv_hom_id_apply {M N : MfldCat 𝕜 n} (f : M ≅ N) (y : N) : f.hom (f.inv y) = y := by
  simp

end ofHom

/-- Morphisms in `MfldCat` are equivalent to `ContMDiffMap`s. -/
@[simps]
def Hom.equivContMDiffMap (M N : MfldCat.{u} 𝕜 n) :
    (M ⟶ N) ≃ ContMDiffMap M.I N.I M N n where
  toFun f := f.hom
  invFun f := ofHom f

/-- Replace a function coercion for a morphism `MfldCat.of X E H I ⟶ MfldCat.of Y E' H' I'` with
the definitionally equal function coercion for a `ContMDiffMap I I' X Y n`. -/
@[simp] theorem coe_of_of {X Y E E' H H' : Type u}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
    {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' n Y]
    {f : ContMDiffMap I I' X Y n} {x} :
    @DFunLike.coe (of (n := n) X E H I ⟶ of (n := n) Y E' H' I')
      ((CategoryTheory.forget (MfldCat 𝕜 n)).obj (of (n := n) X E H I))
      (fun _ ↦ (CategoryTheory.forget (MfldCat 𝕜 n)).obj (of (n := n) Y E' H' I'))
      ConcreteCategory.instFunLike
      (ofHom f) x =
    @DFunLike.coe (ContMDiffMap I I' X Y n) X
      (fun _ ↦ Y) _
      f x :=
  rfl

instance inhabited : Inhabited (MfldCat 𝕜 n) :=
  ⟨of 𝕜 𝕜 𝕜 (modelWithCornersSelf 𝕜 𝕜)⟩

/-- Bundle a normed space as a `C^n` manifold without boundary (modeled on itself). -/
@[simps]
abbrev ofNormedSpace (n : WithTop ℕ∞) (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    MfldCat.{u} 𝕜 n :=
  of E E E (modelWithCornersSelf 𝕜 E)

/-- `MfldCat 𝕜 n` has a forgetful functor to `TopCat`, sending a manifold to its underlying
topological space and a `C^n` map to its underlying continuous map. -/
instance : HasForget₂ (MfldCat.{u} 𝕜 n) TopCat.{u} where
  forget₂.obj M := TopCat.of M
  forget₂.map f := TopCat.ofHom ⟨f.hom, f.hom.contMDiff.continuous⟩

-- TODO: define a functor `FGModuleCat 𝕜 ⥤ MfldCat 𝕜 n` from the category of
-- finite-dimensional `𝕜`-vector spaces. Requires `[CompleteSpace 𝕜]` and a choice of norm on each
-- object (e.g. via `Module.finBasis 𝕜 V` transporting the norm from `EuclideanSpace 𝕜 (Fin _)`).

/-- Any diffeomorphism induces an isomorphism in `MfldCat`. -/
@[simps]
def isoOfDiffeomorph {M N : MfldCat.{u} 𝕜 n} (f : M ≃ₘ^n⟮M.I, N.I⟯ N) : M ≅ N where
  hom := ofHom f.toContMDiffMap
  inv := ofHom f.symm.toContMDiffMap
  hom_inv_id := by ext x; exact f.left_inv x
  inv_hom_id := by ext x; exact f.right_inv x

/-- Any isomorphism in `MfldCat` induces a diffeomorphism. -/
@[simps]
def diffeomorphOfIso {M N : MfldCat.{u} 𝕜 n} (f : M ≅ N) : M ≃ₘ^n⟮M.I, N.I⟯ N where
  toFun := f.hom
  invFun := f.inv
  left_inv _ := by simp
  right_inv _ := by simp
  contMDiff_toFun := f.hom.hom.contMDiff
  contMDiff_invFun := f.inv.hom.contMDiff

@[simp]
theorem of_isoOfDiffeomorph {M N : MfldCat.{u} 𝕜 n} (f : M ≃ₘ^n⟮M.I, N.I⟯ N) :
    diffeomorphOfIso (isoOfDiffeomorph f) = f := by
  ext
  rfl

@[simp]
theorem of_diffeomorphOfIso {M N : MfldCat.{u} 𝕜 n} (f : M ≅ N) :
    isoOfDiffeomorph (diffeomorphOfIso f) = f := by
  ext
  rfl

/-- The constant morphism `M ⟶ N` in `MfldCat` given by `y : N`. -/
def const {M N : MfldCat.{u} 𝕜 n} (y : N) : M ⟶ N :=
  ofHom ⟨fun _ ↦ y, contMDiff_const⟩

@[simp]
lemma const_apply {M N : MfldCat.{u} 𝕜 n} (y : N) (x : M) :
    const y x = y := rfl

end MfldCat
