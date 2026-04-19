/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
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

universe u₁ u₂ u₃ u₄

/-- The category of `C^n` 𝕜-manifolds. -/
structure MfldCat (𝕜 : Type u₁) [NontriviallyNormedField 𝕜] (n : WithTop ℕ∞) where
  /-- The object in `MfldCat` associated to a type equipped with the appropriate typeclasses. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u₂
  /-- The model normed space. -/
  E : Type u₃
  /-- The chart space. -/
  H : Type u₄
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

variable {𝕜 : Type u₁} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {X Y Z : Type u₂} {E E' E'' : Type u₃} {H H' H'' : Type u₄}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {I'' : ModelWithCorners 𝕜 E'' H''}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' n Y]
  [TopologicalSpace Z] [ChartedSpace H'' Z] [IsManifold I'' n Z]

instance : CoeSort (MfldCat 𝕜 n) (Type u₂) := ⟨MfldCat.carrier⟩

attribute [coe] MfldCat.carrier

variable (X E H I) in
lemma coe_of : (of (n := n) X E H I : Type u₂) = X := rfl

lemma of_carrier (M : MfldCat 𝕜 n) : of (n := n) M.carrier M.E M.H M.I = M := rfl

/-- The type of morphisms in `MfldCat`. -/
@[ext]
structure Hom (M N : MfldCat.{u₁, u₂, u₃, u₄} 𝕜 n) where
  /-- The underlying `C^n` map. -/
  hom' : ContMDiffMap M.I N.I M N n

instance : Category (MfldCat 𝕜 n) where
  Hom M N := Hom M N
  id M := ⟨ContMDiffMap.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (MfldCat 𝕜 n)
    (fun M N => ContMDiffMap M.I N.I M N n) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `MfldCat` back into a `ContMDiffMap`. -/
abbrev Hom.hom {M N : MfldCat 𝕜 n} (f : Hom M N) :=
  ConcreteCategory.hom (C := MfldCat 𝕜 n) f

/-- Typecheck a `ContMDiffMap` as a morphism in `MfldCat`. -/
abbrev ofHom (f : ContMDiffMap I I' X Y n) : of (n := n) X E H I ⟶ of (n := n) Y E' H' I' :=
  ConcreteCategory.ofHom (C := MfldCat 𝕜 n) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (M N : MfldCat 𝕜 n) (f : Hom M N) :=
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
def Hom.equivContMDiffMap (M N : MfldCat 𝕜 n) :
    (M ⟶ N) ≃ ContMDiffMap M.I N.I M N n where
  toFun f := f.hom
  invFun f := ofHom f

/-- Replace a function coercion for a morphism `MfldCat.of X E H I ⟶ MfldCat.of Y E' H' I'` with
the definitionally equal function coercion for a `ContMDiffMap I I' X Y n`. -/
@[simp] theorem coe_of_of {f : ContMDiffMap I I' X Y n} {x} :
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

/-- A normed space is a `C^n` manifold (modeled on itself). -/
abbrev ofNormedSpace (n : WithTop ℕ∞) (E : Type u₃) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    MfldCat 𝕜 n :=
  of E E E (modelWithCornersSelf 𝕜 E)

/-- `MfldCat 𝕜 n` has a forgetful functor to `TopCat`. -/
instance : HasForget₂ (MfldCat 𝕜 n) TopCat.{u₂} where
  forget₂.obj M := TopCat.of M
  forget₂.map f := TopCat.ofHom ⟨f.hom, f.hom.contMDiff.continuous⟩

-- TODO: define a functor `FGModuleCat 𝕜 ⥤ MfldCat 𝕜 n`.

/-- Any diffeomorphism induces an isomorphism in `MfldCat`. -/
@[simps]
def isoOfDiffeomorph {M N : MfldCat 𝕜 n} (f : M ≃ₘ^n⟮M.I, N.I⟯ N) : M ≅ N where
  hom := ofHom f.toContMDiffMap
  inv := ofHom f.symm.toContMDiffMap
  hom_inv_id := by ext x; exact f.left_inv x
  inv_hom_id := by ext x; exact f.right_inv x

/-- Any isomorphism in `MfldCat` induces a diffeomorphism. -/
@[simps]
def diffeomorphOfIso {M N : MfldCat 𝕜 n} (f : M ≅ N) : M ≃ₘ^n⟮M.I, N.I⟯ N where
  toFun := f.hom
  invFun := f.inv
  left_inv _ := by simp
  right_inv _ := by simp
  contMDiff_toFun := f.hom.hom.contMDiff
  contMDiff_invFun := f.inv.hom.contMDiff

@[simp]
theorem of_isoOfDiffeomorph {M N : MfldCat 𝕜 n} (f : M ≃ₘ^n⟮M.I, N.I⟯ N) :
    diffeomorphOfIso (isoOfDiffeomorph f) = f := by
  ext
  rfl

@[simp]
theorem of_diffeomorphOfIso {M N : MfldCat 𝕜 n} (f : M ≅ N) :
    isoOfDiffeomorph (diffeomorphOfIso f) = f := by
  ext
  rfl

/-- The constant morphism `M ⟶ N` in `MfldCat` given by `y : N`. -/
def const {M N : MfldCat 𝕜 n} (y : N) : M ⟶ N :=
  ofHom ⟨fun _ ↦ y, contMDiff_const⟩

@[simp]
lemma const_apply {M N : MfldCat 𝕜 n} (y : N) (x : M) :
    const y x = y := rfl

section TangentFunctor

variable (M : MfldCat 𝕜 (n + 1))

local instance : IsManifold M.I 1 M := IsManifold.of_le (n := n + 1) le_add_self
local instance : IsManifold M.I n M := IsManifold.of_le (n := n + 1) le_self_add
-- This implies  `TangentBundle M.I M` is a manifold by `Bundle.TotalSpace.isManifold`
local instance : ContMDiffVectorBundle n M.E (TangentSpace M.I : M → Type u₃) M.I :=
  TangentBundle.contMDiffVectorBundle


/-- The tangent functor `MfldCat 𝕜 (n + 1) ⥤ MfldCat 𝕜 n` -- Sends a `C^(n+1)` manifold to its
tangent bundle; Sends a `C^(n+1)` map to it's pushforward. -/
noncomputable def tangentFunctor :
    MfldCat 𝕜 (n + 1) ⥤ MfldCat 𝕜 n where
  obj M := of (TangentBundle M.I M) (M.E × M.E) (ModelProd M.H M.E) M.I.tangent
  map {M N} f :=
    ofHom ⟨tangentMap M.I N.I f.hom, ContMDiff.contMDiff_tangentMap f.hom.contMDiff le_rfl⟩
  map_id _ := Hom.ext <| Subtype.ext tangentMap_id
  map_comp f g := Hom.ext <| Subtype.ext <| tangentMap_comp
    (g.hom.contMDiff.mdifferentiable (by simp))
    (f.hom.contMDiff.mdifferentiable (by simp))

end TangentFunctor

end MfldCat
