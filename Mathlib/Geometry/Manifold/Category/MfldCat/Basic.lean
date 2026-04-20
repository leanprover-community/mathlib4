/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# The category of $C^n$ manifolds

We introduce two categories of `C^n` manifolds:
* `ModelWithCorners.MfldCat I n`: the category of `C^n` manifolds modeled on a fixed
  `I : ModelWithCorners 𝕜 E H`. For example, choosing `I = 𝓘(ℝ, EuclideanSpace ℝ (Fin d))`
  yields the category of `C^n` real `d`-manifolds without boundary.
* `MfldCat 𝕜 n`: the category of `C^n` 𝕜-manifolds whose model can vary from object to object.
  Each object bundles a model vector space `E`, a model chart space `H`,
  `I : ModelWithCorners 𝕜 E H`, and a term of `ModelWithCorners.MfldCat I n`. Thus
  `MfldCat 𝕜 n` also includes manifolds with boundary and corners, of any dimension.

We define a forgetful functor `forget₂ (MfldCat 𝕜 n) TopCat` taking smooth manifolds to topological
spaces. We also define `MfldCat.ofNormedSpace` turning any `NormedSpace 𝕜 E` into a manifold. In
the future, we plan to define a functor `FGModuleCat 𝕜 ⥤ MfldCat 𝕜 n` from the category of
finite-dimensional vector spaces over `𝕜`.

# Implementation Notes
* We do not assume `[FiniteDimensional 𝕜 E] [T2Space M] [SigmaCompactSpace M]`, so these categories
  include non-Hausdorff, non-paracompact, and infite-dimensional manifolds.
* We keep `E`, `H` and `carrier` all in the same `Type u` since we do not care about large
  manifolds modelled on small spaces. `𝕜` is given a seperate `Type v`.
* The split between `ModelWithCorners.MfldCat` and `MfldCat` follows the principle that it is
  cheap to bundle an unbundled structure but expensive to do the reverse. Downstream code that
  wants "all manifolds modeled on `I`" can use the unbundled category directly.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory
open scoped Manifold ContDiff

universe u v

/-! ### The category `ModelWithCorners.MfldCat I n` of manifolds on a fixed model -/

namespace ModelWithCorners

/-- The category of `C^n` manifolds modeled on a fixed `I : ModelWithCorners 𝕜 E H`. -/
@[pp_with_univ, nolint checkUnivs]
structure MfldCat {𝕜 : Type v} [NontriviallyNormedField 𝕜]
    {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type u} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) where
  /-- The object in `ModelWithCorners.MfldCat I n` associated to a type equipped with the
  appropriate typeclasses. -/
  of ::
  /-- The underlying type. -/
  carrier : Type u
  [instTopologicalSpace : TopologicalSpace carrier]
  [instChartedSpace : ChartedSpace H carrier]
  [instIsManifold : IsManifold I n carrier]

attribute [instance] MfldCat.instTopologicalSpace MfldCat.instChartedSpace MfldCat.instIsManifold

initialize_simps_projections MfldCat
  (-instTopologicalSpace, -instChartedSpace, -instIsManifold)

namespace MfldCat

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {E : Type u} {H : Type u}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {X Y Z : Type u}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
  [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I n Z]

instance : CoeSort (MfldCat I n) (Type u) := ⟨MfldCat.carrier⟩

attribute [coe] MfldCat.carrier

variable (X) in
lemma coe_of : (of (I := I) (n := n) X : Type u) = X := rfl

lemma of_carrier (M : MfldCat I n) : of (I := I) (n := n) M.carrier = M := rfl

/-- The type of morphisms in `ModelWithCorners.MfldCat I n`. -/
@[ext]
structure Hom (M N : MfldCat.{u, v} I n) where
  /-- The underlying `C^n` map. -/
  hom' : ContMDiffMap I I M N n

instance : Category (MfldCat I n) where
  Hom M N := Hom M N
  id M := ⟨ContMDiffMap.id⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (MfldCat I n)
    (fun M N => ContMDiffMap I I M N n) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- Turn a morphism in `ModelWithCorners.MfldCat I n` back into a `ContMDiffMap`. -/
abbrev Hom.hom {M N : MfldCat I n} (f : Hom M N) :=
  ConcreteCategory.hom (C := MfldCat I n) f

/-- Typecheck a `ContMDiffMap` as a morphism in `ModelWithCorners.MfldCat I n`. -/
abbrev ofHom (f : ContMDiffMap I I X Y n) :
    of (I := I) (n := n) X ⟶ of (I := I) (n := n) Y :=
  ConcreteCategory.ofHom (C := MfldCat I n) f

/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (M N : MfldCat.{u, v} I n) (f : Hom M N) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

@[simp]
lemma hom_id {M : MfldCat I n} :
    (𝟙 M : M ⟶ M).hom = ContMDiffMap.id := rfl

@[simp]
theorem id_app (M : MfldCat I n) (x : ↑M) : (𝟙 M : M ⟶ M) x = x := rfl

@[simp]
theorem coe_id (M : MfldCat I n) : (𝟙 M : M → M) = _root_.id := rfl

@[simp]
lemma hom_comp {M N P : MfldCat I n} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[simp]
theorem comp_app {M N P : MfldCat I n} (f : M ⟶ N) (g : N ⟶ P) (x : M) :
    (f ≫ g : M → P) x = g (f x) := rfl

@[simp]
theorem coe_comp {M N P : MfldCat I n} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g : M → P) = g ∘ f := rfl

@[ext]
lemma hom_ext {M N : MfldCat I n} {f g : M ⟶ N} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[ext]
lemma ext {M N : MfldCat I n} {f g : M ⟶ N} (w : ∀ x : M, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

section ofHom

@[simp]
lemma hom_ofHom (f : ContMDiffMap I I X Y n) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {M N : MfldCat I n} (f : M ⟶ N) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id :
    ofHom (ContMDiffMap.id : ContMDiffMap I I X X n) = 𝟙 (of (I := I) (n := n) X) := rfl

@[simp]
lemma ofHom_comp (f : ContMDiffMap I I X Y n) (g : ContMDiffMap I I Y Z n) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g := rfl

lemma ofHom_apply (f : ContMDiffMap I I X Y n) (x : X) : (ofHom f) x = f x := rfl

lemma hom_inv_id_apply {M N : MfldCat I n} (f : M ≅ N) (x : M) : f.inv (f.hom x) = x := by
  simp

lemma inv_hom_id_apply {M N : MfldCat I n} (f : M ≅ N) (y : N) : f.hom (f.inv y) = y := by
  simp

end ofHom

/-- Morphisms in `ModelWithCorners.MfldCat I n` are equivalent to same-model `ContMDiffMap`s. -/
@[simps]
def Hom.equivContMDiffMap (M N : MfldCat I n) :
    (M ⟶ N) ≃ ContMDiffMap I I M N n where
  toFun f := f.hom
  invFun f := ofHom f

/-- Replace a function coercion for a morphism `ModelWithCorners.MfldCat.of X ⟶
ModelWithCorners.MfldCat.of Y` with the definitionally equal function coercion for a
`ContMDiffMap I I X Y n`. -/
@[simp] theorem coe_of_of {f : ContMDiffMap I I X Y n} {x} :
    @DFunLike.coe (of (I := I) (n := n) X ⟶ of (I := I) (n := n) Y)
      ((CategoryTheory.forget (MfldCat I n)).obj (of (I := I) (n := n) X))
      (fun _ ↦ (CategoryTheory.forget (MfldCat I n)).obj (of (I := I) (n := n) Y))
      ConcreteCategory.instFunLike
      (ofHom f) x =
    @DFunLike.coe (ContMDiffMap I I X Y n) X
      (fun _ ↦ Y) _
      f x :=
  rfl

/-- Any diffeomorphism induces an isomorphism in `ModelWithCorners.MfldCat I n`. -/
@[simps]
def isoOfDiffeomorph {M N : MfldCat I n} (f : M ≃ₘ^n⟮I, I⟯ N) : M ≅ N where
  hom := ofHom f.toContMDiffMap
  inv := ofHom f.symm.toContMDiffMap
  hom_inv_id := by ext x; exact f.left_inv x
  inv_hom_id := by ext x; exact f.right_inv x

/-- Any isomorphism in `ModelWithCorners.MfldCat I n` induces a diffeomorphism. -/
@[simps]
def diffeomorphOfIso {M N : MfldCat I n} (f : M ≅ N) : M ≃ₘ^n⟮I, I⟯ N where
  toFun := f.hom
  invFun := f.inv
  left_inv _ := by simp
  right_inv _ := by simp
  contMDiff_toFun := f.hom.hom.contMDiff
  contMDiff_invFun := f.inv.hom.contMDiff

@[simp]
theorem of_isoOfDiffeomorph {M N : MfldCat I n} (f : M ≃ₘ^n⟮I, I⟯ N) :
    diffeomorphOfIso (isoOfDiffeomorph f) = f := by
  ext
  rfl

@[simp]
theorem of_diffeomorphOfIso {M N : MfldCat I n} (f : M ≅ N) :
    isoOfDiffeomorph (diffeomorphOfIso f) = f := by
  ext
  rfl

/-- The constant morphism `M ⟶ N` in `ModelWithCorners.MfldCat I n` given by `y : N`. -/
def const {M N : MfldCat I n} (y : N) : M ⟶ N :=
  ofHom <| ContMDiffMap.const y

@[simp]
lemma const_apply {M N : MfldCat I n} (y : N) (x : M) :
    const y x = y := rfl

end MfldCat

end ModelWithCorners

/-! ### The category `MfldCat 𝕜 n` of `C^n` 𝕜-manifolds with varying models -/

/-- The category of `C^n` 𝕜-manifolds. Each object bundles a model `I : ModelWithCorners 𝕜 E H`
together with a term of `ModelWithCorners.MfldCat I n`. -/
-- Note: Copied from `PFunctor`, but do we need seperate universe levels here? Seems perverse.
@[pp_with_univ, nolint checkUnivs]
structure MfldCat (𝕜 : Type v) [NontriviallyNormedField 𝕜] (n : ℕ∞ω) where
  /-- Bundle an object of `ModelWithCorners.MfldCat I n` into an object of `MfldCat`. -/
  mk ::
  /-- The model normed space. -/
  E : Type u
  /-- The chart space. -/
  H : Type u
  [instNormedAddCommGroup : NormedAddCommGroup E]
  [instNormedSpace : NormedSpace 𝕜 E]
  [instTopologicalSpaceH : TopologicalSpace H]
  /-- The model with corners. -/
  I : ModelWithCorners 𝕜 E H
  /-- The underlying object in the fixed-model category `ModelWithCorners.MfldCat I n`. -/
  toMfldCat : ModelWithCorners.MfldCat I n

attribute [instance] MfldCat.instNormedAddCommGroup MfldCat.instNormedSpace
  MfldCat.instTopologicalSpaceH

initialize_simps_projections MfldCat
  (-instNormedAddCommGroup, -instNormedSpace, -instTopologicalSpaceH)

namespace MfldCat

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {X Y Z : Type u} {E E' E'' : Type u} {H H' H'' : Type u}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [TopologicalSpace H'']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {I'' : ModelWithCorners 𝕜 E'' H''}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' n Y]
  [TopologicalSpace Z] [ChartedSpace H'' Z] [IsManifold I'' n Z]

/-- The underlying type of an object in `MfldCat`. -/
abbrev carrier (M : MfldCat 𝕜 n) : Type u := M.toMfldCat.carrier

instance : CoeSort (MfldCat 𝕜 n) (Type u) := ⟨MfldCat.carrier⟩

attribute [coe] MfldCat.carrier

/-- The object in `MfldCat` associated to a type equipped with the appropriate typeclasses. -/
abbrev of (X : Type u) (E : Type u) (H : Type u)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H)
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X] : MfldCat.{u, v} 𝕜 n :=
  .mk E H I (.of X)

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `MfldCat.of M E H I` being printed as `{ E := E, ... }` by
`delabStructureInstance`. -/
@[app_delab MfldCat.of]
meta def delabOf : Delab := delabApp

end Notation

variable (X E H I) in
lemma coe_of : (of (n := n) X E H I : Type u) = X := rfl

lemma of_carrier (M : MfldCat 𝕜 n) : of (n := n) M.carrier M.E M.H M.I = M := rfl

/-- The type of morphisms in `MfldCat`. -/
@[ext]
structure Hom (M N : MfldCat.{u, v} 𝕜 n) where
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
def Hom.Simps.hom (M N : MfldCat.{u, v} 𝕜 n) (f : Hom M N) :=
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
abbrev ofNormedSpace (n : ℕ∞ω) (E : Type u) [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    MfldCat 𝕜 n :=
  of E E E (modelWithCornersSelf 𝕜 E)

/-- `MfldCat 𝕜 n` has a forgetful functor to `TopCat`. -/
instance : HasForget₂ (MfldCat 𝕜 n) TopCat.{u} where
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
  ofHom <| ContMDiffMap.const y

@[simp]
lemma const_apply {M N : MfldCat 𝕜 n} (y : N) (x : M) :
    const y x = y := rfl

end MfldCat
