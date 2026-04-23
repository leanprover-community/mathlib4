/-
Copyright (c) 2026 Jakob Scharmberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.Topology.Homotopy.TopCat.Basic

/-!
# Topological Pairs

In this file we introduce `TopPair`, the category of topological pairs. It is defined as the
category of arrows in `TopCat` which are topological embeddings.

We provide the inclusion and diagonal functors `TopCat ⥤ TopPair` and show that they are left and
right adjoint to the first projection functor, respectively.

We also define for two morphisms of topological pairs `f, g : X ⟶ Y` the structure `Homotopy f g` of
homotopies between them.
-/

@[expose] public section

universe u

open TopologicalSpace TopCat CategoryTheory MonoidalCategory

/-- A pair of topological spaces consists of an embedding `f : A ⟶ X` in `TopCat`. -/
abbrev TopPair :=
  MorphismProperty.Arrow TopCat.isEmbedding ⊤ ⊤

namespace TopPair

variable {X Y : TopPair.{u}}

/-- The first space of the pair -/
abbrev fst : TopCat.{u} := X.right

/-- The second space of the pair -/
abbrev snd : TopCat.{u} := X.left

/-- The embedding of the second into the first space -/
abbrev map : X.snd ⟶ X.fst := X.hom

lemma isEmbedding_map (X : TopPair.{u}) : Topology.IsEmbedding X.map := X.prop

/-- Construct a topological pair from its components. -/
abbrev of {A X : TopCat.{u}} (f : A ⟶ X) (h : Topology.IsEmbedding f) : TopPair.{u} :=
  MorphismProperty.Arrow.mk (P := TopCat.isEmbedding) f h

/-- Constructor for a topological pair (X, A) where A ⊆ X. -/
abbrev ofSubset {X : TopCat.{u}} (A : Set X) : TopPair.{u} := TopPair.of (A := (TopCat.of A))
  (X := X) ⟨{ toFun := Subtype.val }⟩ Topology.IsEmbedding.subtypeVal

/-- Construct a morphism in `TopPair` from its components. -/
abbrev ofHom (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) (w : g ≫ Y.map = X.map ≫ f := by cat_disch) :=
  MorphismProperty.Arrow.homMk g f w

variable {X Y Z : TopPair.{u}}

/-- The map between the first spaces -/
abbrev Hom.fst (f : X ⟶ Y) : X.fst ⟶ Y.fst := f.hom.right

/-- The map between the second spaces -/
abbrev Hom.snd (f : X ⟶ Y) : X.snd ⟶ Y.snd := f.hom.left

@[reassoc, elementwise]
lemma Hom.w {X Y : TopPair.{u}} (f : X ⟶ Y) :
    Hom.snd f ≫ Y.map = X.map ≫ Hom.fst f :=
  f.hom.w

attribute [local simp] Hom.w_apply

/-- The functor from topological pairs to topological spaces that forgets the second space, i.e. the
projection to the first space. -/
abbrev proj₁ : TopPair.{u} ⥤ TopCat.{u} :=
  MorphismProperty.Arrow.forget _ _ _ ⋙ CategoryTheory.Arrow.rightFunc

/-- The functor from topological pairs to topological spaces that forgets the first space, i.e. the
projection to the second space. -/
abbrev proj₂ : TopPair.{u} ⥤ TopCat.{u} :=
  MorphismProperty.Arrow.forget _ _ _ ⋙ CategoryTheory.Arrow.leftFunc

/-- The inclusion functor from topological spaces to topological pairs that sends a space X to
(X, ∅). -/
@[simps]
def incl : TopCat.{u} ⥤ TopPair.{u} where
  obj X := TopPair.of (TopCat.isInitialPEmpty.to X) (Topology.IsOpenEmbedding.of_isEmpty _).1
  map f := TopPair.ofHom f (𝟙 _) <| by ext x; induction x

/-- The functor from topological spaces to topological pairs that sends a space X to the identity
morphism on X. -/
abbrev diag : TopCat.{u} ⥤ TopPair.{u} where
  obj X := TopPair.of (𝟙 X) Topology.IsEmbedding.id
  map f := TopPair.ofHom f f

/-- The inclusion functor is left adjoint to the projection to the first component. -/
@[simps]
def inclAdjProj₁ : incl ⊣ proj₁ where
  unit.app X := 𝟙 X
  counit.app X := TopPair.ofHom (𝟙 X.fst) (TopCat.isInitialPEmpty.to X.snd)

/-- The projection functor to the first component is left adjoint to the diagonal functor. -/
@[simps]
def proj₁AdjDiag : proj₁ ⊣ diag where
  unit.app X := TopPair.ofHom (𝟙 X.fst) X.map
  unit.naturality X Y f := MorphismProperty.Arrow.Hom.ext f.w (by cat_disch)
  counit.app X := 𝟙 X

/-- The unique morphism (X, ∅) ⟶ (X, A) that is the identity on X. -/
abbrev j (X : TopPair.{u}) : TopPair.incl.obj X.fst ⟶ X :=
  TopPair.ofHom (𝟙 _) (TopCat.isInitialPEmpty.to _)

/-- A homotopy of maps between topological pairs is a homotopy on the first space and a homotopy on
the second space that fit in a commutative square with the maps of the pairs. -/
@[ext]
structure Homotopy (f g : X ⟶ Y) where
  /-- The homotopy on the first space. -/
  fst : TopCat.Homotopy (Hom.fst f) (Hom.fst g)
  /-- The homotopy on the second space. -/
  snd : TopCat.Homotopy (Hom.snd f) (Hom.snd g)
  /-- The proof that the homotopies fit into a commutative square with the maps of the pairs. -/
  w : X.map ▷ _ ≫ fst.h = snd.h ≫ Y.map := by cat_disch

attribute [reassoc, elementwise] Homotopy.w
attribute [local simp] Homotopy.w Homotopy.w_apply

namespace Homotopy

@[local simp]
lemma w_apply' {f g : X ⟶ Y} (H : Homotopy f g) (x : TopPair.snd) (t : unitInterval) :
    H.fst (t, X.map x) = Y.map (H.snd (t, x)) := by
  have := w_apply H (x, I.homeomorph.symm t)
  simp only [Homeomorph.apply_symm_apply] at this
  exact this

/-- Given a morphism `f` of topological pairs, we can define a `Homotopy f f` by
`TopCat.Homotopy.refl` on the first and second components.
-/
@[simps]
def refl (f : X ⟶ Y) : Homotopy f f where
  fst := TopCat.Homotopy.refl (Hom.fst f)
  snd := TopCat.Homotopy.refl (Hom.snd f)

instance : Inhabited (Homotopy (𝟙 X) (𝟙 X)) :=
  ⟨Homotopy.refl _⟩

/-- Given a `Homotopy f₀ f₁`, we can define a `Homotopy f₁ f₀` by `TopCat.Homotopy.symm` on
the first and second components.
-/
@[simps]
def symm {f₀ f₁ : X ⟶ Y} (F : Homotopy f₀ f₁) : Homotopy f₁ f₀ where
  fst := F.fst.symm
  snd := F.snd.symm

@[simp]
theorem symm_symm {f₀ f₁ : X ⟶ Y} (F : Homotopy f₀ f₁) : F.symm.symm = F := by
  ext <;> simp

theorem symm_bijective {f₀ f₁ : X ⟶ Y} :
    Function.Bijective (Homotopy.symm : Homotopy f₀ f₁ → Homotopy f₁ f₀) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
Given `Homotopy f₀ f₁` and `Homotopy f₁ f₂`, we can define a `Homotopy f₀ f₂` by
`TopCat.Homotopy.trans` on the first and second components.
-/
@[simps]
noncomputable def trans {f₀ f₁ f₂ : X ⟶ Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) :
    Homotopy f₀ f₂ where
  fst := F.fst.trans G.fst
  snd := F.snd.trans G.snd
  w := by
    ext ⟨_, _⟩
    simp only [TopCat.comp_app, whiskerRight_apply, Homotopy.h_hom_apply,
      ContinuousMap.Homotopy.trans_apply, one_div]
    split_ifs <;> simp

theorem symm_trans {f₀ f₁ f₂ : X ⟶ Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) :
    (F.trans G).symm = G.symm.trans F.symm := by
      ext : 1 <;> exact ContinuousMap.Homotopy.symm_trans _ _

set_option backward.isDefEq.respectTransparency false in
/-- If we have a `Homotopy g₀ g₁` and a `Homotopy f₀ f₁`, we can define a
`Homotopy (f₀ ≫ g₀) (f₁ ≫ g₁)` by `TopCat.Homotopy.comp` on the first and second components.
-/
@[simps]
def comp {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
    Homotopy (f₀ ≫ g₀) (f₁ ≫ g₁) where
  fst := G.fst.comp F.fst
  snd := G.snd.comp F.snd

end Homotopy

/-- Two maps between topological pairs are homotopic if there is a homotopy between them. -/
def Homotopic (f g : X ⟶ Y) := Nonempty (Homotopy f g)

namespace Homotopic

/-- Two maps of topological pairs being homotopic defines an equivalence relation. -/
theorem equivalence : Equivalence (Homotopic (X := X) (Y := Y)) :=
  ⟨fun f ↦ ⟨Homotopy.refl f⟩, fun h ↦ h.map Homotopy.symm, fun h₀ h₁ ↦ h₀.map2 Homotopy.trans h₁⟩

end Homotopic

end TopPair
