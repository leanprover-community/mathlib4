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
  (X := X) (TopCat.ofHom { toFun := Subtype.val }) Topology.IsEmbedding.subtypeVal

/-- Constructs the topological pair `(X, ∅)` from `X : TopCat`. -/
abbrev ofTopCat (X : TopCat.{u}) : TopPair.{u} :=
  TopPair.of (TopCat.isInitialPEmpty.to X) (Topology.IsOpenEmbedding.of_isEmpty _).1

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
def proj₁ : TopPair.{u} ⥤ TopCat.{u} :=
  MorphismProperty.Arrow.forget _ _ _ ⋙ CategoryTheory.Arrow.rightFunc

-- `simps` generates the wrong lemmas
@[simp]
lemma proj₁_obj : proj₁.obj X = X.fst := rfl

@[simp]
lemma proj₁_map (f : X ⟶ Y) : proj₁.map f = Hom.fst f := rfl

/-- The functor from topological pairs to topological spaces that forgets the first space, i.e. the
projection to the second space. -/
def proj₂ : TopPair.{u} ⥤ TopCat.{u} :=
  MorphismProperty.Arrow.forget _ _ _ ⋙ CategoryTheory.Arrow.leftFunc

-- `simps` generates the wrong lemmas
@[simp]
lemma proj₂_obj : proj₂.obj X = X.snd := rfl

@[simp]
lemma proj₂_map (f : X ⟶ Y) : proj₂.map f = Hom.snd f := rfl

/-- The inclusion functor from topological spaces to topological pairs that sends a space X to
(X, ∅). -/
@[simps]
def incl : TopCat.{u} ⥤ TopPair.{u} where
  obj X := ofTopCat X
  map f := TopPair.ofHom f (𝟙 _) <| by ext x; induction x

/-- The functor from topological spaces to topological pairs that sends a space X to the identity
morphism on X. -/
abbrev diag : TopCat.{u} ⥤ TopPair.{u} where
  obj X := TopPair.of (𝟙 X) Topology.IsEmbedding.id
  map f := TopPair.ofHom f f

set_option backward.defeqAttrib.useBackward true in
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

set_option backward.defeqAttrib.useBackward true in
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
  cat_disch

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
  cat_disch

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
    simp only [TopCat.comp_app, Homotopy.h_hom_apply, ContinuousMap.Homotopy.trans_apply]
    cat_disch

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

section Embedding

/-- A morphism `f : X ⟶ Y` in `TopPair` is an embedding if its first and second component are
embeddings. -/
structure IsEmbedding {X Y : TopPair} (f : X ⟶ Y)where
  fst : Topology.IsEmbedding (Hom.fst f)
  snd : Topology.IsEmbedding (Hom.snd f)

end Embedding

section Complement

/-- Two morphisms `f : A ⟶ X` and `g : B ⟶ X` in `TopPair` are complements if their first and second
components are complements in `TopCat`. -/
protected structure IsCompl {X A B : TopPair} (f : A ⟶ X) (g : B ⟶ X) where
  fst : IsCompl (Set.range (Hom.fst f)) (Set.range (Hom.fst g))
  snd : IsCompl (Set.range (Hom.snd f)) (Set.range (Hom.snd g))

set_option backward.isDefEq.respectTransparency false in
/-- Under the assumptions of excision, the map of the pair `U` is an isomorphism. -/
lemma isIso_of_isCompl_closure ⦃X U V : TopPair⦄ (f : U ⟶ X) (g : V ⟶ X) (hf : IsEmbedding f)
    (hcompl : TopPair.IsCompl f g)
    (hU : closure (Set.range (Hom.fst f)) ⊆ interior (Set.range X.map)) : IsIso U.map := by
  have surjective_U : Function.Surjective U.map := by
    rw [← Set.range_eq_univ, ← Set.univ_subset_iff, ← Set.image_subset_image_iff hf.fst.injective,
      Set.image_univ]
    refine Disjoint.subset_left_of_subset_union (u := Hom.fst g '' (Set.range V.map)) ?_ ?_
    · calc
        _ ⊆ closure (Set.range (Hom.fst f)) := subset_closure
        _ ⊆ interior (Set.range X.map) := hU
        _ ⊆ Set.range X.map := interior_subset
        _ ⊆ _ := by
          simp only [← Set.range_comp, ← CategoryTheory.hom_comp, ← Arrow.w]
          dsimp
          have := hcompl.snd.codisjoint
          simp_all [codisjoint_iff, Set.range_comp, ← Set.image_union, ← Set.sup_eq_union]
    · rw [Set.disjoint_iff, ← Set.disjoint_iff_inter_eq_empty.mp hcompl.fst.disjoint]
      grind
  apply TopCat.isIso_of_bijective_of_isOpenMap _
    ⟨U.prop.injective, surjective_U⟩
  apply Topology.IsInducing.isOpenMap U.prop.isInducing
  simp [Function.Surjective.range_eq surjective_U]

end Complement

end TopPair
