/-
Copyright (c) 2026 Jakob Scharmberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Homotopy.Basic

/-!
# Topological Pairs

In this file we introduce `TopPair`, the category of topological pairs.

We provide the inclusion and diagonal functors `TopCat` ⥤ `TopPair` and show that they are left and
right adjoint to the first projection functor, respectively.

We also define for two morphisms of topological pairs f, g : X ⟶ Y the structure `Homotopy f g` of
homotopies between them.
-/

@[expose] public section

open TopologicalSpace CategoryTheory unitInterval

universe u

/-- A pair of topological spaces consists of two topological spaces X and A and a map f : A → X
such that the topology of A is induced by f. -/
structure TopPair where
  /-- The first space of the pair -/
  fst : TopCat
  /-- The second space of the pair -/
  snd : TopCat
  /-- The map that induces the topology on A -/
  map : snd ⟶ fst
  isInducing_map : Topology.IsInducing map.hom

namespace TopPair

/-- Constructor for a topological (X, A) pair where A ⊆ X. -/
def ofSubset {X : TopCat} (A : Set X) : TopPair where
  fst := X
  snd := TopCat.of A
  map := ⟨{ toFun := (↑) }⟩
  isInducing_map := ⟨TopologicalSpace.ext rfl⟩

variable {X Y Z : TopPair}

/-- A morphism of a pair consists of a morphism between the first spaces and a morphism between the
second spaces that fit in a commutative square with the maps of the pairs. -/
@[ext]
structure Hom (X Y : TopPair) where
  /-- The map between the first spaces -/
  fst : X.fst ⟶ Y.fst
  /-- The map between the second spaces -/
  snd : X.snd ⟶ Y.snd
  /-- The proof that the two maps fit in the commutative square -/
  snd_map : snd ≫ Y.map = X.map ≫ fst := by cat_disch

@[simps]
instance : Category TopPair where
  Hom := Hom
  id X := { fst := 𝟙 X.fst, snd := 𝟙 X.snd }
  comp f g := ⟨f.fst ≫ g.fst, f.snd ≫ g.snd, (CommSq.horiz_comp ⟨f.snd_map⟩ ⟨g.snd_map⟩).w⟩

/-- `TopPair` is equivalent to the full subcategory of the comma category with twice the identity
functor of TopCat on the morphisms that are inducing. -/
def equivComma : TopPair ≌ MorphismProperty.Comma (𝟭 TopCat) (𝟭 TopCat)
    (fun X Y f ↦ Topology.IsInducing (f : TopCat.Hom X Y)) ⊤ ⊤ where
      functor := {
        obj X := {
          left := X.snd
          right := X.fst
          hom := X.map
          prop := X.isInducing_map
        }
        map f := {
          left := f.snd
          right := f.fst
          w := f.snd_map
          prop_hom_left := by simp
          prop_hom_right := by simp
        }
      }
      inverse := {
        obj X := {
          fst := X.right
          snd := X.left
          map := X.hom
          isInducing_map := X.prop
        }
        map f := { fst := f.right, snd := f.left, snd_map := f.w }
      }
      unitIso.hom.app := 𝟙
      unitIso.inv.app := 𝟙
      counitIso.hom.app := 𝟙
      counitIso.inv.app := 𝟙

/-- The functor from topological pairs to topological spaces that forgets the second space, ie. the
projection to the first space. -/
@[simps]
def proj₁ : TopPair ⥤ TopCat where
  obj X := X.fst
  map f := f.fst

/-- The functor from topological pairs to topological spaces that forgets the first space, ie. the
projection to the second space. -/
@[simps]
def proj₂ : TopPair ⥤ TopCat where
  obj X := X.snd
  map f := f.snd

/-- The inclusion functor from topological spaces to topological pairs that sends a space X to
(X, ∅). -/
@[simps]
def incl : TopCat ⥤ TopPair where
  obj X := ⟨_, _, TopCat.isInitialPEmpty.to _, TopCat.IsInducing.empty X⟩
  map f := ⟨f, 𝟙 (TopCat.of PEmpty), by ext x; induction x⟩

/-- The functor from topological spaces to topological pairs that sends a space X to (X, X) with the
identity morphism on X. -/
@[simps]
def diag : TopCat ⥤ TopPair where
  obj X := ⟨_, _, 𝟙 X, Topology.IsInducing.id⟩
  map f := { fst := f, snd := f }

@[simps]
instance : Inhabited TopPair := ⟨incl.obj TopCat.inhabited.default⟩

/-- The inclusion functor is left adjoint to the projection to the first component. -/
@[simps]
def inclAdjProj₁ : incl ⊣ proj₁ where
  unit.app X := 𝟙 X
  counit.app X := {
    fst := 𝟙 X.fst,
    snd := TopCat.isInitialPEmpty.to _
    snd_map := by ext x; induction x
  }
  counit.naturality X Y f := Hom.ext (by simp) (by ext x; induction x)
  left_triangle_components X := Hom.ext (by simp) (by cat_disch)

/-- The projection functor to the first component is left adjoint to the diagonal functor. -/
@[simps]
def proj₁AdjDiag : proj₁ ⊣ diag where
  unit.app X := { fst := 𝟙 X.fst, snd := X.map }
  unit.naturality X Y f := Hom.ext (by simp) f.snd_map
  counit.app X := 𝟙 X

/-- The unique morphism (A, ∅) ⟶ (A, B) that is the identity on A. -/
@[simps]
def j (X : TopPair) : TopPair.incl.obj X.fst ⟶ X where
  fst := 𝟙 X.fst
  snd := TopCat.isInitialPEmpty.to _
  snd_map := by ext x; induction x

/-- A homotopy of maps between topological pairs is a homotopy on the first space and a homotopy on
the second space that fit in a commutative square with the maps of the pairs. -/
@[ext]
structure Homotopy (f g : X ⟶ Y) where
  /-- The homotopy on the first space. -/
  fst : ContinuousMap.Homotopy f.fst.hom g.fst.hom
  /-- The homotopy on the second space. -/
  snd : ContinuousMap.Homotopy f.snd.hom g.snd.hom
  /-- The proof that the homotopies fit into a commutative square with the maps of the pairs. -/
  snd_map : TopCat.ofHom snd.toContinuousMap ≫ Y.map =
    TopCat.ofHom (ContinuousMap.prodMap (ContinuousMap.id I) X.map.hom) ≫
      TopCat.ofHom fst.toContinuousMap := by cat_disch

attribute [reassoc] Homotopy.snd_map

namespace Homotopy

/-- Given a morphism `f` of topological pairs, we can define a `Homotopy f f` by
`ContinuousMap.Homotopy.refl` on the first and second components.
-/
@[simps]
def refl (f : X ⟶ Y) : Homotopy f f where
  fst := ContinuousMap.Homotopy.refl f.fst.hom
  snd := ContinuousMap.Homotopy.refl f.snd.hom
  snd_map := by
    ext ⟨_, _⟩
    simp only [TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_apply,
      ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.refl_apply,
      ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq]
    rw [← TopCat.comp_app, f.snd_map, TopCat.comp_app]

instance : Inhabited (Homotopy (𝟙 X) (𝟙 X)) :=
  ⟨Homotopy.refl _⟩

/-- Given a `Homotopy f₀ f₁`, we can define a `Homotopy f₁ f₀` by `ContinuousMap.Homotopy.symm` on
the first and second components.
-/
@[simps]
def symm {f₀ f₁ : X ⟶ Y} (F : Homotopy f₀ f₁) : Homotopy f₁ f₀ where
  fst := ContinuousMap.Homotopy.symm F.fst
  snd := ContinuousMap.Homotopy.symm F.snd
  snd_map := by
    ext ⟨t, x⟩
    simp only [TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_apply,
      ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.symm_apply,
      ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq]
    rw [← ContinuousMap.Homotopy.coe_toContinuousMap F.snd,
      ← TopCat.hom_ofHom F.snd.toContinuousMap, ← TopCat.comp_app]
    simp [F.snd_map]

@[simp]
theorem symm_symm {f₀ f₁ : X ⟶ Y} (F : Homotopy f₀ f₁) : F.symm.symm = F := by
  ext <;> simp

theorem symm_bijective {f₀ f₁ : X ⟶ Y} :
    Function.Bijective (Homotopy.symm : Homotopy f₀ f₁ → Homotopy f₁ f₀) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
Given `Homotopy f₀ f₁` and `Homotopy f₁ f₂`, we can define a `Homotopy f₀ f₂` by
`ContinuousMap.Homotopy.trans` on the first and second components.
-/
@[simps]
noncomputable def trans {f₀ f₁ f₂ : X ⟶ Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) :
    Homotopy f₀ f₂ where
  fst := ContinuousMap.Homotopy.trans F.fst G.fst
  snd := ContinuousMap.Homotopy.trans F.snd G.snd
  snd_map := by
    ext ⟨t, x⟩
    simp only [TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_apply,
      ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.trans_apply, one_div,
      ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq]
    split_ifs
    · rw [← ContinuousMap.Homotopy.coe_toContinuousMap F.snd,
        ← TopCat.hom_ofHom F.snd.toContinuousMap, ← TopCat.comp_app]
      simp [F.snd_map]
    · rw [← ContinuousMap.Homotopy.coe_toContinuousMap G.snd,
        ← TopCat.hom_ofHom G.snd.toContinuousMap, ← TopCat.comp_app]
      simp [G.snd_map]

theorem symm_trans {f₀ f₁ f₂ : X ⟶ Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) :
    (F.trans G).symm = G.symm.trans F.symm := by
      apply Homotopy.ext
      · simp only [symm_fst, trans_fst]
        exact ContinuousMap.Homotopy.symm_trans _ _
      · simp only [symm_snd, trans_snd]
        exact ContinuousMap.Homotopy.symm_trans _ _

/-- If we have a `Homotopy g₀ g₁` and a `Homotopy f₀ f₁`, then we can compose them and get a
`Homotopy (f₀ ≫ g₀) (f₁ ≫ g₁)`.
-/
@[simps]
def comp {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
    Homotopy (f₀ ≫ g₀) (f₁ ≫ g₁) where
      fst := ContinuousMap.Homotopy.comp G.fst F.fst
      snd := ContinuousMap.Homotopy.comp G.snd F.snd
      snd_map := by
        ext ⟨t, x⟩
        simp only [comp_snd, TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_apply,
          ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.comp_apply, comp_fst,
          ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq]
        rw [← ContinuousMap.Homotopy.coe_toContinuousMap G.snd,
          ← TopCat.hom_ofHom G.snd.toContinuousMap, ← TopCat.comp_app]
        simp only [G.snd_map, TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_apply,
          ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq,
          ContinuousMap.Homotopy.coe_toContinuousMap]
        rw [← ContinuousMap.Homotopy.coe_toContinuousMap F.snd,
          ← TopCat.hom_ofHom F.snd.toContinuousMap, ← TopCat.comp_app]
        simp only [F.snd_map, TopCat.hom_comp, TopCat.hom_ofHom, ContinuousMap.comp_apply,
          ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq,
          ContinuousMap.Homotopy.coe_toContinuousMap]


/-- Composition of a `Homotopy g₀ g₁` and `f : X ⟶ Y` as a homotopy between `f ≫ g₀` and
`f ≫ g₁`. -/
@[simps!]
def compMap {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (f : X ⟶ Y) :
    Homotopy (f ≫ g₀) (f ≫ g₁) :=
  G.comp (.refl f)

end Homotopy

/-- Two maps between topological pairs are homotopic if there is a homotopy between them. -/
def Homotopic (f g : X ⟶ Y) := Nonempty (Homotopy f g)

namespace Homotopic

@[refl]
theorem refl (f : X ⟶ Y) : Homotopic f f :=
  ⟨Homotopy.refl f⟩

@[symm]
theorem symm ⦃f g : X ⟶ Y⦄ (h : Homotopic f g) : Homotopic g f :=
  h.map Homotopy.symm

@[trans]
theorem trans ⦃f g h : X ⟶ Y⦄ (h₀ : Homotopic f g) (h₁ : Homotopic g h) : Homotopic f h :=
  h₀.map2 Homotopy.trans h₁

/-- Two maps of topological pairs being homotopic defines an equivalence relation. -/
theorem equivalence : Equivalence (@Homotopic X Y) :=
  ⟨refl, by apply symm, by apply trans⟩

end Homotopic

end TopPair
