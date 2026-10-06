/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Local properties of presheaves and sheaves

In this file we study properties of presheaves and sheaves that can be checked on a covering
family of objects.

## Main results

- `CategoryTheory.Sheaf.isIso_iff_of_coversTop`: A morphism of sheaves is an isomorphism if it
  is one on a cover.
- `CategoryTheory.GrothendieckTopology.W_of_isIso_of_coversTop`: A morphism of presheaves
  becomes an isomorphism after sheafification if it is one on a cover.
-/
public section

namespace CategoryTheory

open Opposite

variable {C : Type*} [Category* C] {K : GrothendieckTopology C} {A : Type*} [Category* A]

namespace Sheaf

variable {ι : Type*} {X : ι → C}

/-- A sheaf morphism is an isomorphism if it becomes one after pulling back along each
element of a covering family. -/
lemma isIso_of_coversTop (hX : K.CoversTop X) {F G : Sheaf K A} {f : F ⟶ G}
    (h : ∀ i, IsIso ((K.overPullback A (X i)).map f)) :
    IsIso f := by
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  have hiso (Z : C) (i : ι) (g : Z ⟶ X i) : IsIso (f.hom.app (op Z)) :=
    (NatTrans.isIso_iff_isIso_app ((K.overPullback A (X i)).map f).hom).mp inferInstance
      (op (Over.mk g))
  intro W
  let S : K.Cover W.unop := hX.cover W.unop
  have harrow (I : S.Arrow) : IsIso (f.hom.app (op I.Y)) := by
    obtain ⟨i, ⟨g⟩⟩ := I.hf
    exact hiso I.Y i g
  let invMap : G.obj.obj (op W.unop) ⟶ F.obj.obj (op W.unop) :=
    F.property.amalgamate S (fun I => G.obj.map I.f.op ≫ inv (f.hom.app (op I.Y))) (by
      intro I₁ I₂ r
      have hZ : IsIso (f.hom.app (op r.Z)) := by
        obtain ⟨i, ⟨g⟩⟩ := I₁.hf
        exact hiso r.Z i (r.g₁ ≫ g)
      simp only [Category.assoc, f.hom.naturality_inv]
      rw [← Category.assoc, ← Category.assoc, ← G.obj.map_comp, ← G.obj.map_comp,
        ← op_comp, ← op_comp, r.w])
  refine ⟨⟨invMap, ?_, ?_⟩⟩
  · refine F.property.hom_ext S _ _ fun I => ?_
    simp only [op_unop, Category.assoc, Category.id_comp]
    rw [Presheaf.IsSheaf.amalgamate_map, ← f.hom.naturality_assoc]
    simp
  · refine G.property.hom_ext S _ _ fun I => ?_
    simp only [op_unop, Category.assoc, Category.id_comp]
    rw [← f.hom.naturality, Presheaf.IsSheaf.amalgamate_map_assoc]
    simp

/-- A sheaf morphism is an isomorphism iff it becomes one after pulling back along each
element of a covering family. -/
lemma isIso_iff_of_coversTop (hX : K.CoversTop X) {F G : Sheaf K A} (f : F ⟶ G) :
    IsIso f ↔ ∀ i, IsIso ((K.overPullback A (X i)).map f) :=
  ⟨fun _ _ => inferInstance, fun h => isIso_of_coversTop hX h⟩

end Sheaf

section Concrete

variable {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  {ι : Type*} {X : ι → C} {F G : Cᵒᵖ ⥤ A}

namespace Presheaf

/-- A morphism of presheaves is locally injective if its components are injective
on objects lying over a covering family. -/
lemma isLocallyInjective_of_coversTop (hX : K.CoversTop X) (f : F ⟶ G)
    (h : ∀ i (Y : C) (_ : Y ⟶ X i), Function.Injective (f.app (op Y))) :
    IsLocallyInjective K f where
  equalizerSieve_mem {Y} x y hxy := by
    refine K.superset_covering ?_ (hX Y.unop)
    rintro Z g ⟨i, ⟨a⟩⟩
    apply h i Z a
    simpa only [NatTrans.naturality_apply] using congrArg (G.map g.op) hxy

/-- A morphism of presheaves is locally surjective if its components are surjective
on objects lying over a covering family. -/
lemma isLocallySurjective_of_coversTop (hX : K.CoversTop X) (f : F ⟶ G)
    (h : ∀ i (Y : C) (_ : Y ⟶ X i), Function.Surjective (f.app (op Y))) :
    IsLocallySurjective K f where
  imageSieve_mem {Y} s := by
    refine K.superset_covering ?_ (hX Y)
    rintro Z g ⟨i, ⟨a⟩⟩
    exact h i Z a (G.map g.op s)

end Presheaf

/-- A morphism of presheaves becomes an isomorphism after sheafification if its
components are isomorphisms on objects lying over a covering family. -/
lemma GrothendieckTopology.W_of_isIso_of_coversTop [K.WEqualsLocallyBijective A]
    (hX : K.CoversTop X) (f : F ⟶ G)
    (h : ∀ i (Y : C) (_ : Y ⟶ X i), IsIso (f.app (op Y))) : K.W f := by
  have : Presheaf.IsLocallyInjective K f :=
    Presheaf.isLocallyInjective_of_coversTop hX f fun i Y a => by
      have := h i Y a
      exact (ConcreteCategory.bijective_of_isIso (f.app (op Y))).injective
  have : Presheaf.IsLocallySurjective K f :=
    Presheaf.isLocallySurjective_of_coversTop hX f fun i Y a => by
      have := h i Y a
      exact (ConcreteCategory.bijective_of_isIso (f.app (op Y))).surjective
  exact K.W_of_isLocallyBijective f

end Concrete

end CategoryTheory
