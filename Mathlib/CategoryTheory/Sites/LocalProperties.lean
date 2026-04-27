/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.CoversTop

/-!
# Local properties of sheaves

In this file we study properties of sheaves that can be checked on a covering family of objects.

## Main results

- `CategoryTheory.Sheaf.isIso_iff_of_coversTop`: A morphism of sheaves is an isomorphism if it
  is one on a cover.
-/
public section

namespace CategoryTheory

open Limits Opposite

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

end CategoryTheory
