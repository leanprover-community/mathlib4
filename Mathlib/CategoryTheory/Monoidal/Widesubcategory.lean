/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# Monoidal structures on wide subcategories

Given a monoidal category `C` and a morphism property `P : MorphismProperty C`,
this file studies conditions on `P` ensuring that `WideSubcategory P` inherits
additional structure.

We define stability classes under associators, unitors, and braidings, and use
them to construct monoidal, braided, and symmetric structures on
`WideSubcategory P`.

Assuming every object of `C` carries a comonoid structure, and that `P` is also
stable under counit and comultiplication, we construct `ComonObj` (and
commutative comonoid) instances on `WideSubcategory P`.
-/

@[expose] public section

namespace CategoryTheory

open scoped MonoidalCategory ComonObj

namespace MorphismProperty

variable {C : Type*} [Category* C] (P : MorphismProperty C) [MonoidalCategory C]

/-- `widesubcat_ext` unfolds the definition of morphisms in a `WideSubcategory`. -/
macro "widesubcat_ext" : tactic =>
  `(tactic| (rw [Subtype.ext_iff]; try simp only [WideSubcategory.comp_def]))

section IsAssocStable

/-- A morphism property stable under associator isomorphisms of a monoidal category. -/
class IsAssocStable : Prop where
  associator_hom (c c' c'' : C) : P ((α_ c c' c'').hom)
  associator_inv (c c' c'' : C) : P ((α_ c c' c'').inv)

variable [P.IsAssocStable]

lemma associator_hom_mem (c c' c'' : C) : P (α_ c c' c'').hom := IsAssocStable.associator_hom _ _ _

lemma associator_inv_mem (c c' c'' : C) : P (α_ c c' c'').inv := IsAssocStable.associator_inv _ _ _

end IsAssocStable

section IsUnitorStable

/-- A morphism property stable under left and right unitor isomorphisms. -/
class IsUnitorStable : Prop where
  leftUnitor_hom (c : C) : P ((λ_ c).hom)
  leftUnitor_inv (c : C) : P ((λ_ c).inv)
  rightUnitor_hom (c : C) : P ((ρ_ c).hom)
  rightUnitor_inv (c : C) : P ((ρ_ c).inv)

variable [P.IsUnitorStable]

lemma leftUnitor_hom_mem (c : C) : P (λ_ c).hom := IsUnitorStable.leftUnitor_hom _

lemma leftUnitor_inv_mem (c : C) : P (λ_ c).inv := IsUnitorStable.leftUnitor_inv _

lemma rightUnitor_hom_mem (c : C) : P (ρ_ c).hom := IsUnitorStable.rightUnitor_hom _

lemma rightUnitor_inv_mem (c : C) : P (ρ_ c).inv := IsUnitorStable.rightUnitor_inv _

end IsUnitorStable

section IsMonoidalStable

/-- A morphism property stable under tensoring, associators, and unitors. -/
class IsMonoidalStable : Prop extends IsMonoidal P, IsAssocStable P, IsUnitorStable P

variable [P.IsMonoidalStable]

instance : MonoidalCategoryStruct (WideSubcategory P) where
  tensorObj c c' := ⟨c.obj ⊗ c'.obj⟩
  whiskerLeft c c' c'' f := ⟨c.obj ◁ f.1, P.whiskerLeft_mem _ _ f.2⟩
  whiskerRight f c' := ⟨f.1 ▷ c'.obj, P.whiskerRight_mem _ f.2 _⟩
  tensorUnit := ⟨𝟙_ C⟩
  associator c c' c'' := by
    refine ⟨⟨(α_ c.obj c'.obj c''.obj).hom, ?_⟩, ⟨(α_ c.obj c'.obj c''.obj).inv, ?_⟩, ?_, ?_⟩
    · exact P.associator_hom_mem _ _ _
    · exact P.associator_inv_mem _ _ _
    all_goals
    widesubcat_ext
    simp
  leftUnitor c := by
    refine ⟨⟨(λ_ c.obj).hom, ?_⟩, ⟨(λ_ c.obj).inv, ?_⟩, ?_, ?_⟩
    · exact P.leftUnitor_hom_mem _
    · exact P.leftUnitor_inv_mem _
    all_goals
    widesubcat_ext
    simp
  rightUnitor c := by
    refine ⟨⟨(ρ_ c.obj).hom, ?_⟩, ⟨(ρ_ c.obj).inv, ?_⟩, ?_, ?_⟩
    · exact P.rightUnitor_hom_mem _
    · exact P.rightUnitor_inv_mem _
    all_goals
    widesubcat_ext
    simp
  tensorHom f g := ⟨f.1 ⊗ₘ g.1, P.tensorHom_mem _ _ f.2 g.2⟩

instance : MonoidalCategory (WideSubcategory P) := by
  refine Monoidal.induced (wideSubcategoryInclusion P) ?_
  refine ⟨fun c c' ↦ ?_, fun c c' c'' f ↦ ?_, fun f c'' ↦ ?_, fun f g ↦ ?_, ?_, fun c c' c'' ↦ ?_,
    fun c ↦ ?_, fun c ↦ ?_⟩
  · rfl
  · simp only [wideSubcategoryInclusion.obj, wideSubcategoryInclusion.map, Iso.refl_inv,
    Iso.refl_hom, Category.comp_id]
    rw [Category.id_comp <| c.obj ◁ f.1]
    rfl
  · simp only [wideSubcategoryInclusion.obj, wideSubcategoryInclusion.map, Iso.refl_inv,
      Iso.refl_hom, Category.comp_id]
    rw [Category.id_comp <| f.1 ▷ c''.obj]
    rfl
  · simp only [wideSubcategoryInclusion.obj, wideSubcategoryInclusion.map, Iso.refl_inv,
    Iso.refl_hom, Category.comp_id]
    rw [Category.id_comp <| f.1 ⊗ₘ g.1]
    rfl
  · rfl
  · simp only [wideSubcategoryInclusion.obj, wideSubcategoryInclusion.map, Iso.refl_symm,
    Iso.trans_refl, Iso.trans_assoc, Iso.trans_hom, Iso.refl_hom,
    MonoidalCategory.tensorIso_hom, MonoidalCategory.tensorHom_id,
    MonoidalCategory.whiskerRight_tensor, MonoidalCategory.id_whiskerRight, Category.id_comp,
    Iso.inv_hom_id, Category.comp_id]
    rw [MonoidalCategory.id_whiskerRight <| c.obj ⊗ c'.obj,
      Category.id_comp <| (α_ c.obj c'.obj c''.obj).hom]
    rw [show 𝟙 ((c ⊗ c').obj ⊗ c''.obj) = 𝟙 ((c.obj ⊗ c'.obj) ⊗ c''.obj) by rfl,
      Category.id_comp <| (α_ c.obj c'.obj c''.obj).hom]
    rfl
  · simp only [wideSubcategoryInclusion.obj, wideSubcategoryInclusion.map, Iso.refl_symm,
    Iso.trans_assoc, Iso.trans_hom, Iso.refl_hom, MonoidalCategory.tensorIso_hom,
    MonoidalCategory.tensorHom_id]
    rw [MonoidalCategory.id_whiskerRight <| (𝟙_ C)]
    rw [Category.id_comp (λ_ c.obj).hom]
    rw [show 𝟙 ((𝟙_ (WideSubcategory P)).obj ⊗ c.obj) = 𝟙 (𝟙_ C ⊗ c.obj) by rfl,
      Category.id_comp (λ_ c.obj).hom]
    rfl
  · simp only [wideSubcategoryInclusion.obj, wideSubcategoryInclusion.map, Iso.refl_symm,
    Iso.trans_assoc, Iso.trans_hom, Iso.refl_hom, MonoidalCategory.tensorIso_hom,
    MonoidalCategory.id_tensorHom]
    rw [MonoidalCategory.whiskerLeft_id c.obj <| 𝟙_ C, Category.id_comp (ρ_ c.obj).hom]
    rw [show 𝟙 (c.obj ⊗ (𝟙_ (WideSubcategory P)).obj) = 𝟙 (c.obj ⊗ 𝟙_ C) by rfl,
      Category.id_comp (ρ_ c.obj).hom]
    rfl

end IsMonoidalStable

section IsBraidedStable

section BraidedCategory

variable [BraidedCategory C]

/-- A monoidal-stable morphism property also stable under braiding isomorphisms. -/
class IsBraidedStable : Prop extends IsMonoidalStable P where
  braiding_hom (c c' : C) : P ((β_ c c').hom)
  braiding_inv (c c' : C) : P ((β_ c c').inv)

variable [P.IsBraidedStable]

lemma braiding_hom_mem (c c' : C) : P (β_ c c').hom := IsBraidedStable.braiding_hom _ _

lemma braiding_inv_mem (c c' : C) : P (β_ c c').inv := IsBraidedStable.braiding_inv _ _

instance : BraidedCategory (WideSubcategory P) where
  braiding c c' := by
    refine ⟨⟨(β_ c.obj c'.obj).hom, ?_⟩, ⟨(β_ c.obj c'.obj).inv, ?_⟩, ?_, ?_⟩
    · exact P.braiding_hom_mem _ _
    · exact P.braiding_inv_mem _ _
    all_goals
    widesubcat_ext
    simp
  braiding_naturality_right c c' c'' f := by
    widesubcat_ext
    exact BraidedCategory.braiding_naturality_right _ _
  braiding_naturality_left f c := by
    widesubcat_ext
    exact BraidedCategory.braiding_naturality_left _ _
  hexagon_forward c c' c'' := by
    widesubcat_ext
    exact BraidedCategory.hexagon_forward _ _ _
  hexagon_reverse c c' c'' := by
    widesubcat_ext
    exact BraidedCategory.hexagon_reverse _ _ _

end BraidedCategory

section SymmetricCategory

variable [SymmetricCategory C] [P.IsBraidedStable]

instance : SymmetricCategory (WideSubcategory P) where
  symmetry c c' := by
    widesubcat_ext
    exact SymmetricCategory.symmetry _ _

end SymmetricCategory

end IsBraidedStable

section IsComonStable

variable [BraidedCategory C] [∀ {c : C}, ComonObj c]

/-- A braided-stable morphism property stable under comonoid counit and comultiplication. -/
class IsComonStable : Prop extends IsBraidedStable P where
  counit (c : C) : P (ε[c])
  comul (c : C) : P (Δ[c])

variable [P.IsComonStable]

lemma counit_mem (c : C) : P (ε[c]) := IsComonStable.counit _

lemma comul_mem (c : C) : P (Δ[c]) := IsComonStable.comul _

instance {c : WideSubcategory P} : ComonObj c where
  counit := ⟨ε[c.obj], P.counit_mem _⟩
  comul := ⟨Δ[c.obj], P.comul_mem _⟩
  counit_comul := by
    widesubcat_ext
    exact ComonObj.counit_comul _
  comul_counit := by
    widesubcat_ext
    exact ComonObj.comul_counit _
  comul_assoc := by
    widesubcat_ext
    exact ComonObj.comul_assoc _

variable [∀ {c : C}, IsCommComonObj c]

instance {c : WideSubcategory P} : IsCommComonObj c where
  comul_comm := by
    widesubcat_ext
    exact IsCommComonObj.comul_comm _

end IsComonStable

end MorphismProperty

end CategoryTheory
