/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.CategoryTheory.Monoidal.Mon_
public import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Monoidal structures on wide subcategories

Given a monoidal category `C` and a morphism property `P : MorphismProperty C`,
this file introduces conditions on `P` ensuring that `WideSubcategory P` inherits
additional structures.

We define stability classes under associators, unitors, and braidings, and use
them to construct monoidal, braided, and symmetric structures on
`WideSubcategory P`.

-/

@[expose] public section

namespace CategoryTheory

open scoped MonoidalCategory

variable {C : Type*} [Category* C] (P : MorphismProperty C) [MonoidalCategory C]

namespace MorphismProperty

/-- A morphism property stable under associator isomorphisms of a monoidal category. -/
class IsStableUnderAssociator (P : MorphismProperty C) : Prop where
  associator_hom_mem (P) (c c' c'' : C) : P (α_ c c' c'').hom
  associator_inv_mem (P) (c c' c'' : C) : P (α_ c c' c'').inv

export IsStableUnderAssociator (associator_hom_mem associator_inv_mem)

/-- A morphism property stable under left and right unitor isomorphisms. -/
class IsStableUnderUnitor (P : MorphismProperty C) : Prop where
  leftUnitor_hom_mem (P) (c : C) : P ((λ_ c).hom)
  leftUnitor_inv_mem (P) (c : C) : P ((λ_ c).inv)
  rightUnitor_hom_mem (P) (c : C) : P ((ρ_ c).hom)
  rightUnitor_inv_mem (P) (c : C) : P ((ρ_ c).inv)

export IsStableUnderUnitor (leftUnitor_hom_mem leftUnitor_inv_mem rightUnitor_hom_mem
  rightUnitor_inv_mem)

/-- A morphism property stable under tensoring, associators, and unitors. -/
class IsMonoidalStable : Prop extends IsMonoidal P, IsStableUnderAssociator P,
    IsStableUnderUnitor P

/-- A monoidal-stable morphism property also stable under braiding isomorphisms. -/
class IsStableUnderBraiding [BraidedCategory C] (P : MorphismProperty C) : Prop
    extends IsMonoidalStable P where
  braiding_hom_mem (P) (c c' : C) : P (β_ c c').hom
  braiding_inv_mem (P) (c c' : C) : P (β_ c c').inv

export IsStableUnderBraiding (braiding_hom_mem braiding_inv_mem)

end MorphismProperty

namespace WideSubcategory

@[simps]
instance [P.IsMonoidalStable] : MonoidalCategoryStruct (WideSubcategory P) where
  tensorObj c c' := ⟨c.obj ⊗ c'.obj⟩
  whiskerLeft c _ _ f := ⟨c.obj ◁ f.1, P.whiskerLeft_mem _ _ f.2⟩
  whiskerRight f c' := ⟨f.1 ▷ c'.obj, P.whiskerRight_mem _ f.2 _⟩
  tensorUnit := ⟨𝟙_ C⟩
  associator _ _ _ :=
    isoMk (α_ _ _ _) (P.associator_hom_mem _ _ _) (P.associator_inv_mem _ _ _)
  leftUnitor _ :=
    isoMk (λ_ _) (P.leftUnitor_hom_mem _) (P.leftUnitor_inv_mem _)
  rightUnitor _ :=
    isoMk (ρ_ _) (P.rightUnitor_hom_mem _) (P.rightUnitor_inv_mem _)
  tensorHom f g := ⟨f.1 ⊗ₘ g.1, P.tensorHom_mem _ _ f.2 g.2⟩

instance [P.IsMonoidalStable] : MonoidalCategory (WideSubcategory P) :=
  Monoidal.induced (wideSubcategoryInclusion P)
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

instance [BraidedCategory C] [P.IsStableUnderBraiding] :
    BraidedCategory (WideSubcategory P) where
  braiding _ _ :=
    isoMk (β_ _ _) (P.braiding_hom_mem _ _) (P.braiding_inv_mem _ _)

variable {P} in
open MonoidalCategory in
@[simp]
lemma tensorμ_hom [BraidedCategory C] [P.IsStableUnderBraiding] (X Y Z T : WideSubcategory P) :
    (tensorμ X Y Z T).hom = tensorμ _ _ _ _ := rfl

instance [SymmetricCategory C] [P.IsStableUnderBraiding] :
    SymmetricCategory (WideSubcategory P) where
  symmetry c c' := by
    ext
    exact SymmetricCategory.symmetry _ _

end WideSubcategory

end CategoryTheory
