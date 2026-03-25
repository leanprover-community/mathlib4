/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.CategoryTheory.CopyDiscardCategory.Basic
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
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

section IsStableUnderBraiding

variable [BraidedCategory C]

/-- A monoidal-stable morphism property also stable under braiding isomorphisms. -/
class IsStableUnderBraiding (P : MorphismProperty C) : Prop extends IsMonoidalStable P where
  braiding_hom_mem (P) (c c' : C) : P ((β_ c c').hom)
  braiding_inv_mem (P) (c c' : C) : P ((β_ c c').inv)

export IsStableUnderBraiding (braiding_hom_mem braiding_inv_mem)

end IsStableUnderBraiding

section IsStableUnderComonoid

variable [BraidedCategory C] (c : C) [ComonObj c]

/-- A braided-stable morphism property stable under comonoid counit and comultiplication. -/
class IsStableUnderComonoid (P : MorphismProperty C) : Prop where
  counit_mem (P) : P (ε[c])
  comul_mem (P) : P (Δ[c])

export IsStableUnderComonoid (counit_mem comul_mem)

end IsStableUnderComonoid

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

instance [SymmetricCategory C] [P.IsStableUnderBraiding] :
    SymmetricCategory (WideSubcategory P) where
  symmetry c c' := by
    ext
    exact SymmetricCategory.symmetry _ _

section ComonObj

variable [BraidedCategory C] [P.IsStableUnderBraiding] (c : WideSubcategory P) [ComonObj c.obj]
  [P.IsStableUnderComonoid c.obj]

@[simps]
instance : ComonObj c where
  counit := ⟨ε[c.obj], P.counit_mem⟩
  comul := ⟨Δ[c.obj], P.comul_mem⟩

variable [IsCommComonObj c.obj]

instance : IsCommComonObj c where
  comul_comm := by
    ext
    exact IsCommComonObj.comul_comm _

end ComonObj

section CopyDiscardCategory

variable [CopyDiscardCategory C] [P.IsStableUnderBraiding]

@[simp]
lemma tensorμ_hom (X Y Z T : WideSubcategory P) :
    (MonoidalCategory.tensorμ X Y Z T).hom = MonoidalCategory.tensorμ _ _ _ _ := rfl

open CopyDiscardCategory in
attribute [local simp] copy_tensor discard_tensor copy_unit discard_unit in
instance [∀ c, P.IsStableUnderComonoid c] : CopyDiscardCategory (WideSubcategory P) where

end CopyDiscardCategory

end WideSubcategory

end CategoryTheory
