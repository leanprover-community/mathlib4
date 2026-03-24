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

variable [BraidedCategory C] [∀ {c : C}, ComonObj c]

/-- A braided-stable morphism property stable under comonoid counit and comultiplication. -/
class IsStableUnderComonoid (P : MorphismProperty C) : Prop extends IsStableUnderBraiding P where
  counit_mem (P) (c : C) : P (ε[c])
  comul_mem (P) (c : C) : P (Δ[c])

export IsStableUnderComonoid (counit_mem comul_mem)

end IsStableUnderComonoid

end MorphismProperty

namespace WideSubcategory

section MonoidalCategory

variable [P.IsMonoidalStable]

@[simps]
instance : MonoidalCategoryStruct (WideSubcategory P) where
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

instance : MonoidalCategory (WideSubcategory P) :=
  Monoidal.induced (wideSubcategoryInclusion P)
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

end MonoidalCategory

section BraidedCategory

variable [BraidedCategory C] [P.IsStableUnderBraiding]

instance : BraidedCategory (WideSubcategory P) where
  braiding _ _ :=
    isoMk (β_ _ _) (P.braiding_hom_mem _ _) (P.braiding_inv_mem _ _)

end BraidedCategory

section SymmetricCategory

variable [SymmetricCategory C] [P.IsStableUnderBraiding]

instance : SymmetricCategory (WideSubcategory P) where
  symmetry c c' := by
    ext
    exact SymmetricCategory.symmetry _ _

end SymmetricCategory

section ComonObj

variable [BraidedCategory C] [∀ {c : C}, ComonObj c] [P.IsStableUnderComonoid]

@[simps]
instance {c : WideSubcategory P} : ComonObj c where
  counit := ⟨ε[c.obj], P.counit_mem _⟩
  comul := ⟨Δ[c.obj], P.comul_mem _⟩

variable [∀ {c : C}, IsCommComonObj c]

instance {c : WideSubcategory P} : IsCommComonObj c where
  comul_comm := by
    ext
    exact IsCommComonObj.comul_comm _

end ComonObj

section CopyDiscardCategory

variable [CopyDiscardCategory C] [P.IsStableUnderComonoid]

instance : CopyDiscardCategory (WideSubcategory P) where
  copy_tensor c c' := by
    ext
    exact CopyDiscardCategory.copy_tensor c.obj c'.obj
  discard_tensor c c' := by
    ext
    exact CopyDiscardCategory.discard_tensor c.obj c'.obj
  copy_unit := by
    ext
    exact CopyDiscardCategory.copy_unit (C := C)
  discard_unit := by
    ext
    exact CopyDiscardCategory.discard_unit (C := C)

end CopyDiscardCategory

end WideSubcategory

end CategoryTheory
