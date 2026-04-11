/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings

/-!
# The restriction of scalars functor is lax monoidal

-/

@[expose] public section

universe v v' u u'

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {R R' : Cᵒᵖ ⥤ CommRingCat.{u}}
  (α : R ⟶ R')

noncomputable abbrev restrictScalarsOfCommRing :
    PresheafOfModules.{v} (R' ⋙ forget₂ _ _) ⥤ PresheafOfModules (R ⋙ forget₂ _ _) :=
  restrictScalars (Functor.whiskerRight α (forget₂ _ RingCat))

open ConcreteCategory in
set_option backward.isDefEq.respectTransparency false in
noncomputable instance : (restrictScalarsOfCommRing.{u} α).LaxMonoidal where
  ε :=
    { app U := ε (ModuleCat.restrictScalars (α.app U).hom)
      naturality {U V} f := by
        ext
        dsimp
        erw [ModuleCat.restrictScalars_ε, ModuleCat.restrictScalars_ε]
        exact ConcreteCategory.congr_hom (α.naturality f) 1 }
  μ F₁ F₂ :=
    { app U := μ (ModuleCat.restrictScalars (α.app U).hom) _ _
      naturality {U V} f :=
        ModuleCat.MonoidalCategory.tensor_ext (fun m₁ m₂ ↦ by
          dsimp
          erw [ModuleCat.restrictScalars_μ_tmul, ModuleCat.restrictScalars_μ_tmul]
          rfl )}
  μ_natural_left _ _ := by
    ext U : 1
    apply μ_natural_left (ModuleCat.restrictScalars (α.app U).hom)
  μ_natural_right _ _ := by
    ext U : 1
    apply μ_natural_right (ModuleCat.restrictScalars (α.app U).hom)
  associativity _ _ _ := by
    ext U : 1
    apply associativity (ModuleCat.restrictScalars (α.app U).hom)
  left_unitality _ := by
    ext U : 1
    apply left_unitality (ModuleCat.restrictScalars (α.app U).hom)
  right_unitality _ := by
    ext U : 1
    apply right_unitality (ModuleCat.restrictScalars (α.app U).hom)

end PresheafOfModules
