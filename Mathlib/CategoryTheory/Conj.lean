/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.HomCongr

/-!
# Conjugate morphisms by isomorphisms

An isomorphism `α : X ≅ Y` defines
- a monoid isomorphism
  `CategoryTheory.Iso.conj : End X ≃* End Y` by `α.conj f = α.inv ≫ f ≫ α.hom`;
- a group isomorphism `CategoryTheory.Iso.conjAut : Aut X ≃* Aut Y` by
  `α.conjAut f = α.symm ≪≫ f ≪≫ α`
  using
  `CategoryTheory.Iso.homCongr : (X ≅ X₁) → (Y ≅ Y₁) → (X ⟶ Y) ≃ (X₁ ⟶ Y₁)`
  and `CategoryTheory.Iso.isoCongr : (f : X₁ ≅ X₂) → (g : Y₁ ≅ Y₂) → (X₁ ≅ Y₁) ≃ (X₂ ≅ Y₂)`
  which are defined in  `CategoryTheory.HomCongr`.
-/

@[expose] public section

namespace CategoryTheory

namespace Iso

variable {C : Type*} [Category* C]

variable {X Y : C} (α : X ≅ Y)

/-- An isomorphism between two objects defines a monoid isomorphism between their
monoid of endomorphisms. -/
@[implicit_reducible, simps!]
def conj : End X ≃* End Y where
  toEquiv := End.homEquiv.trans ((homCongr α α).trans End.homEquiv.symm)
  map_mul' := by cat_disch

@[deprecated (since := "2026-09-12")] alias conj_apply := conj_apply_asHom

@[deprecated "use map_mul" (since := "2026-09-12")]
theorem conj_comp (f g : End X) : α.conj (f * g) = α.conj f * α.conj g :=
  map_mul _ _ _

@[deprecated "use map_one" (since := "2026-09-12")]
theorem conj_id : α.conj 1 = 1 := map_one _

@[simp]
theorem refl_conj (f : End X) : (Iso.refl X).conj f = f := by
  cat_disch

@[simp]
theorem trans_conj {Z : C} (β : Y ≅ Z) (f : End X) : (α ≪≫ β).conj f = β.conj (α.conj f) := by
  cat_disch

@[simp]
theorem symm_self_conj (f : End X) : α.symm.conj (α.conj f) = f := by
  rw [← trans_conj, α.self_symm_id, refl_conj]

@[simp]
theorem self_symm_conj (f : End Y) : α.conj (α.symm.conj f) = f :=
  α.symm.symm_self_conj f

@[simp]
theorem conj_pow (f : End X) (n : ℕ) : α.conj (f ^ n) = α.conj f ^ n :=
  α.conj.toMonoidHom.map_pow f n

/-- `conj` defines a group isomorphism between groups of automorphisms -/
def conjAut : Aut X ≃* Aut Y :=
  (Aut.unitsEndEquivAut X).symm.trans <| (Units.mapEquiv α.conj).trans <| Aut.unitsEndEquivAut Y

theorem conjAut_apply (f : Aut X) : (α.conjAut f).asIso = α.symm ≪≫ f.asIso ≪≫ α := by
  cat_disch

@[simp]
theorem conjAut_hom (f : Aut X) : (α.conjAut f).asIso.hom = (α.conj f.toEnd).asHom :=
  rfl

@[simp]
theorem trans_conjAut {Z : C} (β : Y ≅ Z) (f : Aut X) :
    (α ≪≫ β).conjAut f = β.conjAut (α.conjAut f) := by
  cat_disch

@[simp]
theorem conjAut_mul (f g : Aut X) : α.conjAut (f * g) = α.conjAut f * α.conjAut g :=
  map_mul α.conjAut f g

@[simp]
theorem conjAut_trans (f g : X ≅ X) :
    (α.conjAut (.of (f ≪≫ g))).asIso =
      (α.conjAut (.of f)).asIso ≪≫ (α.conjAut (.of g)).asIso := by
  cat_disch

@[simp]
theorem conjAut_pow (f : Aut X) (n : ℕ) : α.conjAut (f ^ n) = α.conjAut f ^ n :=
  map_pow α.conjAut f n

@[simp]
theorem conjAut_zpow (f : Aut X) (n : ℤ) : α.conjAut (f ^ n) = α.conjAut f ^ n :=
  map_zpow α.conjAut f n

end Iso

namespace Functor

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (F : C ⥤ D)

theorem map_conj {X Y : C} (α : X ≅ Y) (f : End X) :
    F.map (α.conj f).asHom =
      ((F.mapIso α).conj (F.mapEnd X f)).asHom := by
  cat_disch

theorem map_conjAut (F : C ⥤ D) {X Y : C} (α : X ≅ Y) (f : Aut X) :
    F.mapIso (α.conjAut f).asIso = ((F.mapIso α).conjAut (F.mapAut X f)).asIso := by
  cat_disch

end Functor

end CategoryTheory
