/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.HomCongr

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

universe v u

namespace CategoryTheory

namespace Iso

variable {C : Type u} [Category.{v} C]

variable {X Y : C} (α : X ≅ Y)

/-- An isomorphism between two objects defines a monoid isomorphism between their
monoids of endomorphisms. -/
@[simps!] def conj : End X ≃* End Y :=
  { homCongr α α with map_mul' := fun f g => homCongr_comp α α α g f }

theorem conj_comp (f g : End X) : α.conj (f ≫ g) = α.conj f ≫ α.conj g :=
  map_mul α.conj g f

theorem conj_id : α.conj (𝟙 X) = 𝟙 Y :=
  map_one α.conj

theorem refl_conj (f : End X) : (Iso.refl X).conj f = f := by simp

theorem trans_conj {Z : C} (β : Y ≅ Z) (f : End X) : (α ≪≫ β).conj f = β.conj (α.conj f) :=
  homCongr_trans α α β β f

theorem symm_self_conj (f : End X) : α.symm.conj (α.conj f) = f := by simp

theorem self_symm_conj (f : End Y) : α.conj (α.symm.conj f) = f :=
  α.symm.symm_self_conj f

theorem conj_pow (f : End X) (n : ℕ) : α.conj (f ^ n) = α.conj f ^ n :=
  α.conj.toMonoidHom.map_pow f n

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: change definition so that `conjAut_apply` becomes a `rfl`?
/-- `conj` defines a group isomorphisms between groups of automorphisms -/
def conjAut : Aut X ≃* Aut Y :=
  (Aut.unitsEndEquivAut X).symm.trans <| (Units.mapEquiv α.conj).trans <| Aut.unitsEndEquivAut Y

theorem conjAut_apply (f : Aut X) : α.conjAut f = α.symm ≪≫ f ≪≫ α := by cat_disch

@[simp]
theorem conjAut_hom (f : Aut X) : (α.conjAut f).hom = α.conj f.hom :=
  rfl

@[simp]
theorem trans_conjAut {Z : C} (β : Y ≅ Z) (f : Aut X) :
    (α ≪≫ β).conjAut f = β.conjAut (α.conjAut f) := by
  simp only [conjAut_apply, Iso.trans_symm, Iso.trans_assoc]

@[simp]
theorem conjAut_mul (f g : Aut X) : α.conjAut (f * g) = α.conjAut f * α.conjAut g :=
  map_mul α.conjAut f g

@[simp]
theorem conjAut_trans (f g : Aut X) : α.conjAut (f ≪≫ g) = α.conjAut f ≪≫ α.conjAut g :=
  conjAut_mul α g f

@[simp]
theorem conjAut_pow (f : Aut X) (n : ℕ) : α.conjAut (f ^ n) = α.conjAut f ^ n :=
  map_pow α.conjAut f n

@[simp]
theorem conjAut_zpow (f : Aut X) (n : ℤ) : α.conjAut (f ^ n) = α.conjAut f ^ n :=
  map_zpow α.conjAut f n

end Iso

namespace Functor

universe v₁ u₁

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D] (F : C ⥤ D)

theorem map_conj {X Y : C} (α : X ≅ Y) (f : End X) :
    F.map (α.conj f) = (F.mapIso α).conj (F.map f) :=
  map_homCongr F α α f

theorem map_conjAut (F : C ⥤ D) {X Y : C} (α : X ≅ Y) (f : Aut X) :
    F.mapIso (α.conjAut f) = (F.mapIso α).conjAut (F.mapIso f) := by
  ext; simp only [mapIso_hom, Iso.conjAut_hom, F.map_conj]

-- alternative proof: by simp only [Iso.conjAut_apply, F.mapIso_trans, F.mapIso_symm]
end Functor

namespace Equivalence

universe uC uC' vC vC' uD uD' vD vD'

variable {C : Type uC} [Category.{vC} C]
variable {C' : Type uC'} [Category.{vC'} C']
variable {D : Type uD} [Category.{vD} D]
variable {D' : Type uD'} [Category.{vD'} D']
variable {f : C ⥤ D} {g : C' ⥤ D'}
variable {e : C ≌ C'} {e' : D ≌ D'}

/--
Suppose we have categories `C, C', D, D'` such that the diagram of functors
```
C ===== f =====> D
||e            ||e'
||             ||
C' ==== g ====> D'
```
commutes up to natural isomorphism where `e` and `e'` are equivalence of categories.

Then we have an isomorphism of endomorphism monoids `End f ≃* End g'` and
-/
@[simps!]
noncomputable def endMonoidEquiv (sq₀ : f ⋙ e'.functor ≅ e.functor ⋙ g) : End f ≃* End g :=
  (e'.congrRight.fullyFaithfulFunctor.mulEquivEnd f).trans <| sq₀.conj.trans
    (e.congrLeft.fullyFaithfulInverse.mulEquivEnd g).symm

end Equivalence

end CategoryTheory
