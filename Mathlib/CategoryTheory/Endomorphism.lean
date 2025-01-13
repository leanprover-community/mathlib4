/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Kim Morrison, Simon Hudon
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Opposites

/-!
# Endomorphisms

Definition and basic properties of endomorphisms and automorphisms of an object in a category.

For each `X : C`, we provide `CategoryTheory.End X := X ⟶ X` with a monoid structure,
and `CategoryTheory.Aut X := X ≅ X` with a group structure.
-/


universe v v' u u'

namespace CategoryTheory

/-- Endomorphisms of an object in a category. Arguments order in multiplication agrees with
`Function.comp`, not with `CategoryTheory.CategoryStruct.comp`. -/
def End {C : Type u} [CategoryStruct.{v} C] (X : C) := X ⟶ X

namespace End

section Struct

variable {C : Type u} [CategoryStruct.{v} C] (X : C)

protected instance one : One (End X) := ⟨𝟙 X⟩

protected instance inhabited : Inhabited (End X) := ⟨𝟙 X⟩

/-- Multiplication of endomorphisms agrees with `Function.comp`, not with
`CategoryTheory.CategoryStruct.comp`. -/
protected instance mul : Mul (End X) := ⟨fun x y => y ≫ x⟩

variable {X}

/-- Assist the typechecker by expressing a morphism `X ⟶ X` as a term of `CategoryTheory.End X`. -/
def of (f : X ⟶ X) : End X := f

/-- Assist the typechecker by expressing an endomorphism `f : CategoryTheory.End X` as a term of
`X ⟶ X`. -/
def asHom (f : End X) : X ⟶ X := f

-- dsimp loops when applying this lemma to its LHS,
-- probably https://github.com/leanprover/lean4/pull/2867
@[simp, nolint simpNF] -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: use `of`/`asHom`?
theorem one_def : (1 : End X) = 𝟙 X := rfl

@[simp] -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: use `of`/`asHom`?
theorem mul_def (xs ys : End X) : xs * ys = ys ≫ xs := rfl

end Struct

/-- Endomorphisms of an object form a monoid -/
instance monoid {C : Type u} [Category.{v} C] {X : C} : Monoid (End X) where
  mul_one := Category.id_comp
  one_mul := Category.comp_id
  mul_assoc := fun x y z => (Category.assoc z y x).symm

section MulAction

variable {C : Type u} [Category.{v} C]

open Opposite

instance mulActionRight {X Y : C} : MulAction (End Y) (X ⟶ Y) where
  smul r f := f ≫ r
  one_smul := Category.comp_id
  mul_smul _ _ _ := Eq.symm <| Category.assoc _ _ _

instance mulActionLeft {X : Cᵒᵖ} {Y : C} : MulAction (End X) (unop X ⟶ Y) where
  smul r f := r.unop ≫ f
  one_smul := Category.id_comp
  mul_smul _ _ _ := Category.assoc _ _ _

theorem smul_right {X Y : C} {r : End Y} {f : X ⟶ Y} : r • f = f ≫ r :=
  rfl

theorem smul_left {X : Cᵒᵖ} {Y : C} {r : End X} {f : unop X ⟶ Y} : r • f = r.unop ≫ f :=
  rfl

end MulAction

/-- In a groupoid, endomorphisms form a group -/
instance group {C : Type u} [Groupoid.{v} C] (X : C) : Group (End X) where
  inv_mul_cancel := Groupoid.comp_inv
  inv := Groupoid.inv

end End

theorem isUnit_iff_isIso {C : Type u} [Category.{v} C] {X : C} (f : End X) :
    IsUnit (f : End X) ↔ IsIso f :=
  ⟨fun h => { out := ⟨h.unit.inv, ⟨h.unit.inv_val, h.unit.val_inv⟩⟩ }, fun h =>
    ⟨⟨f, inv f, by simp, by simp⟩, rfl⟩⟩

variable {C : Type u} [Category.{v} C] (X : C)

/-- Automorphisms of an object in a category.

The order of arguments in multiplication agrees with
`Function.comp`, not with `CategoryTheory.CategoryStruct.comp`.
-/
def Aut (X : C) := X ≅ X

namespace Aut

@[ext]
lemma ext {X : C} {φ₁ φ₂ : Aut X} (h : φ₁.hom = φ₂.hom) : φ₁ = φ₂ :=
  Iso.ext h

protected instance inhabited : Inhabited (Aut X) := ⟨Iso.refl X⟩

instance : Group (Aut X) where
  one := Iso.refl X
  inv := Iso.symm
  mul x y := Iso.trans y x
  mul_assoc _ _ _ := (Iso.trans_assoc _ _ _).symm
  one_mul := Iso.trans_refl
  mul_one := Iso.refl_trans
  inv_mul_cancel := Iso.self_symm_id

theorem Aut_mul_def (f g : Aut X) : f * g = g.trans f := rfl

theorem Aut_inv_def (f : Aut X) : f⁻¹ = f.symm := rfl

/-- Units in the monoid of endomorphisms of an object
are (multiplicatively) equivalent to automorphisms of that object.
-/
def unitsEndEquivAut : (End X)ˣ ≃* Aut X where
  toFun f := ⟨f.1, f.2, f.4, f.3⟩
  invFun f := ⟨f.1, f.2, f.4, f.3⟩
  left_inv := fun ⟨_, _, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _, _⟩ => rfl
  map_mul' f g := by cases f; cases g; rfl

/-- The inclusion of `Aut X` to `End X` as a monoid homomorphism. -/
@[simps!]
def toEnd (X : C) : Aut X →* End X := (Units.coeHom (End X)).comp (Aut.unitsEndEquivAut X).symm

/-- Isomorphisms induce isomorphisms of the automorphism group -/
def autMulEquivOfIso {X Y : C} (h : X ≅ Y) : Aut X ≃* Aut Y where
  toFun x := { hom := h.inv ≫ x.hom ≫ h.hom, inv := h.inv ≫ x.inv ≫ h.hom }
  invFun y := { hom := h.hom ≫ y.hom ≫ h.inv, inv := h.hom ≫ y.inv ≫ h.inv }
  left_inv _ := by aesop_cat
  right_inv _ := by aesop_cat
  map_mul' := by simp [Aut_mul_def]

end Aut

namespace Functor

variable {D : Type u'} [Category.{v'} D] (f : C ⥤ D)

/-- `f.map` as a monoid hom between endomorphism monoids. -/
@[simps]
def mapEnd : End X →* End (f.obj X) where
  toFun := f.map
  map_mul' x y := f.map_comp y x
  map_one' := f.map_id X

/-- `f.mapIso` as a group hom between automorphism groups. -/
def mapAut : Aut X →* Aut (f.obj X) where
  toFun := f.mapIso
  map_mul' x y := f.mapIso_trans y x
  map_one' := f.mapIso_refl X

namespace FullyFaithful

variable {f}
variable (hf : FullyFaithful f)

/-- `mulEquivEnd` as an isomorphism between endomorphism monoids. -/
@[simps!]
noncomputable def mulEquivEnd (X : C) :
    End X ≃* End (f.obj X) where
  toEquiv := hf.homEquiv
  __ := mapEnd X f

/-- `mulEquivAut` as an isomorphism between automorphism groups. -/
@[simps!]
noncomputable def autMulEquivOfFullyFaithful (X : C) :
    Aut X ≃* Aut (f.obj X) where
  toEquiv := hf.isoEquiv
  __ := mapAut X f

end FullyFaithful

end Functor

namespace Equivalence

universe uC uC' vC vC' uD uD' vD vD'

variable {C : Type uC} [Category.{vC} C]
variable {C' : Type uC'} [Category.{vC'} C']
variable {D : Type uD} [Category.{vD} D]
variable {D' : Type uD'} [Category.{vD'} D']
variable {f : C ⥤ D}  {g : C' ⥤ D'}
variable {e : C ≌ C'} {e' : D ≌ D'}

/--
Suppose we have categories `C, C', D, D'` such that the diagram of functors
```
C ===== f =====> D
||e            ||e'
||             ||
C' ==== g ====> D'
```
commutes where `e` and `e'` are equivalence of categories.

Then we have an isomorphism of endomorphism monoids `End f ≃* End g'` and
-/
@[simps]
def endMonoidEquiv
    (sq₀ : f.comp e'.functor ≅ e.functor.comp g) : End f ≃* End g :=
  let sq₁ : e.inverse.comp (f.comp e'.functor) ≅ g := sq₀.inverseCompIso
  let sq₂ : f ≅ e.functor.comp (g.comp e'.inverse) := Iso.isoCompInverse sq₀
  { toFun α :=
    { app c :=
        sq₁.inv.app c ≫
        e'.functor.map (α.app (e.inverse.obj c)) ≫
        sq₁.hom.app c
      naturality c c' h := by
        simp only [Functor.comp_obj, NatTrans.naturality_assoc, Functor.comp_map, Category.assoc,
          NatIso.cancel_natIso_inv_left]
        rw [← sq₁.hom.naturality h, ← Category.assoc, ← e'.functor.map_comp, ← Category.assoc,
          Functor.comp_map, Functor.comp_map, ← e'.functor.map_comp, ← α.naturality] }
    invFun α :=
    { app c := sq₂.hom.app c ≫ e'.inverse.map (α.app (e.functor.obj c)) ≫ sq₂.inv.app c
      naturality c c' h := by
        simp only [Functor.comp_obj, NatTrans.naturality_assoc, Functor.comp_map, Category.assoc,
          NatIso.cancel_natIso_hom_left]
        rw [← sq₂.inv.naturality h, ← Category.assoc, ← e'.inverse.map_comp, ← Category.assoc,
          Functor.comp_map, Functor.comp_map, ← e'.inverse.map_comp, ← α.naturality] }
    left_inv α := NatTrans.ext <| funext fun c ↦ by
      simp only [Functor.comp_obj, Iso.isoCompInverse_hom_app, Iso.inverseCompIso_inv_app,
        Iso.inverseCompIso_hom_app, Category.assoc, Functor.map_comp, inv_fun_map, Functor.id_obj,
        Iso.isoCompInverse_inv_app, sq₂, sq₁]
      have eq₀ := sq₀.hom.naturality (e.unit.app c)
      simp only [Functor.id_obj, Functor.comp_obj, Functor.comp_map, sq₁, sq₂] at eq₀
      slice_lhs 2 4 =>
        rw [← e'.inverse.map_comp, ← e'.inverse.map_comp, e.counitInv_app_functor c,
          ← Category.assoc, ← eq₀]
      simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id,
        inv_fun_map, Functor.id_obj, NatTrans.naturality, Iso.hom_inv_id_app_assoc, sq₁, sq₂]
      have eq₁ := sq₀.hom.naturality (e.unitInv.app c)
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, sq₁, sq₂] at eq₁
      slice_lhs 4 6 =>
        rw [← e'.inverse.map_comp, ← e'.inverse.map_comp, e.counit_app_functor c,
          ← Category.assoc, ← eq₁]
      simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id,
        inv_fun_map, Functor.id_obj, Iso.hom_inv_id_app_assoc, sq₁, sq₂]
      simp only [← Functor.map_comp, Iso.hom_inv_id_app, Functor.id_obj, Functor.map_id,
        Category.comp_id, sq₁, sq₂]
    right_inv α := NatTrans.ext <| funext fun c ↦ by
      simp only [Functor.comp_obj, Iso.inverseCompIso_inv_app, Iso.isoCompInverse_hom_app,
        Iso.isoCompInverse_inv_app, Category.assoc, Functor.map_comp, fun_inv_map, Functor.id_obj,
        counitInv_functor_comp, Category.comp_id, Iso.inv_hom_id_app_assoc, functor_unit_comp_assoc,
        Iso.inverseCompIso_hom_app, NatTrans.naturality_assoc, sq₁, sq₂]
      simp only [← Functor.map_comp, Iso.inv_hom_id_app, Functor.id_obj, Functor.map_id,
        Category.comp_id, sq₁, sq₂]
    map_mul' α β := by
      simp only [Functor.comp_obj, Iso.inverseCompIso_inv_app, End.mul_def, NatTrans.comp_app,
        Functor.map_comp, Iso.inverseCompIso_hom_app, Category.assoc, sq₁, sq₂]
      refine NatTrans.ext <| funext fun c ↦ show _ = _ ≫ _ from ?_
      simp only [Category.assoc, sq₁, sq₂]
      congr 2
      rw [← e'.functor.map_comp_assoc, ← g.map_comp_assoc, Iso.hom_inv_id_app]
      simp only [Functor.map_comp, Category.assoc, Functor.comp_obj, Functor.map_id,
        Category.id_comp, Iso.hom_inv_id_app_assoc, sq₁, sq₂] }

end Equivalence

end CategoryTheory
