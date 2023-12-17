/-
Copyright (c) 2023 Qi Ge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qi Ge
-/
import Mathlib.Algebra.GroupRingAction.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.RepresentationTheory.Action
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Group action on rings

This file defines the typeclass of monoid acting on semirings `MulSemiringAction M R`,
and the corresponding typeclass of invariant subrings.

Note that `Algebra` does not satisfy the axioms of `MulSemiringAction`.

## Implementation notes

There is no separate typeclass for group acting on rings, group acting on fields, etc.
They are all grouped under `MulSemiringAction`.

## Tags

group action, invariant subring

-/


open CategoryTheory

universe v u

variable (M : Type u) [Monoid M]

structure MulSemiringActionCat where
  carrier : Type v
  [isSemiring : Semiring carrier]
  [isMulSemiringAction : MulSemiringAction M carrier]

attribute [instance] MulSemiringActionCat.isSemiring MulSemiringActionCat.isMulSemiringAction

instance : CoeSort (MulSemiringActionCat.{v} M) (Type v) :=
  ⟨MulSemiringActionCat.carrier⟩

attribute [coe] MulSemiringActionCat.carrier

instance mulSemiringActionCategory :
    Category.{v, max (v+1) u} (MulSemiringActionCat.{v} M) where
  Hom R S := MulSemiringActionHom M R S
  id _ := MulSemiringActionHom.id M
  comp f g := MulSemiringActionHom.comp g f

instance {R S : MulSemiringActionCat.{v} M} :
    MulSemiringActionHomClass (R ⟶ S) M R S :=
  MulSemiringActionHom.instMulSemiringActionHomClassMulSemiringActionHomToDistribMulActionToDistribMulAction M R S

instance moduleConcreteCategory :
    ConcreteCategory.{v} (MulSemiringActionCat.{v} M) where
  forget := {
    obj := fun R => R
    map := fun f => f.toFun
  }
  forget_faithful := {
    map_injective := by
      intro R S f g h
      apply MulSemiringActionHom.ext
      exact congrFun h
  }

instance {R : MulSemiringActionCat.{v} M} :
    Semiring ((forget (MulSemiringActionCat M)).obj R) :=
  (inferInstance : Semiring R)

instance {R : MulSemiringActionCat.{v} M} :
    MulSemiringAction M ((forget (MulSemiringActionCat M)).obj R) :=
  (inferInstance : MulSemiringAction M R)

@[ext]
lemma ext {R S : MulSemiringActionCat.{v} M} {f₁ f₂ : R ⟶ S} (h : ∀ (r : R), f₁ r = f₂ r) :
    f₁ = f₂ :=
  FunLike.ext _ _ h

instance hasForgetToSemiring : HasForget₂ (MulSemiringActionCat M) SemiRingCat where
  forget₂ := {
    obj := fun R => SemiRingCat.of R
    map := fun f => SemiRingCat.ofHom f.toRingHom
  }

-- Semiring or SemiRing????
def of (R : Type v) [Semiring R] [MulSemiringAction M R] :
    MulSemiringActionCat M :=
  ⟨R⟩

/--
Forgeting an object in the action category to semiring category
is defeq to
the coesion to the underlying semiring in the semiring category
-/
@[simp]
theorem forget₂_obj (R : MulSemiringActionCat M) :
    (forget₂ (MulSemiringActionCat M) SemiRingCat).obj R = SemiRingCat.of R :=
  rfl

/--
Given the data of an actioned ring
assemble to the object in action category
then forget to semiring category
is defeq to
assemble to the object in semiring category
-/
@[simp]
theorem forget₂_obj_SemiRingCat_of (R : Type v) [Semiring R] [MulSemiringAction M R] :
    SemiRingCat.of (of M R) = SemiRingCat.of R :=
  rfl
-- It is said this is not used?

/--
Forgeting a morphism in the action category to semiring category
is defeq to
the coesion to the underlying semiring morphism in the semiring category
-/
@[simp]
theorem forget₂_map (R S : MulSemiringActionCat M) (f : R ⟶ S) :
    (forget₂ (MulSemiringActionCat M) SemiRingCat).map f = MulSemiringActionHom.toRingHom f :=
  rfl

/-- Typecheck a `MulSemiringActionHom` as a morphism in `MulSemiringActionCat M`. -/
def ofHom {R S : Type v} [Semiring R] [MulSemiringAction M R] [Semiring S]
    [MulSemiringAction M S] (f : MulSemiringActionHom M R S) : of M R ⟶ of M S :=
  f

-- why simp 1100
@[simp]
theorem ofHom_apply {R S : Type v} [Semiring R] [MulSemiringAction M R]
    [Semiring S] [MulSemiringAction M S] (f : MulSemiringActionHom M R S) (r : R) :
      ofHom M f r = f r :=
  rfl

-- TODO?: Inhabited and Unique

-- Porting note: the simpNF linter complains, but we really need this?!
@[simp, nolint simpNF]
theorem coe_of (R : Type v) [Semiring R] [MulSemiringAction M R] :
    (of M R : Type v) = R :=
  rfl

-- or id_apply??
@[simp]
theorem coe_id {R: MulSemiringActionCat.{v} M}:
    (𝟙 R : R → R) = id :=
  rfl

@[simp]
theorem coe_comp {R S T : MulSemiringActionCat.{v} M} (f : R ⟶ S) (g : S ⟶ T) :
    f ≫ g = g ∘ f :=
  rfl

@[simp]
theorem comp_def {R S T : MulSemiringActionCat.{v} M} (f : R ⟶ S) (g : S ⟶ T) :
    f ≫ g = g.comp f :=
  rfl

@[simp]
lemma forget_map {R S : MulSemiringActionCat.{v} M} (f : R ⟶ S) :
    (forget (MulSemiringActionCat M)).map f = (f : R → S) :=
  rfl

def F : MulSemiringActionCat M ⥤ Action SemiRingCat (MonCat.of M) where
  obj R := {
    V := SemiRingCat.of R
    ρ := MulSemiringAction.toEndHom M R
  }
  map f := {
    hom := SemiRingCat.ofHom f
    comm := by
      intros m
      apply RingHom.ext
      intros r
      simp only [SemiRingCat.coe_of] at r ⊢
      change f (m • r) = m • f r
      exact map_smul f m r
  }

instance : CategoryTheory.Full (F M) where
  preimage {R S} := fun
    | .mk hom comm => {
      toFun := hom
      map_smul' := by
        intros m r
        change (SemiRingCat.ofHom (MulSemiringAction.toEndHom M R m) ≫ hom) r
          = (hom ≫ (SemiRingCat.ofHom (MulSemiringAction.toEndHom M S m))) r
        have h := comm m
        change SemiRingCat.ofHom (MulSemiringAction.toEndHom M R m) ≫ hom
          = hom ≫ (SemiRingCat.ofHom (MulSemiringAction.toEndHom M S m)) at h
        have t:
            (fun r => (SemiRingCat.ofHom (MulSemiringAction.toEndHom M R m) ≫ hom) r)
              = (fun r => (hom ≫ (SemiRingCat.ofHom (MulSemiringAction.toEndHom M S m))) r) :=
          FunLike.ext'_iff.mp (comm m)
        apply congrFun t r
      map_zero' := hom.map_zero'
      map_add' := hom.map_add'
      map_one' := hom.map_one'
      map_mul' := hom.map_mul'
    }

instance : CategoryTheory.Faithful (F M) where
  map_injective {_ _ a₁ a₂} h := by
    ext r
    change ((F M).map a₁).hom r = ((F M).map a₂).hom r
    exact congrFun (congrArg FunLike.coe (congrArg Action.Hom.hom h)) r

instance : CategoryTheory.EssSurj (F M) where
  mem_essImage
    | .mk V ρ => Functor.obj_mem_essImage (F M) (@of _ _ _ _ (MulSemiringAction.ofEndHom M V ρ))

theorem this : IsEquivalence (F M) := Equivalence.ofFullyFaithfullyEssSurj (F M)
