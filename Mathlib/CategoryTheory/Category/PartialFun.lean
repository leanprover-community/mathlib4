/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module category_theory.category.PartialFun
! leanprover-community/mathlib commit 14b69e9f3c16630440a2cbd46f1ddad0d561dee7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.Data.PFun

/-!
# The category of types with partial functions

This defines `PartialFun`, the category of types equipped with partial functions.

This category is classically equivalent to the category of pointed types. The reason it doesn't hold
constructively stems from the difference between `Part` and `Option`. Both can model partial
functions, but the latter forces a decidable domain.

Precisely, `PartialFunToPointed` turns a partial function `α →. β` into a function
`Option α → Option β` by sending to `none` the undefined values (and `none` to `none`). But being
defined is (generally) undecidable while being sent to `none` is decidable. So it can't be
constructive.

## References

* [nLab, *The category of sets and partial functions*]
  (https://ncatlab.org/nlab/show/partial+function)
-/


open CategoryTheory Option

universe u

variable {α β : Type _}

/-- The category of types equipped with partial functions. -/
def PartialFun : Type _ :=
  Type _
set_option linter.uppercaseLean3 false
#align PartialFun PartialFun

namespace PartialFun

instance : CoeSort PartialFun (Type _) :=
  ⟨id⟩

-- porting note: removed `@[nolint has_nonempty_instance]`
/-- Turns a type into a `PartialFun`. -/
def of : Type _ → PartialFun :=
  id
#align PartialFun.of PartialFun.of

-- porting note: removed this lemma which is useless because of the expansion of coercions
--theorem coe_of (X : Type _) : ↥(of X) = X :=
--  rfl
--#align PartialFun.coe_of PartialFun.coe_of

instance : Inhabited PartialFun :=
  ⟨Type _⟩

instance largeCategory : LargeCategory.{u} PartialFun where
  Hom := PFun
  id := PFun.id
  comp f g := g.comp f
  id_comp := @PFun.comp_id
  comp_id := @PFun.id_comp
  assoc _ _ _ := (PFun.comp_assoc _ _ _).symm
#align PartialFun.large_category PartialFun.largeCategory

/-- Constructs a partial function isomorphism between types from an equivalence between them. -/
@[simps]
def Iso.mk {α β : PartialFun.{u}} (e : α ≃ β) : α ≅ β where
  hom x := e x
  inv x := e.symm x
  hom_inv_id := (PFun.coe_comp _ _).symm.trans (by
    simp only [Equiv.symm_comp_self, PFun.coe_id]
    rfl)
  inv_hom_id := (PFun.coe_comp _ _).symm.trans (by
    simp only [Equiv.self_comp_symm, PFun.coe_id]
    rfl)
#align PartialFun.iso.mk PartialFun.Iso.mk

end PartialFun

/-- The forgetful functor from `Type` to `PartialFun` which forgets that the maps are total. -/
def typeToPartialFun : Type u ⥤ PartialFun where
  obj := id
  map := @PFun.lift
  map_comp _ _ := PFun.coe_comp _ _
#align Type_to_PartialFun typeToPartialFun

instance : Faithful typeToPartialFun where
  map_injective {_ _} := PFun.lift_injective

/-- The functor which deletes the point of a pointed type. In return, this makes the maps partial.
This the computable part of the equivalence `PartialFunEquivPointed`. -/
@[simps map]
def pointedToPartialFun : Pointed.{u} ⥤ PartialFun where
  obj X := { x : X // x ≠ X.point }
  map f := PFun.toSubtype _ f.toFun ∘ Subtype.val
  map_id X :=
    PFun.ext fun a b => PFun.mem_toSubtype_iff.trans (Subtype.coe_inj.trans Part.mem_some_iff.symm)
  map_comp f g := by
    -- porting note: the proof was changed because the original mathlib3 proof no longer worked
    apply PFun.ext _
    rintro ⟨a, ha⟩ ⟨c, hc⟩
    constructor
    . rintro ⟨h₁, h₂⟩
      exact ⟨⟨fun h₀ => h₁ ((congr_arg g.toFun h₀).trans g.map_point), h₁⟩, h₂⟩
    . rintro ⟨_, _, _⟩
      exact ⟨_, rfl⟩
#align Pointed_to_PartialFun pointedToPartialFun

-- porting note: this lemma may need to be added in order to prove `map_comp` for
-- `partialFunToPointed`
lemma _root_.Option.elim'_eq_elim {α β : Type _} (b : β) (f : α → β) (a : Option α) :
    Option.elim' b f a = Option.elim a b f := by
  cases a <;> rfl

/-- The functor which maps undefined values to a new point. This makes the maps total and creates
pointed types. This the noncomputable part of the equivalence `PartialFunEquivPointed`. It can't
be computable because `= Option.none` is decidable while the domain of a general `part` isn't. -/
@[simps map]
noncomputable def partialFunToPointed : PartialFun ⥤ Pointed := by
  classical
  exact
    { obj := fun X => ⟨Option X, none⟩
      map := fun f => ⟨Option.elim' none fun a => (f a).toOption, rfl⟩
      map_id := fun X => Pointed.Hom.ext _ _ <| funext fun o => Option.recOn o rfl fun a => (by
        dsimp [CategoryStruct.id]
        convert Part.some_toOption a)
      map_comp := fun f g => Pointed.Hom.ext _ _ <| funext fun o => Option.recOn o rfl fun a => by
        dsimp [CategoryStruct.comp]
        rw [Part.bind_toOption g (f a), Option.elim'_eq_elim] }
#align PartialFun_to_Pointed partialFunToPointed

/-- The equivalence induced by `PartialFunToPointed` and `PointedToPartialFun`.
`part.equiv_option` made functorial. -/
@[simps]
noncomputable def partialFunEquivPointed : PartialFun.{u} ≌ Pointed := by
  classical exact
    equivalence.mk partialFunToPointed pointedToPartialFun
      (nat_iso.of_components
        (fun X =>
          PartialFun.Iso.mk
            { toFun := fun a => ⟨some a, some_ne_none a⟩
              invFun := fun a => get <| ne_none_iff_is_some.1 a.2
              left_inv := fun a => get_some _ _
              right_inv := fun a => by simp only [Subtype.val_eq_coe, some_get, Subtype.coe_eta] })
        fun X Y f =>
        PFun.ext fun a b => by
          unfold_projs
          dsimp
          rw [Part.bind_some]
          refine' (part.mem_bind_iff.trans _).trans pfun.mem_to_subtype_iff.symm
          obtain ⟨b | b, hb⟩ := b
          · exact (hb rfl).elim
          dsimp
          simp_rw [Part.mem_some_iff, Subtype.mk_eq_mk, exists_prop, some_inj, exists_eq_right']
          refine' part.mem_to_option.symm.trans _
          exact eq_comm)
      (nat_iso.of_components
        (fun X =>
          Pointed.Iso.mk
            { toFun := Option.elim' X.point Subtype.val
              invFun := fun a => if h : a = X.point then none else some ⟨_, h⟩
              left_inv := fun a =>
                Option.recOn a (dif_pos rfl) fun a =>
                  (dif_neg a.2).trans <| by
                    simp only [Option.elim', Subtype.val_eq_coe, Subtype.coe_eta]
              right_inv := fun a => by
                change Option.elim' _ _ (dite _ _ _) = _
                split_ifs
                · rw [h]; rfl
                · rfl }
            rfl)
        fun X Y f =>
        Pointed.Hom.ext _ _ <|
          funext fun a =>
            Option.recOn a f.map_point.symm fun a => by
              unfold_projs
              dsimp
              change Option.elim' _ _ _ = _
              rw [Part.elim_toOption]
              split_ifs
              · rfl
              · exact Eq.symm (of_not_not h))
#align PartialFun_equiv_Pointed partialFunEquivPointed

/-- Forgetting that maps are total and making them total again by adding a point is the same as just
adding a point. -/
@[simps]
noncomputable def typeToPartialFunIsoPartialFunToPointed :
    typeToPartialFun ⋙ partialFunToPointed ≅ typeToPointed :=
  NatIso.ofComponents
    (fun X =>
      { Hom := ⟨id, rfl⟩
        inv := ⟨id, rfl⟩
        hom_inv_id' := rfl
        inv_hom_id' := rfl })
    fun X Y f =>
    Pointed.Hom.ext _ _ <|
      funext fun a => Option.recOn a rfl fun a => by convert Part.some_toOption _
#align Type_to_PartialFun_iso_PartialFun_to_Pointed typeToPartialFunIsoPartialFunToPointed
