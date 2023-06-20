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
constructively stems from the difference between `part` and `option`. Both can model partial
functions, but the latter forces a decidable domain.

Precisely, `PartialFun_to_Pointed` turns a partial function `α →. β` into a function
`option α → option β` by sending to `none` the undefined values (and `none` to `none`). But being
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
#align PartialFun PartialFun

namespace PartialFun

instance : CoeSort PartialFun (Type _) :=
  ⟨id⟩

/-- Turns a type into a `PartialFun`. -/
@[nolint has_nonempty_instance]
def of : Type _ → PartialFun :=
  id
#align PartialFun.of PartialFun.of

@[simp]
theorem coe_of (X : Type _) : ↥(of X) = X :=
  rfl
#align PartialFun.coe_of PartialFun.coe_of

instance : Inhabited PartialFun :=
  ⟨Type _⟩

instance largeCategory : LargeCategory.{u} PartialFun where
  Hom := PFun
  id := PFun.id
  comp X Y Z f g := g.comp f
  id_comp' := @PFun.comp_id
  comp_id' := @PFun.id_comp
  assoc' W X Y Z _ _ _ := (PFun.comp_assoc _ _ _).symm
#align PartialFun.large_category PartialFun.largeCategory

/-- Constructs a partial function isomorphism between types from an equivalence between them. -/
@[simps]
def Iso.mk {α β : PartialFun.{u}} (e : α ≃ β) : α ≅ β where
  Hom := e
  inv := e.symm
  hom_inv_id' := (PFun.coe_comp _ _).symm.trans <| congr_arg coe e.symm_comp_self
  inv_hom_id' := (PFun.coe_comp _ _).symm.trans <| congr_arg coe e.self_comp_symm
#align PartialFun.iso.mk PartialFun.Iso.mk

end PartialFun

/-- The forgetful functor from `Type` to `PartialFun` which forgets that the maps are total. -/
def typeToPartialFun : Type u ⥤ PartialFun where
  obj := id
  map := @PFun.lift
  map_comp' _ _ _ _ _ := PFun.coe_comp _ _
#align Type_to_PartialFun typeToPartialFun

instance : Faithful typeToPartialFun :=
  ⟨fun X Y => PFun.lift_injective⟩

/-- The functor which deletes the point of a pointed type. In return, this makes the maps partial.
This the computable part of the equivalence `PartialFun_equiv_Pointed`. -/
@[simps map]
def pointedToPartialFun : Pointed.{u} ⥤ PartialFun where
  obj X := { x : X // x ≠ X.point }
  map X Y f := PFun.toSubtype _ f.toFun ∘ Subtype.val
  map_id' X :=
    PFun.ext fun a b => PFun.mem_toSubtype_iff.trans (Subtype.coe_inj.trans Part.mem_some_iff.symm)
  map_comp' X Y Z f g :=
    PFun.ext fun a c => by
      refine' (pfun.mem_to_subtype_iff.trans _).trans part.mem_bind_iff.symm
      simp_rw [PFun.mem_toSubtype_iff, Subtype.exists]
      refine'
        ⟨fun h =>
          ⟨f.to_fun a, fun ha =>
            c.2 <| h.trans ((congr_arg g.to_fun ha : g.to_fun _ = _).trans g.map_point), rfl, h⟩,
          _⟩
      rintro ⟨b, _, rfl : b = _, h⟩
      exact h
#align Pointed_to_PartialFun pointedToPartialFun

/-- The functor which maps undefined values to a new point. This makes the maps total and creates
pointed types. This the noncomputable part of the equivalence `PartialFun_equiv_Pointed`. It can't
be computable because `= option.none` is decidable while the domain of a general `part` isn't. -/
@[simps map]
noncomputable def partialFunToPointed : PartialFun ⥤ Pointed := by
  classical exact
    { obj := fun X => ⟨Option X, none⟩
      map := fun X Y f => ⟨Option.elim' none fun a => (f a).toOption, rfl⟩
      map_id' := fun X =>
        Pointed.Hom.ext _ _ <| funext fun o => Option.recOn o rfl fun a => Part.some_toOption _
      map_comp' := fun X Y Z f g =>
        Pointed.Hom.ext _ _ <| funext fun o => Option.recOn o rfl fun a => Part.bind_toOption _ _ }
#align PartialFun_to_Pointed partialFunToPointed

/-- The equivalence induced by `PartialFun_to_Pointed` and `Pointed_to_PartialFun`.
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

