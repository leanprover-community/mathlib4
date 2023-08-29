/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Control.EquivFunctor
import Mathlib.Data.Option.Basic
import Mathlib.Data.Subtype
import Mathlib.Logic.Equiv.Defs

#align_import logic.equiv.option from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
# Equivalences for `Option α`


We define
* `Equiv.optionCongr`: the `Option α ≃ Option β` constructed from `e : α ≃ β` by sending `none` to
  `none`, and applying `e` elsewhere.
* `Equiv.removeNone`: the `α ≃ β` constructed from `Option α ≃ Option β` by removing `none` from
  both sides.
-/


namespace Equiv

open Option

variable {α β γ : Type*}

section OptionCongr

/-- A universe-polymorphic version of `EquivFunctor.mapEquiv Option e`. -/
@[simps apply]
def optionCongr (e : α ≃ β) : Option α ≃ Option β where
  toFun := Option.map e
  invFun := Option.map e.symm
  left_inv x := (Option.map_map _ _ _).trans <| e.symm_comp_self.symm ▸ congr_fun Option.map_id x
  right_inv x := (Option.map_map _ _ _).trans <| e.self_comp_symm.symm ▸ congr_fun Option.map_id x
#align equiv.option_congr Equiv.optionCongr
#align equiv.option_congr_apply Equiv.optionCongr_apply

@[simp]
theorem optionCongr_refl : optionCongr (Equiv.refl α) = Equiv.refl _ :=
  ext <| congr_fun Option.map_id
#align equiv.option_congr_refl Equiv.optionCongr_refl

@[simp]
theorem optionCongr_symm (e : α ≃ β) : (optionCongr e).symm = optionCongr e.symm :=
  rfl
#align equiv.option_congr_symm Equiv.optionCongr_symm

@[simp]
theorem optionCongr_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
    (optionCongr e₁).trans (optionCongr e₂) = optionCongr (e₁.trans e₂) :=
  ext <| Option.map_map _ _
#align equiv.option_congr_trans Equiv.optionCongr_trans

/-- When `α` and `β` are in the same universe, this is the same as the result of
`EquivFunctor.mapEquiv`. -/
theorem optionCongr_eq_equivFunctor_mapEquiv {α β : Type _} (e : α ≃ β) :
    optionCongr e = EquivFunctor.mapEquiv Option e :=
  rfl
#align equiv.option_congr_eq_equiv_function_map_equiv Equiv.optionCongr_eq_equivFunctor_mapEquiv

end OptionCongr

section RemoveNone

variable (e : Option α ≃ Option β)

/-- If we have a value on one side of an `Equiv` of `Option`
    we also have a value on the other side of the equivalence
-/
def removeNone_aux (x : α) : β :=
  if h : (e (some x)).isSome then Option.get _ h
  else
    Option.get _ <|
      show (e none).isSome by
        rw [← Option.ne_none_iff_isSome]
        -- ⊢ ↑e none ≠ none
        intro hn
        -- ⊢ False
        rw [Option.not_isSome_iff_eq_none, ← hn] at h
        -- ⊢ False
        exact Option.some_ne_none _ (e.injective h)
        -- 🎉 no goals
-- Porting note: private
-- #align equiv.remove_none_aux Equiv.removeNone_aux

theorem removeNone_aux_some {x : α} (h : ∃ x', e (some x) = some x') :
    some (removeNone_aux e x) = e (some x) :=
  by simp [removeNone_aux, Option.isSome_iff_exists.mpr h]
     -- 🎉 no goals
-- Porting note: private
-- #align equiv.remove_none_aux_some Equiv.removeNone_aux_some

theorem removeNone_aux_none {x : α} (h : e (some x) = none) :
    some (removeNone_aux e x) = e none := by
  simp [removeNone_aux, Option.not_isSome_iff_eq_none.mpr h]
  -- 🎉 no goals
-- Porting note: private
-- #align equiv.remove_none_aux_none Equiv.removeNone_aux_none

theorem removeNone_aux_inv (x : α) : removeNone_aux e.symm (removeNone_aux e x) = x :=
  Option.some_injective _
    (by
      cases h1 : e.symm (some (removeNone_aux e x)) <;> cases h2 : e (some x)
      -- ⊢ some (removeNone_aux e.symm (removeNone_aux e x)) = some x
                                                        -- ⊢ some (removeNone_aux e.symm (removeNone_aux e x)) = some x
                                                        -- ⊢ some (removeNone_aux e.symm (removeNone_aux e x)) = some x
      · rw [removeNone_aux_none _ h1]
        -- ⊢ ↑e.symm none = some x
        exact (e.eq_symm_apply.mpr h2).symm
        -- 🎉 no goals

      · rw [removeNone_aux_some _ ⟨_, h2⟩] at h1
        -- ⊢ some (removeNone_aux e.symm (removeNone_aux e x)) = some x
        simp at h1
        -- 🎉 no goals

      · rw [removeNone_aux_none _ h2] at h1
        -- ⊢ some (removeNone_aux e.symm (removeNone_aux e x)) = some x
        simp at h1
        -- 🎉 no goals

      · rw [removeNone_aux_some _ ⟨_, h1⟩]
        -- ⊢ ↑e.symm (some (removeNone_aux e x)) = some x
        rw [removeNone_aux_some _ ⟨_, h2⟩]
        -- ⊢ ↑e.symm (↑e (some x)) = some x
        simp
        -- 🎉 no goals
        )
-- Porting note: private
-- #align equiv.remove_none_aux_inv Equiv.removeNone_aux_inv

/-- Given an equivalence between two `Option` types, eliminate `none` from that equivalence by
mapping `e.symm none` to `e none`. -/
def removeNone : α ≃ β where
  toFun := removeNone_aux e
  invFun := removeNone_aux e.symm
  left_inv := removeNone_aux_inv e
  right_inv := removeNone_aux_inv e.symm
#align equiv.remove_none Equiv.removeNone

@[simp]
theorem removeNone_symm : (removeNone e).symm = removeNone e.symm :=
  rfl
#align equiv.remove_none_symm Equiv.removeNone_symm

theorem removeNone_some {x : α} (h : ∃ x', e (some x) = some x') :
    some (removeNone e x) = e (some x) :=
  removeNone_aux_some e h
#align equiv.remove_none_some Equiv.removeNone_some

theorem removeNone_none {x : α} (h : e (some x) = none) : some (removeNone e x) = e none :=
  removeNone_aux_none e h
#align equiv.remove_none_none Equiv.removeNone_none

@[simp]
theorem option_symm_apply_none_iff : e.symm none = none ↔ e none = none :=
  ⟨fun h => by simpa using (congr_arg e h).symm, fun h => by simpa using (congr_arg e.symm h).symm⟩
               -- 🎉 no goals
                                                             -- 🎉 no goals
#align equiv.option_symm_apply_none_iff Equiv.option_symm_apply_none_iff

theorem some_removeNone_iff {x : α} : some (removeNone e x) = e none ↔ e.symm none = some x := by
  cases' h : e (some x) with a
  -- ⊢ some (↑(removeNone e) x) = ↑e none ↔ ↑e.symm none = some x
  · rw [removeNone_none _ h]
    -- ⊢ ↑e none = ↑e none ↔ ↑e.symm none = some x
    simpa using (congr_arg e.symm h).symm
    -- 🎉 no goals
  · rw [removeNone_some _ ⟨a, h⟩]
    -- ⊢ ↑e (some x) = ↑e none ↔ ↑e.symm none = some x
    have h1 := congr_arg e.symm h
    -- ⊢ ↑e (some x) = ↑e none ↔ ↑e.symm none = some x
    rw [symm_apply_apply] at h1
    -- ⊢ ↑e (some x) = ↑e none ↔ ↑e.symm none = some x
    simp only [false_iff_iff, apply_eq_iff_eq]
    -- ⊢ ¬↑e.symm none = some x
    simp [h1, apply_eq_iff_eq]
    -- 🎉 no goals
#align equiv.some_remove_none_iff Equiv.some_removeNone_iff

@[simp]
theorem removeNone_optionCongr (e : α ≃ β) : removeNone e.optionCongr = e :=
  Equiv.ext fun x => Option.some_injective _ <| removeNone_some _ ⟨e x, by simp [EquivFunctor.map]⟩
                                                                           -- 🎉 no goals
#align equiv.remove_none_option_congr Equiv.removeNone_optionCongr

end RemoveNone

theorem optionCongr_injective : Function.Injective (optionCongr : α ≃ β → Option α ≃ Option β) :=
  Function.LeftInverse.injective removeNone_optionCongr
#align equiv.option_congr_injective Equiv.optionCongr_injective

/-- Equivalences between `Option α` and `β` that send `none` to `x` are equivalent to
equivalences between `α` and `{y : β // y ≠ x}`. -/
def optionSubtype [DecidableEq β] (x : β) :
    { e : Option α ≃ β // e none = x } ≃ (α ≃ { y : β // y ≠ x }) where
  toFun e :=
    { toFun := fun a =>
        ⟨(e : Option α ≃ β) a, ((EquivLike.injective _).ne_iff' e.property).2 (some_ne_none _)⟩,
      invFun := fun b =>
        get _
          (ne_none_iff_isSome.1
            (((EquivLike.injective _).ne_iff'
              ((apply_eq_iff_eq_symm_apply _).1 e.property).symm).2 b.property)),
      left_inv := fun a => by
        rw [← some_inj, some_get]
        -- ⊢ ↑(↑e).symm ↑((fun a => { val := ↑↑e (some a), property := (_ : ↑↑e (some a)  …
        exact symm_apply_apply (e : Option α ≃ β) a,
        -- 🎉 no goals
      right_inv := fun b => by
        ext
        -- ⊢ ↑((fun a => { val := ↑↑e (some a), property := (_ : ↑↑e (some a) ≠ x) }) ((f …
        simp }
        -- 🎉 no goals
  invFun e :=
    ⟨{  toFun := fun a => casesOn' a x (Subtype.val ∘ e),
        invFun := fun b => if h : b = x then none else e.symm ⟨b, h⟩,
        left_inv := fun a => by
          cases a with
          | none => simp
          | some a =>
            simp only [casesOn'_some, Function.comp_apply, Subtype.coe_eta,
              symm_apply_apply, dite_eq_ite]
            exact if_neg (e a).property,
        right_inv := fun b => by
          by_cases h : b = x <;> simp [h] },
          -- ⊢ (fun a => casesOn' a x (Subtype.val ∘ ↑e)) ((fun b => if h : b = x then none …
                                 -- 🎉 no goals
                                 -- 🎉 no goals
      rfl⟩
  left_inv e := by
    ext a
    -- ⊢ ↑↑((fun e => { val := { toFun := fun a => casesOn' a x (Subtype.val ∘ ↑e), i …
    cases a
    -- ⊢ ↑↑((fun e => { val := { toFun := fun a => casesOn' a x (Subtype.val ∘ ↑e), i …
    · simpa using e.property.symm
      -- 🎉 no goals
    -- Porting note: this cases had been by `simpa`,
    -- but `simp` here is mysteriously slow, even after squeezing.
    -- `rfl` closes the goal quickly, so we use that.
    · rfl
      -- 🎉 no goals
  right_inv e := by
    ext a
    -- ⊢ ↑(↑((fun e => { toFun := fun a => { val := ↑↑e (some a), property := (_ : ↑↑ …
    rfl
    -- 🎉 no goals
#align equiv.option_subtype Equiv.optionSubtype

@[simp]
theorem optionSubtype_apply_apply
    [DecidableEq β] (x : β)
    (e : { e : Option α ≃ β // e none = x })
    (a : α)
    (h) : optionSubtype x e a = ⟨(e : Option α ≃ β) a, h⟩ := rfl
#align equiv.option_subtype_apply_apply Equiv.optionSubtype_apply_apply

@[simp]
theorem coe_optionSubtype_apply_apply
    [DecidableEq β] (x : β)
    (e : { e : Option α ≃ β // e none = x })
    (a : α) : ↑(optionSubtype x e a) = (e : Option α ≃ β) a := rfl
#align equiv.coe_option_subtype_apply_apply Equiv.coe_optionSubtype_apply_apply

@[simp]
theorem optionSubtype_apply_symm_apply
    [DecidableEq β] (x : β)
    (e : { e : Option α ≃ β // e none = x })
    (b : { y : β // y ≠ x }) : ↑((optionSubtype x e).symm b) = (e : Option α ≃ β).symm b := by
  dsimp only [optionSubtype]
  -- ⊢ some (↑(↑{ toFun := fun e => { toFun := fun a => { val := ↑↑e (some a), prop …
  simp
  -- 🎉 no goals
#align equiv.option_subtype_apply_symm_apply Equiv.optionSubtype_apply_symm_apply

@[simp]
theorem optionSubtype_symm_apply_apply_coe [DecidableEq β] (x : β) (e : α ≃ { y : β // y ≠ x })
    (a : α) : ((optionSubtype x).symm e : Option α ≃ β) a = e a :=
  rfl
#align equiv.option_subtype_symm_apply_apply_coe Equiv.optionSubtype_symm_apply_apply_coe

@[simp]
theorem optionSubtype_symm_apply_apply_some
    [DecidableEq β]
    (x : β)
    (e : α ≃ { y : β // y ≠ x })
    (a : α) : ((optionSubtype x).symm e : Option α ≃ β) (some a) = e a :=
  rfl
#align equiv.option_subtype_symm_apply_apply_some Equiv.optionSubtype_symm_apply_apply_some

@[simp]
theorem optionSubtype_symm_apply_apply_none
    [DecidableEq β]
    (x : β)
    (e : α ≃ { y : β // y ≠ x }) : ((optionSubtype x).symm e : Option α ≃ β) none = x :=
  rfl
#align equiv.option_subtype_symm_apply_apply_none Equiv.optionSubtype_symm_apply_apply_none

@[simp]
theorem optionSubtype_symm_apply_symm_apply [DecidableEq β] (x : β) (e : α ≃ { y : β // y ≠ x })
    (b : { y : β // y ≠ x }) : ((optionSubtype x).symm e : Option α ≃ β).symm b = e.symm b := by
  simp only [optionSubtype, coe_fn_symm_mk, Subtype.coe_mk,
             Subtype.coe_eta, dite_eq_ite, ite_eq_right_iff]
  exact fun h => False.elim (b.property h)
  -- 🎉 no goals
#align equiv.option_subtype_symm_apply_symm_apply Equiv.optionSubtype_symm_apply_symm_apply

end Equiv
