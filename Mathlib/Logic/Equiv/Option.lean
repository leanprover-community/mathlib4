/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Control.EquivFunctor
import Mathlib.Data.Option.Basic
import Mathlib.Data.Subtype
import Mathlib.Logic.Equiv.Defs

/-!
# Equivalences for `option α`


We define
* `equiv.option_congr`: the `option α ≃ option β` constructed from `e : α ≃ β` by sending `none` to
  `none`, and applying a `e` elsewhere.
* `equiv.remove_none`: the `α ≃ β` constructed from `option α ≃ option β` by removing `none` from
  both sides.
-/


namespace Equiv

open Option

variable {α β γ : Type _}

section OptionCongr

/-- A universe-polymorphic version of `equiv_functor.map_equiv option e`. -/
@[simps apply]
def optionCongr (e : α ≃ β) : Option α ≃ Option β where
  toFun := Option.map e
  invFun := Option.map e.symm
  left_inv x := (Option.map_map _ _ _).trans <| e.symm_comp_self.symm ▸ congr_fun Option.map_id x
  right_inv x := (Option.map_map _ _ _).trans <| e.self_comp_symm.symm ▸ congr_fun Option.map_id x
#align equiv.option_congr Equiv.optionCongr

@[simp]
theorem option_congr_refl : optionCongr (Equiv.refl α) = Equiv.refl _ :=
  ext <| congr_fun Option.map_id
#align equiv.option_congr_refl Equiv.option_congr_refl

@[simp]
theorem option_congr_symm (e : α ≃ β) : (optionCongr e).symm = optionCongr e.symm :=
  rfl
#align equiv.option_congr_symm Equiv.option_congr_symm

@[simp]
theorem option_congr_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
    (optionCongr e₁).trans (optionCongr e₂) = optionCongr (e₁.trans e₂) :=
  ext <| Option.map_map _ _
#align equiv.option_congr_trans Equiv.option_congr_trans

/-- When `α` and `β` are in the same universe, this is the same as the result of
`equiv_functor.map_equiv`. -/
theorem option_congr_eq_equiv_function_map_equiv {α β : Type _} (e : α ≃ β) :
    optionCongr e = EquivFunctor.mapEquiv Option e :=
  rfl
#align equiv.option_congr_eq_equiv_function_map_equiv Equiv.option_congr_eq_equiv_function_map_equiv

end OptionCongr

section RemoveNone

variable (e : Option α ≃ Option β)

private def remove_none_aux (x : α) : β :=
  if h : (e (some x)).isSome then Option.get _ h
  else
    Option.get _ <|
      show (e none).isSome by
        rw [← Option.ne_none_iff_isSome]
        intro hn
        rw [Option.not_isSome_iff_eq_none, ← hn] at h
        injection e.injective h

private theorem remove_none_aux_some {x : α} (h : ∃ x', e (some x) = some x') :
    some (remove_none_aux e x) = e (some x) :=
  by simp [remove_none_aux, Option.isSome_iff_exists.mpr h]

private theorem remove_none_aux_none {x : α} (h : e (some x) = none) :
    some (remove_none_aux e x) = e none := by
  simp [remove_none_aux, Option.not_isSome_iff_eq_none.mpr h]

private theorem remove_none_aux_inv (x : α) :
    remove_none_aux e.symm (remove_none_aux e x) = x :=
  Option.some_injective _
    (by
      cases h1 : e.symm (some (remove_none_aux e x)) <;> cases h2 : e (some x)
      · rw [remove_none_aux_none _ h1]
        exact (e.eq_symm_apply.mpr h2).symm

      · rw [remove_none_aux_some _ ⟨_, h2⟩] at h1
        simp at h1

      · rw [remove_none_aux_none _ h2] at h1
        simp at h1

      · rw [remove_none_aux_some _ ⟨_, h1⟩]
        rw [remove_none_aux_some _ ⟨_, h2⟩]
        simp
        )

/-- Given an equivalence between two `option` types, eliminate `none` from that equivalence by
mapping `e.symm none` to `e none`. -/
def removeNone : α ≃ β where
  toFun := remove_none_aux e
  invFun := remove_none_aux e.symm
  left_inv := remove_none_aux_inv e
  right_inv := remove_none_aux_inv e.symm
#align equiv.remove_none Equiv.removeNone

@[simp]
theorem remove_none_symm : (removeNone e).symm = removeNone e.symm :=
  rfl
#align equiv.remove_none_symm Equiv.remove_none_symm

theorem remove_none_some {x : α} (h : ∃ x', e (some x) = some x') :
    some (removeNone e x) = e (some x) :=
  remove_none_aux_some e h
#align equiv.remove_none_some Equiv.remove_none_some

theorem remove_none_none {x : α} (h : e (some x) = none) : some (removeNone e x) = e none :=
  remove_none_aux_none e h
#align equiv.remove_none_none Equiv.remove_none_none

@[simp]
theorem option_symm_apply_none_iff : e.symm none = none ↔ e none = none :=
  ⟨fun h => by simpa using (congr_arg e h).symm, fun h => by simpa using (congr_arg e.symm h).symm⟩
#align equiv.option_symm_apply_none_iff Equiv.option_symm_apply_none_iff

theorem some_remove_none_iff {x : α} : some (removeNone e x) = e none ↔ e.symm none = some x := by
  cases' h : e (some x) with a
  · rw [remove_none_none _ h]
    simpa using (congr_arg e.symm h).symm

  · rw [remove_none_some _ ⟨a, h⟩]
    have := congr_arg e.symm h
    rw [symm_apply_apply] at this
    simp only [false_iff_iff, apply_eq_iff_eq]
    simp [this]

#align equiv.some_remove_none_iff Equiv.some_remove_none_iff

@[simp]
theorem remove_none_option_congr (e : α ≃ β) : removeNone e.optionCongr = e :=
  Equiv.ext fun x => Option.some_injective _ <| remove_none_some _ ⟨e x, by simp [EquivFunctor.map]⟩
#align equiv.remove_none_option_congr Equiv.remove_none_option_congr

end RemoveNone

theorem option_congr_injective : Function.Injective (optionCongr : α ≃ β → Option α ≃ Option β) :=
  Function.LeftInverse.injective remove_none_option_congr
#align equiv.option_congr_injective Equiv.option_congr_injective

set_option maxHeartbeats 1000000

/-- Equivalences between `option α` and `β` that send `none` to `x` are equivalent to
equivalences between `α` and `{y : β // y ≠ x}`. -/
def optionSubtype [DecidableEq β] (x : β) :
    { e : Option α ≃ β // e none = x } ≃ (α ≃ { y : β // y ≠ x }) where
  toFun e :=
    { toFun := fun a => ⟨e.1 a, ((EquivLike.injective _).ne_iff' e.property).2 (some_ne_none _)⟩,
      invFun := fun b =>
        get _
          (ne_none_iff_isSome.1
            (((EquivLike.injective _).ne_iff'
              ((apply_eq_iff_eq_symm_apply _).1 e.property).symm).2 b.property)),
      left_inv := fun a => by
        rw [← some_inj, some_get]
        exact symm_apply_apply (e : Option α ≃ β) a,
      right_inv := fun b => by
        ext
        simp }
  invFun e :=
    ⟨{ toFun := fun a => casesOn' a x (Subtype.val ∘ e),
       invFun := fun b => if h : b = x then none else e.symm ⟨b, h⟩,
       left_inv := fun a => by
          cases a
          · simp

          simp [Function.comp_apply, Subtype.coe_eta, symm_apply_apply, dite_eq_ite]
          exact (e.1 _).property,
       right_inv := fun b => by by_cases h : b = x <;> simp [h] },
      rfl⟩
  left_inv e := by
    ext a
    cases a
    · simpa using e.property.symm

    · simp

  right_inv e := Equiv.ext (fun _ => rfl)

#align equiv.option_subtype Equiv.optionSubtype

@[simp]
theorem option_subtype_apply_apply [DecidableEq β] (x : β) (e : { e : Option α ≃ β // e none = x })
    (a : α) (h) : optionSubtype x e a = ⟨(e : Option α ≃ β) a, h⟩ :=
  rfl
#align equiv.option_subtype_apply_apply Equiv.option_subtype_apply_apply

@[simp]
theorem coe_option_subtype_apply_apply [DecidableEq β] (x : β)
    (e : { e : Option α ≃ β // e none = x }) (a : α) :
    ↑(optionSubtype x e a) = (e : Option α ≃ β) a :=
  rfl
#align equiv.coe_option_subtype_apply_apply Equiv.coe_option_subtype_apply_apply

@[simp]
theorem option_subtype_apply_symm_apply [DecidableEq β] (x : β)
    (e : { e : Option α ≃ β // e none = x })
    (b : { y : β // y ≠ x }) : ↑((optionSubtype x e).symm b) = (e : Option α ≃ β).symm b := by
  dsimp only [optionSubtype]
  simp
#align equiv.option_subtype_apply_symm_apply Equiv.option_subtype_apply_symm_apply

@[simp]
theorem option_subtype_symm_apply_apply_coe [DecidableEq β] (x : β)
    (e : α ≃ { y : β // y ≠ x }) (a : α) :
    ((optionSubtype x).symm e).1 a = e a :=
  rfl
#align equiv.option_subtype_symm_apply_apply_coe Equiv.option_subtype_symm_apply_apply_coe

@[simp]
theorem option_subtype_symm_apply_apply_some [DecidableEq β] (x : β)
    (e : α ≃ { y : β // y ≠ x }) (a : α) :
    ((optionSubtype x).symm e).1 (some a) = e a :=
  rfl
#align equiv.option_subtype_symm_apply_apply_some Equiv.option_subtype_symm_apply_apply_some

@[simp]
theorem option_subtype_symm_apply_apply_none [DecidableEq β] (x : β) (e : α ≃ { y : β // y ≠ x }) :
    ((optionSubtype x).symm e).1 none = x :=
  rfl
#align equiv.option_subtype_symm_apply_apply_none Equiv.option_subtype_symm_apply_apply_none

@[simp]
theorem option_subtype_symm_apply_symm_apply [DecidableEq β] (x : β) (e : α ≃ { y : β // y ≠ x })
    (b : { y : β // y ≠ x }) : ((optionSubtype x).symm e : Option α ≃ β).symm b = e.symm b := by
  simp only [optionSubtype, coe_fn_symm_mk, Subtype.coe_mk, Subtype.coe_eta,
    dite_eq_ite, ite_eq_right_iff]
  exact fun h => False.elim (b.property h)
#align equiv.option_subtype_symm_apply_symm_apply Equiv.option_subtype_symm_apply_symm_apply

end Equiv
