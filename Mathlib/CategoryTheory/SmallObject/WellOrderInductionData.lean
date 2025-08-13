/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Types
import Mathlib.Order.SuccPred.Limit

/-!
# Limits of inverse systems indexed by well-ordered types

Given a functor `F : Jᵒᵖ ⥤ Type v` where `J` is a well-ordered type,
we introduce a structure `F.WellOrderInductionData` which allows
to show that the map `F.sections → F.obj (op ⊥)` is surjective.

The data and properties in `F.WellOrderInductionData` consist of a
section to the maps `F.obj (op (Order.succ j)) → F.obj (op j)` when `j` is not maximal,
and, when `j` is limit, a section to the canonical map from `F.obj (op j)`
to the type of compatible families of elements in `F.obj (op i)` for `i < j`.

In other words, from `val₀ : F.obj (op ⊥)`, a term `d : F.WellOrderInductionData`
allows the construction, by transfinite induction, of a section of `F`
which restricts to `val₀`.

-/

universe v u

namespace CategoryTheory

open Opposite

namespace Functor

variable {J : Type u} [LinearOrder J] [SuccOrder J] (F : Jᵒᵖ ⥤ Type v)

/-- Given a functor `F : Jᵒᵖ ⥤ Type v` where `J` is a well-ordered type, this data
allows to construct a section of `F` from an element in `F.obj (op ⊥)`,
see `WellOrderInductionData.sectionsMk`. -/
structure WellOrderInductionData where
  /-- A section `F.obj (op j) → F.obj (op (Order.succ j))` to the restriction
  `F.obj (op (Order.succ j)) → F.obj (op j)` when `j` is not maximal. -/
  succ (j : J) (hj : ¬IsMax j) (x : F.obj (op j)) : F.obj (op (Order.succ j))
  map_succ (j : J) (hj : ¬IsMax j) (x : F.obj (op j)) :
      F.map (homOfLE (Order.le_succ j)).op (succ j hj x) = x
  /-- When `j` is a limit element, and `x` is a compatible family of elements
  in `F.obj (op i)` for all `i < j`, this is a lifting to `F.obj (op j)`. -/
  lift (j : J) (hj : Order.IsSuccLimit j)
    (x : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙ F).sections) :
      F.obj (op j)
  map_lift (j : J) (hj : Order.IsSuccLimit j)
    (x : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙ F).sections)
    (i : J) (hi : i < j) :
        F.map (homOfLE hi.le).op (lift j hj x) = x.val (op ⟨i, hi⟩)

namespace WellOrderInductionData

variable {F} (d : F.WellOrderInductionData) [OrderBot J]

/-- Given `d : F.WellOrderInductionData`, `val₀ : F.obj (op ⊥)` and `j : J`,
this is the data of an element `val : F.obj (op j)` such that the induced
compatible family of elements in all `F.obj (op i)` for `i ≤ j`
is determined by `val₀` and the choice of "liftings" given by `d`. -/
structure Extension (val₀ : F.obj (op ⊥)) (j : J) where
  /-- An element in `F.obj (op j)`, which, by restriction, induces elements
  in `F.obj (op i)` for all `i ≤ j`. -/
  val : F.obj (op j)
  map_zero : F.map (homOfLE bot_le).op val = val₀
  map_succ (i : J) (hi : i < j) :
    F.map (homOfLE (Order.succ_le_of_lt hi)).op val =
      d.succ i (not_isMax_iff.2 ⟨_, hi⟩) (F.map (homOfLE hi.le).op val)
  map_limit (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j) :
    F.map (homOfLE hij).op val = d.lift i hi
      { val := fun ⟨⟨k, hk⟩⟩ ↦ F.map (homOfLE (hk.le.trans hij)).op val
        property := fun f ↦ by
          dsimp
          rw [← FunctorToTypes.map_comp_apply]
          rfl }

namespace Extension

variable {d} {val₀ : F.obj (op ⊥)}

/-- An element in `d.Extension val₀ j` induces an element in `d.Extension val₀ i` when `i ≤ j`. -/
@[simps]
def ofLE {j : J} (e : d.Extension val₀ j) {i : J} (hij : i ≤ j) : d.Extension val₀ i where
  val := F.map (homOfLE hij).op e.val
  map_zero := by
    rw [← FunctorToTypes.map_comp_apply]
    exact e.map_zero
  map_succ k hk := by
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp,
      homOfLE_comp, homOfLE_comp, e.map_succ k (lt_of_lt_of_le hk hij)]
  map_limit k hk hki := by
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, homOfLE_comp,
      e.map_limit k hk (hki.trans hij)]
    congr
    ext ⟨l, hl⟩
    dsimp
    rw [← FunctorToTypes.map_comp_apply]
    rfl

lemma val_injective {j : J} {e e' : d.Extension val₀ j} (h : e.val = e'.val) : e = e' := by
  cases e
  cases e'
  subst h
  rfl

instance [WellFoundedLT J] (j : J) : Subsingleton (d.Extension val₀ j) := by
  induction j using SuccOrder.limitRecOn with
  | isMin i hi =>
    obtain rfl : i = ⊥ := by simpa using hi
    refine Subsingleton.intro (fun e₁ e₂ ↦ val_injective ?_)
    have h₁ := e₁.map_zero
    have h₂ := e₂.map_zero
    simp only [homOfLE_refl, op_id, FunctorToTypes.map_id_apply] at h₁ h₂
    rw [h₁, h₂]
  | succ i hi hi' =>
    refine Subsingleton.intro (fun e₁ e₂ ↦ val_injective ?_)
    have h₁ := e₁.map_succ i (Order.lt_succ_of_not_isMax hi)
    have h₂ := e₂.map_succ i (Order.lt_succ_of_not_isMax hi)
    simp only [homOfLE_refl, op_id, FunctorToTypes.map_id_apply, homOfLE_leOfHom] at h₁ h₂
    rw [h₁, h₂]
    congr
    exact congr_arg val (Subsingleton.elim (e₁.ofLE (Order.le_succ i)) (e₂.ofLE (Order.le_succ i)))
  | isSuccLimit i hi hi' =>
    refine Subsingleton.intro (fun e₁ e₂ ↦ val_injective ?_)
    have h₁ := e₁.map_limit i hi (by rfl)
    have h₂ := e₂.map_limit i hi (by rfl)
    simp only [homOfLE_refl, op_id, FunctorToTypes.map_id_apply, OrderHom.Subtype.val_coe,
      comp_obj, op_obj, Monotone.functor_obj, homOfLE_leOfHom] at h₁ h₂
    rw [h₁, h₂]
    congr
    ext ⟨⟨l, hl⟩⟩
    have := hi' l hl
    exact congr_arg val (Subsingleton.elim (e₁.ofLE hl.le) (e₂.ofLE hl.le))

lemma compatibility [WellFoundedLT J]
    {j : J} (e : d.Extension val₀ j) {i : J} (e' : d.Extension val₀ i) (h : i ≤ j) :
    F.map (homOfLE h).op e.val = e'.val := by
  obtain rfl : e' = e.ofLE h := Subsingleton.elim _ _
  rfl

variable (d val₀) in
/-- The obvious element in `d.Extension val₀ ⊥`. -/
@[simps]
def zero : d.Extension val₀ ⊥ where
  val := val₀
  map_zero := by simp
  map_succ i hi := by simp at hi
  map_limit i hi hij := by
    obtain rfl : i = ⊥ := by simpa using hij
    simpa using hi.not_isMin

/-- The element in `d.Extension val₀ (Order.succ j)` obtained by extending
an element in `d.Extension val₀ j` when `j` is not maximal. -/
def succ {j : J} (e : d.Extension val₀ j) (hj : ¬IsMax j) :
    d.Extension val₀ (Order.succ j) where
  val := d.succ j hj e.val
  map_zero := by
    simp only [← e.map_zero]
    conv_rhs => rw [← d.map_succ j hj e.val]
    rw [← FunctorToTypes.map_comp_apply]
    rfl
  map_succ i hi := by
    obtain hij | rfl := ((Order.lt_succ_iff_of_not_isMax hj).mp hi).lt_or_eq
    · rw [← homOfLE_comp ((Order.lt_succ_iff_of_not_isMax hj).mp hi) (Order.le_succ j), op_comp,
        FunctorToTypes.map_comp_apply, d.map_succ, ← e.map_succ i hij,
        ← homOfLE_comp (Order.succ_le_of_lt hij) (Order.le_succ j), op_comp,
        FunctorToTypes.map_comp_apply, d.map_succ]
    · simp only [homOfLE_refl, op_id, FunctorToTypes.map_id_apply, homOfLE_leOfHom,
        d.map_succ]
  map_limit i hi hij := by
    obtain hij | rfl := hij.lt_or_eq
    · have hij' : i ≤ j := (Order.lt_succ_iff_of_not_isMax hj).mp hij
      have := congr_arg (F.map (homOfLE hij').op) (d.map_succ j hj e.val)
      rw [e.map_limit i hi, ← FunctorToTypes.map_comp_apply, ← op_comp, homOfLE_comp] at this
      rw [this]
      congr
      ext ⟨⟨l, hl⟩⟩
      dsimp
      conv_lhs => rw [← d.map_succ j hj e.val]
      rw [← FunctorToTypes.map_comp_apply]
      rfl
    · exfalso
      exact hj hi.isMax

variable [WellFoundedLT J]

/-- When `j` is a limit element, this is the extension to `d.Extension val₀ j`
of a family of elements in `d.Extension val₀ i` for all `i < j`. -/
def limit (j : J) (hj : Order.IsSuccLimit j)
    (e : ∀ (i : J) (_ : i < j), d.Extension val₀ i) :
    d.Extension val₀ j where
  val := d.lift j hj
    { val := fun ⟨i, hi⟩ ↦ (e i hi).val
      property := fun f ↦ by apply compatibility }
  map_zero := by
    rw [d.map_lift _ _ _ _ (by simpa [bot_lt_iff_ne_bot] using hj.not_isMin)]
    simpa only [homOfLE_refl, op_id, FunctorToTypes.map_id_apply] using
      (e ⊥ (by simpa [bot_lt_iff_ne_bot] using hj.not_isMin)).map_zero
  map_succ i hi := by
    convert (e (Order.succ i) ((Order.IsSuccLimit.succ_lt_iff hj).mpr hi)).map_succ i
      (by
        simp only [Order.lt_succ_iff_not_isMax, not_isMax_iff]
        exact ⟨_, hi⟩) using 1
    · dsimp
      rw [FunctorToTypes.map_id_apply,
        d.map_lift _ _ _ _ ((Order.IsSuccLimit.succ_lt_iff hj).mpr hi)]
    · congr
      rw [d.map_lift _ _ _ _ hi]
      symm
      apply compatibility
  map_limit i hi hij := by
    obtain hij' | rfl := hij.lt_or_eq
    · have := (e i hij').map_limit i hi (by rfl)
      dsimp at this ⊢
      rw [FunctorToTypes.map_id_apply] at this
      rw [d.map_lift _ _ _ _ hij']
      dsimp
      rw [this]
      congr
      dsimp
      ext ⟨⟨l, hl⟩⟩
      rw [map_lift _ _ _ _ _ (hl.trans hij')]
      apply compatibility
    · dsimp
      rw [FunctorToTypes.map_id_apply]
      congr
      ext ⟨⟨l, hl⟩⟩
      rw [d.map_lift _ _ _ _ hl]

instance (j : J) : Nonempty (d.Extension val₀ j) := by
  induction j using SuccOrder.limitRecOn with
  | isMin i hi =>
    obtain rfl : i = ⊥ := by simpa using hi
    exact ⟨zero d val₀⟩
  | succ i hi hi' => exact ⟨hi'.some.succ hi⟩
  | isSuccLimit i hi hi' => exact ⟨limit i hi (fun l hl ↦ (hi' l hl).some)⟩

noncomputable instance (j : J) : Unique (d.Extension val₀ j) :=
  uniqueOfSubsingleton (Nonempty.some inferInstance)

end Extension

variable [WellFoundedLT J]

/-- When `J` is a well-ordered type, `F : Jᵒᵖ ⥤ Type v`, and `d : F.WellOrderInductionData`,
this is the section of `F` that is determined by `val₀ : F.obj (op ⊥)` -/
noncomputable def sectionsMk (val₀ : F.obj (op ⊥)) : F.sections where
  val j := (default : d.Extension val₀ j.unop).val
  property := fun f ↦ by apply Extension.compatibility

lemma sectionsMk_val_op_bot (val₀ : F.obj (op ⊥)) :
    (d.sectionsMk val₀).val (op ⊥) = val₀ := by
  simpa using (default : d.Extension val₀ ⊥).map_zero

include d in
lemma surjective :
    Function.Surjective ((fun s ↦ s (op ⊥)) ∘ Subtype.val : F.sections → F.obj (op ⊥)) :=
  fun val₀ ↦ ⟨d.sectionsMk val₀, d.sectionsMk_val_op_bot val₀⟩

end WellOrderInductionData

end Functor

end CategoryTheory
