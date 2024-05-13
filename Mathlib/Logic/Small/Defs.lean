/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.MkIffOfInductiveProp
import Mathlib.Tactic.PPWithUniv

#align_import logic.small.basic from "leanprover-community/mathlib"@"d012cd09a9b256d870751284dd6a29882b0be105"

/-!
# Small types

A type is `w`-small if there exists an equivalence to some `S : Type w`.

We provide a noncomputable model `Shrink α : Type w`, and `equivShrink α : α ≃ Shrink α`.

A subsingleton type is `w`-small for any `w`.

If `α ≃ β`, then `Small.{w} α ↔ Small.{w} β`.

See `Mathlib.Logic.Small.Basic` for further instances and theorems.
-/

universe u w v v'

/-- A type is `Small.{w}` if there exists an equivalence to some `S : Type w`.
-/
@[mk_iff, pp_with_univ]
class Small (α : Type v) : Prop where
  /-- If a type is `Small.{w}`, then there exists an equivalence with some `S : Type w` -/
  equiv_small : ∃ S : Type w, Nonempty (α ≃ S)
#align small Small

/-- Constructor for `Small α` from an explicit witness type and equivalence.
-/
theorem Small.mk' {α : Type v} {S : Type w} (e : α ≃ S) : Small.{w} α :=
  ⟨⟨S, ⟨e⟩⟩⟩
#align small.mk' Small.mk'

/-- An arbitrarily chosen model in `Type w` for a `w`-small type.
-/
@[pp_with_univ]
def Shrink (α : Type v) [Small.{w} α] : Type w :=
  Classical.choose (@Small.equiv_small α _)
#align shrink Shrink

/-- The noncomputable equivalence between a `w`-small type and a model.
-/
noncomputable def equivShrink (α : Type v) [Small.{w} α] : α ≃ Shrink α :=
  Nonempty.some (Classical.choose_spec (@Small.equiv_small α _))
#align equiv_shrink equivShrink

@[ext]
theorem Shrink.ext {α : Type v} [Small.{w} α] {x y : Shrink α}
    (w : (equivShrink _).symm x = (equivShrink _).symm y) : x = y := by
  simpa using w

-- It would be nice to mark this as `aesop cases` if
-- https://github.com/JLimperg/aesop/issues/59
-- is resolved.
@[induction_eliminator]
protected noncomputable def Shrink.rec {α : Type*} [Small.{w} α] {F : Shrink α → Sort v}
    (h : ∀ X, F (equivShrink _ X)) : ∀ X, F X :=
  fun X => ((equivShrink _).apply_symm_apply X) ▸ (h _)

-- Porting note: Priority changed to 101
instance (priority := 101) small_self (α : Type v) : Small.{v} α :=
  Small.mk' <| Equiv.refl α
#align small_self small_self

theorem small_map {α : Type*} {β : Type*} [hβ : Small.{w} β] (e : α ≃ β) : Small.{w} α :=
  let ⟨_, ⟨f⟩⟩ := hβ.equiv_small
  Small.mk' (e.trans f)
#align small_map small_map

theorem small_lift (α : Type u) [hα : Small.{v} α] : Small.{max v w} α :=
  let ⟨⟨_, ⟨f⟩⟩⟩ := hα
  Small.mk' <| f.trans (Equiv.ulift.{w}).symm
#align small_lift small_lift

/- This was an instance but useless due to https://github.com/leanprover/lean4/issues/2297. -/
lemma small_max (α : Type v) : Small.{max w v} α :=
  small_lift.{v, w} α
#align small_max small_max

instance small_zero (α : Type) : Small.{w} α := small_max α

instance (priority := 100) small_succ (α : Type v) : Small.{v+1} α :=
  small_lift.{v, v+1} α

instance small_ulift (α : Type u) [Small.{v} α] : Small.{v} (ULift.{w} α) :=
  small_map Equiv.ulift
#align small_ulift small_ulift

theorem small_type : Small.{max (u + 1) v} (Type u) :=
  small_max.{max (u + 1) v} _
#align small_type small_type

section

open scoped Classical

theorem small_congr {α : Type*} {β : Type*} (e : α ≃ β) : Small.{w} α ↔ Small.{w} β :=
  ⟨fun h => @small_map _ _ h e.symm, fun h => @small_map _ _ h e⟩
#align small_congr small_congr

instance small_sigma {α} (β : α → Type*) [Small.{w} α] [∀ a, Small.{w} (β a)] :
    Small.{w} (Σa, β a) :=
  ⟨⟨Σa' : Shrink α, Shrink (β ((equivShrink α).symm a')),
      ⟨Equiv.sigmaCongr (equivShrink α) fun a => by simpa using equivShrink (β a)⟩⟩⟩
#align small_sigma small_sigma

theorem not_small_type : ¬Small.{u} (Type max u v)
  | ⟨⟨S, ⟨e⟩⟩⟩ =>
    @Function.cantor_injective (Σα, e.symm α) (fun a => ⟨_, cast (e.3 _).symm a⟩) fun a b e => by
      dsimp at e
      injection e with h₁ h₂
      simpa using h₂
#align not_small_type not_small_type

end
