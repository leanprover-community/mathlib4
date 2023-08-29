/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import Mathlib.Combinatorics.Quiver.Basic

#align_import combinatorics.quiver.push from "leanprover-community/mathlib"@"2258b40dacd2942571c8ce136215350c702dc78f"

/-!

# Pushing a quiver structure along a map

Given a map `σ : V → W` and a `Quiver` instance on `V`, this files defines a `Quiver` instance
on `W` by associating to each arrow `v ⟶ v'` in `V` an arrow `σ v ⟶ σ v'` in `W`.

-/

namespace Quiver

universe v v₁ v₂ u u₁ u₂

variable {V : Type*} [Quiver V] {W : Type*} (σ : V → W)

/-- The `Quiver` instance obtained by pushing arrows of `V` along the map `σ : V → W` -/
@[nolint unusedArguments]
def Push (_ : V → W) :=
  W
#align quiver.push Quiver.Push

instance [h : Nonempty W] : Nonempty (Push σ) :=
  h

/-- The quiver structure obtained by pushing arrows of `V` along the map `σ : V → W` -/
inductive PushQuiver {V : Type u} [Quiver.{v} V] {W : Type u₂} (σ : V → W) : W → W → Type max u u₂ v
  | arrow {X Y : V} (f : X ⟶ Y) : PushQuiver σ (σ X) (σ Y)
#align quiver.push_quiver Quiver.PushQuiver

instance : Quiver (Push σ) :=
  ⟨PushQuiver σ⟩

namespace Push

/-- The prefunctor induced by pushing arrows via `σ` -/
def of : V ⥤q Push σ where
  obj := σ
  map f := PushQuiver.arrow f
#align quiver.push.of Quiver.Push.of

@[simp]
theorem of_obj : (of σ).obj = σ :=
  rfl
#align quiver.push.of_obj Quiver.Push.of_obj

variable {W' : Type*} [Quiver W'] (φ : V ⥤q W') (τ : W → W') (h : ∀ x, φ.obj x = τ (σ x))

/-- Given a function `τ : W → W'` and a prefunctor `φ : V ⥤q W'`, one can extend `τ` to be
a prefunctor `W ⥤q W'` if `τ` and `σ` factorize `φ` at the level of objects, where `W` is given
the pushforward quiver structure `Push σ`. -/
noncomputable def lift : Push σ ⥤q W' where
  obj := τ
  map :=
    @PushQuiver.rec V _ W σ (fun X Y _ => τ X ⟶ τ Y) @fun X Y f => by
      dsimp only
      -- ⊢ τ (σ X) ⟶ τ (σ Y)
      rw [← h X, ← h Y]
      -- ⊢ φ.obj X ⟶ φ.obj Y
      exact φ.map f
      -- 🎉 no goals
#align quiver.push.lift Quiver.Push.lift

theorem lift_obj : (lift σ φ τ h).obj = τ :=
  rfl
#align quiver.push.lift_obj Quiver.Push.lift_obj

theorem lift_comp : (of σ ⋙q lift σ φ τ h) = φ := by
  fapply Prefunctor.ext
  -- ⊢ ∀ (X : V), (of σ ⋙q lift σ φ τ h).obj X = φ.obj X
  · rintro X
    -- ⊢ (of σ ⋙q lift σ φ τ h).obj X = φ.obj X
    simp only [Prefunctor.comp_obj]
    -- ⊢ (lift σ φ τ h).obj ((of σ).obj X) = φ.obj X
    apply Eq.symm
    -- ⊢ φ.obj X = (lift σ φ τ h).obj ((of σ).obj X)
    exact h X
    -- 🎉 no goals
  · rintro X Y f
    -- ⊢ (of σ ⋙q lift σ φ τ h).map f = Eq.recOn (_ : φ.obj Y = (of σ ⋙q lift σ φ τ h …
    simp only [Prefunctor.comp_map]
    -- ⊢ (lift σ φ τ h).map ((of σ).map f) = (_ : φ.obj Y = (of σ ⋙q lift σ φ τ h).ob …
    apply eq_of_heq
    -- ⊢ HEq ((lift σ φ τ h).map ((of σ).map f)) ((_ : φ.obj Y = (of σ ⋙q lift σ φ τ  …
    iterate 2 apply (cast_heq _ _).trans
    -- ⊢ HEq (φ.map f) ((_ : φ.obj Y = (of σ ⋙q lift σ φ τ h).obj Y) ▸ (_ : φ.obj X = …
    apply HEq.symm
    -- ⊢ HEq ((_ : φ.obj Y = (of σ ⋙q lift σ φ τ h).obj Y) ▸ (_ : φ.obj X = (of σ ⋙q  …
    apply (eqRec_heq _ _).trans
    -- ⊢ HEq ((_ : φ.obj X = (of σ ⋙q lift σ φ τ h).obj X) ▸ φ.map f) (φ.map f)
    have : ∀ {α γ} {β : α → γ → Sort _} {a a'} (p : a = a') g (b : β a g), HEq (p ▸ b) b := by
      intros
      subst_vars
      rfl
    apply this
    -- 🎉 no goals
#align quiver.push.lift_comp Quiver.Push.lift_comp

theorem lift_unique (Φ : Push σ ⥤q W') (Φ₀ : Φ.obj = τ) (Φcomp : (of σ ⋙q Φ) = φ) :
    Φ = lift σ φ τ h := by
  dsimp only [of, lift]
  -- ⊢ Φ = { obj := τ, map := @PushQuiver.rec V inst✝¹ W σ (fun X Y x => τ X ⟶ τ Y) …
  fapply Prefunctor.ext
  -- ⊢ ∀ (X : Push σ), Φ.obj X = { obj := τ, map := @PushQuiver.rec V inst✝¹ W σ (f …
  · intro X
    -- ⊢ Φ.obj X = { obj := τ, map := @PushQuiver.rec V inst✝¹ W σ (fun X Y x => τ X  …
    simp only
    -- ⊢ Φ.obj X = τ X
    rw [Φ₀]
    -- 🎉 no goals
  · rintro _ _ ⟨⟩
    -- ⊢ Φ.map (PushQuiver.arrow f✝) = Eq.recOn (_ : { obj := τ, map := @PushQuiver.r …
    subst_vars
    -- ⊢ Φ.map (PushQuiver.arrow f✝) = Eq.recOn (_ : { obj := Φ.obj, map := @PushQuiv …
    simp only [Prefunctor.comp_map, cast_eq]
    -- ⊢ Φ.map (PushQuiver.arrow f✝) = id (Eq.mpr (_ : (Φ.obj (σ X✝) ⟶ Φ.obj (σ Y✝))  …
    rfl
    -- 🎉 no goals
#align quiver.push.lift_unique Quiver.Push.lift_unique

end Push

end Quiver
