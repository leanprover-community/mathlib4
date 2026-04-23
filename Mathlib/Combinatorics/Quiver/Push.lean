/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
module

public import Mathlib.Combinatorics.Quiver.Prefunctor
import Batteries.Tactic.Init
import Mathlib.Init
import Mathlib.Util.CompileInductive

/-!

# Pushing a quiver structure along a map

Given a map `σ : V → W` and a `Quiver` instance on `V`, this file defines a `Quiver` instance
on `W` by associating to each arrow `v ⟶ v'` in `V` an arrow `σ v ⟶ σ v'` in `W`.

-/

@[expose] public section

namespace Quiver

universe v v₁ v₂ u u₁ u₂

variable {V : Type*} [Quiver V] {W : Type*} (σ : V → W)

/-- The `Quiver` instance obtained by pushing arrows of `V` along the map `σ : V → W` -/
@[nolint unusedArguments]
def Push (_ : V → W) :=
  W

instance [h : Nonempty W] : Nonempty (Push σ) :=
  h

/-- The quiver structure obtained by pushing arrows of `V` along the map `σ : V → W` -/
inductive PushQuiver {V : Type u} [Quiver.{v} V] {W : Type u₂} (σ : V → W) : W → W → Type max u u₂ v
  | arrow {X Y : V} (f : X ⟶ Y) : PushQuiver σ (σ X) (σ Y)

instance : Quiver (Push σ) :=
  ⟨PushQuiver σ⟩

namespace Push

/-- The prefunctor induced by pushing arrows via `σ` -/
def of : V ⥤q Push σ where
  obj := σ
  map f := PushQuiver.arrow f

@[simp]
theorem of_obj : (of σ).obj = σ :=
  rfl

variable {W' : Type*} [Quiver W'] (φ : V ⥤q W') (τ : W → W') (h : ∀ x, φ.obj x = τ (σ x))

/-- Given a function `τ : W → W'` and a prefunctor `φ : V ⥤q W'`, one can extend `τ` to be
a prefunctor `W ⥤q W'` if `τ` and `σ` factorize `φ` at the level of objects, where `W` is given
the pushforward quiver structure `Push σ`. -/
noncomputable def lift : Push σ ⥤q W' where
  obj := τ
  map :=
    @PushQuiver.rec V _ W σ (fun X Y _ => τ X ⟶ τ Y) @fun X Y f => by
      dsimp only
      rw [← h X, ← h Y]
      exact φ.map f

theorem lift_obj : (lift σ φ τ h).obj = τ :=
  rfl

theorem lift_comp : (of σ ⋙q lift σ φ τ h) = φ := by
  fapply Prefunctor.ext
  · rintro X
    simp only [Prefunctor.comp_obj]
    apply Eq.symm
    exact h X
  · rintro X Y f
    simp only [Prefunctor.comp_map]
    apply eq_of_heq
    iterate 2 apply (cast_heq _ _).trans
    simp

theorem lift_unique (Φ : Push σ ⥤q W') (Φ₀ : Φ.obj = τ) (Φcomp : (of σ ⋙q Φ) = φ) :
    Φ = lift σ φ τ h := by
  dsimp only [of, lift]
  fapply Prefunctor.ext
  · intro X
    simp only
    rw [Φ₀]
  · rintro _ _ ⟨⟩
    subst_vars
    simp only [Prefunctor.comp_map]
    rfl

end Push

end Quiver
