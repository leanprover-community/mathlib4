/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import Mathlib.Combinatorics.Quiver.Basic

/-!

# Pushing a quiver structure along a map

Given a map `σ : V → W` and a `quiver` instance on `V`, this files defines a `quiver` instance
on `W` by associating to each arrow `v ⟶ v'` in `V` an arrow `σ v ⟶ σ v'` in `W`.

-/


universe v v₁ v₂ u u₁ u₂

variable {V : Type _} [Quiver V] {W : Type _} (σ : V → W)

/-- The `quiver` instance obtained by pushing arrows of `V` along the map `σ : V → W` -/
def Push (_ : V → W) :=
  W
#align push Push

instance [h : Nonempty W] : Nonempty (Push σ) :=
  h

/-- The quiver structure obtained by pushing arrows of `V` along the map `σ : V → W` -/
inductive PushQuiver {V : Type u} [Quiver.{v} V] {W : Type u₂} (σ : V → W) : W → W → Type max u u₂ v
  | arrow {X Y : V} (f : X ⟶ Y) : PushQuiver σ (σ X) (σ Y)
#align push_quiver PushQuiver

instance : Quiver (Push σ) :=
  ⟨PushQuiver σ⟩

namespace Push

/-- The prefunctor induced by pushing arrows via `σ` -/
def of : V ⥤q Push σ where
  obj := σ
  map f := PushQuiver.arrow f
#align push.of Push.of

@[simp]
theorem of_obj : (of σ).obj = σ :=
  rfl
#align push.of_obj Push.of_obj

variable {W' : Type _} [Quiver W'] (φ : V ⥤q W') (τ : W → W') (h : ∀ x, φ.obj x = τ (σ x))

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
#align push.lift Push.lift

theorem lift_obj : (lift σ φ τ h).obj = τ :=
  rfl
#align push.lift_obj Push.lift_obj

theorem eqRec_heq' {α : Sort u} {φ : α → Sort v} {a a' : α} : (h : a = a') → (p : φ a)
  → HEq (Eq.rec (motive := fun x _ => φ x) p h) p
  | rfl, p => HEq.refl p

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
    apply HEq.symm
    apply (eqRec_heq' _ _).trans
    have : ∀ p : Prefunctor.obj φ X = Prefunctor.obj (of σ ⋙q lift σ φ τ h) X,
      HEq (p ▸ Prefunctor.map φ f) (Prefunctor.map φ f) := by

    apply eqRec_heq' _ (Prefunctor.map φ f)
    rfl
#align push.lift_comp Push.lift_comp

theorem lift_unique (Φ : Push σ ⥤q W') (Φ₀ : Φ.obj = τ) (Φcomp : (of σ ⋙q Φ) = φ) :
    Φ = lift σ φ τ h := by
  dsimp only [of, lift]
  fapply Prefunctor.ext
  · intro X
    simp only
    rw [Φ₀]
  · rintro _ _ ⟨⟩
    subst_vars
    simp only [Prefunctor.comp_map, cast_eq]
    rfl
#align push.lift_unique Push.lift_unique

end Push
