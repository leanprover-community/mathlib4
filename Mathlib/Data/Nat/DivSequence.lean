/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Group.Action.Pi

/-!
# Divisibility sequences

A sequence `f : ℕ → ℕ` is a divisibility sequence if it satisfies `f a ∣ f b` whenever `a ∣ b`.

A sequence `f : ℕ → ℕ` is a strong divisibility sequence if `gcd (f a) (f b) = f (gcd a b)`.

This file defines divisibility sequences and strong divisibility sequences and provides some basic
API for these definitions.

## Main definitions

- `IsDvdSeq`: A function `f` is a divisibility sequence if `a ∣ b` implies `f a ∣ f b`.
- `Nat.IsStrongDvdSeq`: A function `f : ℕ → ℕ` is a strong divisibility sequence if `f` satisfies
  `gcd (f a) (f b) = f (gcd a b)`.
-/

@[expose] public section

variable {α β γ : Type*}

/-- A function `f : α → β` is a divisibility sequence if `a ∣ b` implies `f a ∣ f b`. -/
def IsDvdSeq [Dvd α] [Dvd β] (f : α → β) : Prop :=
  ∀ a b, a ∣ b → f a ∣ f b

namespace IsDvdSeq

protected theorem id [Dvd α] : IsDvdSeq (id : α → α) :=
  fun _ _ ↦ id

protected theorem const [Dvd α] [Monoid β] (b : β) : IsDvdSeq (fun _ : α ↦ b) := by
  simp [IsDvdSeq]

protected theorem smul' [Dvd α] [Monoid β] [Monoid γ] {f : α → β} {g : α → γ} [SMul β γ]
    [IsScalarTower β γ γ] [IsScalarTower β β γ] [SMulCommClass β γ γ]
    (hf : IsDvdSeq f) (hg : IsDvdSeq g) : IsDvdSeq (f • g) :=
  fun a b hab ↦ smul_dvd_smul (hf a b hab) (hg a b hab)

protected theorem mul [Dvd α] [CommMonoid β] {f g : α → β}
    (hf : IsDvdSeq f) (hg : IsDvdSeq g) : IsDvdSeq (f * g) :=
  .smul' hf hg

protected theorem smul [Dvd α] [Monoid β] [Monoid γ] {f : α → γ} [SMul β γ]
    [IsScalarTower β γ γ] [IsScalarTower β β γ] [SMulCommClass β γ γ]
    (b : β) (hg : IsDvdSeq f) : IsDvdSeq (b • f) :=
  .smul' (.const b) hg

end IsDvdSeq

namespace Nat

/-- A function `f : ℕ → ℕ` is a strong divisibility sequence if `gcd (f a) (f b) = f (gcd a b)`. -/
def IsStrongDvdSeq (f : ℕ → ℕ) : Prop :=
  ∀ a b, (f a).gcd (f b) = f (a.gcd b)

namespace IsStrongDvdSeq

theorem isDvdSeq {f : ℕ → ℕ} (hf : IsStrongDvdSeq f) : IsDvdSeq f := by
  intro a b hab
  simpa [gcd_eq_left hab, gcd_eq_left_iff_dvd] using hf a b

protected theorem id : IsStrongDvdSeq (id : ℕ → ℕ) :=
  fun _ _ ↦ rfl

protected theorem const (n : ℕ) : IsStrongDvdSeq (fun _ ↦ n) := by
  simp [IsStrongDvdSeq]

end IsStrongDvdSeq

end Nat
