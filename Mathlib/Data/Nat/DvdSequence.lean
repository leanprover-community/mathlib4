/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Action.Pi

/-!
# Divisibility sequences

A sequence `f : ℕ → ℕ` is a *divisibility sequence* if it satisfies `f a ∣ f b` whenever `a ∣ b`.

A sequence `f : ℕ → ℕ` is a *strong divisibility sequence* if `gcd (f a) (f b) = f (gcd a b)`.

This file defines divisibility sequences and strong divisibility sequences, and provides some basic
API for these definitions.

## Main definitions

* `IsDvdSeq`: A function `f` is a divisibility sequence if `a ∣ b` implies `f a ∣ f b`.
* `Nat.IsStrongDvdSeq`: A function `f : ℕ → ℕ` is a strong divisibility sequence if `f` satisfies
  `gcd (f a) (f b) = f (gcd a b)`.
-/

@[expose] public section

variable {α β γ : Type*}

-- this lemma regarding interaction between `smul` and `dvd` does not have a good home in mathlib
lemma smul_dvd_smul [Monoid α] [Monoid β] [SMul α β] [IsScalarTower α β β]
    [IsScalarTower α α β] [SMulCommClass α β β] {a b : α} {c d : β}
    (hab : a ∣ b) (hcd : c ∣ d) : (a • c) ∣ (b • d) := by
  obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := hab, hcd
  exact ⟨x • y, mul_smul_mul_comm a x c y⟩

/-- A function `f : α → β` is a divisibility sequence if `a ∣ b` implies `f a ∣ f b`. -/
def IsDvdSequence [Dvd α] [Dvd β] (f : α → β) : Prop :=
  ∀ a b, a ∣ b → f a ∣ f b

@[deprecated (since := "2026-06-30")] alias IsDivSequence := IsDvdSequence

namespace IsDvdSequence

variable (α) in
protected theorem id [Dvd α] : IsDvdSequence (id : α → α) :=
  fun _ _ ↦ id

variable (α) in
protected theorem const [Dvd α] [Monoid β] (b : β) : IsDvdSequence (fun _ : α ↦ b) := by
  simp [IsDvdSequence]

protected theorem smul' [Dvd α] [Monoid β] [Monoid γ] {f : α → β} {g : α → γ} [SMul β γ]
    [IsScalarTower β γ γ] [IsScalarTower β β γ] [SMulCommClass β γ γ]
    (hf : IsDvdSequence f) (hg : IsDvdSequence g) : IsDvdSequence (f • g) :=
  fun a b hab ↦ smul_dvd_smul (hf a b hab) (hg a b hab)

protected theorem mul [Dvd α] [CommMonoid β] {f g : α → β} (hf : IsDvdSequence f)
    (hg : IsDvdSequence g) : IsDvdSequence (f * g) :=
  .smul' hf hg

protected theorem smul [Dvd α] [Monoid β] [Monoid γ] {f : α → γ} [SMul β γ] [IsScalarTower β γ γ]
    [IsScalarTower β β γ] [SMulCommClass β γ γ] (b : β) (hg : IsDvdSequence f) :
    IsDvdSequence (b • f) :=
  .smul' (.const α b) hg

end IsDvdSequence

@[deprecated (since := "2026-06-30")] alias IsDivSequence.smul := IsDvdSequence.smul
@[deprecated (since := "2026-06-30")] alias isDivSequence_id := IsDvdSequence.id

namespace Nat

/-- A function `f : ℕ → ℕ` is a strong divisibility sequence if `gcd (f a) (f b) = f (gcd a b)`. -/
def IsStrongDvdSequence (f : ℕ → ℕ) : Prop :=
  ∀ a b, (f a).gcd (f b) = f (a.gcd b)

namespace IsStrongDvdSequence

theorem isDvdSequence {f : ℕ → ℕ} (hf : IsStrongDvdSequence f) : IsDvdSequence f := by
  intro a b hab
  simpa [gcd_eq_left hab, gcd_eq_left_iff_dvd] using hf a b

protected theorem id : IsStrongDvdSequence (id : ℕ → ℕ) :=
  fun _ _ ↦ rfl

protected theorem const (n : ℕ) : IsStrongDvdSequence (fun _ ↦ n) := by
  simp [IsStrongDvdSequence]

end IsStrongDvdSequence

end Nat
