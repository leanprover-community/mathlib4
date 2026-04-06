/-
Copyright (c) 2026 zayn7lie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Wang
-/
module

public import Mathlib.Logic.Relation

/-!
# Confluent Reduction

This file contain the definition of the Diamond property and
Confluent property. Then investigate the relationship between
these two property.

## Main definition

- `Diamond r`: $r$ is diamond iff we have $a$ to $b$ and $a$ to $c$ through $r$,
    then we could find a $d$ where $b$ and $c$ arrives through $r$.
- `Confluent r`: $r$ is confluent iff we have $a$ to $b$ and $a$ to $c$ through $r^*$,
    then we could find a $d$ where $b$ and $c$ arrives through $r^*$.

## Main Theorem

- `confluent_of_diamond`: Diamond is the confluence of the refl-closure.
- `rtc_eq_of_sandwich`: if we can find a relation $p$ where `r ⊆ p ⊆ r*`,
    then the refl-trans closure $p^* = r^*$.

-/

open Relation

namespace Lambda

@[simp, expose] public def Diamond {α} (r : α → α → Prop) : Prop :=
  ∀ ⦃a b c⦄, r a b → r a c → ∃ d, r b d ∧ r c d

@[simp, expose] public def Confluent {α} (r : α → α → Prop) : Prop :=
  ∀ ⦃a b c⦄,
    ReflTransGen r a b →
    ReflTransGen r a c →
    ∃ d, ReflTransGen r b d ∧ ReflTransGen r c d

/-- Diamond = confluence of the refl–trans closure. -/
public theorem confluent_of_diamond {α} {r : α → α → Prop}
    (hd : Diamond r) : Confluent r := by
  have strip : ∀ ⦃a b c⦄, r a b → ReflTransGen r a c →
      ∃ d, ReflTransGen r b d ∧ r c d := by
    intro a b c hab hac
    induction hac with
    | refl => exact ⟨b, ReflTransGen.refl, hab⟩
    | tail had hce ih =>
        rcases ih with ⟨d, hbd, hcd⟩
        rcases hd hcd hce with ⟨f, hdf, hef⟩
        exact ⟨f, ReflTransGen.tail hbd hdf, hef⟩
  intro a b c hab hac
  induction hab with
  | refl => exact ⟨c, hac, ReflTransGen.refl⟩
  | tail hab hbc ih =>
      rcases ih with ⟨d, hbd, hcd⟩
      rcases strip hbc hbd with ⟨f, hcf, hdf⟩
      exact ⟨f, hcf, ReflTransGen.tail hcd hdf⟩

/-- Sandwich: if `r ⊆ p ⊆ r*` then `r* = p*`. -/
public theorem rtc_eq_of_sandwich {α} {r p : α → α → Prop}
    (h₁ : ∀ ⦃a b⦄, r a b → p a b)
    (h₂ : ∀ ⦃a b⦄, p a b → ReflTransGen r a b) :
    ∀ {a b}, ReflTransGen r a b ↔ ReflTransGen p a b := by
  intro a b
  constructor
  · intro hr
    induction hr with
    | refl => exact ReflTransGen.refl
    | tail hab hbc ih => exact ReflTransGen.tail ih (h₁ hbc)
  · intro hp
    induction hp with
    | refl => exact ReflTransGen.refl
    | tail hab hbc ih => exact ReflTransGen.trans ih (h₂ hbc)

end Lambda
