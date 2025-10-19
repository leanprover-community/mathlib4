/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Subtype
import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Countable and uncountable types

In this file we define a typeclass `Countable` saying that a given `Sort*` is countable
and a typeclass `Uncountable` saying that a given `Type*` is uncountable.

See also `Encodable` for a version that singles out
a specific encoding of elements of `α` by natural numbers.

This file also provides a few instances of these typeclasses.
More instances can be found in other files.
-/

open Function

universe u v

variable {α : Sort u} {β : Sort v}

/-!
### Definition and basic properties
-/

/-- A type `α` is countable if there exists an injective map `α → ℕ`. -/
@[mk_iff countable_iff_exists_injective]
class Countable (α : Sort u) : Prop where
  /-- A type `α` is countable if there exists an injective map `α → ℕ`. -/
  exists_injective_nat' : ∃ f : α → ℕ, Injective f

lemma Countable.exists_injective_nat (α : Sort u) [Countable α] : ∃ f : α → ℕ, Injective f :=
  Countable.exists_injective_nat'

instance : Countable ℕ :=
  ⟨⟨id, injective_id⟩⟩

export Countable (exists_injective_nat)

protected theorem Function.Injective.countable [Countable β] {f : α → β} (hf : Injective f) :
    Countable α :=
  let ⟨g, hg⟩ := exists_injective_nat β
  ⟨⟨g ∘ f, hg.comp hf⟩⟩

protected theorem Function.Surjective.countable [Countable α] {f : α → β} (hf : Surjective f) :
    Countable β :=
  (injective_surjInv hf).countable

theorem exists_surjective_nat (α : Sort u) [Nonempty α] [Countable α] : ∃ f : ℕ → α, Surjective f :=
  let ⟨f, hf⟩ := exists_injective_nat α
  ⟨invFun f, invFun_surjective hf⟩

theorem countable_iff_exists_surjective [Nonempty α] : Countable α ↔ ∃ f : ℕ → α, Surjective f :=
  ⟨@exists_surjective_nat _ _, fun ⟨_, hf⟩ ↦ hf.countable⟩

theorem Countable.of_equiv (α : Sort*) [Countable α] (e : α ≃ β) : Countable β :=
  e.symm.injective.countable

theorem Equiv.countable_iff (e : α ≃ β) : Countable α ↔ Countable β :=
  ⟨fun h => @Countable.of_equiv _ _ h e, fun h => @Countable.of_equiv _ _ h e.symm⟩

instance {β : Type v} [Countable β] : Countable (ULift.{u} β) :=
  Countable.of_equiv _ Equiv.ulift.symm

/-!
### Operations on `Sort*`s
-/


instance [Countable α] : Countable (PLift α) :=
  Equiv.plift.injective.countable

instance (priority := 100) Subsingleton.to_countable [Subsingleton α] : Countable α :=
  ⟨⟨fun _ => 0, fun x y _ => Subsingleton.elim x y⟩⟩

instance (priority := 500) Subtype.countable [Countable α] {p : α → Prop} :
    Countable { x // p x } :=
  Subtype.val_injective.countable

instance {n : ℕ} : Countable (Fin n) :=
  Function.Injective.countable (@Fin.eq_of_val_eq n)

instance (priority := 100) Finite.to_countable [Finite α] : Countable α :=
  let ⟨_, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  Countable.of_equiv _ e.symm

instance : Countable PUnit.{u} :=
  Subsingleton.to_countable

instance (priority := 100) Prop.countable (p : Prop) : Countable p :=
  Subsingleton.to_countable

instance Bool.countable : Countable Bool :=
  ⟨⟨fun b => cond b 0 1, Bool.injective_iff.2 Nat.one_ne_zero⟩⟩

instance Prop.countable' : Countable Prop :=
  Countable.of_equiv Bool Equiv.propEquivBool.symm

instance (priority := 500) Quotient.countable [Countable α] {r : α → α → Prop} :
    Countable (Quot r) :=
  Quot.mk_surjective.countable

instance (priority := 500) [Countable α] {s : Setoid α} : Countable (Quotient s) :=
  (inferInstance : Countable (@Quot α _))

/-!
### Uncountable types
-/

/-- A type `α` is uncountable if it is not countable. -/
@[mk_iff uncountable_iff_not_countable]
class Uncountable (α : Sort*) : Prop where
  /-- A type `α` is uncountable if it is not countable. -/
  not_countable : ¬Countable α

@[push]
lemma not_uncountable_iff : ¬Uncountable α ↔ Countable α := by
  rw [uncountable_iff_not_countable, not_not]

@[push]
lemma not_countable_iff : ¬Countable α ↔ Uncountable α := (uncountable_iff_not_countable α).symm

@[simp]
lemma not_uncountable [Countable α] : ¬Uncountable α := not_uncountable_iff.2 ‹_›

@[simp]
lemma not_countable [Uncountable α] : ¬Countable α := Uncountable.not_countable

protected theorem Function.Injective.uncountable [Uncountable α] {f : α → β} (hf : Injective f) :
    Uncountable β :=
  ⟨fun _ ↦ not_countable hf.countable⟩

protected theorem Function.Surjective.uncountable [Uncountable β] {f : α → β} (hf : Surjective f) :
    Uncountable α := (injective_surjInv hf).uncountable

lemma not_injective_uncountable_countable [Uncountable α] [Countable β] (f : α → β) :
    ¬Injective f := fun hf ↦ not_countable hf.countable

lemma not_surjective_countable_uncountable [Countable α] [Uncountable β] (f : α → β) :
    ¬Surjective f := fun hf ↦
  not_countable hf.countable

theorem uncountable_iff_forall_not_surjective [Nonempty α] :
    Uncountable α ↔ ∀ f : ℕ → α, ¬Surjective f := by
  rw [← not_countable_iff, countable_iff_exists_surjective, not_exists]

theorem Uncountable.of_equiv (α : Sort*) [Uncountable α] (e : α ≃ β) : Uncountable β :=
  e.injective.uncountable

theorem Equiv.uncountable_iff (e : α ≃ β) : Uncountable α ↔ Uncountable β :=
  ⟨fun h => @Uncountable.of_equiv _ _ h e, fun h => @Uncountable.of_equiv _ _ h e.symm⟩

instance {β : Type v} [Uncountable β] : Uncountable (ULift.{u} β) :=
  .of_equiv _ Equiv.ulift.symm

instance [Uncountable α] : Uncountable (PLift α) :=
  .of_equiv _ Equiv.plift.symm

instance (priority := 100) [Uncountable α] : Infinite α :=
  ⟨fun _ ↦ not_countable (α := α) inferInstance⟩
