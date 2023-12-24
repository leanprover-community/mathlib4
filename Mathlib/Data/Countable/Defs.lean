/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Finite.Defs
import Mathlib.Init.Data.Fin.Basic
import Mathlib.Tactic.Common

#align_import data.countable.defs from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
# Countable types

In this file we define a typeclass saying that a given `Sort*` is countable. See also `Encodable`
for a version that singles out a specific encoding of elements of `α` by natural numbers.

This file also provides a few instances of this typeclass. More instances can be found in other
files.
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
#align countable Countable
#align countable_iff_exists_injective countable_iff_exists_injective

lemma Countable.exists_injective_nat (α : Sort u) [Countable α] : ∃ f : α → ℕ, Injective f :=
  Countable.exists_injective_nat'

instance : Countable ℕ :=
  ⟨⟨id, injective_id⟩⟩

export Countable (exists_injective_nat)

protected theorem Function.Injective.countable [Countable β] {f : α → β} (hf : Injective f) :
    Countable α :=
  let ⟨g, hg⟩ := exists_injective_nat β
  ⟨⟨g ∘ f, hg.comp hf⟩⟩
#align function.injective.countable Function.Injective.countable

protected theorem Function.Surjective.countable [Countable α] {f : α → β} (hf : Surjective f) :
    Countable β :=
  (injective_surjInv hf).countable
#align function.surjective.countable Function.Surjective.countable

theorem exists_surjective_nat (α : Sort u) [Nonempty α] [Countable α] : ∃ f : ℕ → α, Surjective f :=
  let ⟨f, hf⟩ := exists_injective_nat α
  ⟨invFun f, invFun_surjective hf⟩
#align exists_surjective_nat exists_surjective_nat

theorem countable_iff_exists_surjective [Nonempty α] : Countable α ↔ ∃ f : ℕ → α, Surjective f :=
  ⟨@exists_surjective_nat _ _, fun ⟨_, hf⟩ ↦ hf.countable⟩
#align countable_iff_exists_surjective countable_iff_exists_surjective

theorem Countable.of_equiv (α : Sort*) [Countable α] (e : α ≃ β) : Countable β :=
  e.symm.injective.countable
#align countable.of_equiv Countable.of_equiv

theorem Equiv.countable_iff (e : α ≃ β) : Countable α ↔ Countable β :=
  ⟨fun h => @Countable.of_equiv _ _ h e, fun h => @Countable.of_equiv _ _ h e.symm⟩
#align equiv.countable_iff Equiv.countable_iff

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
  Function.Injective.countable (@Fin.eq_of_veq n)

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
  (surjective_quot_mk r).countable

instance (priority := 500) [Countable α] {s : Setoid α} : Countable (Quotient s) :=
  (inferInstance : Countable (@Quot α _))


/-
# Uncountable types

This typeclass says that a given `Sort*` is not countable.
-/

@[mk_iff]
class Uncountable (α : Sort*) : Prop where
  not_countable : ¬Countable α

lemma countable_iff_not_uncountable {α : Sort u} : Countable α ↔ ¬ Uncountable α := by
  constructor
  · intro h
    contrapose! h
    exact (Uncountable_iff α).mp h
  · intro h
    contrapose! h
    exact (Uncountable_iff α).mpr h

lemma countable_not_uncountable [Countable α] : ¬ Uncountable α := by
  apply countable_iff_not_uncountable.mp
  trivial

lemma uncountable_not_countable [Uncountable α] : ¬ Countable α := by
  apply (Uncountable_iff α).mp
  trivial

lemma Uncountable.not_exists_injective_nat (α : Sort u) [Uncountable α] :
    ¬ (∃ f : α → ℕ, Injective f) := by
  by_contra h
  have : Countable α := { exists_injective_nat' := h}
  have : ¬ Countable α := Uncountable.not_countable
  contradiction

export Uncountable (not_exists_injective_nat)

protected theorem Function.Injective.uncountable [Uncountable α] {f : α → β} (hf : Injective f) :
    Uncountable β := by
  by_contra h
  apply countable_iff_not_uncountable.mpr at h
  have this1 := Function.Injective.countable hf
  have this2 := @uncountable_not_countable α
  exact this2 this1

protected theorem Function.Surjective.uncountable [Uncountable β] {f : α → β} (hf : Surjective f) :
    Uncountable α := (injective_surjInv hf).uncountable

theorem not_exists_surjective_nat (α : Sort u) [Nonempty α] [Uncountable α] :
   ¬ ∃ f : ℕ → α, Surjective f := by
  by_contra h
  rcases h with ⟨f, hf⟩
  have : Countable α := by
    refine countable_iff_exists_surjective.mpr ?_
    use f
  apply countable_iff_not_uncountable.mp this
  trivial

theorem uncountable_iff_not_exists_surjective [Nonempty α] : Uncountable α ↔
    ¬ ∃ f : ℕ → α, Surjective f := by
    constructor
    · exact @not_exists_surjective_nat _ _
    · intro hf
      refine { not_countable := ?mpr.not_countable }
      contrapose! hf
      apply exists_surjective_nat

theorem Uncountable.of_equiv (α : Sort*) [Uncountable α] (e : α ≃ β) : Uncountable β := by
  by_contra h
  have := countable_iff_not_uncountable.mpr h
  have hca := Countable.of_equiv β e.symm
  have := @uncountable_not_countable α _
  contradiction

theorem Equiv.uncountable_iff (e : α ≃ β) : Uncountable α ↔ Uncountable β :=
  ⟨fun h => @Uncountable.of_equiv _ _ h e, fun h => @Uncountable.of_equiv _ _ h e.symm⟩

instance {β : Type v} [Uncountable β] : Uncountable (ULift.{u} β) :=
  Uncountable.of_equiv _ Equiv.ulift.symm
