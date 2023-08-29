/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Logic.Equiv.Nat
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.Countable.Defs

#align_import data.countable.basic from "leanprover-community/mathlib"@"1f0096e6caa61e9c849ec2adbd227e960e9dff58"

/-!
# Countable types

In this file we provide basic instances of the `Countable` typeclass defined elsewhere.
-/


universe u v w

open Function

instance : Countable ℤ :=
  Countable.of_equiv ℕ Equiv.intEquivNat.symm

/-!
### Definition in terms of `Function.Embedding`
-/

section Embedding

variable {α : Sort u} {β : Sort v}

theorem countable_iff_nonempty_embedding : Countable α ↔ Nonempty (α ↪ ℕ) :=
  ⟨fun ⟨⟨f, hf⟩⟩ => ⟨⟨f, hf⟩⟩, fun ⟨f⟩ => ⟨⟨f, f.2⟩⟩⟩
#align countable_iff_nonempty_embedding countable_iff_nonempty_embedding

theorem nonempty_embedding_nat (α) [Countable α] : Nonempty (α ↪ ℕ) :=
  countable_iff_nonempty_embedding.1 ‹_›
#align nonempty_embedding_nat nonempty_embedding_nat

protected theorem Function.Embedding.countable [Countable β] (f : α ↪ β) : Countable α :=
  f.injective.countable
#align function.embedding.countable Function.Embedding.countable

end Embedding

/-!
### Operations on `Type*`s
-/

section type

variable {α : Type u} {β : Type v} {π : α → Type w}

instance [Countable α] [Countable β] : Countable (Sum α β) := by
  rcases exists_injective_nat α with ⟨f, hf⟩
  -- ⊢ Countable (α ⊕ β)
  rcases exists_injective_nat β with ⟨g, hg⟩
  -- ⊢ Countable (α ⊕ β)
  exact (Equiv.natSumNatEquivNat.injective.comp <| hf.sum_map hg).countable
  -- 🎉 no goals

instance [Countable α] : Countable (Option α) :=
  Countable.of_equiv _ (Equiv.optionEquivSumPUnit.{_, 0} α).symm

instance [Countable α] [Countable β] : Countable (α × β) := by
  rcases exists_injective_nat α with ⟨f, hf⟩
  -- ⊢ Countable (α × β)
  rcases exists_injective_nat β with ⟨g, hg⟩
  -- ⊢ Countable (α × β)
  exact (Nat.pairEquiv.injective.comp <| hf.Prod_map hg).countable
  -- 🎉 no goals

instance [Countable α] [∀ a, Countable (π a)] : Countable (Sigma π) := by
  rcases exists_injective_nat α with ⟨f, hf⟩
  -- ⊢ Countable (Sigma π)
  choose g hg using fun a => exists_injective_nat (π a)
  -- ⊢ Countable (Sigma π)
  exact ((Equiv.sigmaEquivProd ℕ ℕ).injective.comp <| hf.sigma_map hg).countable
  -- 🎉 no goals

end type

section sort

variable {α : Sort u} {β : Sort v} {π : α → Sort w}

/-!
### Operations on `Sort*`s
-/

instance (priority := 500) SetCoe.countable {α} [Countable α] (s : Set α) : Countable s :=
  Subtype.countable
#align set_coe.countable SetCoe.countable

instance [Countable α] [Countable β] : Countable (PSum α β) :=
  Countable.of_equiv (Sum (PLift α) (PLift β)) (Equiv.plift.sumPSum Equiv.plift)

instance [Countable α] [Countable β] : Countable (PProd α β) :=
  Countable.of_equiv (PLift α × PLift β) (Equiv.plift.prodPProd Equiv.plift)

instance [Countable α] [∀ a, Countable (π a)] : Countable (PSigma π) :=
  Countable.of_equiv (Σa : PLift α, PLift (π a.down)) (Equiv.psigmaEquivSigmaPLift π).symm

instance [Finite α] [∀ a, Countable (π a)] : Countable (∀ a, π a) := by
  have : ∀ n, Countable (Fin n → ℕ) := by
    intro n
    induction' n with n ihn
    · change Countable (Fin 0 → ℕ); infer_instance
    · haveI := ihn
      exact Countable.of_equiv (ℕ × (Fin n → ℕ)) (Equiv.piFinSucc _ _).symm
  rcases Finite.exists_equiv_fin α with ⟨n, ⟨e⟩⟩
  -- ⊢ Countable ((a : α) → π a)
  have f := fun a => (nonempty_embedding_nat (π a)).some
  -- ⊢ Countable ((a : α) → π a)
  exact ((Embedding.piCongrRight f).trans (Equiv.piCongrLeft' _ e).toEmbedding).countable
  -- 🎉 no goals

end sort
