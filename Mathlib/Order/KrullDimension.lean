/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li
-/

import Mathlib.Order.RelSeries
import Mathlib.Order.WithBot
import Mathlib.Data.Nat.Lattice

/-!
# Krull dimension of a preordered set

If `α` is a preordered set, then `krullDim α` is defined to be `sup {n | a₀ < a₁ < ... < aₙ}`.
In case that `α` is empty, then its Krull dimension is defined to be negative infinity; if the
length of all series `a₀ < a₁ < ... < aₙ` is unbounded, then its Krull dimension is defined to
be positive infinity.

For `a : α`, its height is defined to be the krull dimension of the subset `(-∞, a]` while its
coheight is defined to be the krull dimension of `[a, +∞)`.

## Implementation notes
Krull dimensions are defined to take value in `WithBot (WithTop ℕ)` so that `(-∞) + (+∞)` is
also negative infinity. This is because we want Krull dimensions to be additive with respect
to product of varieties so that `-∞` being the Krull dimension of empty variety is equal to
sum of `-∞` and the Krull dimension of any other varieties.

We could generalize the notion of Krull dimension to an arbitrary binary relation; many results
in this file would generalize as well. But we don't think it would be useful, so we only define
Krull dimension of a preorder.
-/

section definitions

variable (α : Type*) [Preorder α]

/--
The **Krull dimension** of a preorder `α` is the supremum of the rightmost index of all relation
series of `α` order by `<`. If there is no series `a₀ < a₁ < ... < aₙ` in `α`, then its Krull
dimension is defined to be negative infinity; if the length of all series `a₀ < a₁ < ... < aₙ` is
unbounded, its Krull dimension is defined to be positive infinity.
-/
noncomputable def krullDim : WithBot (WithTop ℕ) :=
  ⨆ (p : LTSeries α), p.length

/--
Height of an element `a` of a preordered set `α` is the Krull dimension of the subset `(-∞, a]`
-/
noncomputable def height (a : α) : WithBot (WithTop ℕ) := krullDim (Set.Iic a)

/--
Coheight of an element `a` of a pre-ordered set `α` is the Krull dimension of the subset `[a, +∞)`
-/
noncomputable def coheight (a : α) : WithBot (WithTop ℕ) := krullDim (Set.Ici a)

end definitions

section krullDim

variable {α β : Type*}

variable [Preorder α] [Preorder β]

lemma krullDim_nonneg_of_nonempty [Nonempty α] : 0 ≤ krullDim α :=
  le_sSup ⟨⟨0, fun _ ↦ @Nonempty.some α inferInstance, fun f ↦ f.elim0⟩, rfl⟩

lemma krullDim_eq_bot_of_isEmpty [IsEmpty α] : krullDim α = ⊥ := WithBot.ciSup_empty _

lemma krullDim_eq_top_of_infiniteDimensionalOrder [InfiniteDimensionalOrder α] :
    krullDim α = ⊤ :=
  le_antisymm le_top <| le_iSup_iff.mpr <| fun m hm ↦ match m, hm with
  | ⊥, hm => False.elim <| by
    haveI : Inhabited α := ⟨LTSeries.withLength _ 0 0⟩
    exact not_le_of_lt (WithBot.bot_lt_coe _ : ⊥ < (0 : WithBot (WithTop ℕ))) <| hm default
  | some ⊤, _ => le_refl _
  | some (some m), hm => by
    refine (not_lt_of_le (hm (LTSeries.withLength _ (m + 1))) ?_).elim
    erw [WithBot.coe_lt_coe, WithTop.coe_lt_coe]
    simp

lemma krullDim_le_of_strictMono (f : α → β) (hf : StrictMono f) : krullDim α ≤ krullDim β :=
  iSup_le <| fun p ↦ le_sSup ⟨p.map f hf, rfl⟩

lemma height_mono {a b : α} (h : a ≤ b) : height α a ≤ height α b :=
  krullDim_le_of_strictMono (fun x ↦ ⟨x, le_trans x.2 h⟩) <| fun _ _ ↦ id

lemma krullDim_eq_length_of_finiteDimensionalOrder [FiniteDimensionalOrder α] :
    krullDim α = (LTSeries.longestOf α).length :=
  le_antisymm
    (iSup_le <| fun _ ↦ WithBot.coe_le_coe.mpr <| WithTop.coe_le_coe.mpr <|
      RelSeries.length_le_length_longestOf _ _) <|
    le_iSup (fun (i : LTSeries _) ↦ (i.length : WithBot (WithTop ℕ))) <| LTSeries.longestOf _

lemma krullDim_eq_zero_of_unique [Unique α] : krullDim α = 0 := by
  rw [krullDim_eq_length_of_finiteDimensionalOrder (α := α), Nat.cast_eq_zero]
  refine (LTSeries.longestOf_len_unique (default : LTSeries α) fun q ↦ show _ ≤ 0 from ?_).symm
  by_contra r
  exact ne_of_lt (q.step ⟨0, not_le.mp r⟩) <| Subsingleton.elim _ _

lemma krullDim_le_of_strictComono_and_surj
    (f : α → β) (hf : ∀ ⦃a b⦄, f a < f b → a < b) (hf' : Function.Surjective f) :
    krullDim β ≤ krullDim α :=
  iSup_le fun p ↦ le_sSup ⟨p.comap _ hf hf', rfl⟩

lemma krullDim_eq_of_orderIso (f : α ≃o β) : krullDim α = krullDim β :=
  le_antisymm (krullDim_le_of_strictMono _ f.strictMono) <|
    krullDim_le_of_strictMono _ f.symm.strictMono

lemma krullDim_eq_iSup_height : krullDim α = ⨆ (a : α), height α a :=
  le_antisymm
    (iSup_le fun i ↦ le_iSup_of_le (i ⟨i.length, lt_add_one _⟩) <|
    le_sSup ⟨⟨_, fun m ↦ ⟨i m, i.strictMono.monotone <| show m.1 ≤ i.length by omega⟩,
      i.step⟩, rfl⟩) <|
    iSup_le fun a ↦ krullDim_le_of_strictMono Subtype.val fun _ _ h ↦ h

@[simp] lemma krullDim_orderDual : krullDim αᵒᵈ = krullDim α :=
  le_antisymm (iSup_le fun i ↦ le_sSup ⟨i.reverse, rfl⟩) <|
    iSup_le fun i ↦ le_sSup ⟨i.reverse, rfl⟩

end krullDim
