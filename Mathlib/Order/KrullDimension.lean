/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
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
-/

section definitions

variable {β : Type _} (r : Rel β β)
variable (α : Type _) [Preorder α]

/--
Krull dimension of a set `α` with a binary relation `r` is the supremum of the rightmost index of
all relation series of `r`. If there is no relation series `a₀, a₁, ..., aₙ` in `α`, then its Krull
dimension is defined to be negative infinity; if the length of all relation series `a₀, a₁, ..., aₙ`
is unbounded, its Krull dimension is defined to be positive infinity. (Not sure if this definition
is useful.)
-/
noncomputable def krullDimOfRel : WithBot (WithTop ℕ) :=
  ⨆ (p : RelSeries r), p.length

/--
Krull dimension of a preorder `α` is the supremum of the rightmost index of all relation
series of `α` order by `<`. If there is no series `a₀ < a₁ < ... < aₙ` in `α`, then its Krull
dimension is defined to be negative infinity; if the length of all series `a₀ < a₁ < ... < aₙ` is
unbounded, its Krull dimension is defined to be positive infinity.
-/
noncomputable def krullDim : WithBot (WithTop ℕ) :=
  ⨆ (p : LTSeries α), p.length

lemma krullDim_eq_krullDimOfRel : krullDim α = krullDimOfRel (. < . : α → _) := rfl

/--
Height of an element `a` of a preordered set `α` is the Krull dimension of the subset `(-∞, a]`
-/
noncomputable def height (a : α) : WithBot (WithTop ℕ) := krullDim (Set.Iic a)

/--
Coheight of an element `a` of a pre-ordered set `α` is the Krull dimension of the subset `[a, +∞)`
-/
noncomputable def coheight (a : α) : WithBot (WithTop ℕ) := krullDim (Set.Ici a)

end definitions

namespace krullDimOfRel

variable {α β : Type _} (r : Rel α α) (s : Rel β β)

lemma nonneg_of_Nonempty [Nonempty α] : 0 ≤ krullDimOfRel r :=
  le_sSup ⟨⟨0, λ _ ↦ @Nonempty.some α inferInstance, λ f ↦ False.elim $
    Nat.le_lt_antisymm (Nat.zero_le ↑f) f.2⟩, rfl⟩

lemma eq_bot_of_isEmpty [IsEmpty α] : krullDimOfRel r = ⊥ := WithBot.ciSup_empty _

variable {r s}
lemma le_of_map (f : α → β) (map : ∀ (x y : α), r x y → s (f x) (f y)) :
    krullDimOfRel r ≤ krullDimOfRel s :=
  iSup_le $ fun p => le_sSup ⟨p.map _ f map, rfl⟩

lemma eq_of_relIso (f : r ≃r s) : krullDimOfRel r = krullDimOfRel s :=
  le_antisymm (le_of_map f fun _ _ h => f.2.mpr h) $ le_of_map f.symm fun _ _ h => f.2.mp $ by
    convert h <;> exact f.toEquiv.eq_symm_apply.mp rfl

variable (r)
lemma eq_top_of_infiniteDimensional [r.InfiniteDimensional] :
  krullDimOfRel r = ⊤ :=
le_antisymm le_top $ le_iSup_iff.mpr $ fun m hm => match m, hm with
| ⊥, hm => False.elim $ by
  haveI : Inhabited α := ⟨RelSeries.withLength r 0 0⟩
  exact not_le_of_lt (WithBot.bot_lt_coe _ : ⊥ < (0 : WithBot (WithTop ℕ))) $ hm default
| some ⊤, _ => le_refl _
| some (some m), hm => by
  obtain ⟨p, hp⟩ := RelSeries.exists_len_gt_of_infiniteDimensional r m
  specialize hm p
  refine (not_lt_of_le hm ?_).elim
  erw [WithBot.coe_lt_coe, WithTop.coe_lt_coe]
  assumption

lemma eq_len_of_finiteDimensional [r.FiniteDimensional] :
  krullDimOfRel r = (RelSeries.longestOf r).length :=
le_antisymm
  (iSup_le $ fun _ => WithBot.coe_le_coe.mpr $ WithTop.coe_le_coe.mpr $
    RelSeries.length_le_length_longestOf _ _) $
  le_iSup (fun (i : RelSeries r) => (i.length : WithBot (WithTop ℕ))) $ RelSeries.longestOf _

end krullDimOfRel

namespace krullDim

variable {α β : Type _}

variable [Preorder α] [Preorder β]

lemma nonneg_of_Nonempty [Nonempty α] : 0 ≤ krullDim α :=
  krullDimOfRel.nonneg_of_Nonempty _

lemma eq_bot_of_isEmpty [IsEmpty α] : krullDim α = ⊥ := krullDimOfRel.eq_bot_of_isEmpty _

lemma eq_top_of_infiniteDimensionalType [InfiniteDimensionalOrder α] :
  krullDim α = ⊤ := krullDimOfRel.eq_top_of_infiniteDimensional _

lemma eq_len_of_finiteDimensionalType [FiniteDimensionalOrder α] :
  krullDim α = (LTSeries.longestOf α).length := krullDimOfRel.eq_len_of_finiteDimensional _

/-- If `f : α → β` is a strictly monotonic function and `α` is an infinite dimensional type then so
  is `β`. -/
lemma infiniteDimensional_of_strictMono
    (f : α → β) (hf : StrictMono f) [InfiniteDimensionalOrder α] :
    InfiniteDimensionalOrder β :=
  ⟨fun n ↦ ⟨(LTSeries.withLength _ n).map f hf, LTSeries.length_withLength α n⟩⟩
  -- longRelSeries := λ n ↦ LTSeries.map (h.longRelSeries n) f hf
  -- longRelSeries_length := λ n ↦ h.longRelSeries_length n

lemma eq_zero_of_unique [Unique α] : krullDim α = 0 := by
  rw [eq_len_of_finiteDimensionalType, Nat.cast_eq_zero]
  refine (LTSeries.longestOf_len_unique (default : LTSeries α) fun q ↦ show _ ≤ 0 from ?_).symm
  by_contra r
  rw [not_le] at r
  exact ne_of_lt (q.step ⟨0, r⟩) <| Subsingleton.elim _ _

lemma le_of_strictMono (f : α → β) (hf : StrictMono f) : krullDim α ≤ krullDim β :=
  krullDimOfRel.le_of_map f hf

lemma height_mono {a b : α} (h : a ≤ b) : height α a ≤ height α b :=
  le_of_strictMono (λ x ↦ ⟨x, le_trans x.2 h⟩) $ λ _ _ h ↦ h

lemma le_of_strictComono_and_surj
  (f : α → β) (hf : StrictComono f) (hf' : Function.Surjective f) :
    krullDim β ≤ krullDim α :=
iSup_le $ λ p ↦ le_sSup ⟨p.comap _ hf hf', rfl⟩

lemma eq_of_orderIso (f : α ≃o β) : krullDim α = krullDim β := krullDimOfRel.eq_of_relIso
  ⟨f, fun {_ _} => f.lt_iff_lt⟩

lemma eq_iSup_height : krullDim α = ⨆ (a : α), height α a := by
{ refine' le_antisymm (iSup_le $ λ i ↦ le_iSup_of_le (i ⟨i.length, lt_add_one _⟩)
    $ le_sSup ⟨⟨?_, λ m ↦ ⟨i m, i.strictMono.monotone $ by
      rw [show m = ⟨m.1, m.2⟩ by cases m; rfl, Fin.mk_le_mk]; linarith [m.2]⟩,
        λ j ↦ i.step j⟩, rfl⟩) $ iSup_le $ λ a ↦ le_of_strictMono Subtype.val $
          λ _ _ h ↦ h }

lemma le_orderDual : krullDim α ≤ krullDim αᵒᵈ :=
  iSup_le $ λ i ↦ le_sSup $ ⟨i.rev, rfl⟩

lemma orderDual_le : krullDim αᵒᵈ ≤ krullDim α :=
  le_orderDual.trans $ le_of_strictMono
    (OrderDual.ofDual ∘ OrderDual.ofDual) $ λ _ _ h ↦ h

lemma eq_orderDual : krullDim α = krullDim αᵒᵈ :=
  le_antisymm le_orderDual $ orderDual_le

end krullDim
