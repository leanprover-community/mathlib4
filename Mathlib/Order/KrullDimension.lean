/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li
-/

import Mathlib.Data.Nat.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.RelSeries
import Mathlib.Order.RelIso.Basic

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

-- Not sure if this definition is useful
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

lemma eq_bot_of_isEmpty [IsEmpty α] : krullDimOfRel r = ⊥ := WithBot.ciSup_empty _

variable {r s}
lemma le_of_map (f : α → β) (map : ∀ (x y : α), r x y → s (f x) (f y)) :
    krullDimOfRel r ≤ krullDimOfRel s :=
  iSup_le $ fun p => le_sSup ⟨p.map _ f map, rfl⟩

lemma eq_of_relIso (f : r ≃r s) : krullDimOfRel r = krullDimOfRel s :=
  le_antisymm (le_of_map f fun _ _ h => f.2.mpr h) $ le_of_map f.symm fun _ _ h => f.2.mp $ by
    convert h <;> exact f.toEquiv.eq_symm_apply.mp rfl

variable (r)
lemma eq_top_of_noTopOrder [Nonempty α] [NoTopOrder (RelSeries r)] :
  krullDimOfRel r = ⊤ :=
le_antisymm le_top $ le_iSup_iff.mpr $ fun m hm => match m, hm with
| ⊥, hm => False.elim $ by
  haveI : Inhabited α := Classical.inhabited_of_nonempty inferInstance
  exact not_le_of_lt (WithBot.bot_lt_coe _ : ⊥ < (0 : WithBot (WithTop ℕ))) $ hm default
| some ⊤, _ => le_refl _
| some (some m), hm => by
  obtain ⟨p, hp⟩ := RelSeries.exists_len_gt_of_noTopOrder r m
  specialize hm p
  refine (not_lt_of_le hm ?_).elim
  erw [WithBot.some_eq_coe, WithBot.coe_lt_coe, WithTop.some_eq_coe, WithTop.coe_lt_coe]
  assumption

lemma eq_len_of_orderTop [OrderTop (RelSeries r)] :
  krullDimOfRel r = (⊤ : RelSeries r).length :=
le_antisymm
  (iSup_le $ fun i => WithBot.coe_le_coe.mpr $ WithTop.coe_le_coe.mpr $ OrderTop.le_top i) $
  le_iSup (fun (i : RelSeries r) => (i.length : WithBot (WithTop ℕ  ))) (⊤ : RelSeries r)

variable {r}
lemma eq_len_of_orderTop' [OrderTop (RelSeries r)]
  (q : RelSeries r) (h : IsTop q) : krullDimOfRel r = q.length :=
(eq_len_of_orderTop r).trans $ RelSeries.top_len_unique r _ h ▸ rfl


end krullDimOfRel

namespace krullDim

variable {α β : Type _}

variable [Preorder α] [Preorder β]

lemma eq_bot_of_isEmpty [IsEmpty α] : krullDim α = ⊥ := krullDimOfRel.eq_bot_of_isEmpty _

lemma eq_top_of_noTopOrder [Nonempty α] [NoTopOrder (LTSeries α)] :
  krullDim α = ⊤ := krullDimOfRel.eq_top_of_noTopOrder _

lemma eq_len_of_orderTop [OrderTop (LTSeries α)] :
  krullDim α = (⊤ : LTSeries α).length := krullDimOfRel.eq_len_of_orderTop _

lemma eq_len_of_orderTop' [OrderTop (LTSeries α)]
  (q : LTSeries α) (h : IsTop q) : krullDim α = q.length :=
krullDimOfRel.eq_len_of_orderTop' _ h

lemma NoTopOrder_of_strictMono (f : α → β) (hf : StrictMono f) [NoTopOrder (LTSeries α)]
  [Nonempty α]: (NoTopOrder (LTSeries β)) where
    exists_not_le := by
      intro smb
      rcases (RelSeries.exists_len_gt_of_noTopOrder ((. < .) : Rel α α) smb.length) with ⟨p, hp⟩
      exact ⟨LTSeries.map p f hf, not_le_of_lt hp⟩

lemma le_of_strictMono (f : α → β) (hf : StrictMono f) : krullDim α ≤ krullDim β :=
  krullDimOfRel.le_of_map f hf

lemma le_of_strictComono_and_surj
  (f : α → β) (hf : StrictComono f) (hf' : Function.Surjective f) :
    krullDim β ≤ krullDim α :=
iSup_le $ λ p ↦ le_sSup ⟨p.comap _ hf hf', rfl⟩

lemma eq_of_OrderIso (f : α ≃o β) : krullDim α = krullDim β := krullDimOfRel.eq_of_relIso
  ⟨f, fun {_ _} => f.lt_iff_lt⟩

lemma eq_iSup_height : krullDim α = ⨆ (a : α), height α a := by
{ refine' le_antisymm (iSup_le $ λ i ↦ le_iSup_of_le (i ⟨i.length, lt_add_one _⟩)
    $ le_sSup ⟨⟨?_, λ m ↦ ⟨i m, i.strictMono.monotone $ by
      rw [show m = ⟨m.1, m.2⟩ by cases m; rfl, Fin.mk_le_mk]; linarith [m.2]⟩,
        λ j ↦ i.step j⟩, rfl⟩) $ iSup_le $ λ a ↦ le_of_strictMono Subtype.val $
          λ _ _ h ↦ h }

lemma le_OrderDual : krullDim α ≤ krullDim αᵒᵈ :=
  iSup_le $ λ i ↦ le_sSup $ ⟨i.rev, rfl⟩

lemma OrderDual_le : krullDim αᵒᵈ ≤ krullDim α :=
  le_OrderDual.trans $ le_of_strictMono
    (OrderDual.ofDual ∘ OrderDual.ofDual) $ λ _ _ h ↦ h

lemma eq_OrderDual : krullDim α = krullDim αᵒᵈ :=
  le_antisymm le_OrderDual $ OrderDual_le

end krullDim
