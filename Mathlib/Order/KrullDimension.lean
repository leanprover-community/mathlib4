/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li
-/

import Mathlib.Order.RelSeries
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.WithBot
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.Module.LocalizedModule
import Mathlib.Order.ConditionallyCompleteLattice.Basic

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

/--
A function `f : α → β` is said to be strictly comonotonic (dual to strictly monotonic)
if and only if `a < b` is implied by `f a < f b` for all `a, b : β`.
-/
def strictComono (f : α → β) : Prop := ∀ ⦃a b⦄, f a < f b → a < b

lemma krull_dim_eq_bot_of_is_empty [IsEmpty α] : krullDim α = ⊥ :=
  WithBot.ciSup_empty _

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

lemma krullDim_le_of_strictMono (f : α → β) (hf : StrictMono f) : krullDim α ≤ krullDim β :=
  iSup_le $ λ p ↦ le_sSup ⟨p.map f hf, rfl⟩

lemma le_of_strictMono (f : α → β) (hf : StrictMono f) : krullDim α ≤ krullDim β :=
  krullDimOfRel.le_of_map f hf

lemma krullDim_le_of_strictComono_and_surj
  (f : α → β) (hf : strictComono f) (hf' : Function.Surjective f) :
    krullDim β ≤ krullDim α :=
iSup_le $ λ p ↦ le_sSup ⟨p.comap _ hf hf', rfl⟩

lemma krullDim_eq_of_OrderIso (f : α ≃o β) : krullDim α = krullDim β :=
  le_antisymm (krullDim_le_of_strictMono f f.strictMono) $ krullDim_le_of_strictComono_and_surj
    f (λ _ _ h ↦ Iff.mp (map_lt_map_iff f) h) f.surjective

lemma krullDim_eq_iSup_height : krullDim α = ⨆ (a : α), height α a := by
{ refine' le_antisymm (iSup_le $ λ i ↦ le_iSup_of_le (i ⟨i.length, lt_add_one _⟩)
    $ le_sSup ⟨⟨?_, λ m ↦ ⟨i m, i.strictMono.monotone $ by
      rw [show m = ⟨m.1, m.2⟩ by cases m; rfl, Fin.mk_le_mk]; linarith [m.2]⟩,
        λ j ↦ i.step j⟩, rfl⟩) $ iSup_le $ λ a ↦ krullDim_le_of_strictMono Subtype.val $
          λ _ _ h ↦ h }

end krullDim
