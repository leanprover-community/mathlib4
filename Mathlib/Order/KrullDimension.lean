/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li, Joachim Breitner
-/

import Mathlib.Order.RelSeries
import Mathlib.Data.ENat.Lattice

/-!
# Krull dimension of a preordered set and height of an element

If `α` is a preordered set, then `krullDim α : WithBot ℕ∞` is defined to be
`sup {n | a₀ < a₁ < ... < aₙ}`.

In case that `α` is empty, then its Krull dimension is defined to be negative infinity; if the
length of all series `a₀ < a₁ < ... < aₙ` is unbounded, then its Krull dimension is defined to be
positive infinity.

For `a : α`, its height (in `ℕ∞`) is defined to be `sup {n | a₀ < a₁ < ... < aₙ ≤ a}` while its
coheight is defined to be `sup {n | a ≤ a₀ < a₁ < ... < aₙ}` .

## Main results

* The Krull dimension is the same as that of the dual order (`krullDim_orderDual`).

* The Krull dimension is the supremum of the heights of the elements (`krullDim_eq_iSup_height`).

* The height is monotone.

## Design notes

Krull dimensions are defined to take value in `WithBot ℕ∞` so that `(-∞) + (+∞)` is
also negative infinity. This is because we want Krull dimensions to be additive with respect
to product of varieties so that `-∞` being the Krull dimension of empty variety is equal to
sum of `-∞` and the Krull dimension of any other varieties.

We could generalize the notion of Krull dimension to an arbitrary binary relation; many results
in this file would generalize as well. But we don't think it would be useful, so we only define
Krull dimension of a preorder.
-/

namespace Order

section definitions

/--
The **Krull dimension** of a preorder `α` is the supremum of the rightmost index of all relation
series of `α` ordered by `<`. If there is no series `a₀ < a₁ < ... < aₙ` in `α`, then its Krull
dimension is defined to be negative infinity; if the length of all series `a₀ < a₁ < ... < aₙ` is
unbounded, its Krull dimension is defined to be positive infinity.
-/
noncomputable def krullDim (α : Type*) [Preorder α] : WithBot ℕ∞ :=
  ⨆ (p : LTSeries α), p.length

/--
The **height** of an element `a` in a preorder `α` is the supremum of the rightmost index of all
relation series of `α` ordered by `<` and ending below or at `a`.
-/
noncomputable def height {α : Type*} [Preorder α] (a : α) : ℕ∞ :=
  ⨆ (p : LTSeries α) (_ : p.last ≤ a), p.length

/--
The **coheight** of an element `a` in a preorder `α` is the supremum of the rightmost index of all
relation series of `α` ordered by `<` and beginning with `a`.

The definition of `coheight` is via the `height` in the dual order, in order to easily transfer
theorems between `height` and `coheight`.
-/
noncomputable def coheight {α : Type*} [Preorder α] (a : α) : ℕ∞ := height (α := αᵒᵈ) a

end definitions

/-!
## Height
-/

section height

variable {α β : Type*}

variable [Preorder α] [Preorder β]

lemma height_le_iff {a : α} {n : ℕ∞} :
    height a ≤ n ↔ ∀ ⦃p : LTSeries α⦄, p.last ≤ a → p.length ≤ n := by
 rw [height, iSup₂_le_iff]

lemma height_le {a : α} {n : ℕ∞} (h : ∀ (p : LTSeries α), p.last = a → p.length ≤ n) :
    height a ≤ n := by
  apply height_le_iff.mpr
  intro p hlast
  wlog hlenpos : p.length ≠ 0
  · simp_all
  -- We replace the last element in the series with `a`
  let p' := p.eraseLast.snoc a (lt_of_lt_of_le (p.eraseLast_last_rel_last (by simp_all)) hlast)
  rw [show p.length = p'.length by simp [p']; omega]
  apply h
  simp [p']

lemma height_le_iff' {a : α} {n : ℕ∞} :
    height a ≤ n ↔ ∀ ⦃p : LTSeries α⦄, p.last = a → p.length ≤ n := by
 constructor
 · rw [height_le_iff]
   exact fun h p hlast => h (le_of_eq hlast)
 · exact height_le

/--
Alternative definition of height, with the supremum ranging only over those series that end at `a`.
-/
lemma height_eq_iSup_last_eq (a : α) :
    height a = ⨆ (p : LTSeries α) (_ : p.last = a), ↑(p.length) := by
  apply eq_of_forall_ge_iff
  intro n
  rw [height_le_iff', iSup₂_le_iff]

lemma length_le_height {p : LTSeries α} {x : α} (hlast : p.last ≤ x) :
    p.length ≤ height x := by
  by_cases hlen0 : p.length ≠ 0
  · let p' := p.eraseLast.snoc x (by
      apply lt_of_lt_of_le
      · apply p.step ⟨p.length - 1, by omega⟩
      · convert hlast
        simp only [Fin.succ_mk, Nat.succ_eq_add_one, RelSeries.last, Fin.last]
        congr; omega)
    suffices p'.length ≤ height x by
      simp [p'] at this
      convert this
      norm_cast
      omega
    refine le_iSup₂_of_le p' ?_ le_rfl
    simp [p']
  · simp_all

/--
The height of the last element in a series is larger or equal to the length of the series.
-/
lemma length_le_height_last {p : LTSeries α} : p.length ≤ height p.last :=
  length_le_height le_rfl

/--
The height of an element in a series is larger or equal to its index in the series.
-/
lemma index_le_height (p : LTSeries α) (i : Fin (p.length + 1)) : i ≤ height (p i) :=
  length_le_height_last (p := p.take i)

/--
In a maximally long series, i.e one as long as the height of the last element, the height of each
element is its index in the series.
-/
lemma height_eq_index_of_length_eq_height_last {p : LTSeries α} (h : p.length = height p.last)
    (i : Fin (p.length + 1)) : height (p i) = i := by
  refine le_antisymm (height_le ?_) (index_le_height p i)
  intro p' hp'
  have hp'' := length_le_height_last (p := p'.smash (p.drop i) (by simpa))
  simp [← h] at hp''; clear h
  norm_cast at *
  omega

lemma height_mono : Monotone (α := α) height :=
  fun _ _ hab ↦ biSup_mono (fun _ hla => hla.trans hab)

@[gcongr] protected lemma _root_.GCongr.height_le_height (a b : α) (hab : a ≤ b) :
    height a ≤ height b := height_mono hab

end height

/-!
## Krull dimension
-/

section krullDim

variable {α β : Type*}

variable [Preorder α] [Preorder β]

lemma krullDim_nonneg_of_nonempty [Nonempty α] : 0 ≤ krullDim α :=
  le_sSup ⟨⟨0, fun _ ↦ @Nonempty.some α inferInstance, fun f ↦ f.elim0⟩, rfl⟩

/-- A definition of krullDim for nonempty `α` that avoids `WithBot` -/
lemma krullDim_eq_iSup_length [Nonempty α] :
    krullDim α = ⨆ (p : LTSeries α), (p.length : ℕ∞) := by
  unfold krullDim
  rw [WithBot.coe_iSup (OrderTop.bddAbove _)]
  rfl

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

@[simp] lemma krullDim_orderDual : krullDim αᵒᵈ = krullDim α :=
  le_antisymm (iSup_le fun i ↦ le_sSup ⟨i.reverse, rfl⟩) <|
    iSup_le fun i ↦ le_sSup ⟨i.reverse, rfl⟩

/--
The Krull dimension is the supremum of the elements' heights.
-/
lemma krullDim_eq_iSup_height : krullDim α = ⨆ (a : α), ↑(height a) := by
  cases isEmpty_or_nonempty α with
  | inl h => simp [krullDim_eq_bot_of_isEmpty]
  | inr h =>
    rw [← WithBot.coe_iSup (OrderTop.bddAbove _)]
    apply le_antisymm
    · apply iSup_le
      intro p
      suffices p.length ≤ ⨆ (a : α), height a by
        exact (WithBot.unbot'_le_iff fun _ => this).mp this
      apply le_iSup_of_le p.last (length_le_height_last (p := p))
    · rw [krullDim_eq_iSup_length]
      simp only [WithBot.coe_le_coe, iSup_le_iff]
      intro x
      exact height_le fun p _ ↦ le_iSup_of_le p le_rfl

end krullDim

end Order
