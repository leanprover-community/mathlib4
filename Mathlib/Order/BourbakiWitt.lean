/-
Copyright (c) 2025 Finn Mortimore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Finn Mortimore
-/
import Mathlib.Order.Preorder.Chain
import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.FixedPoints.Basic

/-!
# Bourbaki-Witt Theorem

This file proves the Bourbaki-Witt Theorem.

## Main definitions

- class `ChainCompletePartialOrder` : A non-empty partial order is a chain complete partial order
  such that every non-empty chain has a supremum
- structure `Inflationary` : Let $X$ be a partial order. A function $f : X → X$ is inflationary if,
  for all $x ∈ X$, $x ≤ f x$

## Main statements

- `bourbaki_witt` : The Bourbaki-Witt Theorem : If $X$ is a chain complete
partial order and $f : X → X$ is inflationary, then $f$ has a fixed point

## References

The proof used can be found in [serge_lang_algebra]
-/

/-- The type of non-empty chains of an order -/
@[ext]
structure NonemptyChain (α : Type) [LE α] where
  /-- The underlying set of a non-empty chain -/
  carrier : Set α
  /-- By definition, a non-empty chain is non-empty -/
  Nonempty' : carrier.Nonempty
  /-- By definition, a non-empty chain is a chain -/
  isChain' : IsChain (· ≤ ·) carrier

instance {α : Type} [LE α] : SetLike (NonemptyChain α) α where
  coe := NonemptyChain.carrier
  coe_injective' _ _ := NonemptyChain.ext

/-- A chain complete partial order is a non-empty partial order such that every chain has a supremum
(which we call `cSup`) -/
class ChainCompletePartialOrder (α : Type) [Nonempty α] extends PartialOrder α where
  /-- The supremum of a non-empty chain -/
  cSup : NonemptyChain α → α
  /-- `cSup` is an upper bound of the non-empty chain -/
  le_cSup (c : NonemptyChain α) (x : α) : x ∈ c.carrier → x ≤ cSup c
  /-- `cSup` is a lower bound of the set of upper bounds of the non-empty chain -/
  cSup_le (c : NonemptyChain α) (x : α) : (∀ y ∈ c.carrier, y ≤ x) → cSup c ≤ x

/-- A function `f : α → α` is inflationary if for all `x : α`, `x ≤ f x` -/
structure Inflationary (α : Type) [PartialOrder α] where
  /-- The underlying function of an inflationary function -/
  toFun : α → α
  /-- The underlying function of an inflationary function is inflationary -/
  le_map (x : α) : x ≤ toFun x

instance {α : Type} [PartialOrder α] : CoeFun (Inflationary α) (fun _ ↦ α → α) where
  coe := Inflationary.toFun

open ChainCompletePartialOrder Set

section

namespace BourbakiWitt

variable {α : Type} [Nonempty α] [ChainCompletePartialOrder α] {x : α} {f : Inflationary α}

/-- The definition of an admissible set with base point `x` and inflationary function `f` -/
structure IsAdmissible (x : α) (f : Inflationary α) (s : Set α) : Prop where
  /-- The base point is a member of an admissible set -/
  base_mem : x ∈ s
  /-- The image of an admissible set under the inflationary function is a subset of itself -/
  image_self_sub_self : f '' s ⊆ s
  /-- If a chain is a subset of an admissible set, its `cSup` is a member of the admissible set -/
  cSup_mem : ∀ (c : NonemptyChain α), ↑c ⊆ s → cSup c ∈ s
  /-- The base point is the least element of an admissible set -/
  base_least : ∀ y ∈ s, x ≤ y

/-- `upset x` is the set of elements `y` such that `x ≤ y` -/
abbrev upset (x : α) : Set α := {y | x ≤ y}

lemma upset_isAdmissible : IsAdmissible x f (upset x) where
  base_mem := le_refl x
  image_self_sub_self := by
    rintro _ ⟨y, hy, rfl⟩
    exact le_trans hy (f.le_map _)
  cSup_mem := by
    intro c hc
    have ⟨y, hy⟩ := c.Nonempty'
    apply le_trans (hc hy) (le_cSup _ _ hy)
  base_least := fun _ h ↦ h

/-- The bottom admissible set with base point `x` and inflationary function `f` -/
abbrev bot (x : α) (f : Inflationary α) : Set α := ⋂₀ {s | IsAdmissible x f s}

lemma mem_bot_iff {y : α} :
    y ∈ bot x f ↔ ∀ s ∈ {s | IsAdmissible x f s}, y ∈ s := by
  unfold bot
  exact mem_sInter

lemma bot_isAdmissible : IsAdmissible x f (bot x f) where
  base_mem := by
    rw [mem_bot_iff]
    exact fun _ h ↦ h.base_mem
  image_self_sub_self := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_bot_iff]
    rintro s hs
    exact hs.image_self_sub_self ⟨y, ⟨mem_sInter.1 hy _ hs, rfl⟩⟩
  cSup_mem := by
    intro c hc
    rw [mem_bot_iff]
    intro s hs
    exact hs.cSup_mem c (subset_trans hc (sInter_subset_of_mem hs))
  base_least := by
    intro y hy
    rw [mem_bot_iff] at hy
    exact (hy (upset x) upset_isAdmissible)

lemma sub_bot_eq_bot {s : Set α} (h : IsAdmissible x f s) (h' : s ⊆ bot x f) : s = bot x f :=
  subset_antisymm h' (sInter_subset_of_mem h)

/-- The definition of an extreme point used in [serge_lang_algebra] -/
structure IsExtremePt (x : α) (f : Inflationary α) (y : α) : Prop where
  /-- By defintion, an extreme point is a member of `bot` -/
  mem_bot : y ∈ bot x f
  /-- By defintion, an extreme point `y` satisfies `f z ≤ y` for all `z < y` -/
  map_le {z : α} (h : z ∈ bot x f) (h' : z < y) : f z ≤ y

lemma map_mem_bot {y : α} (h : y ∈ bot x f) : f y ∈ bot x f := by
  apply bot_isAdmissible.image_self_sub_self
  use y

lemma eq_bot {y : α} (hy : IsExtremePt x f y) : {z ∈ bot x f | z ≤ y ∨ f y ≤ z} = bot x f := by
  apply sub_bot_eq_bot _ (sep_subset _ _)
  apply IsAdmissible.mk
  · exact ⟨bot_isAdmissible.base_mem, Or.inl (bot_isAdmissible.base_least y hy.mem_bot)⟩
  · rintro _ ⟨z, ⟨hz, (hzy | hyz)⟩, rfl⟩ <;>
      refine ⟨map_mem_bot hz, ?_⟩
    · rcases le_iff_lt_or_eq.1 hzy with (hzy | rfl)
      · left; exact hy.map_le hz hzy
      · right; exact le_refl _
    · right; exact le_trans hyz (f.le_map z)
  · intro c hc
    refine ⟨bot_isAdmissible.cSup_mem _ (subset_trans hc (sep_subset _ _)), ?_⟩
    · by_cases h : ∀ z ∈ c, z ≤ y
      · left; apply cSup_le c y h
      · push_neg at h
        rcases h with ⟨z, hz, hzy⟩
        obtain h' := Or.resolve_left (hc hz).2 hzy
        right
        apply le_trans h' (le_cSup _ _ hz)
  · exact fun y h ↦ bot_isAdmissible.base_least y h.1

lemma setOf_isExtremePt_eq_bot : {y | IsExtremePt x f y} = bot x f := by
  apply sub_bot_eq_bot _ (fun _ h ↦ h.mem_bot)
  apply IsAdmissible.mk
  · refine ⟨bot_isAdmissible.base_mem, ?_⟩
    intro y hy hyx
    exfalso
    exact lt_irrefl x (lt_of_le_of_lt (bot_isAdmissible.base_least y hy) hyx)
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨map_mem_bot hy.mem_bot, ?_⟩
    intro z hz hzy
    have hz' := hz
    rw [← eq_bot hy] at hz'
    rcases hz' with ⟨_, (hz' | hz')⟩
    · rcases le_iff_lt_or_eq.1 hz' with (hz' | rfl)
      · exact le_trans (hy.map_le hz hz') (f.le_map y)
      · exact le_refl (f z)
    · exfalso
      exact lt_irrefl z (lt_of_lt_of_le hzy hz')
  · intro c hc
    refine ⟨bot_isAdmissible.cSup_mem _ (subset_trans hc (fun _ h ↦ h.mem_bot)), ?_⟩
    intro y hy hy'
    by_cases h : ∀ z ∈ c, f z ≤ y
    · exfalso
      apply lt_irrefl y (lt_of_lt_of_le hy' ?_)
      apply cSup_le
      intro z hz
      apply le_trans (f.le_map z) (h z hz)
    · push_neg at h
      obtain ⟨z, hz, hzy⟩ := h
      have h := hy
      rw [← eq_bot (hc hz)] at h
      obtain (hyz | rfl) := le_iff_lt_or_eq.1 (Or.resolve_right h.2 hzy)
      · exact le_trans ((hc hz).map_le hy hyz) (le_cSup _ _ hz)
      · have hc' := bot_isAdmissible.cSup_mem _ (subset_trans hc ((fun _ h ↦ h.mem_bot)))
        rw [← eq_bot (hc hz)] at hc'
        obtain ⟨_, (hc' | hc')⟩ := hc'
        · exfalso
          apply lt_irrefl y (lt_of_lt_of_le hy' hc')
        · exact hc'
  · exact fun y h ↦ bot_isAdmissible.base_least y h.1

lemma mem_bot_iff_isExtremePt {y : α} : y ∈ bot x f ↔ IsExtremePt x f y := by
  rw [← setOf_isExtremePt_eq_bot]
  rfl

lemma bot_isChain : IsChain (· ≤ ·) (bot x f) := by
  intro y hy z hz _
  rw [mem_bot_iff_isExtremePt] at hy
  rw [← eq_bot hy] at hz
  obtain ⟨_, (hz | hz)⟩ := hz
  · right; exact hz
  · left; exact le_trans (f.le_map y) hz

end BourbakiWitt

end

open BourbakiWitt Function

/- **The Bourbaki-Witt Theorem**: If `α` is a chain complete partial order and `f : α → α` is
inflationary, then `f` has a fixed point -/
theorem bourbaki_witt {α : Type} [Nonempty α] [ChainCompletePartialOrder α]
    (f : Inflationary α) : (fixedPoints f).Nonempty := by
  let x : α := Classical.ofNonempty
  let y : α := cSup (NonemptyChain.mk (bot x f) ⟨x, bot_isAdmissible.base_mem⟩ (bot_isChain))
  use y
  apply le_antisymm _ (f.le_map y)
  apply le_cSup _ _
  apply bot_isAdmissible.image_self_sub_self
  use y
  exact ⟨bot_isAdmissible.cSup_mem _ (subset_refl _), rfl⟩
