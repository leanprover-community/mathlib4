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

- class `ChainCompletePartialOrder` : A nonempty partial order is a chain complete partial order
  such that every nonempty chain has a supremum
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
structure NonemptyChain (α : Type*) [LE α] where
  /-- The underlying set of a non-empty chain -/
  carrier : Set α
  Nonempty' : carrier.Nonempty
  isChain' : IsChain (· ≤ ·) carrier

instance {α : Type} [LE α] : SetLike (NonemptyChain α) α where
  coe := NonemptyChain.carrier
  coe_injective' _ _ := NonemptyChain.ext

/-- A chain complete partial order (CCPO) is a non-empty partial order such that every
nonempty chain has a supremum (which we call `cSup`) -/
class ChainCompletePartialOrder (α : Type) extends PartialOrder α where
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

/-- An admissible set for given `x` and `f` has `x` as a least element and is closed under applying `f` and `cSup`. -/
structure IsAdmissible (x : α) (f : Inflationary α) (s : Set α) : Prop where
  /-- The base point is the least element of an admissible set -/
  base_isLeast : IsLeast s x
  /-- The image of an admissible set under the inflationary function is a subset of itself -/
  image_self_sub_self : f '' s ⊆ s
  /-- If a chain is a subset of an admissible set, its `cSup` is a member of the admissible set -/
  cSup_mem : ∀ (c : NonemptyChain α), ↑c ⊆ s → cSup c ∈ s

lemma ici_isAdmissible : IsAdmissible x f (Ici x) where
  base_isLeast := ⟨le_refl x, fun _ h ↦ h⟩
  image_self_sub_self := by
    rintro _ ⟨y, hy, rfl⟩
    exact le_trans hy (f.le_map _)
  cSup_mem := by
    intro c hc
    have ⟨y, hy⟩ := c.Nonempty'
    apply le_trans (hc hy) (le_cSup _ _ hy)

/-- The bottom admissible set with base point `x` and inflationary function `f` -/
abbrev bot (x : α) (f : Inflationary α) : Set α := ⋂₀ {s | IsAdmissible x f s}

lemma mem_bot_iff {y : α} :
    y ∈ bot x f ↔ ∀ s ∈ {s | IsAdmissible x f s}, y ∈ s := by
  unfold bot
  exact mem_sInter

lemma bot_isAdmissible : IsAdmissible x f (bot x f) where
  base_isLeast := by
    constructor
    · rw [mem_bot_iff]
      exact fun _ h ↦ h.base_isLeast.1
    · intro y hy
      rw [mem_bot_iff] at hy
      exact (hy (Ici x) ici_isAdmissible)
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

lemma subset_bot_iff {s : Set α} (h : IsAdmissible x f s) : s ⊆ bot x f ↔ s = bot x f :=
  subset_antisymm h' (sInter_subset_of_mem h)

/-- `y` is an extreme point for `x : α` and `f : α → α` if it is in the bottom admissible set and `y` is larger than `f z` for any `z < y` in the bottom admissible set.

This definition comes from [serge_lang_algebra] -/
structure IsExtremePt (x : α) (f : Inflationary α) (y : α) : Prop where
  mem_bot : y ∈ bot x f
  map_le_of_mem_of_lt {z : α} (h : z ∈ bot x f) (h' : z < y) : f z ≤ y

lemma map_mem_bot {y : α} (h : y ∈ bot x f) : f y ∈ bot x f := by
  apply bot_isAdmissible.image_self_sub_self
  use y

lemma eq_bot {y : α} (hy : IsExtremePt x f y) : {z ∈ bot x f | z ≤ y ∨ f y ≤ z} = bot x f := by
  apply sub_bot_eq_bot _ (sep_subset _ _)
  apply IsAdmissible.mk
  · constructor
    · exact ⟨bot_isAdmissible.base_isLeast.1, Or.inl (bot_isAdmissible.base_isLeast.2 hy.mem_bot)⟩
    · exact fun y h ↦ bot_isAdmissible.base_isLeast.2 h.1
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

lemma setOf_isExtremePt_eq_bot : {y | IsExtremePt x f y} = bot x f := by
  apply sub_bot_eq_bot _ (fun _ h ↦ h.mem_bot)
  apply IsAdmissible.mk
  · constructor
    · refine ⟨bot_isAdmissible.base_isLeast.1, ?_⟩
      intro y hy hyx
      exfalso
      exact lt_irrefl x (lt_of_le_of_lt (bot_isAdmissible.base_isLeast.2 hy) hyx)
    · exact fun y h ↦ bot_isAdmissible.base_isLeast.2 h.1
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
theorem nonempty_fixedPoints_of_inflationary {α : Type} [Nonempty α] [ChainCompletePartialOrder α]
    (f : Inflationary α) : (fixedPoints f).Nonempty := by
  let x : α := Classical.ofNonempty
  let y : α := cSup (NonemptyChain.mk (bot x f) ⟨x, bot_isAdmissible.base_isLeast.1⟩ (bot_isChain))
  use y
  apply le_antisymm _ (f.le_map y)
  apply le_cSup _ _
  apply bot_isAdmissible.image_self_sub_self
  use y
  exact ⟨bot_isAdmissible.cSup_mem _ (subset_refl _), rfl⟩
