/-
Copyright (c) 2024 Ira Fesefeldt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ira Fesefeldt
-/
module

public import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Ordinal Approximants for the Fixed points on complete lattices

This file sets up the ordinal-indexed approximation theory of fixed points
of a monotone function in a complete lattice [Cousot1979].
The proof follows loosely the one from [Echenique2005].

However, the proof given here is not constructive as we use the non-constructive axiomatization of
ordinals from mathlib. It still allows an approximation scheme indexed over the ordinals.

## Main definitions

* `OrdinalApprox.lfpApprox`: The ordinal-indexed approximation of the least fixed point
  greater or equal than an initial value of a bundled monotone function.
* `OrdinalApprox.gfpApprox`: The ordinal-indexed approximation of the greatest fixed point
  less or equal than an initial value of a bundled monotone function.

## Main theorems
* `OrdinalApprox.lfp_mem_range_lfpApprox`: The ordinal-indexed approximation of
  the least fixed point eventually reaches the least fixed point
* `OrdinalApprox.gfp_mem_range_gfpApprox`: The ordinal-indexed approximation of
  the greatest fixed point eventually reaches the greatest fixed point

## References
* [F. Echenique, *A short and constructive proof of Tarski’s fixed-point theorem*][Echenique2005]
* [P. Cousot & R. Cousot, *Constructive Versions of Tarski's Fixed Point Theorems*][Cousot1979]

## Tags

fixed point, complete lattice, monotone function, ordinals, approximation
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace Cardinal

universe u
variable {α : Type u}
variable (g : Ordinal → α)

open Cardinal Ordinal SuccOrder Function Set

theorem not_injective_limitation_set : ¬ InjOn g (Iio (ord <| succ #α)) := by
  intro h_inj
  have h := lift_mk_le_lift_mk_of_injective <| injOn_iff_injective.1 h_inj
  have mk_initialSeg_subtype :
      #(Iio (ord <| succ #α)) = lift.{u + 1} (succ #α) := by
    simpa only [coe_setOf, card_typein, card_ord] using mk_Iio_ordinal (ord <| succ #α)
  rw [mk_initialSeg_subtype, lift_lift, lift_le] at h
  exact not_le_of_gt (Order.lt_succ #α) h

end Cardinal

namespace OrdinalApprox

universe u
variable {α : Type u}
variable [CompleteLattice α] (f : α →o α) {x : α} {a b c : Ordinal.{u}}

open Function fixedPoints Cardinal Order OrderHom

variable (x) in
/-- The ordinal-indexed sequence approximating the least fixed point greater than
an initial value `x`. It is defined in such a way that we have `lfpApprox 0 x = x` and
`lfpApprox a x = ⨆ b < a, f (lfpApprox b x)`. -/
def lfpApprox (a : Ordinal.{u}) : α :=
  x ⊔ ⨆ b < a, f (lfpApprox b)
termination_by a

theorem lfpApprox_mono_right : Monotone (lfpApprox f x) := by
  intro a b h
  rw [lfpApprox, lfpApprox]
  apply sup_le_sup_left (iSup₂_mono' _)
  grind

@[deprecated (since := "2026-03-30")] alias lfpApprox_monotone := lfpApprox_mono_right

theorem lfpApprox_zero : lfpApprox f x 0 = x := by
  rw [lfpApprox]
  simp

theorem le_lfpApprox {a : Ordinal} : x ≤ lfpApprox f x a := by
  rw [lfpApprox]
  exact le_sup_left

theorem apply_lfpApprox_le_lfpApprox_of_lt {a b : Ordinal} (h : a < b) :
    f (lfpApprox f x a) ≤ lfpApprox f x b := by
  nth_rw 2 [lfpApprox]
  exact le_sup_of_le_right <| le_iSup₂_of_le a h le_rfl

theorem lfpApprox_add_one (hx : x ≤ f x) (a : Ordinal) :
    lfpApprox f x (a + 1) = f (lfpApprox f x a) := by
  apply (apply_lfpApprox_le_lfpApprox_of_lt f (lt_add_one a)).antisymm'
  rw [lfpApprox]
  apply sup_le <| hx.trans (f.mono (le_lfpApprox f))
  simpa using fun i h ↦ f.monotone.comp (lfpApprox_mono_right f) h

theorem lfpApprox_of_isSuccLimit {a : Ordinal} (ha : Order.IsSuccLimit a) :
    lfpApprox f x a = ⨆ b : Set.Iio a, lfpApprox f x b := by
  apply (iSup_le fun b => lfpApprox_mono_right f b.2.le).antisymm'
  rw [lfpApprox, sup_le_iff, iSup_le_iff]
  constructor
  · refine le_iSup_of_le ⟨0, ha.bot_lt⟩ (by simp [lfpApprox_zero])
  · exact fun b => iSup_mono' fun hab => ⟨⟨b + 1, ha.succ_lt hab⟩, (by
    simpa using apply_lfpApprox_le_lfpApprox_of_lt f (lt_add_one b))⟩

theorem lfpApprox_mono_left : Monotone (lfpApprox : (α →o α) → _) := by
  intro f g h x a
  induction a using WellFoundedLT.induction with | ind i IH
  rw [lfpApprox, lfpApprox]
  exact sup_le_sup_left (iSup₂_mono fun j hj ↦ (f.mono (IH j hj)).trans (h _)) _

theorem lfpApprox_mono_mid : Monotone (lfpApprox f) := by
  intro x₁ x₂ h a
  induction a using WellFoundedLT.induction with | ind i IH
  rw [lfpApprox, lfpApprox]
  exact sup_le_sup h <| iSup₂_mono fun j hj ↦ f.mono (IH j hj)

/-- The approximations of the least fixed point stabilize at a fixed point of `f` -/
theorem lfpApprox_eq_of_mem_fixedPoints (hab : a ≤ b)
    (hf : lfpApprox f x a ∈ fixedPoints f) : lfpApprox f x b = lfpApprox f x a := by
  rw [mem_fixedPoints_iff] at hf
  induction b using WellFoundedLT.induction with | ind b IH
  apply (lfpApprox_mono_right f hab).antisymm'
  rw [lfpApprox]
  apply sup_le (le_lfpApprox ..)
  rw [iSup₂_le_iff]
  intro i hi
  by_cases! hi' : i < a
  · exact apply_lfpApprox_le_lfpApprox_of_lt f hi'
  · simp [IH i hi hi', hf]

variable (x) in
/-- There are distinct indices smaller than the successor of the domain's cardinality
yielding the same value -/
theorem exists_lfpApprox_eq_lfpApprox : ∃ a < ord <| succ #α, ∃ b < ord <| succ #α,
    a ≠ b ∧ lfpApprox f x a = lfpApprox f x b := by
  have h_ninj := not_injective_limitation_set <| lfpApprox f x
  rw [Set.injOn_iff_injective, Function.not_injective_iff] at h_ninj
  let ⟨a, b, h_fab, h_nab⟩ := h_ninj
  use a.val; apply And.intro a.prop
  use b.val; apply And.intro b.prop
  apply And.intro
  · intro h_eq; rw [Subtype.coe_inj] at h_eq; exact h_nab h_eq
  · exact h_fab

/-- If the sequence of ordinal-indexed approximations takes a value twice,
then it actually stabilised at that value. -/
lemma lfpApprox_mem_fixedPoints_of_eq (hx : x ≤ f x) (hab : a < b) (hac : a ≤ c)
    (hf : lfpApprox f x a = lfpApprox f x b) : lfpApprox f x c ∈ fixedPoints f := by
  have H : lfpApprox f x a ∈ fixedPoints f := by
    rw [mem_fixedPoints_iff, ← lfpApprox_add_one f hx]
    exact (lfpApprox_mono_right f).eq_of_ge_of_le
      hf (lt_add_one a).le (add_one_le_of_lt hab)
  rwa [lfpApprox_eq_of_mem_fixedPoints f hac H]

/-- The approximation at the index of the successor of the domain's cardinality is a fixed point -/
theorem lfpApprox_ord_mem_fixedPoint (hx : x ≤ f x) :
    lfpApprox f x (ord <| succ #α) ∈ fixedPoints f := by
  let ⟨a, ha, b, hb, hne, hf⟩ := exists_lfpApprox_eq_lfpApprox f x
  cases le_total a b with
  | inl hab => exact lfpApprox_mem_fixedPoints_of_eq f hx (hne.lt_of_le hab) ha.le hf
  | inr hba => exact lfpApprox_mem_fixedPoints_of_eq f hx (hne.symm.lt_of_le hba) hb.le hf.symm

/-- Every value of the approximation is less or equal than every fixed point of `f`
greater or equal than the initial value -/
theorem lfpApprox_le_of_mem_fixedPoints {a : α}
    (ha : a ∈ fixedPoints f) (hxa : x ≤ a) (i : Ordinal) : lfpApprox f x i ≤ a := by
  induction i using WellFoundedLT.induction with | ind i IH
  rw [lfpApprox]
  apply sup_le hxa
  rw [iSup₂_le_iff, ← ha.eq]
  exact fun y hy ↦ f.mono (IH y hy)

/-- The approximation sequence converges at the successor of the domain's cardinality
to the least fixed point if starting from `⊥` -/
theorem lfpApprox_ord_eq_lfp : lfpApprox f ⊥ (ord <| succ #α) = f.lfp := by
  apply le_antisymm
  · have h_lfp : ∃ y : fixedPoints f, f.lfp = y := by use ⊥; exact rfl
    let ⟨y, h_y⟩ := h_lfp; rw [h_y]
    exact lfpApprox_le_of_mem_fixedPoints f y.2 bot_le (ord <| succ #α)
  · have h_fix : ∃ y : fixedPoints f, lfpApprox f ⊥ (ord <| succ #α) = y := by
      simpa only [Subtype.exists, mem_fixedPoints, exists_prop, exists_eq_right'] using
        lfpApprox_ord_mem_fixedPoint f bot_le
    let ⟨x, h_x⟩ := h_fix; rw [h_x]
    exact lfp_le_fixed f x.prop

/-- Some approximation of the least fixed point starting from `⊥` is the least fixed point. -/
theorem lfp_mem_range_lfpApprox : f.lfp ∈ Set.range (lfpApprox f ⊥) := by
  use ord <| succ #α
  exact lfpApprox_ord_eq_lfp f

variable (x) in
/-- The ordinal-indexed sequence approximating the greatest fixed point greater than
an initial value `x`. It is defined in such a way that we have `gfpApprox 0 x = x` and
`gfpApprox a x = ⨅ b < a, f (lfpApprox b x)`. -/
def gfpApprox (a : Ordinal.{u}) : α :=
  x ⊓ ⨅ b < a, f (gfpApprox b)
termination_by a

-- By unsealing these recursive definitions we can relate them
-- by definitional equality
unseal gfpApprox lfpApprox

theorem gfpApprox_zero : gfpApprox f x 0 = x := by
  exact lfpApprox_zero f.dual

theorem gfpApprox_anti_right : Antitone (gfpApprox f x) :=
  lfpApprox_mono_right f.dual

@[deprecated (since := "2026-03-30")] alias gfpApprox_antitone := gfpApprox_anti_right

theorem gfpApprox_le {a : Ordinal} : gfpApprox f x a ≤ x :=
  le_lfpApprox f.dual

theorem gfpApprox_add_one (hx : f x ≤ x) (a : Ordinal) :
    gfpApprox f x (a + 1) = f (gfpApprox f x a) :=
  lfpApprox_add_one f.dual hx a

theorem gfpApprox_le_apply_gfpApprox_of_lt {a b : Ordinal} (h : a < b) :
    gfpApprox f x b ≤ f (gfpApprox f x a) :=
  apply_lfpApprox_le_lfpApprox_of_lt f.dual h

theorem gfpApprox_of_isSuccLimit {a : Ordinal} (ha : Order.IsSuccLimit a) :
    gfpApprox f x a = ⨅ b : Set.Iio a, gfpApprox f x b :=
  lfpApprox_of_isSuccLimit f.dual ha

theorem gfpApprox_mono_left : Monotone (gfpApprox : (α →o α) → _) := by
  intro f g h
  have : g.dual ≤ f.dual := h
  exact lfpApprox_mono_left this

theorem gfpApprox_mono_mid : Monotone (gfpApprox f) :=
  fun _ _ h => lfpApprox_mono_mid f.dual h

/-- The approximations of the greatest fixed point stabilize at a fixed point of `f` -/
theorem gfpApprox_eq_of_mem_fixedPoints {a b : Ordinal} (h_ab : a ≤ b)
    (h : gfpApprox f x a ∈ fixedPoints f) : gfpApprox f x b = gfpApprox f x a :=
  lfpApprox_eq_of_mem_fixedPoints f.dual h_ab h

/-- There are distinct indices smaller than the successor of the domain's cardinality
yielding the same value -/
theorem exists_gfpApprox_eq_gfpApprox : ∃ a < ord <| succ #α, ∃ b < ord <| succ #α,
    a ≠ b ∧ gfpApprox f x a = gfpApprox f x b :=
  exists_lfpApprox_eq_lfpApprox f.dual x

/-- The approximation at the index of the successor of the domain's cardinality is a fixed point -/
lemma gfpApprox_ord_mem_fixedPoint (hx : f x ≤ x) :
    gfpApprox f x (ord <| succ #α) ∈ fixedPoints f :=
  lfpApprox_ord_mem_fixedPoint f.dual hx

/-- Every value of the approximation is greater or equal than every fixed point of `f`
less or equal than the initial value -/
lemma le_gfpApprox_of_mem_fixedPoints {a : α}
    (ha : a ∈ fixedPoints f) (hax : a ≤ x) (i : Ordinal) : a ≤ gfpApprox f x i :=
  lfpApprox_le_of_mem_fixedPoints f.dual ha hax i

/-- The approximation sequence converges at the successor of the domain's cardinality
to the greatest fixed point if starting from `⊥` -/
theorem gfpApprox_ord_eq_gfp : gfpApprox f ⊤ (ord <| succ #α) = f.gfp :=
  lfpApprox_ord_eq_lfp f.dual

/-- Some approximation of the least fixed point starting from `⊤` is the greatest fixed point. -/
theorem gfp_mem_range_gfpApprox : f.gfp ∈ Set.range (gfpApprox f ⊤) :=
  lfp_mem_range_lfpApprox f.dual

end OrdinalApprox
