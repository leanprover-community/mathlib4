/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module control.lawful_fix
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Stream.Init
import Mathbin.Tactic.Apply
import Mathbin.Control.Fix
import Mathbin.Order.OmegaCompletePartialOrder

/-!
# Lawful fixed point operators

This module defines the laws required of a `has_fix` instance, using the theory of
omega complete partial orders (ωCPO). Proofs of the lawfulness of all `has_fix` instances in
`control.fix` are provided.

## Main definition

 * class `lawful_fix`
-/


universe u v

open Classical

variable {α : Type _} {β : α → Type _}

open OmegaCompletePartialOrder

/-- Intuitively, a fixed point operator `fix` is lawful if it satisfies `fix f = f (fix f)` for all
`f`, but this is inconsistent / uninteresting in most cases due to the existence of "exotic"
functions `f`, such as the function that is defined iff its argument is not, familiar from the
halting problem. Instead, this requirement is limited to only functions that are `continuous` in the
sense of `ω`-complete partial orders, which excludes the example because it is not monotone
(making the input argument less defined can make `f` more defined). -/
class LawfulFix (α : Type _) [OmegaCompletePartialOrder α] extends Fix α where
  fix_eq : ∀ {f : α →o α}, Continuous f → Fix.fix f = f (Fix.fix f)
#align lawful_fix LawfulFix

theorem LawfulFix.fix_eq' {α} [OmegaCompletePartialOrder α] [LawfulFix α] {f : α → α}
    (hf : Continuous' f) : Fix.fix f = f (Fix.fix f) :=
  LawfulFix.fix_eq (hf.to_bundled _)
#align lawful_fix.fix_eq' LawfulFix.fix_eq'

namespace Part

open Part Nat Nat.Upto

namespace Fix

variable (f : (∀ a, Part <| β a) →o ∀ a, Part <| β a)

theorem approx_mono' {i : ℕ} : Fix.approx f i ≤ Fix.approx f (succ i) :=
  by
  induction i; dsimp [approx]; apply @bot_le _ _ _ (f ⊥)
  intro ; apply f.monotone; apply i_ih
#align part.fix.approx_mono' Part.fix.approx_mono'

theorem approx_mono ⦃i j : ℕ⦄ (hij : i ≤ j) : approx f i ≤ approx f j :=
  by
  induction' j with j ih;
  · cases hij
    exact le_rfl
  cases hij; · exact le_rfl
  exact le_trans (ih ‹_›) (approx_mono' f)
#align part.fix.approx_mono Part.fix.approx_mono

theorem mem_iff (a : α) (b : β a) : b ∈ Part.fix f a ↔ ∃ i, b ∈ approx f i a :=
  by
  by_cases h₀ : ∃ i : ℕ, (approx f i a).Dom
  · simp only [Part.fix_def f h₀]
    constructor <;> intro hh
    exact ⟨_, hh⟩
    have h₁ := Nat.find_spec h₀
    rw [dom_iff_mem] at h₁
    cases' h₁ with y h₁
    replace h₁ := approx_mono' f _ _ h₁
    suffices : y = b
    subst this
    exact h₁
    cases' hh with i hh
    revert h₁
    generalize succ (Nat.find h₀) = j
    intro
    wlog : i ≤ j := le_total i j using i j b y, j i y b
    replace hh := approx_mono f case _ _ hh
    apply Part.mem_unique h₁ hh
  · simp only [fix_def' (⇑f) h₀, not_exists, false_iff_iff, not_mem_none]
    simp only [dom_iff_mem, not_exists] at h₀
    intro
    apply h₀
#align part.fix.mem_iff Part.fix.mem_iff

theorem approx_le_fix (i : ℕ) : approx f i ≤ Part.fix f := fun a b hh =>
  by
  rw [mem_iff f]
  exact ⟨_, hh⟩
#align part.fix.approx_le_fix Part.fix.approx_le_fix

theorem exists_fix_le_approx (x : α) : ∃ i, Part.fix f x ≤ approx f i x :=
  by
  by_cases hh : ∃ i b, b ∈ approx f i x
  · rcases hh with ⟨i, b, hb⟩
    exists i
    intro b' h'
    have hb' := approx_le_fix f i _ _ hb
    obtain rfl := Part.mem_unique h' hb'
    exact hb
  · simp only [not_exists] at hh
    exists 0
    intro b' h'
    simp only [mem_iff f] at h'
    cases' h' with i h'
    cases hh _ _ h'
#align part.fix.exists_fix_le_approx Part.fix.exists_fix_le_approx

include f

/-- The series of approximations of `fix f` (see `approx`) as a `chain` -/
def approxChain : Chain (∀ a, Part <| β a) :=
  ⟨approx f, approx_mono f⟩
#align part.fix.approx_chain Part.fix.approxChain

theorem le_f_of_mem_approx {x} : x ∈ approxChain f → x ≤ f x :=
  by
  simp only [(· ∈ ·), forall_exists_index]
  rintro i rfl
  apply approx_mono'
#align part.fix.le_f_of_mem_approx Part.fix.le_f_of_mem_approx

theorem approx_mem_approxChain {i} : approx f i ∈ approxChain f :=
  Stream'.mem_of_nth_eq rfl
#align part.fix.approx_mem_approx_chain Part.fix.approx_mem_approxChain

end Fix

open Fix

variable {α}

variable (f : (∀ a, Part <| β a) →o ∀ a, Part <| β a)

open OmegaCompletePartialOrder

open Part hiding ωSup

open Nat

open Nat.Upto OmegaCompletePartialOrder

theorem fix_eq_ωSup : Part.fix f = ωSup (approxChain f) :=
  by
  apply le_antisymm
  · intro x
    cases' exists_fix_le_approx f x with i hx
    trans approx f i.succ x
    · trans
      apply hx
      apply approx_mono' f
    apply le_ωSup_of_le i.succ
    dsimp [approx]
    rfl
  · apply ωSup_le _ _ _
    simp only [fix.approx_chain, OrderHom.coe_fun_mk]
    intro y x
    apply approx_le_fix f
#align part.fix_eq_ωSup Part.fix_eq_ωSup

theorem fix_le {X : ∀ a, Part <| β a} (hX : f X ≤ X) : Part.fix f ≤ X :=
  by
  rw [fix_eq_ωSup f]
  apply ωSup_le _ _ _
  simp only [fix.approx_chain, OrderHom.coe_fun_mk]
  intro i
  induction i; dsimp [fix.approx]; apply bot_le
  trans f X; apply f.monotone i_ih
  apply hX
#align part.fix_le Part.fix_le

variable {f} (hc : Continuous f)

include hc

theorem fix_eq : Part.fix f = f (Part.fix f) :=
  by
  rw [fix_eq_ωSup f, hc]
  apply le_antisymm
  · apply ωSup_le_ωSup_of_le _
    intro i
    exists i
    intro x
    -- intros x y hx,
    apply le_f_of_mem_approx _ ⟨i, rfl⟩
  · apply ωSup_le_ωSup_of_le _
    intro i
    exists i.succ
    rfl
#align part.fix_eq Part.fix_eq

end Part

namespace Part

/-- `to_unit` as a monotone function -/
@[simps]
def toUnitMono (f : Part α →o Part α) : (Unit → Part α) →o Unit → Part α
    where
  toFun x u := f (x u)
  monotone' x y (h : x ≤ y) u := f.Monotone <| h u
#align part.to_unit_mono Part.toUnitMono

theorem to_unit_cont (f : Part α →o Part α) (hc : Continuous f) : Continuous (toUnitMono f)
  | c => by
    ext ⟨⟩ : 1
    dsimp [OmegaCompletePartialOrder.ωSup]
    erw [hc, chain.map_comp]; rfl
#align part.to_unit_cont Part.to_unit_cont

instance : LawfulFix (Part α) :=
  ⟨fun f hc => show Part.fix (toUnitMono f) () = _ by rw [Part.fix_eq (to_unit_cont f hc)] <;> rfl⟩

end Part

open Sigma

namespace Pi

instance {β} : LawfulFix (α → Part β) :=
  ⟨fun f => Part.fix_eq⟩

variable {γ : ∀ a : α, β a → Type _}

section Monotone

variable (α β γ)

/-- `sigma.curry` as a monotone function. -/
@[simps]
def monotoneCurry [∀ x y, Preorder <| γ x y] : (∀ x : Σa, β a, γ x.1 x.2) →o ∀ (a) (b : β a), γ a b
    where
  toFun := curry
  monotone' x y h a b := h ⟨a, b⟩
#align pi.monotone_curry Pi.monotoneCurry

/-- `sigma.uncurry` as a monotone function. -/
@[simps]
def monotoneUncurry [∀ x y, Preorder <| γ x y] :
    (∀ (a) (b : β a), γ a b) →o ∀ x : Σa, β a, γ x.1 x.2
    where
  toFun := uncurry
  monotone' x y h a := h a.1 a.2
#align pi.monotone_uncurry Pi.monotoneUncurry

variable [∀ x y, OmegaCompletePartialOrder <| γ x y]

open OmegaCompletePartialOrder.Chain

theorem continuous_curry : continuous <| monotoneCurry α β γ := fun c =>
  by
  ext (x y)
  dsimp [curry, ωSup]
  rw [map_comp, map_comp]
  rfl
#align pi.continuous_curry Pi.continuous_curry

theorem continuous_uncurry : continuous <| monotoneUncurry α β γ := fun c =>
  by
  ext (x y)
  dsimp [uncurry, ωSup]
  rw [map_comp, map_comp]
  rfl
#align pi.continuous_uncurry Pi.continuous_uncurry

end Monotone

open Fix

instance [Fix <| ∀ x : Sigma β, γ x.1 x.2] : Fix (∀ (x) (y : β x), γ x y) :=
  ⟨fun f => curry (fix <| uncurry ∘ f ∘ curry)⟩

variable [∀ x y, OmegaCompletePartialOrder <| γ x y]

section Curry

variable {f : (∀ (x) (y : β x), γ x y) →o ∀ (x) (y : β x), γ x y}

variable (hc : Continuous f)

theorem uncurry_curry_continuous :
    continuous <| (monotoneUncurry α β γ).comp <| f.comp <| monotoneCurry α β γ :=
  continuous_comp _ _ (continuous_comp _ _ (continuous_curry _ _ _) hc) (continuous_uncurry _ _ _)
#align pi.uncurry_curry_continuous Pi.uncurry_curry_continuous

end Curry

instance Pi.lawfulFix' [LawfulFix <| ∀ x : Sigma β, γ x.1 x.2] : LawfulFix (∀ x y, γ x y)
    where fix_eq f hc := by
    dsimp [fix]
    conv =>
      lhs
      erw [LawfulFix.fix_eq (uncurry_curry_continuous hc)]
    rfl
#align pi.pi.lawful_fix' Pi.Pi.lawfulFix'

end Pi

