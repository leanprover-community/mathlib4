/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Data.Stream.Init
import Mathlib.Tactic.ApplyFun
import Mathlib.Control.Fix
import Mathlib.Order.OmegaCompletePartialOrder

/-!
# Lawful fixed point operators

This module defines the laws required of a `Fix` instance, using the theory of
omega complete partial orders (ωCPO). Proofs of the lawfulness of all `Fix` instances in
`Control.Fix` are provided.

## Main definition

 * class `LawfulFix`
-/

universe u v

open scoped Classical

variable {α : Type*} {β : α → Type*}

open OmegaCompletePartialOrder

/-- Intuitively, a fixed point operator `fix` is lawful if it satisfies `fix f = f (fix f)` for all
`f`, but this is inconsistent / uninteresting in most cases due to the existence of "exotic"
functions `f`, such as the function that is defined iff its argument is not, familiar from the
halting problem. Instead, this requirement is limited to only functions that are `Continuous` in the
sense of `ω`-complete partial orders, which excludes the example because it is not monotone
(making the input argument less defined can make `f` more defined). -/
class LawfulFix (α : Type*) [OmegaCompletePartialOrder α] extends Fix α where
  fix_eq : ∀ {f : α →o α}, Continuous f → Fix.fix f = f (Fix.fix f)

theorem LawfulFix.fix_eq' {α} [OmegaCompletePartialOrder α] [LawfulFix α] {f : α → α}
    (hf : Continuous' f) : Fix.fix f = f (Fix.fix f) :=
  LawfulFix.fix_eq (hf.to_bundled _)

namespace Part

open Part Nat Nat.Upto

namespace Fix

variable (f : ((a : _) → Part <| β a) →o (a : _) → Part <| β a)

theorem approx_mono' {i : ℕ} : Fix.approx f i ≤ Fix.approx f (succ i) := by
  induction i with
  | zero => dsimp [approx]; apply @bot_le _ _ _ (f ⊥)
  | succ _ i_ih => intro; apply f.monotone; apply i_ih

theorem approx_mono ⦃i j : ℕ⦄ (hij : i ≤ j) : approx f i ≤ approx f j := by
  induction' j with j ih
  · cases hij
    exact le_rfl
  cases hij; · exact le_rfl
  exact le_trans (ih ‹_›) (approx_mono' f)

theorem mem_iff (a : α) (b : β a) : b ∈ Part.fix f a ↔ ∃ i, b ∈ approx f i a := by
  by_cases h₀ : ∃ i : ℕ, (approx f i a).Dom
  · simp only [Part.fix_def f h₀]
    constructor <;> intro hh
    · exact ⟨_, hh⟩
    have h₁ := Nat.find_spec h₀
    rw [dom_iff_mem] at h₁
    cases' h₁ with y h₁
    replace h₁ := approx_mono' f _ _ h₁
    suffices y = b by
      subst this
      exact h₁
    cases' hh with i hh
    revert h₁; generalize succ (Nat.find h₀) = j; intro h₁
    wlog case : i ≤ j
    · rcases le_total i j with H | H <;> [skip; symm] <;> apply_assumption <;> assumption
    replace hh := approx_mono f case _ _ hh
    apply Part.mem_unique h₁ hh
  · simp only [fix_def' (⇑f) h₀, not_exists, false_iff_iff, not_mem_none]
    simp only [dom_iff_mem, not_exists] at h₀
    intro; apply h₀

theorem approx_le_fix (i : ℕ) : approx f i ≤ Part.fix f := fun a b hh ↦ by
  rw [mem_iff f]
  exact ⟨_, hh⟩

theorem exists_fix_le_approx (x : α) : ∃ i, Part.fix f x ≤ approx f i x := by
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

/-- The series of approximations of `fix f` (see `approx`) as a `Chain` -/
def approxChain : Chain ((a : _) → Part <| β a) :=
  ⟨approx f, approx_mono f⟩

theorem le_f_of_mem_approx {x} : x ∈ approxChain f → x ≤ f x := by
  simp only [(· ∈ ·), forall_exists_index]
  rintro i rfl
  apply approx_mono'

theorem approx_mem_approxChain {i} : approx f i ∈ approxChain f :=
  Stream'.mem_of_get_eq rfl

end Fix

open Fix

variable {α : Type*}
variable (f : ((a : _) → Part <| β a) →o (a : _) → Part <| β a)

open OmegaCompletePartialOrder

open Part hiding ωSup

open Nat

open Nat.Upto OmegaCompletePartialOrder

theorem fix_eq_ωSup : Part.fix f = ωSup (approxChain f) := by
  apply le_antisymm
  · intro x
    cases' exists_fix_le_approx f x with i hx
    trans approx f i.succ x
    · trans
      · apply hx
      · apply approx_mono' f
    apply le_ωSup_of_le i.succ
    dsimp [approx]
    rfl
  · apply ωSup_le _ _ _
    simp only [Fix.approxChain, OrderHom.coe_mk]
    intro y x
    apply approx_le_fix f

theorem fix_le {X : (a : _) → Part <| β a} (hX : f X ≤ X) : Part.fix f ≤ X := by
  rw [fix_eq_ωSup f]
  apply ωSup_le _ _ _
  simp only [Fix.approxChain, OrderHom.coe_mk]
  intro i
  induction i with
  | zero => dsimp [Fix.approx]; apply bot_le
  | succ _ i_ih =>
    trans f X
    · apply f.monotone i_ih
    · apply hX

variable {f}

theorem fix_eq (hc : Continuous f) : Part.fix f = f (Part.fix f) := by
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

end Part

namespace Part

/-- `toUnit` as a monotone function -/
@[simps]
def toUnitMono (f : Part α →o Part α) : (Unit → Part α) →o Unit → Part α where
  toFun x u := f (x u)
  monotone' x y (h : x ≤ y) u := f.monotone <| h u

theorem to_unit_cont (f : Part α →o Part α) (hc : Continuous f) : Continuous (toUnitMono f)
  | _ => by
    ext ⟨⟩ : 1
    dsimp [OmegaCompletePartialOrder.ωSup]
    erw [hc, Chain.map_comp]; rfl

instance lawfulFix : LawfulFix (Part α) :=
  ⟨fun {f : Part α →o Part α} hc ↦ show Part.fix (toUnitMono f) () = _ by
    rw [Part.fix_eq (to_unit_cont f hc)]; rfl⟩

end Part

open Sigma

namespace Pi

instance lawfulFix {β} : LawfulFix (α → Part β) :=
  ⟨fun {_f} ↦ Part.fix_eq⟩

variable {γ : ∀ a : α, β a → Type*}

section Monotone

variable (α β γ)

/-- `Sigma.curry` as a monotone function. -/
@[simps]
def monotoneCurry [(x y : _) → Preorder <| γ x y] :
    (∀ x : Σa, β a, γ x.1 x.2) →o ∀ (a) (b : β a), γ a b where
  toFun := curry
  monotone' _x _y h a b := h ⟨a, b⟩

/-- `Sigma.uncurry` as a monotone function. -/
@[simps]
def monotoneUncurry [(x y : _) → Preorder <| γ x y] :
    (∀ (a) (b : β a), γ a b) →o ∀ x : Σa, β a, γ x.1 x.2 where
  toFun := uncurry
  monotone' _x _y h a := h a.1 a.2

variable [(x y : _) → OmegaCompletePartialOrder <| γ x y]

open OmegaCompletePartialOrder.Chain

theorem continuous_curry : Continuous <| monotoneCurry α β γ := fun c ↦ by
  ext x y
  dsimp [curry, ωSup]
  rw [map_comp, map_comp]
  rfl

theorem continuous_uncurry : Continuous <| monotoneUncurry α β γ := fun c ↦ by
  ext ⟨x, y⟩
  dsimp [uncurry, ωSup]
  rw [map_comp, map_comp]
  rfl

end Monotone

open Fix

instance hasFix [Fix <| (x : Sigma β) → γ x.1 x.2] : Fix ((x : _) → (y : β x) → γ x y) :=
  ⟨fun f ↦ curry (fix <| uncurry ∘ f ∘ curry)⟩

variable [∀ x y, OmegaCompletePartialOrder <| γ x y]

section Curry

variable {f : ((x : _) → (y : β x) → γ x y) →o (x : _) → (y : β x) → γ x y}

theorem uncurry_curry_continuous (hc : Continuous f) :
    Continuous <| (monotoneUncurry α β γ).comp <| f.comp <| monotoneCurry α β γ :=
  continuous_comp _ _ (continuous_comp _ _ (continuous_curry _ _ _) hc) (continuous_uncurry _ _ _)

end Curry

instance lawfulFix' [LawfulFix <| (x : Sigma β) → γ x.1 x.2] :
    LawfulFix ((x y : _) → γ x y) where
  fix_eq {_f} hc := by
    dsimp [fix]
    conv_lhs => erw [LawfulFix.fix_eq (uncurry_curry_continuous hc)]
    rfl

end Pi
