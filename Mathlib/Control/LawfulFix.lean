/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Data.Stream.Init
import Mathlib.Tactic.ApplyFun
import Mathlib.Control.Fix
import Mathlib.Order.OmegaCompletePartialOrder

#align_import control.lawful_fix from "leanprover-community/mathlib"@"92ca63f0fb391a9ca5f22d2409a6080e786d99f7"

/-!
# Lawful fixed point operators

This module defines the laws required of a `Fix` instance, using the theory of
omega complete partial orders (ωCPO). Proofs of the lawfulness of all `Fix` instances in
`Control.Fix` are provided.

## Main definition

 * class `LawfulFix`
-/

universe u v

open Classical

variable {α : Type*} {β : α → Type*}

open OmegaCompletePartialOrder

/- Porting note: in `#align`s, mathport is putting some `fix`es where `Fix`es should be. -/
/-- Intuitively, a fixed point operator `fix` is lawful if it satisfies `fix f = f (fix f)` for all
`f`, but this is inconsistent / uninteresting in most cases due to the existence of "exotic"
functions `f`, such as the function that is defined iff its argument is not, familiar from the
halting problem. Instead, this requirement is limited to only functions that are `Continuous` in the
sense of `ω`-complete partial orders, which excludes the example because it is not monotone
(making the input argument less defined can make `f` more defined). -/
class LawfulFix (α : Type*) [OmegaCompletePartialOrder α] extends Fix α where
  fix_eq : ∀ {f : α →o α}, Continuous f → Fix.fix f = f (Fix.fix f)
#align lawful_fix LawfulFix

theorem LawfulFix.fix_eq' {α} [OmegaCompletePartialOrder α] [LawfulFix α] {f : α → α}
    (hf : Continuous' f) : Fix.fix f = f (Fix.fix f) :=
  LawfulFix.fix_eq (hf.to_bundled _)
#align lawful_fix.fix_eq' LawfulFix.fix_eq'

namespace Part

open Part Nat Nat.Upto

namespace Fix

variable (f : ((a : _) → Part <| β a) →o (a : _) → Part <| β a)

theorem approx_mono' {i : ℕ} : Fix.approx f i ≤ Fix.approx f (succ i) := by
  induction i with
  | zero => dsimp [approx]; apply @bot_le _ _ _ (f ⊥)
  | succ _ i_ih => intro; apply f.monotone; apply i_ih
#align part.fix.approx_mono' Part.Fix.approx_mono'

theorem approx_mono ⦃i j : ℕ⦄ (hij : i ≤ j) : approx f i ≤ approx f j := by
  induction' j with j ih
  -- ⊢ approx (↑f) i ≤ approx (↑f) Nat.zero
  · cases hij
    -- ⊢ approx (↑f) Nat.zero ≤ approx (↑f) Nat.zero
    exact le_rfl
    -- 🎉 no goals
  cases hij; · exact le_rfl
  -- ⊢ approx (↑f) (Nat.succ j) ≤ approx (↑f) (Nat.succ j)
               -- 🎉 no goals
  exact le_trans (ih ‹_›) (approx_mono' f)
  -- 🎉 no goals
#align part.fix.approx_mono Part.Fix.approx_mono

theorem mem_iff (a : α) (b : β a) : b ∈ Part.fix f a ↔ ∃ i, b ∈ approx f i a := by
  by_cases h₀ : ∃ i : ℕ, (approx f i a).Dom
  -- ⊢ b ∈ Part.fix (↑f) a ↔ ∃ i, b ∈ approx (↑f) i a
  · simp only [Part.fix_def f h₀]
    -- ⊢ b ∈ approx (↑f) (Nat.succ (Nat.find h₀)) a ↔ ∃ i, b ∈ approx (↑f) i a
    constructor <;> intro hh
    -- ⊢ b ∈ approx (↑f) (Nat.succ (Nat.find h₀)) a → ∃ i, b ∈ approx (↑f) i a
                    -- ⊢ ∃ i, b ∈ approx (↑f) i a
                    -- ⊢ b ∈ approx (↑f) (Nat.succ (Nat.find h₀)) a
    · exact ⟨_, hh⟩
      -- 🎉 no goals
    have h₁ := Nat.find_spec h₀
    -- ⊢ b ∈ approx (↑f) (Nat.succ (Nat.find h₀)) a
    rw [dom_iff_mem] at h₁
    -- ⊢ b ∈ approx (↑f) (Nat.succ (Nat.find h₀)) a
    cases' h₁ with y h₁
    -- ⊢ b ∈ approx (↑f) (Nat.succ (Nat.find h₀)) a
    replace h₁ := approx_mono' f _ _ h₁
    -- ⊢ b ∈ approx (↑f) (Nat.succ (Nat.find h₀)) a
    suffices : y = b
    -- ⊢ b ∈ approx (↑f) (Nat.succ (Nat.find h₀)) a
    · subst this
      -- ⊢ y ∈ approx (↑f) (Nat.succ (Nat.find h₀)) a
      exact h₁
      -- 🎉 no goals
    cases' hh with i hh
    -- ⊢ y = b
    revert h₁; generalize succ (Nat.find h₀) = j; intro h₁
    -- ⊢ y ∈ approx (↑f) (Nat.succ (Nat.find h₀)) a → y = b
               -- ⊢ y ∈ approx (↑f) j a → y = b
                                                  -- ⊢ y = b
    wlog case : i ≤ j
    -- ⊢ y = b
    · cases' le_total i j with H H <;> [skip; symm] <;> apply_assumption <;> assumption
      -- ⊢ y = b
                                                                             -- 🎉 no goals
                                                                             -- 🎉 no goals
                                                                             -- 🎉 no goals
                                                                             -- 🎉 no goals
                                                                             -- 🎉 no goals
                                                                             -- 🎉 no goals
                                                                             -- 🎉 no goals
                                                                             -- 🎉 no goals
    replace hh := approx_mono f case _ _ hh
    -- ⊢ y = b
    apply Part.mem_unique h₁ hh
    -- 🎉 no goals
  · simp only [fix_def' (⇑f) h₀, not_exists, false_iff_iff, not_mem_none]
    -- ⊢ ∀ (x : ℕ), ¬b ∈ approx (↑f) x a
    simp only [dom_iff_mem, not_exists] at h₀
    -- ⊢ ∀ (x : ℕ), ¬b ∈ approx (↑f) x a
    intro; apply h₀
    -- ⊢ ¬b ∈ approx (↑f) x✝ a
           -- 🎉 no goals
#align part.fix.mem_iff Part.Fix.mem_iff

theorem approx_le_fix (i : ℕ) : approx f i ≤ Part.fix f := fun a b hh ↦ by
  rw [mem_iff f]
  -- ⊢ ∃ i, b ∈ approx (↑f) i a
  exact ⟨_, hh⟩
  -- 🎉 no goals
#align part.fix.approx_le_fix Part.Fix.approx_le_fix

theorem exists_fix_le_approx (x : α) : ∃ i, Part.fix f x ≤ approx f i x := by
  by_cases hh : ∃ i b, b ∈ approx f i x
  -- ⊢ ∃ i, Part.fix (↑f) x ≤ approx (↑f) i x
  · rcases hh with ⟨i, b, hb⟩
    -- ⊢ ∃ i, Part.fix (↑f) x ≤ approx (↑f) i x
    exists i
    -- ⊢ Part.fix (↑f) x ≤ approx (↑f) i x
    intro b' h'
    -- ⊢ b' ∈ approx (↑f) i x
    have hb' := approx_le_fix f i _ _ hb
    -- ⊢ b' ∈ approx (↑f) i x
    obtain rfl := Part.mem_unique h' hb'
    -- ⊢ b' ∈ approx (↑f) i x
    exact hb
    -- 🎉 no goals
  · simp only [not_exists] at hh
    -- ⊢ ∃ i, Part.fix (↑f) x ≤ approx (↑f) i x
    exists 0
    -- ⊢ Part.fix (↑f) x ≤ approx (↑f) 0 x
    intro b' h'
    -- ⊢ b' ∈ approx (↑f) 0 x
    simp only [mem_iff f] at h'
    -- ⊢ b' ∈ approx (↑f) 0 x
    cases' h' with i h'
    -- ⊢ b' ∈ approx (↑f) 0 x
    cases hh _ _ h'
    -- 🎉 no goals
#align part.fix.exists_fix_le_approx Part.Fix.exists_fix_le_approx

/-- The series of approximations of `fix f` (see `approx`) as a `Chain` -/
def approxChain : Chain ((a : _) → Part <| β a) :=
  ⟨approx f, approx_mono f⟩
#align part.fix.approx_chain Part.Fix.approxChain

theorem le_f_of_mem_approx {x} : x ∈ approxChain f → x ≤ f x := by
  simp only [(· ∈ ·), forall_exists_index]
  -- ⊢ ∀ (x_1 : ℕ), x = ↑(approxChain f) x_1 → x ≤ ↑f x
  rintro i rfl
  -- ⊢ ↑(approxChain f) i ≤ ↑f (↑(approxChain f) i)
  apply approx_mono'
  -- 🎉 no goals
#align part.fix.le_f_of_mem_approx Part.Fix.le_f_of_mem_approx

theorem approx_mem_approxChain {i} : approx f i ∈ approxChain f :=
  Stream'.mem_of_nth_eq rfl
#align part.fix.approx_mem_approx_chain Part.Fix.approx_mem_approxChain

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
  -- ⊢ Part.fix ↑f ≤ ωSup (approxChain f)
  · intro x
    -- ⊢ Part.fix (↑f) x ≤ ωSup (approxChain f) x
    cases' exists_fix_le_approx f x with i hx
    -- ⊢ Part.fix (↑f) x ≤ ωSup (approxChain f) x
    trans approx f i.succ x
    -- ⊢ Part.fix (↑f) x ≤ approx (↑f) (Nat.succ i) x
    · trans
      apply hx
      -- ⊢ approx (↑f) i x ≤ approx (↑f) (Nat.succ i) x
      apply approx_mono' f
      -- 🎉 no goals
    apply le_ωSup_of_le i.succ
    -- ⊢ approx (↑f) (Nat.succ i) x ≤ ↑(Chain.map (approxChain f) (Pi.evalOrderHom x) …
    dsimp [approx]
    -- ⊢ ↑f (approx (↑f) i) x ≤ ↑(approxChain f) (Nat.succ i) x
    rfl
    -- 🎉 no goals
  · apply ωSup_le _ _ _
    -- ⊢ ∀ (i : ℕ), ↑(approxChain f) i ≤ Part.fix ↑f
    simp only [Fix.approxChain, OrderHom.coe_mk]
    -- ⊢ ∀ (i : ℕ), ↑{ toFun := approx ↑f, monotone' := (_ : ∀ ⦃i j : ℕ⦄, i ≤ j → app …
    intro y x
    -- ⊢ ↑{ toFun := approx ↑f, monotone' := (_ : ∀ ⦃i j : ℕ⦄, i ≤ j → approx (↑f) i  …
    apply approx_le_fix f
    -- 🎉 no goals
#align part.fix_eq_ωSup Part.fix_eq_ωSup

theorem fix_le {X : (a : _) → Part <| β a} (hX : f X ≤ X) : Part.fix f ≤ X := by
  rw [fix_eq_ωSup f]
  -- ⊢ ωSup (approxChain f) ≤ X
  apply ωSup_le _ _ _
  -- ⊢ ∀ (i : ℕ), ↑(approxChain f) i ≤ X
  simp only [Fix.approxChain, OrderHom.coe_mk]
  -- ⊢ ∀ (i : ℕ), ↑{ toFun := approx ↑f, monotone' := (_ : ∀ ⦃i j : ℕ⦄, i ≤ j → app …
  intro i
  -- ⊢ ↑{ toFun := approx ↑f, monotone' := (_ : ∀ ⦃i j : ℕ⦄, i ≤ j → approx (↑f) i  …
  induction i with
  | zero => dsimp [Fix.approx]; apply bot_le
  | succ _ i_ih => trans f X; apply f.monotone i_ih; apply hX
#align part.fix_le Part.fix_le

variable {f} (hc : Continuous f)

theorem fix_eq : Part.fix f = f (Part.fix f) := by
  rw [fix_eq_ωSup f, hc]
  -- ⊢ ωSup (approxChain f) = ωSup (Chain.map (approxChain f) f)
  apply le_antisymm
  -- ⊢ ωSup (approxChain f) ≤ ωSup (Chain.map (approxChain f) f)
  · apply ωSup_le_ωSup_of_le _
    -- ⊢ approxChain f ≤ Chain.map (approxChain f) f
    intro i
    -- ⊢ ∃ j, ↑(approxChain f) i ≤ ↑(Chain.map (approxChain f) f) j
    exists i
    -- ⊢ ↑(approxChain f) i ≤ ↑(Chain.map (approxChain f) f) i
    intro x
    -- ⊢ ↑(approxChain f) i x ≤ ↑(Chain.map (approxChain f) f) i x
    -- intros x y hx,
    apply le_f_of_mem_approx _ ⟨i, rfl⟩
    -- 🎉 no goals
  · apply ωSup_le_ωSup_of_le _
    -- ⊢ Chain.map (approxChain f) f ≤ approxChain f
    intro i
    -- ⊢ ∃ j, ↑(Chain.map (approxChain f) f) i ≤ ↑(approxChain f) j
    exists i.succ
    -- 🎉 no goals
#align part.fix_eq Part.fix_eq

end Part

namespace Part

/-- `toUnit` as a monotone function -/
@[simps]
def toUnitMono (f : Part α →o Part α) : (Unit → Part α) →o Unit → Part α where
  toFun x u := f (x u)
  monotone' x y (h : x ≤ y) u := f.monotone <| h u
#align part.to_unit_mono Part.toUnitMono

theorem to_unit_cont (f : Part α →o Part α) (hc : Continuous f) : Continuous (toUnitMono f)
  | _ => by
    ext ⟨⟩ : 1
    -- ⊢ ↑(toUnitMono f) (ωSup x✝) PUnit.unit = ωSup (Chain.map x✝ (toUnitMono f)) PU …
    dsimp [OmegaCompletePartialOrder.ωSup]
    -- ⊢ ↑f (Part.ωSup (Chain.map x✝ (Pi.evalOrderHom PUnit.unit))) = Part.ωSup (Chai …
    erw [hc, Chain.map_comp]; rfl
    -- ⊢ ωSup (Chain.map x✝ (OrderHom.comp f (Pi.evalOrderHom PUnit.unit))) = Part.ωS …
                              -- 🎉 no goals
#align part.to_unit_cont Part.to_unit_cont

instance lawfulFix : LawfulFix (Part α) :=
  ⟨fun {f : Part α →o Part α} hc ↦ show Part.fix (toUnitMono f) () = _ by
    rw [Part.fix_eq (to_unit_cont f hc)]; rfl⟩
    -- ⊢ ↑(toUnitMono f) (Part.fix ↑(toUnitMono f)) () = ↑f (Fix.fix ↑f)
                                          -- 🎉 no goals
#align part.lawful_fix Part.lawfulFix

end Part

open Sigma

namespace Pi

instance lawfulFix {β} : LawfulFix (α → Part β) :=
  ⟨fun {_f} ↦ Part.fix_eq⟩
#align pi.lawful_fix Pi.lawfulFix

variable {γ : ∀ a : α, β a → Type*}

section Monotone

variable (α β γ)

/-- `Sigma.curry` as a monotone function. -/
@[simps]
def monotoneCurry [(x y : _) → Preorder <| γ x y] :
    (∀ x : Σa, β a, γ x.1 x.2) →o ∀ (a) (b : β a), γ a b where
  toFun := curry
  monotone' _x _y h a b := h ⟨a, b⟩
#align pi.monotone_curry Pi.monotoneCurry

/-- `Sigma.uncurry` as a monotone function. -/
@[simps]
def monotoneUncurry [(x y : _) → Preorder <| γ x y] :
    (∀ (a) (b : β a), γ a b) →o ∀ x : Σa, β a, γ x.1 x.2 where
  toFun := uncurry
  monotone' _x _y h a := h a.1 a.2
#align pi.monotone_uncurry Pi.monotoneUncurry

variable [(x y : _) → OmegaCompletePartialOrder <| γ x y]

open OmegaCompletePartialOrder.Chain

theorem continuous_curry : Continuous <| monotoneCurry α β γ := fun c ↦ by
  ext x y
  -- ⊢ ↑(monotoneCurry α β γ) (ωSup c) x y = ωSup (Chain.map c (monotoneCurry α β γ …
  dsimp [curry, ωSup]
  -- ⊢ ωSup (Chain.map c (evalOrderHom { fst := x, snd := y })) = ωSup (Chain.map ( …
  rw [map_comp, map_comp]
  -- ⊢ ωSup (Chain.map c (evalOrderHom { fst := x, snd := y })) = ωSup (Chain.map c …
  rfl
  -- 🎉 no goals
#align pi.continuous_curry Pi.continuous_curry

theorem continuous_uncurry : Continuous <| monotoneUncurry α β γ := fun c ↦ by
  ext ⟨x, y⟩
  -- ⊢ ↑(monotoneUncurry α β γ) (ωSup c) { fst := x, snd := y } = ωSup (Chain.map c …
  dsimp [uncurry, ωSup]
  -- ⊢ ωSup (Chain.map (Chain.map c (evalOrderHom x)) (evalOrderHom y)) = ωSup (Cha …
  rw [map_comp, map_comp]
  -- ⊢ ωSup (Chain.map c (OrderHom.comp (evalOrderHom y) (evalOrderHom x))) = ωSup  …
  rfl
  -- 🎉 no goals
#align pi.continuous_uncurry Pi.continuous_uncurry

end Monotone

open Fix

instance hasFix [Fix <| (x : Sigma β) → γ x.1 x.2] : Fix ((x : _) → (y : β x) → γ x y) :=
  ⟨fun f ↦ curry (fix <| uncurry ∘ f ∘ curry)⟩
#align pi.has_fix Pi.hasFix

variable [∀ x y, OmegaCompletePartialOrder <| γ x y]

section Curry

variable {f : ((x : _) → (y : β x) → γ x y) →o (x : _) → (y : β x) → γ x y}

variable (hc : Continuous f)

theorem uncurry_curry_continuous :
    Continuous <| (monotoneUncurry α β γ).comp <| f.comp <| monotoneCurry α β γ :=
  continuous_comp _ _ (continuous_comp _ _ (continuous_curry _ _ _) hc) (continuous_uncurry _ _ _)
#align pi.uncurry_curry_continuous Pi.uncurry_curry_continuous

end Curry

instance Pi.lawfulFix' [LawfulFix <| (x : Sigma β) → γ x.1 x.2] :
    LawfulFix ((x y : _) → γ x y) where
  fix_eq {_f} hc := by
    dsimp [fix]
    -- ⊢ curry (fix (uncurry ∘ ↑_f ∘ curry)) = ↑_f (curry (fix (uncurry ∘ ↑_f ∘ curry …
    conv =>
      lhs
      erw [LawfulFix.fix_eq (uncurry_curry_continuous hc)]
#align pi.pi.lawful_fix' Pi.Pi.lawfulFix'

end Pi
