/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Data.Stream.Init
public import Mathlib.Control.Fix
public import Mathlib.Order.OmegaCompletePartialOrder

/-!
# Lawful fixed point operators

This module defines the laws required of a `Fix` instance, using the theory of
omega complete partial orders (ωCPO). Proofs of the lawfulness of all `Fix` instances in
`Control.Fix` are provided.

## Main definition

* class `LawfulFix`
-/

@[expose] public section

universe u v

variable {α : Type*} {β : α → Type*}

open OmegaCompletePartialOrder

/-- Intuitively, a fixed point operator `fix` is lawful if it satisfies `fix f = f (fix f)` for all
`f`, but this is inconsistent / uninteresting in most cases due to the existence of "exotic"
functions `f`, such as the function that is defined iff its argument is not, familiar from the
halting problem. Instead, this requirement is limited to only functions that are `Continuous` in the
sense of `ω`-complete partial orders, which excludes the example because it is not monotone
(making the input argument less defined can make `f` more defined). -/
class LawfulFix (α : Type*) [OmegaCompletePartialOrder α] extends Fix α where
  fix_eq : ∀ {f : α → α}, ωScottContinuous f → Fix.fix f = f (Fix.fix f)

namespace Part

open Nat Nat.Upto

namespace Fix

variable (f : ((a : _) → Part <| β a) →o (a : _) → Part <| β a)

theorem approx_mono' {i : ℕ} : Fix.approx f i ≤ Fix.approx f (succ i) := by
  induction i with
  | zero => dsimp [approx]; apply @bot_le _ _ _ (f ⊥)
  | succ _ i_ih => intro; apply f.monotone; apply i_ih

theorem approx_mono ⦃i j : ℕ⦄ (hij : i ≤ j) : approx f i ≤ approx f j := by
  induction j with
  | zero => cases hij; exact le_rfl
  | succ j ih =>
    cases hij; · exact le_rfl
    exact le_trans (ih ‹_›) (approx_mono' f)

theorem mem_iff (a : α) (b : β a) : b ∈ Part.fix f a ↔ ∃ i, b ∈ approx f i a := by
  classical
  by_cases h₀ : ∃ i : ℕ, (approx f i a).Dom
  · simp only [Part.fix_def f h₀]
    constructor <;> intro hh
    · exact ⟨_, hh⟩
    have h₁ := Nat.find_spec h₀
    rw [dom_iff_mem] at h₁
    obtain ⟨y, h₁⟩ := h₁
    replace h₁ := approx_mono' f _ _ h₁
    suffices y = b by
      subst this
      exact h₁
    obtain ⟨i, hh⟩ := hh
    revert h₁; generalize succ (Nat.find h₀) = j; intro h₁
    wlog case : i ≤ j
    · rcases le_total i j with H | H <;> [skip; symm] <;> apply_assumption <;> assumption
    replace hh := approx_mono f case _ _ hh
    apply Part.mem_unique h₁ hh
  · simp only [fix_def' (⇑f) h₀, not_exists, false_iff, notMem_none]
    simp only [dom_iff_mem, not_exists] at h₀
    intro; apply h₀

theorem approx_le_fix (i : ℕ) : approx f i ≤ Part.fix f := fun a b hh ↦ by
  rw [mem_iff f]
  exact ⟨_, hh⟩

theorem exists_fix_le_approx (x : α) : ∃ i, Part.fix f x ≤ approx f i x := by
  by_cases! hh : ∃ i b, b ∈ approx f i x
  · rcases hh with ⟨i, b, hb⟩
    exists i
    intro b' h'
    have hb' := approx_le_fix f i _ _ hb
    obtain rfl := Part.mem_unique h' hb'
    exact hb
  · exists 0
    intro b' h'
    simp only [mem_iff f] at h'
    obtain ⟨i, h'⟩ := h'
    cases hh _ _ h'

/-- The series of approximations of `fix f` (see `approx`) as a `Chain` -/
def approxChain : Chain ((a : _) → Part <| β a) :=
  ⟨approx f, approx_mono f⟩

theorem le_f_of_mem_approx {x} : x ∈ approxChain f → x ≤ f x := by
  simp only [Membership.mem, forall_exists_index]
  rintro i rfl
  apply approx_mono'

theorem approx_mem_approxChain {i} : approx f i ∈ approxChain f :=
  Stream'.mem_of_get_eq rfl

/-- The `n`-th approximation `Fix.approx f n` is the `n`-th iterate of `f` from `⊥`. -/
theorem approx_eq_iterate_bot (n : ℕ) : Fix.approx f n = f^[n] ⊥ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih]; rfl

/-- The chain `approxChain f` agrees with `iterateChain f ⊥ bot_le`. -/
theorem approxChain_eq_iterateChain :
    approxChain f = fixedPoints.iterateChain f ⊥ bot_le :=
  Chain.ext (funext (approx_eq_iterate_bot f))

end Fix

open Fix

variable {α : Type*}
variable (f : ((a : _) → Part <| β a) →o (a : _) → Part <| β a)

theorem fix_eq_ωSup : Part.fix f = ωSup (approxChain f) := by
  apply le_antisymm
  · intro x
    obtain ⟨i, hx⟩ := exists_fix_le_approx f x
    trans approx f i.succ x
    · trans
      · apply hx
      · apply approx_mono' f
    apply le_ωSup_of_le i.succ
    dsimp [approx]
    rfl
  · apply ωSup_le _ _ _
    simp only [Fix.approxChain]
    intro y x
    apply approx_le_fix f

theorem fix_le {X : (a : _) → Part <| β a} (hX : f X ≤ X) : Part.fix f ≤ X := by
  rw [fix_eq_ωSup f]
  apply ωSup_le _ _ _
  simp only [Fix.approxChain]
  intro i
  induction i with
  | zero => dsimp [Fix.approx]; apply bot_le
  | succ _ i_ih =>
    trans f X
    · apply f.monotone i_ih
    · apply hX

variable {g : ((a : _) → Part <| β a) → (a : _) → Part <| β a}

/-- If `y ∈ Part.fix g x`, then `y` is already in some finite approximation of `g` at `x`.
The monotone analogue is `Part.Fix.mem_iff`. -/
theorem exists_mem_approx_of_mem_fix {x} {y : β x}
    (h : y ∈ Part.fix g x) : ∃ n, y ∈ Fix.approx g n x := by
  by_cases h' : ∃ i, (Fix.approx g i x).Dom
  · exact ⟨_, (Part.fix_def g h') ▸ h⟩
  · rw [Part.fix_def' g h'] at h
    exact absurd h (Part.notMem_none _)

theorem fix_eq_ωSup_of_ωScottContinuous (hc : ωScottContinuous g) : Part.fix g =
    ωSup (approxChain (⟨g,hc.monotone⟩ : ((a : _) → Part <| β a) →o (a : _) → Part <| β a)) := by
  rw [← fix_eq_ωSup]
  rfl

theorem fix_eq_of_ωScottContinuous (hc : ωScottContinuous g) :
    Part.fix g = g (Part.fix g) := by
  rw [fix_eq_ωSup_of_ωScottContinuous hc, hc.map_ωSup]
  apply le_antisymm
  · apply ωSup_le_ωSup_of_le _
    intro i
    exists i
    apply le_f_of_mem_approx _ ⟨i, rfl⟩
  · apply ωSup_le_ωSup_of_le _
    intro i
    exists i.succ

/-- `Part.fix g` is the least fixed point of the ω-Scott continuous functional `g`. -/
theorem fix_eq_lfp (hc : ωScottContinuous g) :
    Part.fix g = ContinuousHom.lfp (.ofFun g hc) := by
  rw [fix_eq_ωSup_of_ωScottContinuous hc, Fix.approxChain_eq_iterateChain]
  rfl

/-- **Scott induction** for `Part.fix`: for an ω-Scott continuous functional `g` and a
predicate `p` that holds at `⊥`, is preserved by `g`, and is closed under ωSup of chains,
`p` holds at `Part.fix g`. -/
theorem fix_scott_induction {p : (∀ a, Part (β a)) → Prop} (hc : ωScottContinuous g)
    (h_bot : p ⊥) (h_step : ∀ f, p f → p (g f))
    (h_sup : ∀ c : Chain (∀ a, Part (β a)), (∀ n, p (c n)) → p (ωSup c)) :
    p (Part.fix g) := by
  rw [fix_eq_lfp hc]
  exact ContinuousHom.lfp_induction _ h_bot h_step h_sup

/-- Induction on membership in `Part.fix`, derived from `fix_scott_induction`: to prove `P x y`
whenever `y ∈ Part.fix g x`, it suffices that for any approximation `f` on which `P` holds
pointwise, `g f` still satisfies `P` pointwise. -/
theorem fix_induction_mem {P : ∀ a, β a → Prop} (hc : ωScottContinuous g)
    (h_step : ∀ f, (∀ x y, y ∈ f x → P x y) → ∀ x y, y ∈ g f x → P x y)
    {x} {y : β x} (h : y ∈ Part.fix g x) : P x y := by
  have key : ∀ x y, y ∈ Part.fix g x → P x y := by
    apply fix_scott_induction (p := fun f => ∀ x y, y ∈ f x → P x y) hc
    · exact fun _ _ hy => absurd hy (Part.notMem_none _)
    · exact h_step
    · intro c ih x y hy
      have hy' : y ∈ ωSup (c.map (Pi.evalOrderHom x)) := hy
      rw [Part.mem_ωSup] at hy'
      obtain ⟨n, hn⟩ := hy'
      have hcn : c n x = Part.some y := hn.symm
      exact ih n x y (hcn ▸ Part.mem_some y)
  exact key x y h

end Part

namespace Part

/-- `toUnit` as a monotone function -/
@[simps]
def toUnitMono (f : Part α →o Part α) : (Unit → Part α) →o Unit → Part α where
  toFun x u := f (x u)
  monotone' x y (h : x ≤ y) u := f.monotone <| h u

theorem ωScottContinuous_toUnitMono (f : Part α → Part α) (hc : ωScottContinuous f) :
    ωScottContinuous (toUnitMono ⟨f,hc.monotone⟩) := .of_map_ωSup_of_orderHom fun _ => by
  ext ⟨⟩ : 1
  dsimp [OmegaCompletePartialOrder.ωSup]
  erw [hc.map_ωSup]
  rw [Chain.map_comp]
  rfl

noncomputable instance lawfulFix : LawfulFix (Part α) :=
  ⟨fun {f : Part α → Part α} hc ↦ show Part.fix (toUnitMono ⟨f,hc.monotone⟩) () = _ by
    rw [Part.fix_eq_of_ωScottContinuous (ωScottContinuous_toUnitMono f hc)]; rfl⟩

end Part

open Sigma

namespace Pi

noncomputable instance lawfulFix {β} : LawfulFix (α → Part β) :=
  ⟨fun {_f} ↦ Part.fix_eq_of_ωScottContinuous⟩

variable {γ : ∀ a : α, β a → Type*}

section Monotone

variable (α β γ)

/-- `Sigma.curry` as a monotone function. -/
@[simps]
def monotoneCurry [(x y : _) → Preorder <| γ x y] :
    (∀ x : Σ a, β a, γ x.1 x.2) →o ∀ (a) (b : β a), γ a b where
  toFun := curry
  monotone' _x _y h a b := h ⟨a, b⟩

/-- `Sigma.uncurry` as a monotone function. -/
@[simps]
def monotoneUncurry [(x y : _) → Preorder <| γ x y] :
    (∀ (a) (b : β a), γ a b) →o ∀ x : Σ a, β a, γ x.1 x.2 where
  toFun := uncurry
  monotone' _x _y h a := h a.1 a.2

variable [(x y : _) → OmegaCompletePartialOrder <| γ x y]

open OmegaCompletePartialOrder.Chain

theorem ωScottContinuous_curry :
    ωScottContinuous (monotoneCurry α β γ) :=
  ωScottContinuous.of_map_ωSup_of_orderHom fun c ↦ by
    ext x y
    dsimp [curry, ωSup]
    rw [map_comp, map_comp]
    rfl

theorem ωScottContinuous_uncurry :
    ωScottContinuous (monotoneUncurry α β γ) :=
    .of_map_ωSup_of_orderHom fun c ↦ by
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

variable {f : (∀ a b, γ a b) → ∀ a b, γ a b}

theorem uncurry_curry_ωScottContinuous (hc : ωScottContinuous f) :
    ωScottContinuous <| (monotoneUncurry α β γ).comp <|
      (⟨f,hc.monotone⟩ : ((x : _) → (y : β x) → γ x y) →o (x : _) → (y : β x) → γ x y).comp <|
      monotoneCurry α β γ :=
  (ωScottContinuous_uncurry _ _ _).comp (hc.comp (ωScottContinuous_curry _ _ _))

end Curry

instance lawfulFix' [LawfulFix <| (x : Sigma β) → γ x.1 x.2] :
    LawfulFix ((x y : _) → γ x y) where
  fix_eq {_f} hc := by
    dsimp [fix]
    conv_lhs => erw [LawfulFix.fix_eq (uncurry_curry_ωScottContinuous hc)]
    rfl

end Pi
