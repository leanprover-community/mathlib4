/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.NormedSpace.Basic

#align_import analysis.asymptotics.theta from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Asymptotic equivalence up to a constant

In this file we define `Asymptotics.IsTheta l f g` (notation: `f =Θ[l] g`) as
`f =O[l] g ∧ g =O[l] f`, then prove basic properties of this equivalence relation.
-/


open Filter

open Topology

namespace Asymptotics

set_option linter.uppercaseLean3 false -- is_Theta

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']

variable [NormedField 𝕜] [NormedField 𝕜']
variable {c c' c₁ c₂ : ℝ} {f : α → E} {g : α → F} {k : α → G}
variable {f' : α → E'} {g' : α → F'} {k' : α → G'}
variable {f'' : α → E''} {g'' : α → F''}
variable {l l' : Filter α}

/-- We say that `f` is `Θ(g)` along a filter `l` (notation: `f =Θ[l] g`) if `f =O[l] g` and
`g =O[l] f`. -/
def IsTheta (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  IsBigO l f g ∧ IsBigO l g f
#align asymptotics.is_Theta Asymptotics.IsTheta

@[inherit_doc]
notation:100 f " =Θ[" l "] " g:100 => IsTheta l f g

theorem IsBigO.antisymm (h₁ : f =O[l] g) (h₂ : g =O[l] f) : f =Θ[l] g :=
  ⟨h₁, h₂⟩
#align asymptotics.is_O.antisymm Asymptotics.IsBigO.antisymm

lemma IsTheta.isBigO (h : f =Θ[l] g) : f =O[l] g := h.1

lemma IsTheta.isBigO_symm (h : f =Θ[l] g) : g =O[l] f := h.2

@[refl]
theorem isTheta_refl (f : α → E) (l : Filter α) : f =Θ[l] f :=
  ⟨isBigO_refl _ _, isBigO_refl _ _⟩
#align asymptotics.is_Theta_refl Asymptotics.isTheta_refl

theorem isTheta_rfl : f =Θ[l] f :=
  isTheta_refl _ _
#align asymptotics.is_Theta_rfl Asymptotics.isTheta_rfl

@[symm]
nonrec theorem IsTheta.symm (h : f =Θ[l] g) : g =Θ[l] f :=
  h.symm
#align asymptotics.is_Theta.symm Asymptotics.IsTheta.symm

theorem isTheta_comm : f =Θ[l] g ↔ g =Θ[l] f :=
  ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩
#align asymptotics.is_Theta_comm Asymptotics.isTheta_comm

@[trans]
theorem IsTheta.trans {f : α → E} {g : α → F'} {k : α → G} (h₁ : f =Θ[l] g) (h₂ : g =Θ[l] k) :
    f =Θ[l] k :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩
#align asymptotics.is_Theta.trans Asymptotics.IsTheta.trans

-- Porting note (#10754): added instance
instance : Trans (α := α → E) (β := α → F') (γ := α → G) (IsTheta l) (IsTheta l) (IsTheta l) :=
  ⟨IsTheta.trans⟩

@[trans]
theorem IsBigO.trans_isTheta {f : α → E} {g : α → F'} {k : α → G} (h₁ : f =O[l] g)
    (h₂ : g =Θ[l] k) : f =O[l] k :=
  h₁.trans h₂.1
#align asymptotics.is_O.trans_is_Theta Asymptotics.IsBigO.trans_isTheta

-- Porting note (#10754): added instance
instance : Trans (α := α → E) (β := α → F') (γ := α → G) (IsBigO l) (IsTheta l) (IsBigO l) :=
  ⟨IsBigO.trans_isTheta⟩

@[trans]
theorem IsTheta.trans_isBigO {f : α → E} {g : α → F'} {k : α → G} (h₁ : f =Θ[l] g)
    (h₂ : g =O[l] k) : f =O[l] k :=
  h₁.1.trans h₂
#align asymptotics.is_Theta.trans_is_O Asymptotics.IsTheta.trans_isBigO

-- Porting note (#10754): added instance
instance : Trans (α := α → E) (β := α → F') (γ := α → G) (IsTheta l) (IsBigO l) (IsBigO l) :=
  ⟨IsTheta.trans_isBigO⟩

@[trans]
theorem IsLittleO.trans_isTheta {f : α → E} {g : α → F} {k : α → G'} (h₁ : f =o[l] g)
    (h₂ : g =Θ[l] k) : f =o[l] k :=
  h₁.trans_isBigO h₂.1
#align asymptotics.is_o.trans_is_Theta Asymptotics.IsLittleO.trans_isTheta

-- Porting note (#10754): added instance
instance : Trans (α := α → E) (β := α → F') (γ := α → G') (IsLittleO l) (IsTheta l) (IsLittleO l) :=
  ⟨IsLittleO.trans_isTheta⟩

@[trans]
theorem IsTheta.trans_isLittleO {f : α → E} {g : α → F'} {k : α → G} (h₁ : f =Θ[l] g)
    (h₂ : g =o[l] k) : f =o[l] k :=
  h₁.1.trans_isLittleO h₂
#align asymptotics.is_Theta.trans_is_o Asymptotics.IsTheta.trans_isLittleO

-- Porting note (#10754): added instance
instance : Trans (α := α → E) (β := α → F') (γ := α → G) (IsTheta l) (IsLittleO l) (IsLittleO l) :=
  ⟨IsTheta.trans_isLittleO⟩

@[trans]
theorem IsTheta.trans_eventuallyEq {f : α → E} {g₁ g₂ : α → F} (h : f =Θ[l] g₁) (hg : g₁ =ᶠ[l] g₂) :
    f =Θ[l] g₂ :=
  ⟨h.1.trans_eventuallyEq hg, hg.symm.trans_isBigO h.2⟩
#align asymptotics.is_Theta.trans_eventually_eq Asymptotics.IsTheta.trans_eventuallyEq

-- Porting note (#10754): added instance
instance : Trans (α := α → E) (β := α → F) (γ := α → F) (IsTheta l) (EventuallyEq l) (IsTheta l) :=
  ⟨IsTheta.trans_eventuallyEq⟩

@[trans]
theorem _root_.Filter.EventuallyEq.trans_isTheta {f₁ f₂ : α → E} {g : α → F} (hf : f₁ =ᶠ[l] f₂)
    (h : f₂ =Θ[l] g) : f₁ =Θ[l] g :=
  ⟨hf.trans_isBigO h.1, h.2.trans_eventuallyEq hf.symm⟩
#align filter.eventually_eq.trans_is_Theta Filter.EventuallyEq.trans_isTheta

-- Porting note (#10754): added instance
instance : Trans (α := α → E) (β := α → E) (γ := α → F) (EventuallyEq l) (IsTheta l) (IsTheta l) :=
  ⟨EventuallyEq.trans_isTheta⟩

lemma _root_.Filter.EventuallyEq.isTheta {f g : α → E} (h : f =ᶠ[l] g) : f =Θ[l] g :=
  h.trans_isTheta isTheta_rfl

@[simp]
theorem isTheta_norm_left : (fun x ↦ ‖f' x‖) =Θ[l] g ↔ f' =Θ[l] g := by simp [IsTheta]
#align asymptotics.is_Theta_norm_left Asymptotics.isTheta_norm_left

@[simp]
theorem isTheta_norm_right : (f =Θ[l] fun x ↦ ‖g' x‖) ↔ f =Θ[l] g' := by simp [IsTheta]
#align asymptotics.is_Theta_norm_right Asymptotics.isTheta_norm_right

alias ⟨IsTheta.of_norm_left, IsTheta.norm_left⟩ := isTheta_norm_left
#align asymptotics.is_Theta.of_norm_left Asymptotics.IsTheta.of_norm_left
#align asymptotics.is_Theta.norm_left Asymptotics.IsTheta.norm_left

alias ⟨IsTheta.of_norm_right, IsTheta.norm_right⟩ := isTheta_norm_right
#align asymptotics.is_Theta.of_norm_right Asymptotics.IsTheta.of_norm_right
#align asymptotics.is_Theta.norm_right Asymptotics.IsTheta.norm_right

theorem isTheta_of_norm_eventuallyEq (h : (fun x ↦ ‖f x‖) =ᶠ[l] fun x ↦ ‖g x‖) : f =Θ[l] g :=
  ⟨IsBigO.of_bound 1 <| by simpa only [one_mul] using h.le,
    IsBigO.of_bound 1 <| by simpa only [one_mul] using h.symm.le⟩
#align asymptotics.is_Theta_of_norm_eventually_eq Asymptotics.isTheta_of_norm_eventuallyEq

theorem isTheta_of_norm_eventuallyEq' {g : α → ℝ} (h : (fun x ↦ ‖f' x‖) =ᶠ[l] g) : f' =Θ[l] g :=
  isTheta_of_norm_eventuallyEq <| h.mono fun x hx ↦ by simp only [← hx, norm_norm]
#align asymptotics.is_Theta_of_norm_eventually_eq' Asymptotics.isTheta_of_norm_eventuallyEq'

theorem IsTheta.isLittleO_congr_left (h : f' =Θ[l] g') : f' =o[l] k ↔ g' =o[l] k :=
  ⟨h.symm.trans_isLittleO, h.trans_isLittleO⟩
#align asymptotics.is_Theta.is_o_congr_left Asymptotics.IsTheta.isLittleO_congr_left

theorem IsTheta.isLittleO_congr_right (h : g' =Θ[l] k') : f =o[l] g' ↔ f =o[l] k' :=
  ⟨fun H ↦ H.trans_isTheta h, fun H ↦ H.trans_isTheta h.symm⟩
#align asymptotics.is_Theta.is_o_congr_right Asymptotics.IsTheta.isLittleO_congr_right

theorem IsTheta.isBigO_congr_left (h : f' =Θ[l] g') : f' =O[l] k ↔ g' =O[l] k :=
  ⟨h.symm.trans_isBigO, h.trans_isBigO⟩
#align asymptotics.is_Theta.is_O_congr_left Asymptotics.IsTheta.isBigO_congr_left

theorem IsTheta.isBigO_congr_right (h : g' =Θ[l] k') : f =O[l] g' ↔ f =O[l] k' :=
  ⟨fun H ↦ H.trans_isTheta h, fun H ↦ H.trans_isTheta h.symm⟩
#align asymptotics.is_Theta.is_O_congr_right Asymptotics.IsTheta.isBigO_congr_right

lemma IsTheta.isTheta_congr_left (h : f' =Θ[l] g') : f' =Θ[l] k ↔ g' =Θ[l] k :=
  h.isBigO_congr_left.and h.isBigO_congr_right

lemma IsTheta.isTheta_congr_right (h : f' =Θ[l] g') : k =Θ[l] f' ↔ k =Θ[l] g' :=
  h.isBigO_congr_right.and h.isBigO_congr_left

theorem IsTheta.mono (h : f =Θ[l] g) (hl : l' ≤ l) : f =Θ[l'] g :=
  ⟨h.1.mono hl, h.2.mono hl⟩
#align asymptotics.is_Theta.mono Asymptotics.IsTheta.mono

theorem IsTheta.sup (h : f' =Θ[l] g') (h' : f' =Θ[l'] g') : f' =Θ[l ⊔ l'] g' :=
  ⟨h.1.sup h'.1, h.2.sup h'.2⟩
#align asymptotics.is_Theta.sup Asymptotics.IsTheta.sup

@[simp]
theorem isTheta_sup : f' =Θ[l ⊔ l'] g' ↔ f' =Θ[l] g' ∧ f' =Θ[l'] g' :=
  ⟨fun h ↦ ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h ↦ h.1.sup h.2⟩
#align asymptotics.is_Theta_sup Asymptotics.isTheta_sup

theorem IsTheta.eq_zero_iff (h : f'' =Θ[l] g'') : ∀ᶠ x in l, f'' x = 0 ↔ g'' x = 0 :=
  h.1.eq_zero_imp.mp <| h.2.eq_zero_imp.mono fun _ ↦ Iff.intro
#align asymptotics.is_Theta.eq_zero_iff Asymptotics.IsTheta.eq_zero_iff

theorem IsTheta.tendsto_zero_iff (h : f'' =Θ[l] g'') :
    Tendsto f'' l (𝓝 0) ↔ Tendsto g'' l (𝓝 0) := by
  simp only [← isLittleO_one_iff ℝ, h.isLittleO_congr_left]
#align asymptotics.is_Theta.tendsto_zero_iff Asymptotics.IsTheta.tendsto_zero_iff

theorem IsTheta.tendsto_norm_atTop_iff (h : f' =Θ[l] g') :
    Tendsto (norm ∘ f') l atTop ↔ Tendsto (norm ∘ g') l atTop := by
  simp only [Function.comp, ← isLittleO_const_left_of_ne (one_ne_zero' ℝ), h.isLittleO_congr_right]
#align asymptotics.is_Theta.tendsto_norm_at_top_iff Asymptotics.IsTheta.tendsto_norm_atTop_iff

theorem IsTheta.isBoundedUnder_le_iff (h : f' =Θ[l] g') :
    IsBoundedUnder (· ≤ ·) l (norm ∘ f') ↔ IsBoundedUnder (· ≤ ·) l (norm ∘ g') := by
  simp only [← isBigO_const_of_ne (one_ne_zero' ℝ), h.isBigO_congr_left]
#align asymptotics.is_Theta.is_bounded_under_le_iff Asymptotics.IsTheta.isBoundedUnder_le_iff

theorem IsTheta.smul [NormedSpace 𝕜 E'] [NormedSpace 𝕜' F'] {f₁ : α → 𝕜} {f₂ : α → 𝕜'} {g₁ : α → E'}
    {g₂ : α → F'} (hf : f₁ =Θ[l] f₂) (hg : g₁ =Θ[l] g₂) :
    (fun x ↦ f₁ x • g₁ x) =Θ[l] fun x ↦ f₂ x • g₂ x :=
  ⟨hf.1.smul hg.1, hf.2.smul hg.2⟩
#align asymptotics.is_Theta.smul Asymptotics.IsTheta.smul

theorem IsTheta.mul {f₁ f₂ : α → 𝕜} {g₁ g₂ : α → 𝕜'} (h₁ : f₁ =Θ[l] g₁) (h₂ : f₂ =Θ[l] g₂) :
    (fun x ↦ f₁ x * f₂ x) =Θ[l] fun x ↦ g₁ x * g₂ x :=
  h₁.smul h₂
#align asymptotics.is_Theta.mul Asymptotics.IsTheta.mul

theorem IsTheta.inv {f : α → 𝕜} {g : α → 𝕜'} (h : f =Θ[l] g) :
    (fun x ↦ (f x)⁻¹) =Θ[l] fun x ↦ (g x)⁻¹ :=
  ⟨h.2.inv_rev h.1.eq_zero_imp, h.1.inv_rev h.2.eq_zero_imp⟩
#align asymptotics.is_Theta.inv Asymptotics.IsTheta.inv

@[simp]
theorem isTheta_inv {f : α → 𝕜} {g : α → 𝕜'} :
    ((fun x ↦ (f x)⁻¹) =Θ[l] fun x ↦ (g x)⁻¹) ↔ f =Θ[l] g :=
  ⟨fun h ↦ by simpa only [inv_inv] using h.inv, IsTheta.inv⟩
#align asymptotics.is_Theta_inv Asymptotics.isTheta_inv

theorem IsTheta.div {f₁ f₂ : α → 𝕜} {g₁ g₂ : α → 𝕜'} (h₁ : f₁ =Θ[l] g₁) (h₂ : f₂ =Θ[l] g₂) :
    (fun x ↦ f₁ x / f₂ x) =Θ[l] fun x ↦ g₁ x / g₂ x := by
  simpa only [div_eq_mul_inv] using h₁.mul h₂.inv
#align asymptotics.is_Theta.div Asymptotics.IsTheta.div

theorem IsTheta.pow {f : α → 𝕜} {g : α → 𝕜'} (h : f =Θ[l] g) (n : ℕ) :
    (fun x ↦ f x ^ n) =Θ[l] fun x ↦ g x ^ n :=
  ⟨h.1.pow n, h.2.pow n⟩
#align asymptotics.is_Theta.pow Asymptotics.IsTheta.pow

theorem IsTheta.zpow {f : α → 𝕜} {g : α → 𝕜'} (h : f =Θ[l] g) (n : ℤ) :
    (fun x ↦ f x ^ n) =Θ[l] fun x ↦ g x ^ n := by
  cases n
  · simpa only [Int.ofNat_eq_coe, zpow_natCast] using h.pow _
  · simpa only [zpow_negSucc] using (h.pow _).inv
#align asymptotics.is_Theta.zpow Asymptotics.IsTheta.zpow

theorem isTheta_const_const {c₁ : E''} {c₂ : F''} (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    (fun _ : α ↦ c₁) =Θ[l] fun _ ↦ c₂ :=
  ⟨isBigO_const_const _ h₂ _, isBigO_const_const _ h₁ _⟩
#align asymptotics.is_Theta_const_const Asymptotics.isTheta_const_const

@[simp]
theorem isTheta_const_const_iff [NeBot l] {c₁ : E''} {c₂ : F''} :
    ((fun _ : α ↦ c₁) =Θ[l] fun _ ↦ c₂) ↔ (c₁ = 0 ↔ c₂ = 0) := by
  simpa only [IsTheta, isBigO_const_const_iff, ← iff_def] using Iff.comm
#align asymptotics.is_Theta_const_const_iff Asymptotics.isTheta_const_const_iff

@[simp]
theorem isTheta_zero_left : (fun _ ↦ (0 : E')) =Θ[l] g'' ↔ g'' =ᶠ[l] 0 := by
  simp only [IsTheta, isBigO_zero, isBigO_zero_right_iff, true_and_iff]
#align asymptotics.is_Theta_zero_left Asymptotics.isTheta_zero_left

@[simp]
theorem isTheta_zero_right : (f'' =Θ[l] fun _ ↦ (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  isTheta_comm.trans isTheta_zero_left
#align asymptotics.is_Theta_zero_right Asymptotics.isTheta_zero_right

theorem isTheta_const_smul_left [NormedSpace 𝕜 E'] {c : 𝕜} (hc : c ≠ 0) :
    (fun x ↦ c • f' x) =Θ[l] g ↔ f' =Θ[l] g :=
  and_congr (isBigO_const_smul_left hc) (isBigO_const_smul_right hc)
#align asymptotics.is_Theta_const_smul_left Asymptotics.isTheta_const_smul_left

alias ⟨IsTheta.of_const_smul_left, IsTheta.const_smul_left⟩ := isTheta_const_smul_left
#align asymptotics.is_Theta.of_const_smul_left Asymptotics.IsTheta.of_const_smul_left
#align asymptotics.is_Theta.const_smul_left Asymptotics.IsTheta.const_smul_left

theorem isTheta_const_smul_right [NormedSpace 𝕜 F'] {c : 𝕜} (hc : c ≠ 0) :
    (f =Θ[l] fun x ↦ c • g' x) ↔ f =Θ[l] g' :=
  and_congr (isBigO_const_smul_right hc) (isBigO_const_smul_left hc)
#align asymptotics.is_Theta_const_smul_right Asymptotics.isTheta_const_smul_right

alias ⟨IsTheta.of_const_smul_right, IsTheta.const_smul_right⟩ := isTheta_const_smul_right
#align asymptotics.is_Theta.of_const_smul_right Asymptotics.IsTheta.of_const_smul_right
#align asymptotics.is_Theta.const_smul_right Asymptotics.IsTheta.const_smul_right

theorem isTheta_const_mul_left {c : 𝕜} {f : α → 𝕜} (hc : c ≠ 0) :
    (fun x ↦ c * f x) =Θ[l] g ↔ f =Θ[l] g := by
  simpa only [← smul_eq_mul] using isTheta_const_smul_left hc
#align asymptotics.is_Theta_const_mul_left Asymptotics.isTheta_const_mul_left

alias ⟨IsTheta.of_const_mul_left, IsTheta.const_mul_left⟩ := isTheta_const_mul_left
#align asymptotics.is_Theta.of_const_mul_left Asymptotics.IsTheta.of_const_mul_left
#align asymptotics.is_Theta.const_mul_left Asymptotics.IsTheta.const_mul_left

theorem isTheta_const_mul_right {c : 𝕜} {g : α → 𝕜} (hc : c ≠ 0) :
    (f =Θ[l] fun x ↦ c * g x) ↔ f =Θ[l] g := by
  simpa only [← smul_eq_mul] using isTheta_const_smul_right hc
#align asymptotics.is_Theta_const_mul_right Asymptotics.isTheta_const_mul_right

alias ⟨IsTheta.of_const_mul_right, IsTheta.const_mul_right⟩ := isTheta_const_mul_right
#align asymptotics.is_Theta.of_const_mul_right Asymptotics.IsTheta.of_const_mul_right
#align asymptotics.is_Theta.const_mul_right Asymptotics.IsTheta.const_mul_right

theorem IsLittleO.right_isTheta_add {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) :
    f₂ =Θ[l] (f₁ + f₂) :=
  ⟨h.right_isBigO_add, h.add_isBigO (isBigO_refl _ _)⟩

theorem IsLittleO.right_isTheta_add' {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) :
    f₂ =Θ[l] (f₂ + f₁) :=
  add_comm f₁ f₂ ▸ h.right_isTheta_add

lemma IsTheta.add_isLittleO {f₁ f₂ : α → E'} {g : α → F}
    (hΘ : f₁ =Θ[l] g) (ho : f₂ =o[l] g) : (f₁ + f₂) =Θ[l] g :=
  (ho.trans_isTheta hΘ.symm).right_isTheta_add'.symm.trans hΘ

lemma IsLittleO.add_isTheta {f₁ f₂ : α → E'} {g : α → F}
    (ho : f₁ =o[l] g) (hΘ : f₂ =Θ[l] g) : (f₁ + f₂) =Θ[l] g :=
  add_comm f₁ f₂ ▸ hΘ.add_isLittleO ho

end Asymptotics
