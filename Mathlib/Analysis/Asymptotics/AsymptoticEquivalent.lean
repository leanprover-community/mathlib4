/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.Normed.Order.Basic

#align_import analysis.asymptotics.asymptotic_equivalent from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Asymptotic equivalence

In this file, we define the relation `IsEquivalent l u v`, which means that `u-v` is little o of
`v` along the filter `l`.

Unlike `Is(Little|Big)O` relations, this one requires `u` and `v` to have the same codomain `β`.
While the definition only requires `β` to be a `NormedAddCommGroup`, most interesting properties
require it to be a `NormedField`.

## Notations

We introduce the notation `u ~[l] v := IsEquivalent l u v`, which you can use by opening the
`Asymptotics` locale.

## Main results

If `β` is a `NormedAddCommGroup` :

- `_ ~[l] _` is an equivalence relation
- Equivalent statements for `u ~[l] const _ c` :
  - If `c ≠ 0`, this is true iff `Tendsto u l (𝓝 c)` (see `isEquivalent_const_iff_tendsto`)
  - For `c = 0`, this is true iff `u =ᶠ[l] 0` (see `isEquivalent_zero_iff_eventually_zero`)

If `β` is a `NormedField` :

- Alternative characterization of the relation (see `isEquivalent_iff_exists_eq_mul`) :

  `u ~[l] v ↔ ∃ (φ : α → β) (hφ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v`

- Provided some non-vanishing hypothesis, this can be seen as `u ~[l] v ↔ Tendsto (u/v) l (𝓝 1)`
  (see `isEquivalent_iff_tendsto_one`)
- For any constant `c`, `u ~[l] v` implies `Tendsto u l (𝓝 c) ↔ Tendsto v l (𝓝 c)`
  (see `IsEquivalent.tendsto_nhds_iff`)
- `*` and `/` are compatible with `_ ~[l] _` (see `IsEquivalent.mul` and `IsEquivalent.div`)

If `β` is a `NormedLinearOrderedField` :

- If `u ~[l] v`, we have `Tendsto u l atTop ↔ Tendsto v l atTop`
  (see `IsEquivalent.tendsto_atTop_iff`)

## Implementation Notes

Note that `IsEquivalent` takes the parameters `(l : Filter α) (u v : α → β)` in that order.
This is to enable `calc` support, as `calc` requires that the last two explicit arguments are `u v`.

-/


namespace Asymptotics

open Filter Function

open Topology

section NormedAddCommGroup

variable {α β : Type*} [NormedAddCommGroup β]

/-- Two functions `u` and `v` are said to be asymptotically equivalent along a filter `l` when
    `u x - v x = o(v x)` as `x` converges along `l`. -/
def IsEquivalent (l : Filter α) (u v : α → β) :=
  (u - v) =o[l] v
#align asymptotics.is_equivalent Asymptotics.IsEquivalent

@[inherit_doc] scoped notation:50 u " ~[" l:50 "] " v:50 => Asymptotics.IsEquivalent l u v

variable {u v w : α → β} {l : Filter α}

theorem IsEquivalent.isLittleO (h : u ~[l] v) : (u - v) =o[l] v := h
#align asymptotics.is_equivalent.is_o Asymptotics.IsEquivalent.isLittleO

nonrec theorem IsEquivalent.isBigO (h : u ~[l] v) : u =O[l] v :=
  (IsBigO.congr_of_sub h.isBigO.symm).mp (isBigO_refl _ _)
set_option linter.uppercaseLean3 false in
#align asymptotics.is_equivalent.is_O Asymptotics.IsEquivalent.isBigO

theorem IsEquivalent.isBigO_symm (h : u ~[l] v) : v =O[l] u := by
  convert h.isLittleO.right_isBigO_add
  simp
set_option linter.uppercaseLean3 false in
#align asymptotics.is_equivalent.is_O_symm Asymptotics.IsEquivalent.isBigO_symm

theorem IsEquivalent.isTheta (h : u ~[l] v) : u =Θ[l] v :=
  ⟨h.isBigO, h.isBigO_symm⟩

theorem IsEquivalent.isTheta_symm (h : u ~[l] v) : v =Θ[l] u :=
  ⟨h.isBigO_symm, h.isBigO⟩

@[refl]
theorem IsEquivalent.refl : u ~[l] u := by
  rw [IsEquivalent, sub_self]
  exact isLittleO_zero _ _
#align asymptotics.is_equivalent.refl Asymptotics.IsEquivalent.refl

@[symm]
theorem IsEquivalent.symm (h : u ~[l] v) : v ~[l] u :=
  (h.isLittleO.trans_isBigO h.isBigO_symm).symm
#align asymptotics.is_equivalent.symm Asymptotics.IsEquivalent.symm

@[trans]
theorem IsEquivalent.trans {l : Filter α} {u v w : α → β} (huv : u ~[l] v) (hvw : v ~[l] w) :
    u ~[l] w :=
  (huv.isLittleO.trans_isBigO hvw.isBigO).triangle hvw.isLittleO
#align asymptotics.is_equivalent.trans Asymptotics.IsEquivalent.trans

theorem IsEquivalent.congr_left {u v w : α → β} {l : Filter α} (huv : u ~[l] v) (huw : u =ᶠ[l] w) :
    w ~[l] v :=
  huv.congr' (huw.sub (EventuallyEq.refl _ _)) (EventuallyEq.refl _ _)
#align asymptotics.is_equivalent.congr_left Asymptotics.IsEquivalent.congr_left

theorem IsEquivalent.congr_right {u v w : α → β} {l : Filter α} (huv : u ~[l] v) (hvw : v =ᶠ[l] w) :
    u ~[l] w :=
  (huv.symm.congr_left hvw).symm
#align asymptotics.is_equivalent.congr_right Asymptotics.IsEquivalent.congr_right

theorem isEquivalent_zero_iff_eventually_zero : u ~[l] 0 ↔ u =ᶠ[l] 0 := by
  rw [IsEquivalent, sub_zero]
  exact isLittleO_zero_right_iff
#align asymptotics.is_equivalent_zero_iff_eventually_zero Asymptotics.isEquivalent_zero_iff_eventually_zero

theorem isEquivalent_zero_iff_isBigO_zero : u ~[l] 0 ↔ u =O[l] (0 : α → β) := by
  refine ⟨IsEquivalent.isBigO, fun h ↦ ?_⟩
  rw [isEquivalent_zero_iff_eventually_zero, eventuallyEq_iff_exists_mem]
  exact ⟨{ x : α | u x = 0 }, isBigO_zero_right_iff.mp h, fun x hx ↦ hx⟩
set_option linter.uppercaseLean3 false in
#align asymptotics.is_equivalent_zero_iff_is_O_zero Asymptotics.isEquivalent_zero_iff_isBigO_zero

theorem isEquivalent_const_iff_tendsto {c : β} (h : c ≠ 0) :
    u ~[l] const _ c ↔ Tendsto u l (𝓝 c) := by
  simp (config := { unfoldPartialApp := true }) only [IsEquivalent, const, isLittleO_const_iff h]
  constructor <;> intro h
  · have := h.sub (tendsto_const_nhds (x := -c))
    simp only [Pi.sub_apply, sub_neg_eq_add, sub_add_cancel, zero_add] at this
    exact this
  · have := h.sub (tendsto_const_nhds (x := c))
    rwa [sub_self] at this
#align asymptotics.is_equivalent_const_iff_tendsto Asymptotics.isEquivalent_const_iff_tendsto

theorem IsEquivalent.tendsto_const {c : β} (hu : u ~[l] const _ c) : Tendsto u l (𝓝 c) := by
  rcases em <| c = 0 with rfl | h
  · exact (tendsto_congr' <| isEquivalent_zero_iff_eventually_zero.mp hu).mpr tendsto_const_nhds
  · exact (isEquivalent_const_iff_tendsto h).mp hu
#align asymptotics.is_equivalent.tendsto_const Asymptotics.IsEquivalent.tendsto_const

theorem IsEquivalent.tendsto_nhds {c : β} (huv : u ~[l] v) (hu : Tendsto u l (𝓝 c)) :
    Tendsto v l (𝓝 c) := by
  by_cases h : c = 0
  · subst c
    rw [← isLittleO_one_iff ℝ] at hu ⊢
    simpa using (huv.symm.isLittleO.trans hu).add hu
  · rw [← isEquivalent_const_iff_tendsto h] at hu ⊢
    exact huv.symm.trans hu
#align asymptotics.is_equivalent.tendsto_nhds Asymptotics.IsEquivalent.tendsto_nhds

theorem IsEquivalent.tendsto_nhds_iff {c : β} (huv : u ~[l] v) :
    Tendsto u l (𝓝 c) ↔ Tendsto v l (𝓝 c) :=
  ⟨huv.tendsto_nhds, huv.symm.tendsto_nhds⟩
#align asymptotics.is_equivalent.tendsto_nhds_iff Asymptotics.IsEquivalent.tendsto_nhds_iff

theorem IsEquivalent.add_isLittleO (huv : u ~[l] v) (hwv : w =o[l] v) : u + w ~[l] v := by
  simpa only [IsEquivalent, add_sub_right_comm] using huv.add hwv
#align asymptotics.is_equivalent.add_is_o Asymptotics.IsEquivalent.add_isLittleO

theorem IsEquivalent.sub_isLittleO (huv : u ~[l] v) (hwv : w =o[l] v) : u - w ~[l] v := by
  simpa only [sub_eq_add_neg] using huv.add_isLittleO hwv.neg_left
#align asymptotics.is_equivalent.sub_is_o Asymptotics.IsEquivalent.sub_isLittleO

theorem IsLittleO.add_isEquivalent (hu : u =o[l] w) (hv : v ~[l] w) : u + v ~[l] w :=
  add_comm v u ▸ hv.add_isLittleO hu
#align asymptotics.is_o.add_is_equivalent Asymptotics.IsLittleO.add_isEquivalent

theorem IsLittleO.isEquivalent (huv : (u - v) =o[l] v) : u ~[l] v := huv
#align asymptotics.is_o.is_equivalent Asymptotics.IsLittleO.isEquivalent

theorem IsEquivalent.neg (huv : u ~[l] v) : (fun x ↦ -u x) ~[l] fun x ↦ -v x := by
  rw [IsEquivalent]
  convert huv.isLittleO.neg_left.neg_right
  simp [neg_add_eq_sub]
#align asymptotics.is_equivalent.neg Asymptotics.IsEquivalent.neg

end NormedAddCommGroup

open Asymptotics

section NormedField

variable {α β : Type*} [NormedField β] {t u v w : α → β} {l : Filter α}

theorem isEquivalent_iff_exists_eq_mul :
    u ~[l] v ↔ ∃ (φ : α → β) (_ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v := by
  rw [IsEquivalent, isLittleO_iff_exists_eq_mul]
  constructor <;> rintro ⟨φ, hφ, h⟩ <;> [refine ⟨φ + 1, ?_, ?_⟩; refine ⟨φ - 1, ?_, ?_⟩]
  · conv in 𝓝 _ => rw [← zero_add (1 : β)]
    exact hφ.add tendsto_const_nhds
  · convert h.add (EventuallyEq.refl l v) <;> simp [add_mul]
  · conv in 𝓝 _ => rw [← sub_self (1 : β)]
    exact hφ.sub tendsto_const_nhds
  · convert h.sub (EventuallyEq.refl l v); simp [sub_mul]
#align asymptotics.is_equivalent_iff_exists_eq_mul Asymptotics.isEquivalent_iff_exists_eq_mul

theorem IsEquivalent.exists_eq_mul (huv : u ~[l] v) :
    ∃ (φ : α → β) (_ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v :=
  isEquivalent_iff_exists_eq_mul.mp huv
#align asymptotics.is_equivalent.exists_eq_mul Asymptotics.IsEquivalent.exists_eq_mul

theorem isEquivalent_of_tendsto_one (hz : ∀ᶠ x in l, v x = 0 → u x = 0)
    (huv : Tendsto (u / v) l (𝓝 1)) : u ~[l] v := by
  rw [isEquivalent_iff_exists_eq_mul]
  exact ⟨u / v, huv, hz.mono fun x hz' ↦ (div_mul_cancel_of_imp hz').symm⟩
#align asymptotics.is_equivalent_of_tendsto_one Asymptotics.isEquivalent_of_tendsto_one

theorem isEquivalent_of_tendsto_one' (hz : ∀ x, v x = 0 → u x = 0) (huv : Tendsto (u / v) l (𝓝 1)) :
    u ~[l] v :=
  isEquivalent_of_tendsto_one (eventually_of_forall hz) huv
#align asymptotics.is_equivalent_of_tendsto_one' Asymptotics.isEquivalent_of_tendsto_one'

theorem isEquivalent_iff_tendsto_one (hz : ∀ᶠ x in l, v x ≠ 0) :
    u ~[l] v ↔ Tendsto (u / v) l (𝓝 1) := by
  constructor
  · intro hequiv
    have := hequiv.isLittleO.tendsto_div_nhds_zero
    simp only [Pi.sub_apply, sub_div] at this
    have key : Tendsto (fun x ↦ v x / v x) l (𝓝 1) :=
      (tendsto_congr' <| hz.mono fun x hnz ↦ @div_self _ _ (v x) hnz).mpr tendsto_const_nhds
    convert this.add key
    · simp
    · norm_num
  · exact isEquivalent_of_tendsto_one (hz.mono fun x hnvz hz ↦ (hnvz hz).elim)
#align asymptotics.is_equivalent_iff_tendsto_one Asymptotics.isEquivalent_iff_tendsto_one

end NormedField

section SMul

theorem IsEquivalent.smul {α E 𝕜 : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {a b : α → 𝕜} {u v : α → E} {l : Filter α} (hab : a ~[l] b) (huv : u ~[l] v) :
    (fun x ↦ a x • u x) ~[l] fun x ↦ b x • v x := by
  rcases hab.exists_eq_mul with ⟨φ, hφ, habφ⟩
  have : ((fun x ↦ a x • u x) - (fun x ↦ b x • v x)) =ᶠ[l] fun x ↦ b x • (φ x • u x - v x) := by
    -- Porting note: `convert` has become too strong, so we need to specify `using 1`.
    convert (habφ.comp₂ (· • ·) <| EventuallyEq.refl _ u).sub
      (EventuallyEq.refl _ fun x ↦ b x • v x) using 1
    ext
    rw [Pi.mul_apply, mul_comm, mul_smul, ← smul_sub]
  refine (isLittleO_congr this.symm <| EventuallyEq.rfl).mp ((isBigO_refl b l).smul_isLittleO ?_)
  rcases huv.isBigO.exists_pos with ⟨C, hC, hCuv⟩
  rw [IsEquivalent] at *
  rw [isLittleO_iff] at *
  rw [IsBigOWith] at hCuv
  simp only [Metric.tendsto_nhds, dist_eq_norm] at hφ
  intro c hc
  specialize hφ (c / 2 / C) (div_pos (div_pos hc zero_lt_two) hC)
  specialize huv (div_pos hc zero_lt_two)
  refine hφ.mp (huv.mp <| hCuv.mono fun x hCuvx huvx hφx ↦ ?_)
  have key :=
    calc
      ‖φ x - 1‖ * ‖u x‖ ≤ c / 2 / C * ‖u x‖ := by gcongr
      _ ≤ c / 2 / C * (C * ‖v x‖) := by gcongr
      _ = c / 2 * ‖v x‖ := by
        field_simp [hC.ne.symm]
        ring
  calc
    ‖((fun x : α ↦ φ x • u x) - v) x‖ = ‖(φ x - 1) • u x + (u x - v x)‖ := by
      simp [sub_smul, sub_add]
    _ ≤ ‖(φ x - 1) • u x‖ + ‖u x - v x‖ := norm_add_le _ _
    _ = ‖φ x - 1‖ * ‖u x‖ + ‖u x - v x‖ := by rw [norm_smul]
    _ ≤ c / 2 * ‖v x‖ + ‖u x - v x‖ := by gcongr
    _ ≤ c / 2 * ‖v x‖ + c / 2 * ‖v x‖ := by gcongr; exact huvx
    _ = c * ‖v x‖ := by ring
#align asymptotics.is_equivalent.smul Asymptotics.IsEquivalent.smul

end SMul

section mul_inv

variable {α β : Type*} [NormedField β] {t u v w : α → β} {l : Filter α}

theorem IsEquivalent.mul (htu : t ~[l] u) (hvw : v ~[l] w) : t * v ~[l] u * w :=
  htu.smul hvw
#align asymptotics.is_equivalent.mul Asymptotics.IsEquivalent.mul

theorem IsEquivalent.inv (huv : u ~[l] v) : (fun x ↦ (u x)⁻¹) ~[l] fun x ↦ (v x)⁻¹ := by
  rw [isEquivalent_iff_exists_eq_mul] at *
  rcases huv with ⟨φ, hφ, h⟩
  rw [← inv_one]
  refine ⟨fun x ↦ (φ x)⁻¹, Tendsto.inv₀ hφ (by norm_num), ?_⟩
  convert h.inv
  simp [mul_comm]
#align asymptotics.is_equivalent.inv Asymptotics.IsEquivalent.inv

theorem IsEquivalent.div (htu : t ~[l] u) (hvw : v ~[l] w) :
    (fun x ↦ t x / v x) ~[l] fun x ↦ u x / w x := by
  simpa only [div_eq_mul_inv] using htu.mul hvw.inv
#align asymptotics.is_equivalent.div Asymptotics.IsEquivalent.div

end mul_inv

section NormedLinearOrderedField

variable {α β : Type*} [NormedLinearOrderedField β] {u v : α → β} {l : Filter α}

theorem IsEquivalent.tendsto_atTop [OrderTopology β] (huv : u ~[l] v) (hu : Tendsto u l atTop) :
    Tendsto v l atTop :=
  let ⟨φ, hφ, h⟩ := huv.symm.exists_eq_mul
  Tendsto.congr' h.symm (mul_comm u φ ▸ hu.atTop_mul zero_lt_one hφ)
#align asymptotics.is_equivalent.tendsto_at_top Asymptotics.IsEquivalent.tendsto_atTop

theorem IsEquivalent.tendsto_atTop_iff [OrderTopology β] (huv : u ~[l] v) :
    Tendsto u l atTop ↔ Tendsto v l atTop :=
  ⟨huv.tendsto_atTop, huv.symm.tendsto_atTop⟩
#align asymptotics.is_equivalent.tendsto_at_top_iff Asymptotics.IsEquivalent.tendsto_atTop_iff

theorem IsEquivalent.tendsto_atBot [OrderTopology β] (huv : u ~[l] v) (hu : Tendsto u l atBot) :
    Tendsto v l atBot := by
  convert tendsto_neg_atTop_atBot.comp (huv.neg.tendsto_atTop <| tendsto_neg_atBot_atTop.comp hu)
  ext
  simp
#align asymptotics.is_equivalent.tendsto_at_bot Asymptotics.IsEquivalent.tendsto_atBot

theorem IsEquivalent.tendsto_atBot_iff [OrderTopology β] (huv : u ~[l] v) :
    Tendsto u l atBot ↔ Tendsto v l atBot :=
  ⟨huv.tendsto_atBot, huv.symm.tendsto_atBot⟩
#align asymptotics.is_equivalent.tendsto_at_bot_iff Asymptotics.IsEquivalent.tendsto_atBot_iff

end NormedLinearOrderedField

end Asymptotics

open Filter Asymptotics

open Asymptotics

variable {α β β₂ : Type*} [NormedAddCommGroup β] [Norm β₂] {l : Filter α}

theorem Filter.EventuallyEq.isEquivalent {u v : α → β} (h : u =ᶠ[l] v) : u ~[l] v :=
  IsEquivalent.congr_right (isLittleO_refl_left _ _) h
#align filter.eventually_eq.is_equivalent Filter.EventuallyEq.isEquivalent

@[trans]
theorem Filter.EventuallyEq.trans_isEquivalent {f g₁ g₂ : α → β} (h : f =ᶠ[l] g₁)
    (h₂ : g₁ ~[l] g₂) : f ~[l] g₂ :=
  h.isEquivalent.trans h₂

namespace Asymptotics

instance transIsEquivalentIsEquivalent :
    @Trans (α → β) (α → β) (α → β) (IsEquivalent l) (IsEquivalent l) (IsEquivalent l) where
  trans := IsEquivalent.trans

instance transEventuallyEqIsEquivalent :
    @Trans (α → β) (α → β) (α → β) (EventuallyEq l) (IsEquivalent l) (IsEquivalent l) where
  trans := EventuallyEq.trans_isEquivalent

@[trans]
theorem IsEquivalent.trans_eventuallyEq {f g₁ g₂ : α → β} (h : f ~[l] g₁)
    (h₂ : g₁ =ᶠ[l] g₂) : f ~[l] g₂ :=
  h.trans h₂.isEquivalent

instance transIsEquivalentEventuallyEq :
    @Trans (α → β) (α → β) (α → β) (IsEquivalent l) (EventuallyEq l) (IsEquivalent l) where
  trans := IsEquivalent.trans_eventuallyEq

@[trans]
theorem IsEquivalent.trans_isBigO {f g₁ : α → β} {g₂ : α → β₂} (h : f ~[l] g₁) (h₂ : g₁ =O[l] g₂) :
    f =O[l] g₂ :=
  IsBigO.trans h.isBigO h₂

instance transIsEquivalentIsBigO :
    @Trans (α → β) (α → β) (α → β₂) (IsEquivalent l) (IsBigO l) (IsBigO l) where
  trans := IsEquivalent.trans_isBigO

@[trans]
theorem IsBigO.trans_isEquivalent {f : α → β₂} {g₁ g₂ : α → β} (h : f =O[l] g₁) (h₂ : g₁ ~[l] g₂) :
    f =O[l] g₂ :=
  IsBigO.trans h h₂.isBigO

instance transIsBigOIsEquivalent :
    @Trans (α → β₂) (α → β) (α → β) (IsBigO l) (IsEquivalent l) (IsBigO l) where
  trans := IsBigO.trans_isEquivalent

@[trans]
theorem IsEquivalent.trans_isLittleO {f g₁ : α → β} {g₂ : α → β₂} (h : f ~[l] g₁)
    (h₂ : g₁ =o[l] g₂) : f =o[l] g₂ :=
  IsBigO.trans_isLittleO h.isBigO h₂

instance transIsEquivalentIsLittleO :
    @Trans (α → β) (α → β) (α → β₂) (IsEquivalent l) (IsLittleO l) (IsLittleO l) where
  trans := IsEquivalent.trans_isLittleO

@[trans]
theorem IsLittleO.trans_isEquivalent {f : α → β₂} {g₁ g₂ : α → β} (h : f =o[l] g₁)
    (h₂ : g₁ ~[l] g₂) : f =o[l] g₂ :=
  IsLittleO.trans_isBigO h h₂.isBigO

instance transIsLittleOIsEquivalent :
    @Trans (α → β₂) (α → β) (α → β) (IsLittleO l) (IsEquivalent l) (IsLittleO l) where
  trans := IsLittleO.trans_isEquivalent

@[trans]
theorem IsEquivalent.trans_isTheta {f g₁ : α → β} {g₂ : α → β₂} (h : f ~[l] g₁)
    (h₂ : g₁ =Θ[l] g₂) : f =Θ[l] g₂ :=
  IsTheta.trans h.isTheta h₂

instance transIsEquivalentIsTheta :
    @Trans (α → β) (α → β) (α → β₂) (IsEquivalent l) (IsTheta l) (IsTheta l) where
  trans := IsEquivalent.trans_isTheta

@[trans]
theorem IsTheta.trans_isEquivalent {f : α → β₂} {g₁ g₂ : α → β} (h : f =Θ[l] g₁)
    (h₂ : g₁ ~[l] g₂) : f =Θ[l] g₂ :=
  IsTheta.trans h h₂.isTheta

instance transIsThetaIsEquivalent :
    @Trans (α → β₂) (α → β) (α → β) (IsTheta l) (IsEquivalent l) (IsTheta l) where
  trans := IsTheta.trans_isEquivalent

end Asymptotics
