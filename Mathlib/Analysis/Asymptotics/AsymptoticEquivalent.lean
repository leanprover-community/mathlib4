/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Analysis.Asymptotics.Theta

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

/-- Two functions `u` and `v` are said to be asymptotically equivalent along a filter `l`
  (denoted as `u ~[l] v` in the `Asymptotics` namespace)
  when `u x - v x = o(v x)` as `x` converges along `l`. -/
def IsEquivalent (l : Filter α) (u v : α → β) :=
  (u - v) =o[l] v

@[inherit_doc] scoped notation:50 u " ~[" l:50 "] " v:50 => Asymptotics.IsEquivalent l u v

variable {u v w : α → β} {l : Filter α}

theorem IsEquivalent.isLittleO (h : u ~[l] v) : (u - v) =o[l] v := h

nonrec theorem IsEquivalent.isBigO (h : u ~[l] v) : u =O[l] v :=
  (IsBigO.congr_of_sub h.isBigO.symm).mp (isBigO_refl _ _)

theorem IsEquivalent.isBigO_symm (h : u ~[l] v) : v =O[l] u := by
  convert h.isLittleO.right_isBigO_add
  simp

theorem IsEquivalent.isTheta (h : u ~[l] v) : u =Θ[l] v :=
  ⟨h.isBigO, h.isBigO_symm⟩

theorem IsEquivalent.isTheta_symm (h : u ~[l] v) : v =Θ[l] u :=
  ⟨h.isBigO_symm, h.isBigO⟩

@[refl]
theorem IsEquivalent.refl : u ~[l] u := by
  rw [IsEquivalent, sub_self]
  exact isLittleO_zero _ _

@[symm]
theorem IsEquivalent.symm (h : u ~[l] v) : v ~[l] u :=
  (h.isLittleO.trans_isBigO h.isBigO_symm).symm

@[trans]
theorem IsEquivalent.trans {l : Filter α} {u v w : α → β} (huv : u ~[l] v) (hvw : v ~[l] w) :
    u ~[l] w :=
  (huv.isLittleO.trans_isBigO hvw.isBigO).triangle hvw.isLittleO

theorem IsEquivalent.congr_left {u v w : α → β} {l : Filter α} (huv : u ~[l] v) (huw : u =ᶠ[l] w) :
    w ~[l] v :=
  huv.congr' (huw.sub (EventuallyEq.refl _ _)) (EventuallyEq.refl _ _)

theorem IsEquivalent.congr_right {u v w : α → β} {l : Filter α} (huv : u ~[l] v) (hvw : v =ᶠ[l] w) :
    u ~[l] w :=
  (huv.symm.congr_left hvw).symm

theorem isEquivalent_zero_iff_eventually_zero : u ~[l] 0 ↔ u =ᶠ[l] 0 := by
  rw [IsEquivalent, sub_zero]
  exact isLittleO_zero_right_iff

theorem isEquivalent_zero_iff_isBigO_zero : u ~[l] 0 ↔ u =O[l] (0 : α → β) := by
  refine ⟨IsEquivalent.isBigO, fun h ↦ ?_⟩
  rw [isEquivalent_zero_iff_eventually_zero, eventuallyEq_iff_exists_mem]
  exact ⟨{ x : α | u x = 0 }, isBigO_zero_right_iff.mp h, fun x hx ↦ hx⟩

theorem isEquivalent_const_iff_tendsto {c : β} (h : c ≠ 0) :
    u ~[l] const _ c ↔ Tendsto u l (𝓝 c) := by
  simp +unfoldPartialApp only [IsEquivalent, const, isLittleO_const_iff h]
  constructor <;> intro h
  · have := h.sub (tendsto_const_nhds (x := -c))
    simp only [Pi.sub_apply, sub_neg_eq_add, sub_add_cancel, zero_add] at this
    exact this
  · have := h.sub (tendsto_const_nhds (x := c))
    rwa [sub_self] at this

theorem IsEquivalent.tendsto_const {c : β} (hu : u ~[l] const _ c) : Tendsto u l (𝓝 c) := by
  rcases em <| c = 0 with rfl | h
  · exact (tendsto_congr' <| isEquivalent_zero_iff_eventually_zero.mp hu).mpr tendsto_const_nhds
  · exact (isEquivalent_const_iff_tendsto h).mp hu

theorem IsEquivalent.tendsto_nhds {c : β} (huv : u ~[l] v) (hu : Tendsto u l (𝓝 c)) :
    Tendsto v l (𝓝 c) := by
  by_cases h : c = 0
  · subst c
    rw [← isLittleO_one_iff ℝ] at hu ⊢
    simpa using (huv.symm.isLittleO.trans hu).add hu
  · rw [← isEquivalent_const_iff_tendsto h] at hu ⊢
    exact huv.symm.trans hu

theorem IsEquivalent.tendsto_nhds_iff {c : β} (huv : u ~[l] v) :
    Tendsto u l (𝓝 c) ↔ Tendsto v l (𝓝 c) :=
  ⟨huv.tendsto_nhds, huv.symm.tendsto_nhds⟩

theorem IsEquivalent.add_isLittleO (huv : u ~[l] v) (hwv : w =o[l] v) : u + w ~[l] v := by
  simpa only [IsEquivalent, add_sub_right_comm] using huv.add hwv

theorem IsEquivalent.sub_isLittleO (huv : u ~[l] v) (hwv : w =o[l] v) : u - w ~[l] v := by
  simpa only [sub_eq_add_neg] using huv.add_isLittleO hwv.neg_left

theorem IsLittleO.add_isEquivalent (hu : u =o[l] w) (hv : v ~[l] w) : u + v ~[l] w :=
  add_comm v u ▸ hv.add_isLittleO hu

theorem IsEquivalent.add_const_of_norm_tendsto_atTop {c : β}
    (huv : u ~[l] v) (hv : Tendsto (norm ∘ v) l atTop) :
    (u · + c) ~[l] v :=
  huv.add_isLittleO <| isLittleO_const_left.mpr (Or.inr hv)

theorem IsEquivalent.const_add_of_norm_tendsto_atTop {c : β}
    (huv : u ~[l] v) (hv : Tendsto (norm ∘ v) l atTop) :
    (c + u ·) ~[l] v :=
  (isLittleO_const_left.mpr (Or.inr hv)).add_isEquivalent huv

theorem IsLittleO.isEquivalent (huv : (u - v) =o[l] v) : u ~[l] v := huv

theorem IsEquivalent.neg (huv : u ~[l] v) : (fun x ↦ -u x) ~[l] fun x ↦ -v x := by
  rw [IsEquivalent]
  convert huv.isLittleO.neg_left.neg_right
  simp [neg_add_eq_sub]

end NormedAddCommGroup

open Asymptotics

section NormedField

variable {α β : Type*} [NormedField β] {u v : α → β} {l : Filter α}

theorem isEquivalent_iff_exists_eq_mul :
    u ~[l] v ↔ ∃ (φ : α → β) (_ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v := by
  rw [IsEquivalent, isLittleO_iff_exists_eq_mul]
  constructor <;> rintro ⟨φ, hφ, h⟩ <;> [refine ⟨φ + 1, ?_, ?_⟩; refine ⟨φ - 1, ?_, ?_⟩]
  · conv in 𝓝 _ => rw [← zero_add (1 : β)]
    exact hφ.add tendsto_const_nhds
  · convert h.fun_add (EventuallyEq.refl l v) <;> simp [add_mul]
  · conv in 𝓝 _ => rw [← sub_self (1 : β)]
    exact hφ.sub tendsto_const_nhds
  · convert h.fun_sub (EventuallyEq.refl l v); simp [sub_mul]

theorem IsEquivalent.exists_eq_mul (huv : u ~[l] v) :
    ∃ (φ : α → β) (_ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v :=
  isEquivalent_iff_exists_eq_mul.mp huv

theorem isEquivalent_of_tendsto_one (hz : ∀ᶠ x in l, v x = 0 → u x = 0)
    (huv : Tendsto (u / v) l (𝓝 1)) : u ~[l] v := by
  rw [isEquivalent_iff_exists_eq_mul]
  exact ⟨u / v, huv, hz.mono fun x hz' ↦ (div_mul_cancel_of_imp hz').symm⟩

theorem isEquivalent_of_tendsto_one' (hz : ∀ x, v x = 0 → u x = 0) (huv : Tendsto (u / v) l (𝓝 1)) :
    u ~[l] v :=
  isEquivalent_of_tendsto_one (Eventually.of_forall hz) huv

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

end NormedField

section SMul

theorem IsEquivalent.smul {α E 𝕜 : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {a b : α → 𝕜} {u v : α → E} {l : Filter α} (hab : a ~[l] b) (huv : u ~[l] v) :
    (fun x ↦ a x • u x) ~[l] fun x ↦ b x • v x := by
  rcases hab.exists_eq_mul with ⟨φ, hφ, habφ⟩
  have : ((fun x ↦ a x • u x) - (fun x ↦ b x • v x)) =ᶠ[l] fun x ↦ b x • (φ x • u x - v x) := by
    convert (habφ.comp₂ (· • ·) <| EventuallyEq.refl _ u).fun_sub
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
        field_simp
  calc
    ‖((fun x : α ↦ φ x • u x) - v) x‖ = ‖(φ x - 1) • u x + (u x - v x)‖ := by
      simp [sub_smul, sub_add]
    _ ≤ ‖(φ x - 1) • u x‖ + ‖u x - v x‖ := norm_add_le _ _
    _ = ‖φ x - 1‖ * ‖u x‖ + ‖u x - v x‖ := by rw [norm_smul]
    _ ≤ c / 2 * ‖v x‖ + ‖u x - v x‖ := by gcongr
    _ ≤ c / 2 * ‖v x‖ + c / 2 * ‖v x‖ := by gcongr; exact huvx
    _ = c * ‖v x‖ := by ring

end SMul

section mul_inv

variable {α ι β : Type*} [NormedField β] {t u v w : α → β} {l : Filter α}

protected theorem IsEquivalent.mul (htu : t ~[l] u) (hvw : v ~[l] w) : t * v ~[l] u * w :=
  htu.smul hvw

theorem IsEquivalent.listProd {L : List ι} {f g : ι → α → β} (h : ∀ i ∈ L, f i ~[l] g i) :
    (fun x ↦ (L.map (f · x)).prod) ~[l] (fun x ↦ (L.map (g · x)).prod) := by
  induction L with
  | nil => simp [IsEquivalent.refl]
  | cons i L ihL =>
    simp only [List.forall_mem_cons, List.map_cons, List.prod_cons] at h ⊢
    exact h.1.mul (ihL h.2)

theorem IsEquivalent.multisetProd {s : Multiset ι} {f g : ι → α → β} (h : ∀ i ∈ s, f i ~[l] g i) :
    (fun x ↦ (s.map (f · x)).prod) ~[l] (fun x ↦ (s.map (g · x)).prod) := by
  obtain ⟨l, rfl⟩ : ∃ l : List ι, ↑l = s := Quotient.mk_surjective s
  exact listProd h

theorem IsEquivalent.finsetProd {s : Finset ι} {f g : ι → α → β} (h : ∀ i ∈ s, f i ~[l] g i) :
    (∏ i ∈ s, f i ·) ~[l] (∏ i ∈ s, g i ·) :=
  multisetProd h

protected theorem IsEquivalent.inv (huv : u ~[l] v) : u⁻¹ ~[l] v⁻¹ := by
  rw [isEquivalent_iff_exists_eq_mul] at *
  rcases huv with ⟨φ, hφ, h⟩
  rw [← inv_one]
  refine ⟨fun x ↦ (φ x)⁻¹, Tendsto.inv₀ hφ (by simp), ?_⟩
  convert h.fun_inv
  simp [mul_comm]

protected theorem IsEquivalent.div (htu : t ~[l] u) (hvw : v ~[l] w) :
    t / v ~[l] u / w := by
  simpa only [div_eq_mul_inv] using htu.mul hvw.inv

protected theorem IsEquivalent.pow (h : t ~[l] u) (n : ℕ) : t ^ n ~[l] u ^ n := by
  induction n with
  | zero => simpa using IsEquivalent.refl
  | succ _ ih => simpa [pow_succ] using ih.mul h

protected theorem IsEquivalent.zpow (h : t ~[l] u) (z : ℤ) : t ^ z ~[l] u ^ z := by
  match z with
  | Int.ofNat _ => simpa using h.pow _
  | Int.negSucc _ => simpa using (h.pow _).inv

end mul_inv

section NormedLinearOrderedField

variable {α β : Type*} [NormedField β] [LinearOrder β] [IsStrictOrderedRing β]
  {u v : α → β} {l : Filter α}

theorem IsEquivalent.tendsto_atTop [OrderTopology β] (huv : u ~[l] v) (hu : Tendsto u l atTop) :
    Tendsto v l atTop :=
  let ⟨φ, hφ, h⟩ := huv.symm.exists_eq_mul
  Tendsto.congr' h.symm (mul_comm u φ ▸ hu.atTop_mul_pos zero_lt_one hφ)

theorem IsEquivalent.tendsto_atTop_iff [OrderTopology β] (huv : u ~[l] v) :
    Tendsto u l atTop ↔ Tendsto v l atTop :=
  ⟨huv.tendsto_atTop, huv.symm.tendsto_atTop⟩

theorem IsEquivalent.tendsto_atBot [OrderTopology β] (huv : u ~[l] v) (hu : Tendsto u l atBot) :
    Tendsto v l atBot := by
  convert tendsto_neg_atTop_atBot.comp (huv.neg.tendsto_atTop <| tendsto_neg_atBot_atTop.comp hu)
  ext
  simp

theorem IsEquivalent.tendsto_atBot_iff [OrderTopology β] (huv : u ~[l] v) :
    Tendsto u l atBot ↔ Tendsto v l atBot :=
  ⟨huv.tendsto_atBot, huv.symm.tendsto_atBot⟩

end NormedLinearOrderedField

section Real

theorem IsEquivalent.add_add_of_nonneg {α : Type*} {u v t w : α → ℝ} {l : Filter α}
    (hu : 0 ≤ v) (hw : 0 ≤ w) (htu : u ~[l] v) (hvw : t ~[l] w) :
    u + t ~[l] v + w := by
  simp only [IsEquivalent, add_sub_add_comm]
  change (fun x ↦ (u - v) x + (t - w) x) =o[l] (fun x ↦ v x + w x)
  conv => enter [3, x]; rw [← abs_eq_self.mpr (hu x), ← abs_eq_self.mpr (hw x)]
  simpa [← Real.norm_eq_abs] using .add_add htu hvw

end Real

end Asymptotics

open Filter Asymptotics

open Asymptotics

variable {α β β₂ : Type*} [NormedAddCommGroup β] [Norm β₂] {l : Filter α}

theorem Filter.EventuallyEq.isEquivalent {u v : α → β} (h : u =ᶠ[l] v) : u ~[l] v :=
  IsEquivalent.congr_right (isLittleO_refl_left _ _) h

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

theorem IsEquivalent.comp_tendsto {α₂ : Type*} {f g : α₂ → β} {l' : Filter α₂}
    (hfg : f ~[l'] g) {k : α → α₂} (hk : Filter.Tendsto k l l') : (f ∘ k) ~[l] (g ∘ k) :=
  IsLittleO.comp_tendsto hfg hk

@[simp]
theorem isEquivalent_map {α₂ : Type*} {f g : α₂ → β} {k : α → α₂} :
    f ~[Filter.map k l] g ↔ (f ∘ k) ~[l] (g ∘ k) :=
  isLittleO_map

theorem IsEquivalent.mono {f g : α → β} {l' : Filter α} (h : f ~[l'] g) (hl : l ≤ l') :
    f ~[l] g :=
  IsLittleO.mono h hl

end Asymptotics
