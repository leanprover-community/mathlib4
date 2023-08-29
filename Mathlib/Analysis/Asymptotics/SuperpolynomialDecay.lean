/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.Normed.Order.Basic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Topology.Algebra.Order.LiminfLimsup

#align_import analysis.asymptotics.superpolynomial_decay from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Super-Polynomial Function Decay

This file defines a predicate `Asymptotics.SuperpolynomialDecay f` for a function satisfying
  one of following equivalent definitions (The definition is in terms of the first condition):

* `x ^ n * f` tends to `𝓝 0` for all (or sufficiently large) naturals `n`
* `|x ^ n * f|` tends to `𝓝 0` for all naturals `n` (`superpolynomialDecay_iff_abs_tendsto_zero`)
* `|x ^ n * f|` is bounded for all naturals `n` (`superpolynomialDecay_iff_abs_isBoundedUnder`)
* `f` is `o(x ^ c)` for all integers `c` (`superpolynomialDecay_iff_isLittleO`)
* `f` is `O(x ^ c)` for all integers `c` (`superpolynomialDecay_iff_isBigO`)

These conditions are all equivalent to conditions in terms of polynomials, replacing `x ^ c` with
  `p(x)` or `p(x)⁻¹` as appropriate, since asymptotically `p(x)` behaves like `X ^ p.natDegree`.
These further equivalences are not proven in mathlib but would be good future projects.

The definition of superpolynomial decay for `f : α → β` is relative to a parameter `k : α → β`.
Super-polynomial decay then means `f x` decays faster than `(k x) ^ c` for all integers `c`.
Equivalently `f x` decays faster than `p.eval (k x)` for all polynomials `p : β[X]`.
The definition is also relative to a filter `l : Filter α` where the decay rate is compared.

When the map `k` is given by `n ↦ ↑n : ℕ → ℝ` this defines negligible functions:
https://en.wikipedia.org/wiki/Negligible_function

When the map `k` is given by `(r₁,...,rₙ) ↦ r₁*...*rₙ : ℝⁿ → ℝ` this is equivalent
  to the definition of rapidly decreasing functions given here:
https://ncatlab.org/nlab/show/rapidly+decreasing+function

# Main Theorems

* `SuperpolynomialDecay.polynomial_mul` says that if `f(x)` is negligible,
    then so is `p(x) * f(x)` for any polynomial `p`.
* `superpolynomialDecay_iff_zpow_tendsto_zero` gives an equivalence between definitions in terms
    of decaying faster than `k(x) ^ n` for all naturals `n` or `k(x) ^ c` for all integer `c`.
-/


namespace Asymptotics

open Topology Polynomial

open Filter

/-- `f` has superpolynomial decay in parameter `k` along filter `l` if
  `k ^ n * f` tends to zero at `l` for all naturals `n` -/
def SuperpolynomialDecay {α β : Type*} [TopologicalSpace β] [CommSemiring β] (l : Filter α)
    (k : α → β) (f : α → β) :=
  ∀ n : ℕ, Tendsto (fun a : α => k a ^ n * f a) l (𝓝 0)
#align asymptotics.superpolynomial_decay Asymptotics.SuperpolynomialDecay

variable {α β : Type*} {l : Filter α} {k : α → β} {f g g' : α → β}

section CommSemiring

variable [TopologicalSpace β] [CommSemiring β]

theorem SuperpolynomialDecay.congr' (hf : SuperpolynomialDecay l k f) (hfg : f =ᶠ[l] g) :
    SuperpolynomialDecay l k g := fun z =>
  (hf z).congr' (EventuallyEq.mul (EventuallyEq.refl l _) hfg)
#align asymptotics.superpolynomial_decay.congr' Asymptotics.SuperpolynomialDecay.congr'

theorem SuperpolynomialDecay.congr (hf : SuperpolynomialDecay l k f) (hfg : ∀ x, f x = g x) :
    SuperpolynomialDecay l k g := fun z =>
  (hf z).congr fun x => (congr_arg fun a => k x ^ z * a) <| hfg x
#align asymptotics.superpolynomial_decay.congr Asymptotics.SuperpolynomialDecay.congr

@[simp]
theorem superpolynomialDecay_zero (l : Filter α) (k : α → β) : SuperpolynomialDecay l k 0 :=
  fun z => by simpa only [Pi.zero_apply, mul_zero] using tendsto_const_nhds
              -- 🎉 no goals
#align asymptotics.superpolynomial_decay_zero Asymptotics.superpolynomialDecay_zero

theorem SuperpolynomialDecay.add [ContinuousAdd β] (hf : SuperpolynomialDecay l k f)
    (hg : SuperpolynomialDecay l k g) : SuperpolynomialDecay l k (f + g) := fun z => by
  simpa only [mul_add, add_zero, Pi.add_apply] using (hf z).add (hg z)
  -- 🎉 no goals
#align asymptotics.superpolynomial_decay.add Asymptotics.SuperpolynomialDecay.add

theorem SuperpolynomialDecay.mul [ContinuousMul β] (hf : SuperpolynomialDecay l k f)
    (hg : SuperpolynomialDecay l k g) : SuperpolynomialDecay l k (f * g) := fun z => by
  simpa only [mul_assoc, one_mul, mul_zero, pow_zero] using (hf z).mul (hg 0)
  -- 🎉 no goals
#align asymptotics.superpolynomial_decay.mul Asymptotics.SuperpolynomialDecay.mul

theorem SuperpolynomialDecay.mul_const [ContinuousMul β] (hf : SuperpolynomialDecay l k f) (c : β) :
    SuperpolynomialDecay l k fun n => f n * c := fun z => by
  simpa only [← mul_assoc, zero_mul] using Tendsto.mul_const c (hf z)
  -- 🎉 no goals
#align asymptotics.superpolynomial_decay.mul_const Asymptotics.SuperpolynomialDecay.mul_const

theorem SuperpolynomialDecay.const_mul [ContinuousMul β] (hf : SuperpolynomialDecay l k f) (c : β) :
    SuperpolynomialDecay l k fun n => c * f n :=
  (hf.mul_const c).congr fun _ => mul_comm _ _
#align asymptotics.superpolynomial_decay.const_mul Asymptotics.SuperpolynomialDecay.const_mul

theorem SuperpolynomialDecay.param_mul (hf : SuperpolynomialDecay l k f) :
    SuperpolynomialDecay l k (k * f) := fun z =>
  tendsto_nhds.2 fun s hs hs0 =>
    l.sets_of_superset ((tendsto_nhds.1 (hf <| z + 1)) s hs hs0) fun x hx => by
      simpa only [Set.mem_preimage, Pi.mul_apply, ← mul_assoc, ← pow_succ'] using hx
      -- 🎉 no goals
#align asymptotics.superpolynomial_decay.param_mul Asymptotics.SuperpolynomialDecay.param_mul

theorem SuperpolynomialDecay.mul_param (hf : SuperpolynomialDecay l k f) :
    SuperpolynomialDecay l k (f * k) :=
  hf.param_mul.congr fun _ => mul_comm _ _
#align asymptotics.superpolynomial_decay.mul_param Asymptotics.SuperpolynomialDecay.mul_param

theorem SuperpolynomialDecay.param_pow_mul (hf : SuperpolynomialDecay l k f) (n : ℕ) :
    SuperpolynomialDecay l k (k ^ n * f) := by
  induction' n with n hn
  -- ⊢ SuperpolynomialDecay l k (k ^ Nat.zero * f)
  · simpa only [Nat.zero_eq, one_mul, pow_zero] using hf
    -- 🎉 no goals
  · simpa only [pow_succ, mul_assoc] using hn.param_mul
    -- 🎉 no goals
#align asymptotics.superpolynomial_decay.param_pow_mul Asymptotics.SuperpolynomialDecay.param_pow_mul

theorem SuperpolynomialDecay.mul_param_pow (hf : SuperpolynomialDecay l k f) (n : ℕ) :
    SuperpolynomialDecay l k (f * k ^ n) :=
  (hf.param_pow_mul n).congr fun _ => mul_comm _ _
#align asymptotics.superpolynomial_decay.mul_param_pow Asymptotics.SuperpolynomialDecay.mul_param_pow

theorem SuperpolynomialDecay.polynomial_mul [ContinuousAdd β] [ContinuousMul β]
    (hf : SuperpolynomialDecay l k f) (p : β[X]) :
    SuperpolynomialDecay l k fun x => (p.eval <| k x) * f x :=
  Polynomial.induction_on' p (fun p q hp hq => by simpa [add_mul] using hp.add hq) fun n c => by
                                                  -- 🎉 no goals
    simpa [mul_assoc] using (hf.param_pow_mul n).const_mul c
    -- 🎉 no goals
#align asymptotics.superpolynomial_decay.polynomial_mul Asymptotics.SuperpolynomialDecay.polynomial_mul

theorem SuperpolynomialDecay.mul_polynomial [ContinuousAdd β] [ContinuousMul β]
    (hf : SuperpolynomialDecay l k f) (p : β[X]) :
    SuperpolynomialDecay l k fun x => f x * (p.eval <| k x) :=
  (hf.polynomial_mul p).congr fun _ => mul_comm _ _
#align asymptotics.superpolynomial_decay.mul_polynomial Asymptotics.SuperpolynomialDecay.mul_polynomial

end CommSemiring

section OrderedCommSemiring

variable [TopologicalSpace β] [OrderedCommSemiring β] [OrderTopology β]

theorem SuperpolynomialDecay.trans_eventuallyLE (hk : 0 ≤ᶠ[l] k) (hg : SuperpolynomialDecay l k g)
    (hg' : SuperpolynomialDecay l k g') (hfg : g ≤ᶠ[l] f) (hfg' : f ≤ᶠ[l] g') :
    SuperpolynomialDecay l k f := fun z =>
  tendsto_of_tendsto_of_tendsto_of_le_of_le' (hg z) (hg' z)
    (hfg.mp (hk.mono fun _ hx hx' => mul_le_mul_of_nonneg_left hx' (pow_nonneg hx z)))
    (hfg'.mp (hk.mono fun _ hx hx' => mul_le_mul_of_nonneg_left hx' (pow_nonneg hx z)))
#align asymptotics.superpolynomial_decay.trans_eventually_le Asymptotics.SuperpolynomialDecay.trans_eventuallyLE

end OrderedCommSemiring

section LinearOrderedCommRing

variable [TopologicalSpace β] [LinearOrderedCommRing β] [OrderTopology β]

variable (l k f)

theorem superpolynomialDecay_iff_abs_tendsto_zero :
    SuperpolynomialDecay l k f ↔ ∀ n : ℕ, Tendsto (fun a : α => |k a ^ n * f a|) l (𝓝 0) :=
  ⟨fun h z => (tendsto_zero_iff_abs_tendsto_zero _).1 (h z), fun h z =>
    (tendsto_zero_iff_abs_tendsto_zero _).2 (h z)⟩
#align asymptotics.superpolynomial_decay_iff_abs_tendsto_zero Asymptotics.superpolynomialDecay_iff_abs_tendsto_zero

theorem superpolynomialDecay_iff_superpolynomialDecay_abs :
    SuperpolynomialDecay l k f ↔ SuperpolynomialDecay l (fun a => |k a|) fun a => |f a| :=
  (superpolynomialDecay_iff_abs_tendsto_zero l k f).trans
    (by simp_rw [SuperpolynomialDecay, abs_mul, abs_pow])
        -- 🎉 no goals
#align asymptotics.superpolynomial_decay_iff_superpolynomial_decay_abs Asymptotics.superpolynomialDecay_iff_superpolynomialDecay_abs

variable {l k f}

theorem SuperpolynomialDecay.trans_eventually_abs_le (hf : SuperpolynomialDecay l k f)
    (hfg : abs ∘ g ≤ᶠ[l] abs ∘ f) : SuperpolynomialDecay l k g := by
  rw [superpolynomialDecay_iff_abs_tendsto_zero] at hf ⊢
  -- ⊢ ∀ (n : ℕ), Tendsto (fun a => |k a ^ n * g a|) l (𝓝 0)
  refine' fun z =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hf z)
      (eventually_of_forall fun x => abs_nonneg _) (hfg.mono fun x hx => _)
  calc
    |k x ^ z * g x| = |k x ^ z| * |g x| := abs_mul (k x ^ z) (g x)
    _ ≤ |k x ^ z| * |f x| := by gcongr; exact hx
    _ = |k x ^ z * f x| := (abs_mul (k x ^ z) (f x)).symm
#align asymptotics.superpolynomial_decay.trans_eventually_abs_le Asymptotics.SuperpolynomialDecay.trans_eventually_abs_le

theorem SuperpolynomialDecay.trans_abs_le (hf : SuperpolynomialDecay l k f)
    (hfg : ∀ x, |g x| ≤ |f x|) : SuperpolynomialDecay l k g :=
  hf.trans_eventually_abs_le (eventually_of_forall hfg)
#align asymptotics.superpolynomial_decay.trans_abs_le Asymptotics.SuperpolynomialDecay.trans_abs_le

end LinearOrderedCommRing

section Field

variable [TopologicalSpace β] [Field β] (l k f)

theorem superpolynomialDecay_mul_const_iff [ContinuousMul β] {c : β} (hc0 : c ≠ 0) :
    (SuperpolynomialDecay l k fun n => f n * c) ↔ SuperpolynomialDecay l k f :=
  ⟨fun h => (h.mul_const c⁻¹).congr fun x => by simp [mul_assoc, mul_inv_cancel hc0], fun h =>
                                                -- 🎉 no goals
    h.mul_const c⟩
#align asymptotics.superpolynomial_decay_mul_const_iff Asymptotics.superpolynomialDecay_mul_const_iff

theorem superpolynomialDecay_const_mul_iff [ContinuousMul β] {c : β} (hc0 : c ≠ 0) :
    (SuperpolynomialDecay l k fun n => c * f n) ↔ SuperpolynomialDecay l k f :=
  ⟨fun h => (h.const_mul c⁻¹).congr fun x => by simp [← mul_assoc, inv_mul_cancel hc0], fun h =>
                                                -- 🎉 no goals
    h.const_mul c⟩
#align asymptotics.superpolynomial_decay_const_mul_iff Asymptotics.superpolynomialDecay_const_mul_iff

variable {l k f}

end Field

section LinearOrderedField

variable [TopologicalSpace β] [LinearOrderedField β] [OrderTopology β]

variable (f)

theorem superpolynomialDecay_iff_abs_isBoundedUnder (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔
    ∀ z : ℕ, IsBoundedUnder (· ≤ ·) l fun a : α => |k a ^ z * f a| := by
  refine'
    ⟨fun h z => Tendsto.isBoundedUnder_le (Tendsto.abs (h z)), fun h =>
      (superpolynomialDecay_iff_abs_tendsto_zero l k f).2 fun z => _⟩
  obtain ⟨m, hm⟩ := h (z + 1)
  -- ⊢ Tendsto (fun a => |k a ^ z * f a|) l (𝓝 0)
  have h1 : Tendsto (fun _ : α => (0 : β)) l (𝓝 0) := tendsto_const_nhds
  -- ⊢ Tendsto (fun a => |k a ^ z * f a|) l (𝓝 0)
  have h2 : Tendsto (fun a : α => |(k a)⁻¹| * m) l (𝓝 0) :=
    zero_mul m ▸
      Tendsto.mul_const m ((tendsto_zero_iff_abs_tendsto_zero _).1 hk.inv_tendsto_atTop)
  refine'
    tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2 (eventually_of_forall fun x => abs_nonneg _)
      ((eventually_map.1 hm).mp _)
  refine' (hk.eventually_ne_atTop 0).mono fun x hk0 hx => _
  -- ⊢ |k x ^ z * f x| ≤ |(k x)⁻¹| * m
  refine' Eq.trans_le _ (mul_le_mul_of_nonneg_left hx <| abs_nonneg (k x)⁻¹)
  -- ⊢ |k x ^ z * f x| = |(k x)⁻¹| * |k x ^ (z + 1) * f x|
  rw [← abs_mul, ← mul_assoc, pow_succ, ← mul_assoc, inv_mul_cancel hk0, one_mul]
  -- 🎉 no goals
#align asymptotics.superpolynomial_decay_iff_abs_is_bounded_under Asymptotics.superpolynomialDecay_iff_abs_isBoundedUnder

theorem superpolynomialDecay_iff_zpow_tendsto_zero (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔ ∀ z : ℤ, Tendsto (fun a : α => k a ^ z * f a) l (𝓝 0) := by
  refine' ⟨fun h z => _, fun h n => by simpa only [zpow_ofNat] using h (n : ℤ)⟩
  -- ⊢ Tendsto (fun a => k a ^ z * f a) l (𝓝 0)
  by_cases hz : 0 ≤ z
  -- ⊢ Tendsto (fun a => k a ^ z * f a) l (𝓝 0)
  · unfold Tendsto
    -- ⊢ Filter.map (fun a => k a ^ z * f a) l ≤ 𝓝 0
    lift z to ℕ using hz
    -- ⊢ Filter.map (fun a => k a ^ ↑z * f a) l ≤ 𝓝 0
    simpa using h z
    -- 🎉 no goals
  · have : Tendsto (fun a => k a ^ z) l (𝓝 0) :=
      Tendsto.comp (tendsto_zpow_atTop_zero (not_le.1 hz)) hk
    have h : Tendsto f l (𝓝 0) := by simpa using h 0
    -- ⊢ Tendsto (fun a => k a ^ z * f a) l (𝓝 0)
    exact zero_mul (0 : β) ▸ this.mul h
    -- 🎉 no goals
#align asymptotics.superpolynomial_decay_iff_zpow_tendsto_zero Asymptotics.superpolynomialDecay_iff_zpow_tendsto_zero

variable {f}

theorem SuperpolynomialDecay.param_zpow_mul (hk : Tendsto k l atTop)
    (hf : SuperpolynomialDecay l k f) (z : ℤ) :
    SuperpolynomialDecay l k fun a => k a ^ z * f a := by
  rw [superpolynomialDecay_iff_zpow_tendsto_zero _ hk] at hf ⊢
  -- ⊢ ∀ (z_1 : ℤ), Tendsto (fun a => k a ^ z_1 * (k a ^ z * f a)) l (𝓝 0)
  refine' fun z' => (hf <| z' + z).congr' ((hk.eventually_ne_atTop 0).mono fun x hx => _)
  -- ⊢ k x ^ (z' + z) * f x = (fun a => k a ^ z' * (k a ^ z * f a)) x
  simp [zpow_add₀ hx, mul_assoc, Pi.mul_apply]
  -- 🎉 no goals
#align asymptotics.superpolynomial_decay.param_zpow_mul Asymptotics.SuperpolynomialDecay.param_zpow_mul

theorem SuperpolynomialDecay.mul_param_zpow (hk : Tendsto k l atTop)
    (hf : SuperpolynomialDecay l k f) (z : ℤ) : SuperpolynomialDecay l k fun a => f a * k a ^ z :=
  (hf.param_zpow_mul hk z).congr fun _ => mul_comm _ _
#align asymptotics.superpolynomial_decay.mul_param_zpow Asymptotics.SuperpolynomialDecay.mul_param_zpow

theorem SuperpolynomialDecay.inv_param_mul (hk : Tendsto k l atTop)
    (hf : SuperpolynomialDecay l k f) : SuperpolynomialDecay l k (k⁻¹ * f) := by
  simpa using hf.param_zpow_mul hk (-1)
  -- 🎉 no goals
#align asymptotics.superpolynomial_decay.inv_param_mul Asymptotics.SuperpolynomialDecay.inv_param_mul

theorem SuperpolynomialDecay.param_inv_mul (hk : Tendsto k l atTop)
    (hf : SuperpolynomialDecay l k f) : SuperpolynomialDecay l k (f * k⁻¹) :=
  (hf.inv_param_mul hk).congr fun _ => mul_comm _ _
#align asymptotics.superpolynomial_decay.param_inv_mul Asymptotics.SuperpolynomialDecay.param_inv_mul

variable (f)

theorem superpolynomialDecay_param_mul_iff (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k (k * f) ↔ SuperpolynomialDecay l k f :=
  ⟨fun h =>
    (h.inv_param_mul hk).congr'
      ((hk.eventually_ne_atTop 0).mono fun x hx => by simp [← mul_assoc, inv_mul_cancel hx]),
                                                      -- 🎉 no goals
    fun h => h.param_mul⟩
#align asymptotics.superpolynomial_decay_param_mul_iff Asymptotics.superpolynomialDecay_param_mul_iff

theorem superpolynomialDecay_mul_param_iff (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k (f * k) ↔ SuperpolynomialDecay l k f := by
  simpa [mul_comm k] using superpolynomialDecay_param_mul_iff f hk
  -- 🎉 no goals
#align asymptotics.superpolynomial_decay_mul_param_iff Asymptotics.superpolynomialDecay_mul_param_iff

theorem superpolynomialDecay_param_pow_mul_iff (hk : Tendsto k l atTop) (n : ℕ) :
    SuperpolynomialDecay l k (k ^ n * f) ↔ SuperpolynomialDecay l k f := by
  induction' n with n hn
  -- ⊢ SuperpolynomialDecay l k (k ^ Nat.zero * f) ↔ SuperpolynomialDecay l k f
  · simp
    -- 🎉 no goals
  · simpa [pow_succ, ← mul_comm k, mul_assoc,
      superpolynomialDecay_param_mul_iff (k ^ n * f) hk] using hn
#align asymptotics.superpolynomial_decay_param_pow_mul_iff Asymptotics.superpolynomialDecay_param_pow_mul_iff

theorem superpolynomialDecay_mul_param_pow_iff (hk : Tendsto k l atTop) (n : ℕ) :
    SuperpolynomialDecay l k (f * k ^ n) ↔ SuperpolynomialDecay l k f := by
  simpa [mul_comm f] using superpolynomialDecay_param_pow_mul_iff f hk n
  -- 🎉 no goals
#align asymptotics.superpolynomial_decay_mul_param_pow_iff Asymptotics.superpolynomialDecay_mul_param_pow_iff

variable {f}

end LinearOrderedField

section NormedLinearOrderedField

variable [NormedLinearOrderedField β]

variable (l k f)

theorem superpolynomialDecay_iff_norm_tendsto_zero :
    SuperpolynomialDecay l k f ↔ ∀ n : ℕ, Tendsto (fun a : α => ‖k a ^ n * f a‖) l (𝓝 0) :=
  ⟨fun h z => tendsto_zero_iff_norm_tendsto_zero.1 (h z), fun h z =>
    tendsto_zero_iff_norm_tendsto_zero.2 (h z)⟩
#align asymptotics.superpolynomial_decay_iff_norm_tendsto_zero Asymptotics.superpolynomialDecay_iff_norm_tendsto_zero

theorem superpolynomialDecay_iff_superpolynomialDecay_norm :
    SuperpolynomialDecay l k f ↔ SuperpolynomialDecay l (fun a => ‖k a‖) fun a => ‖f a‖ :=
  (superpolynomialDecay_iff_norm_tendsto_zero l k f).trans (by simp [SuperpolynomialDecay])
                                                               -- 🎉 no goals
#align asymptotics.superpolynomial_decay_iff_superpolynomial_decay_norm Asymptotics.superpolynomialDecay_iff_superpolynomialDecay_norm

variable {l k}

variable [OrderTopology β]

theorem superpolynomialDecay_iff_isBigO (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔ ∀ z : ℤ, f =O[l] fun a : α => k a ^ z := by
  refine' (superpolynomialDecay_iff_zpow_tendsto_zero f hk).trans _
  -- ⊢ (∀ (z : ℤ), Tendsto (fun a => k a ^ z * f a) l (𝓝 0)) ↔ ∀ (z : ℤ), f =O[l] f …
  have hk0 : ∀ᶠ x in l, k x ≠ 0 := hk.eventually_ne_atTop 0
  -- ⊢ (∀ (z : ℤ), Tendsto (fun a => k a ^ z * f a) l (𝓝 0)) ↔ ∀ (z : ℤ), f =O[l] f …
  refine' ⟨fun h z => _, fun h z => _⟩
  -- ⊢ f =O[l] fun a => k a ^ z
  · refine' isBigO_of_div_tendsto_nhds (hk0.mono fun x hx hxz => absurd (zpow_eq_zero hxz) hx) 0 _
    -- ⊢ Tendsto (f / fun a => k a ^ z) l (𝓝 0)
    have : (fun a : α => k a ^ z)⁻¹ = fun a : α => k a ^ (-z) := funext fun x => by simp
    -- ⊢ Tendsto (f / fun a => k a ^ z) l (𝓝 0)
    rw [div_eq_mul_inv, mul_comm f, this]
    -- ⊢ Tendsto ((fun a => k a ^ (-z)) * f) l (𝓝 0)
    exact h (-z)
    -- 🎉 no goals
  · suffices : (fun a : α => k a ^ z * f a) =O[l] fun a : α => (k a)⁻¹
    -- ⊢ Tendsto (fun a => k a ^ z * f a) l (𝓝 0)
    exact IsBigO.trans_tendsto this hk.inv_tendsto_atTop
    -- ⊢ (fun a => k a ^ z * f a) =O[l] fun a => (k a)⁻¹
    refine'
      ((isBigO_refl (fun a => k a ^ z) l).mul (h (-(z + 1)))).trans
        (IsBigO.of_bound 1 <| hk0.mono fun a ha0 => _)
    simp only [one_mul, neg_add z 1, zpow_add₀ ha0, ← mul_assoc, zpow_neg,
      mul_inv_cancel (zpow_ne_zero z ha0), zpow_one]
    rfl
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align asymptotics.superpolynomial_decay_iff_is_O Asymptotics.superpolynomialDecay_iff_isBigO

theorem superpolynomialDecay_iff_isLittleO (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔ ∀ z : ℤ, f =o[l] fun a : α => k a ^ z := by
  refine' ⟨fun h z => _, fun h => (superpolynomialDecay_iff_isBigO f hk).2 fun z => (h z).isBigO⟩
  -- ⊢ f =o[l] fun a => k a ^ z
  have hk0 : ∀ᶠ x in l, k x ≠ 0 := hk.eventually_ne_atTop 0
  -- ⊢ f =o[l] fun a => k a ^ z
  have : (fun _ : α => (1 : β)) =o[l] k :=
    isLittleO_of_tendsto' (hk0.mono fun x hkx hkx' => absurd hkx' hkx)
      (by simpa using hk.inv_tendsto_atTop)
  have : f =o[l] fun x : α => k x * k x ^ (z - 1) := by
    simpa using this.mul_isBigO ((superpolynomialDecay_iff_isBigO f hk).1 h <| z - 1)
  refine' this.trans_isBigO (IsBigO.of_bound 1 (hk0.mono fun x hkx => le_of_eq _))
  -- ⊢ ‖k x * k x ^ (z - 1)‖ = 1 * ‖k x ^ z‖
  rw [one_mul, zpow_sub_one₀ hkx, mul_comm (k x), mul_assoc, inv_mul_cancel hkx, mul_one]
  -- 🎉 no goals
#align asymptotics.superpolynomial_decay_iff_is_o Asymptotics.superpolynomialDecay_iff_isLittleO

end NormedLinearOrderedField

end Asymptotics
