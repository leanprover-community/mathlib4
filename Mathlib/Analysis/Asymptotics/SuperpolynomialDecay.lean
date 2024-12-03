/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.Normed.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

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

variable {α β : Type*} {l : Filter α} {k : α → β} {f g g' : α → β}

section CommSemiring

variable [TopologicalSpace β] [CommSemiring β]

theorem SuperpolynomialDecay.congr' (hf : SuperpolynomialDecay l k f) (hfg : f =ᶠ[l] g) :
    SuperpolynomialDecay l k g := fun z =>
  (hf z).congr' (EventuallyEq.mul (EventuallyEq.refl l _) hfg)

theorem SuperpolynomialDecay.congr (hf : SuperpolynomialDecay l k f) (hfg : ∀ x, f x = g x) :
    SuperpolynomialDecay l k g := fun z =>
  (hf z).congr fun x => (congr_arg fun a => k x ^ z * a) <| hfg x

@[simp]
theorem superpolynomialDecay_zero (l : Filter α) (k : α → β) : SuperpolynomialDecay l k 0 :=
  fun z => by simpa only [Pi.zero_apply, mul_zero] using tendsto_const_nhds

theorem SuperpolynomialDecay.add [ContinuousAdd β] (hf : SuperpolynomialDecay l k f)
    (hg : SuperpolynomialDecay l k g) : SuperpolynomialDecay l k (f + g) := fun z => by
  simpa only [mul_add, add_zero, Pi.add_apply] using (hf z).add (hg z)

theorem SuperpolynomialDecay.mul [ContinuousMul β] (hf : SuperpolynomialDecay l k f)
    (hg : SuperpolynomialDecay l k g) : SuperpolynomialDecay l k (f * g) := fun z => by
  simpa only [mul_assoc, one_mul, mul_zero, pow_zero] using (hf z).mul (hg 0)

theorem SuperpolynomialDecay.mul_const [ContinuousMul β] (hf : SuperpolynomialDecay l k f) (c : β) :
    SuperpolynomialDecay l k fun n => f n * c := fun z => by
  simpa only [← mul_assoc, zero_mul] using Tendsto.mul_const c (hf z)

theorem SuperpolynomialDecay.const_mul [ContinuousMul β] (hf : SuperpolynomialDecay l k f) (c : β) :
    SuperpolynomialDecay l k fun n => c * f n :=
  (hf.mul_const c).congr fun _ => mul_comm _ _

theorem SuperpolynomialDecay.param_mul (hf : SuperpolynomialDecay l k f) :
    SuperpolynomialDecay l k (k * f) := fun z =>
  tendsto_nhds.2 fun s hs hs0 =>
    l.sets_of_superset ((tendsto_nhds.1 (hf <| z + 1)) s hs hs0) fun x hx => by
      simpa only [Set.mem_preimage, Pi.mul_apply, ← mul_assoc, ← pow_succ] using hx

theorem SuperpolynomialDecay.mul_param (hf : SuperpolynomialDecay l k f) :
    SuperpolynomialDecay l k (f * k) :=
  hf.param_mul.congr fun _ => mul_comm _ _

theorem SuperpolynomialDecay.param_pow_mul (hf : SuperpolynomialDecay l k f) (n : ℕ) :
    SuperpolynomialDecay l k (k ^ n * f) := by
  induction n with
  | zero => simpa only [one_mul, pow_zero] using hf
  | succ n hn => simpa only [pow_succ', mul_assoc] using hn.param_mul

theorem SuperpolynomialDecay.mul_param_pow (hf : SuperpolynomialDecay l k f) (n : ℕ) :
    SuperpolynomialDecay l k (f * k ^ n) :=
  (hf.param_pow_mul n).congr fun _ => mul_comm _ _

theorem SuperpolynomialDecay.polynomial_mul [ContinuousAdd β] [ContinuousMul β]
    (hf : SuperpolynomialDecay l k f) (p : β[X]) :
    SuperpolynomialDecay l k fun x => (p.eval <| k x) * f x :=
  Polynomial.induction_on' p (fun p q hp hq => by simpa [add_mul] using hp.add hq) fun n c => by
    simpa [mul_assoc] using (hf.param_pow_mul n).const_mul c

theorem SuperpolynomialDecay.mul_polynomial [ContinuousAdd β] [ContinuousMul β]
    (hf : SuperpolynomialDecay l k f) (p : β[X]) :
    SuperpolynomialDecay l k fun x => f x * (p.eval <| k x) :=
  (hf.polynomial_mul p).congr fun _ => mul_comm _ _

end CommSemiring

section OrderedCommSemiring

variable [TopologicalSpace β] [OrderedCommSemiring β] [OrderTopology β]

theorem SuperpolynomialDecay.trans_eventuallyLE (hk : 0 ≤ᶠ[l] k) (hg : SuperpolynomialDecay l k g)
    (hg' : SuperpolynomialDecay l k g') (hfg : g ≤ᶠ[l] f) (hfg' : f ≤ᶠ[l] g') :
    SuperpolynomialDecay l k f := fun z =>
  tendsto_of_tendsto_of_tendsto_of_le_of_le' (hg z) (hg' z)
    (hfg.mp (hk.mono fun _ hx hx' => mul_le_mul_of_nonneg_left hx' (pow_nonneg hx z)))
    (hfg'.mp (hk.mono fun _ hx hx' => mul_le_mul_of_nonneg_left hx' (pow_nonneg hx z)))

end OrderedCommSemiring

section LinearOrderedCommRing

variable [TopologicalSpace β] [LinearOrderedCommRing β] [OrderTopology β]
variable (l k f)

theorem superpolynomialDecay_iff_abs_tendsto_zero :
    SuperpolynomialDecay l k f ↔ ∀ n : ℕ, Tendsto (fun a : α => |k a ^ n * f a|) l (𝓝 0) :=
  ⟨fun h z => (tendsto_zero_iff_abs_tendsto_zero _).1 (h z), fun h z =>
    (tendsto_zero_iff_abs_tendsto_zero _).2 (h z)⟩

theorem superpolynomialDecay_iff_superpolynomialDecay_abs :
    SuperpolynomialDecay l k f ↔ SuperpolynomialDecay l (fun a => |k a|) fun a => |f a| :=
  (superpolynomialDecay_iff_abs_tendsto_zero l k f).trans
    (by simp_rw [SuperpolynomialDecay, abs_mul, abs_pow])

variable {l k f}

theorem SuperpolynomialDecay.trans_eventually_abs_le (hf : SuperpolynomialDecay l k f)
    (hfg : abs ∘ g ≤ᶠ[l] abs ∘ f) : SuperpolynomialDecay l k g := by
  rw [superpolynomialDecay_iff_abs_tendsto_zero] at hf ⊢
  refine fun z =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hf z)
      (Eventually.of_forall fun x => abs_nonneg _) (hfg.mono fun x hx => ?_)
  calc
    |k x ^ z * g x| = |k x ^ z| * |g x| := abs_mul (k x ^ z) (g x)
    _ ≤ |k x ^ z| * |f x| := by gcongr _ * ?_; exact hx
    _ = |k x ^ z * f x| := (abs_mul (k x ^ z) (f x)).symm

theorem SuperpolynomialDecay.trans_abs_le (hf : SuperpolynomialDecay l k f)
    (hfg : ∀ x, |g x| ≤ |f x|) : SuperpolynomialDecay l k g :=
  hf.trans_eventually_abs_le (Eventually.of_forall hfg)

end LinearOrderedCommRing

section Field

variable [TopologicalSpace β] [Field β] (l k f)

theorem superpolynomialDecay_mul_const_iff [ContinuousMul β] {c : β} (hc0 : c ≠ 0) :
    (SuperpolynomialDecay l k fun n => f n * c) ↔ SuperpolynomialDecay l k f :=
  ⟨fun h => (h.mul_const c⁻¹).congr fun x => by simp [mul_assoc, mul_inv_cancel₀ hc0], fun h =>
    h.mul_const c⟩

theorem superpolynomialDecay_const_mul_iff [ContinuousMul β] {c : β} (hc0 : c ≠ 0) :
    (SuperpolynomialDecay l k fun n => c * f n) ↔ SuperpolynomialDecay l k f :=
  ⟨fun h => (h.const_mul c⁻¹).congr fun x => by simp [← mul_assoc, inv_mul_cancel₀ hc0], fun h =>
    h.const_mul c⟩

variable {l k f}

end Field

section LinearOrderedField

variable [TopologicalSpace β] [LinearOrderedField β] [OrderTopology β]
variable (f)

theorem superpolynomialDecay_iff_abs_isBoundedUnder (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔
    ∀ z : ℕ, IsBoundedUnder (· ≤ ·) l fun a : α => |k a ^ z * f a| := by
  refine
    ⟨fun h z => Tendsto.isBoundedUnder_le (Tendsto.abs (h z)), fun h =>
      (superpolynomialDecay_iff_abs_tendsto_zero l k f).2 fun z => ?_⟩
  obtain ⟨m, hm⟩ := h (z + 1)
  have h1 : Tendsto (fun _ : α => (0 : β)) l (𝓝 0) := tendsto_const_nhds
  have h2 : Tendsto (fun a : α => |(k a)⁻¹| * m) l (𝓝 0) :=
    zero_mul m ▸
      Tendsto.mul_const m ((tendsto_zero_iff_abs_tendsto_zero _).1 hk.inv_tendsto_atTop)
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2 (Eventually.of_forall fun x => abs_nonneg _)
      ((eventually_map.1 hm).mp ?_)
  refine (hk.eventually_ne_atTop 0).mono fun x hk0 hx => ?_
  refine Eq.trans_le ?_ (mul_le_mul_of_nonneg_left hx <| abs_nonneg (k x)⁻¹)
  rw [← abs_mul, ← mul_assoc, pow_succ', ← mul_assoc, inv_mul_cancel₀ hk0, one_mul]

theorem superpolynomialDecay_iff_zpow_tendsto_zero (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔ ∀ z : ℤ, Tendsto (fun a : α => k a ^ z * f a) l (𝓝 0) := by
  refine ⟨fun h z => ?_, fun h n => by simpa only [zpow_natCast] using h (n : ℤ)⟩
  by_cases hz : 0 ≤ z
  · unfold Tendsto
    lift z to ℕ using hz
    simpa using h z
  · have : Tendsto (fun a => k a ^ z) l (𝓝 0) :=
      Tendsto.comp (tendsto_zpow_atTop_zero (not_le.1 hz)) hk
    have h : Tendsto f l (𝓝 0) := by simpa using h 0
    exact zero_mul (0 : β) ▸ this.mul h

variable {f}

theorem SuperpolynomialDecay.param_zpow_mul (hk : Tendsto k l atTop)
    (hf : SuperpolynomialDecay l k f) (z : ℤ) :
    SuperpolynomialDecay l k fun a => k a ^ z * f a := by
  rw [superpolynomialDecay_iff_zpow_tendsto_zero _ hk] at hf ⊢
  refine fun z' => (hf <| z' + z).congr' ((hk.eventually_ne_atTop 0).mono fun x hx => ?_)
  simp [zpow_add₀ hx, mul_assoc, Pi.mul_apply]

theorem SuperpolynomialDecay.mul_param_zpow (hk : Tendsto k l atTop)
    (hf : SuperpolynomialDecay l k f) (z : ℤ) : SuperpolynomialDecay l k fun a => f a * k a ^ z :=
  (hf.param_zpow_mul hk z).congr fun _ => mul_comm _ _

theorem SuperpolynomialDecay.inv_param_mul (hk : Tendsto k l atTop)
    (hf : SuperpolynomialDecay l k f) : SuperpolynomialDecay l k (k⁻¹ * f) := by
  simpa using hf.param_zpow_mul hk (-1)

theorem SuperpolynomialDecay.param_inv_mul (hk : Tendsto k l atTop)
    (hf : SuperpolynomialDecay l k f) : SuperpolynomialDecay l k (f * k⁻¹) :=
  (hf.inv_param_mul hk).congr fun _ => mul_comm _ _

variable (f)

theorem superpolynomialDecay_param_mul_iff (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k (k * f) ↔ SuperpolynomialDecay l k f :=
  ⟨fun h =>
    (h.inv_param_mul hk).congr'
      ((hk.eventually_ne_atTop 0).mono fun x hx => by simp [← mul_assoc, inv_mul_cancel₀ hx]),
    fun h => h.param_mul⟩

theorem superpolynomialDecay_mul_param_iff (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k (f * k) ↔ SuperpolynomialDecay l k f := by
  simpa [mul_comm k] using superpolynomialDecay_param_mul_iff f hk

theorem superpolynomialDecay_param_pow_mul_iff (hk : Tendsto k l atTop) (n : ℕ) :
    SuperpolynomialDecay l k (k ^ n * f) ↔ SuperpolynomialDecay l k f := by
  induction n with
  | zero => simp
  | succ n hn =>
    simpa [pow_succ, ← mul_comm k, mul_assoc,
      superpolynomialDecay_param_mul_iff (k ^ n * f) hk] using hn

theorem superpolynomialDecay_mul_param_pow_iff (hk : Tendsto k l atTop) (n : ℕ) :
    SuperpolynomialDecay l k (f * k ^ n) ↔ SuperpolynomialDecay l k f := by
  simpa [mul_comm f] using superpolynomialDecay_param_pow_mul_iff f hk n

variable {f}

end LinearOrderedField

section NormedLinearOrderedField

variable [NormedLinearOrderedField β]
variable (l k f)

theorem superpolynomialDecay_iff_norm_tendsto_zero :
    SuperpolynomialDecay l k f ↔ ∀ n : ℕ, Tendsto (fun a : α => ‖k a ^ n * f a‖) l (𝓝 0) :=
  ⟨fun h z => tendsto_zero_iff_norm_tendsto_zero.1 (h z), fun h z =>
    tendsto_zero_iff_norm_tendsto_zero.2 (h z)⟩

theorem superpolynomialDecay_iff_superpolynomialDecay_norm :
    SuperpolynomialDecay l k f ↔ SuperpolynomialDecay l (fun a => ‖k a‖) fun a => ‖f a‖ :=
  (superpolynomialDecay_iff_norm_tendsto_zero l k f).trans (by simp [SuperpolynomialDecay])

variable {l k}
variable [OrderTopology β]

theorem superpolynomialDecay_iff_isBigO (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔ ∀ z : ℤ, f =O[l] fun a : α => k a ^ z := by
  refine (superpolynomialDecay_iff_zpow_tendsto_zero f hk).trans ?_
  have hk0 : ∀ᶠ x in l, k x ≠ 0 := hk.eventually_ne_atTop 0
  refine ⟨fun h z => ?_, fun h z => ?_⟩
  · refine isBigO_of_div_tendsto_nhds (hk0.mono fun x hx hxz ↦ absurd hxz (zpow_ne_zero _ hx)) 0 ?_
    have : (fun a : α => k a ^ z)⁻¹ = fun a : α => k a ^ (-z) := funext fun x => by simp
    rw [div_eq_mul_inv, mul_comm f, this]
    exact h (-z)
  · suffices (fun a : α => k a ^ z * f a) =O[l] fun a : α => (k a)⁻¹ from
      IsBigO.trans_tendsto this hk.inv_tendsto_atTop
    refine
      ((isBigO_refl (fun a => k a ^ z) l).mul (h (-(z + 1)))).trans
        (IsBigO.of_bound 1 <| hk0.mono fun a ha0 => ?_)
    simp only [one_mul, neg_add z 1, zpow_add₀ ha0, ← mul_assoc, zpow_neg,
      mul_inv_cancel₀ (zpow_ne_zero z ha0), zpow_one]
    rfl

theorem superpolynomialDecay_iff_isLittleO (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔ ∀ z : ℤ, f =o[l] fun a : α => k a ^ z := by
  refine ⟨fun h z => ?_, fun h => (superpolynomialDecay_iff_isBigO f hk).2 fun z => (h z).isBigO⟩
  have hk0 : ∀ᶠ x in l, k x ≠ 0 := hk.eventually_ne_atTop 0
  have : (fun _ : α => (1 : β)) =o[l] k :=
    isLittleO_of_tendsto' (hk0.mono fun x hkx hkx' => absurd hkx' hkx)
      (by simpa using hk.inv_tendsto_atTop)
  have : f =o[l] fun x : α => k x * k x ^ (z - 1) := by
    simpa using this.mul_isBigO ((superpolynomialDecay_iff_isBigO f hk).1 h <| z - 1)
  refine this.trans_isBigO (IsBigO.of_bound 1 (hk0.mono fun x hkx => le_of_eq ?_))
  rw [one_mul, zpow_sub_one₀ hkx, mul_comm (k x), mul_assoc, inv_mul_cancel₀ hkx, mul_one]

end NormedLinearOrderedField

end Asymptotics
