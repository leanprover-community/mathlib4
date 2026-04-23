/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
import Batteries.Tactic.Trans
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Map
import Mathlib.Order.Filter.Prod
meta import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.NhdsWithin

/-!
# Asymptotics

We introduce these relations:

* `IsBigOWith c l f g` : "f is big O of g along l with constant c";
* `f =O[l] g` : "f is big O of g along l";
* `f =Θ[l] g` : "f is big O of g along l and vice versa";
* `f =o[l] g` : "f is little o of g along l";
* `f ~[l] g` : `f` and `g` are equivalent, i.e., `f - g =o[l] g`.

Here `l` is any filter on the domain of `f` and `g`, which are assumed to be the same. The codomains
of `f` and `g` do not need to be the same; all that is needed is that there is a norm associated
with these types, and it is the norm that is compared asymptotically.

The relation `IsBigOWith c` is introduced to factor out common algebraic arguments in the proofs of
similar properties of `IsBigO` and `IsLittleO`. Usually proofs outside of this file should use
`IsBigO` instead.

Often the ranges of `f` and `g` will be the real numbers, in which case the norm is the absolute
value. In general, we have

  `f =O[l] g ↔ (fun x ↦ ‖f x‖) =O[l] (fun x ↦ ‖g x‖)`,

and similarly for `IsLittleO`. But our setup allows us to use the notions e.g. with functions
to the integers, rationals, complex numbers, or any normed vector space without mentioning the
norm explicitly.

If `f` and `g` are functions to a normed field like the reals or complex numbers and `g` is always
nonzero, we have

  `f =o[l] g ↔ Tendsto (fun x ↦ f x / (g x)) l (𝓝 0)`.

In fact, the right-to-left direction holds without the hypothesis on `g`, and in the other direction
it suffices to assume that `f` is zero wherever `g` is. (This generalization is useful in defining
the Fréchet derivative.)

Sometimes Landau notation may be embedded in more complex expressions, such as
$f(n) = n ^ {1 + O(g(n))}$. This can be expressed using the existential pattern, for example:

  `∃ (e : ℕ → ℝ) (he : e =O[l] g), f =ᶠ[l] fun n ↦ n ^ (1 + e n)`.

-/

set_option linter.style.longFile 1600

@[expose] public section

assert_not_exists IsBoundedSMul Summable OpenPartialHomeomorph BoundedLENhdsClass

open Set Topology Filter NNReal

namespace Asymptotics


variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {E''' : Type*}
  {R : Type*} {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedAddGroup E''']
  [SeminormedRing R']

variable {S : Type*} [NormedRing S] [NormMulClass S]
variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜']
variable {c c' c₁ c₂ : ℝ} {f : α → E} {g : α → F} {k : α → G}
variable {f' : α → E'} {g' : α → F'} {k' : α → G'}
variable {f'' : α → E''} {g'' : α → F''} {k'' : α → G''}
variable {l l' : Filter α}

section Defs

/-! ### Definitions -/


/-- This version of the Landau notation `IsBigOWith C l f g` where `f` and `g` are two functions on
a type `α` and `l` is a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by `C * ‖g‖`.
In other words, `‖f‖ / ‖g‖` is eventually bounded by `C`, modulo division by zero issues that are
avoided by this definition. Probably you want to use `IsBigO` instead of this relation. -/
irreducible_def IsBigOWith (c : ℝ) (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖

/-- Definition of `IsBigOWith`. We record it in a lemma as `IsBigOWith` is irreducible. -/
theorem isBigOWith_iff : IsBigOWith c l f g ↔ ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by rw [IsBigOWith_def]

alias ⟨IsBigOWith.bound, IsBigOWith.of_bound⟩ := isBigOWith_iff

/-- The Landau notation `f =O[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by a constant multiple of `‖g‖`.
In other words, `‖f‖ / ‖g‖` is eventually bounded, modulo division by zero issues that are avoided
by this definition. -/
irreducible_def IsBigO (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∃ c : ℝ, IsBigOWith c l f g

@[inherit_doc]
notation:100 f " =O[" l "] " g:100 => IsBigO l f g

/-- Definition of `IsBigO` in terms of `IsBigOWith`. We record it in a lemma as `IsBigO` is
irreducible. -/
theorem isBigO_iff_isBigOWith : f =O[l] g ↔ ∃ c : ℝ, IsBigOWith c l f g := by rw [IsBigO_def]

/-- Definition of `IsBigO` in terms of filters. -/
theorem isBigO_iff : f =O[l] g ↔ ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  simp only [IsBigO_def, IsBigOWith_def]

/-- Definition of `IsBigO` in terms of filters, with a positive constant. -/
theorem isBigO_iff' {g : α → E'''} :
    f =O[l] g ↔ ∃ c > 0, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  refine ⟨fun h => ?mp, fun h => ?mpr⟩
  case mp =>
    rw [isBigO_iff] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨max c 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
    filter_upwards [hc] with x hx
    apply hx.trans
    gcongr
    exact le_max_left _ _
  case mpr =>
    rw [isBigO_iff]
    obtain ⟨c, ⟨_, hc⟩⟩ := h
    exact ⟨c, hc⟩

/-- Definition of `IsBigO` in terms of filters, with the constant in the lower bound. -/
theorem isBigO_iff'' {g : α → E'''} :
    f =O[l] g ↔ ∃ c > 0, ∀ᶠ x in l, c * ‖f x‖ ≤ ‖g x‖ := by
  refine ⟨fun h => ?mp, fun h => ?mpr⟩
  case mp =>
    rw [isBigO_iff'] at h
    obtain ⟨c, ⟨hc_pos, hc⟩⟩ := h
    refine ⟨c⁻¹, ⟨by positivity, ?_⟩⟩
    filter_upwards [hc] with x hx
    rwa [inv_mul_le_iff₀ (by positivity)]
  case mpr =>
    rw [isBigO_iff']
    obtain ⟨c, ⟨hc_pos, hc⟩⟩ := h
    refine ⟨c⁻¹, ⟨by positivity, ?_⟩⟩
    filter_upwards [hc] with x hx
    rwa [← inv_inv c, inv_mul_le_iff₀ (by positivity)] at hx

theorem IsBigO.of_bound (c : ℝ) (h : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g :=
  isBigO_iff.2 ⟨c, h⟩

theorem IsBigO.of_bound' (h : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖) : f =O[l] g :=
  .of_bound 1 <| by simpa only [one_mul] using h

theorem IsBigO.bound : f =O[l] g → ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isBigO_iff.1

/-- See also `Filter.Eventually.isBigO`, which is the same lemma
stated using `Filter.Eventually` instead of `Filter.EventuallyLE`. -/
theorem IsBigO.of_norm_eventuallyLE {g : α → ℝ} (h : (‖f ·‖) ≤ᶠ[l] g) : f =O[l] g :=
  .of_bound' <| h.mono fun _ h ↦ h.trans <| le_abs_self _

theorem IsBigO.of_norm_le {g : α → ℝ} (h : ∀ x, ‖f x‖ ≤ g x) : f =O[l] g :=
  .of_norm_eventuallyLE <| .of_forall h

/-- We say that `f` is `Θ(g)` along a filter `l` (notation: `f =Θ[l] g`) if `f =O[l] g` and
`g =O[l] f`. -/
def IsTheta (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  IsBigO l f g ∧ IsBigO l g f

@[inherit_doc]
notation:100 f " =Θ[" l "] " g:100 => IsTheta l f g

theorem IsBigO.antisymm (h₁ : f =O[l] g) (h₂ : g =O[l] f) : f =Θ[l] g :=
  ⟨h₁, h₂⟩

lemma IsTheta.isBigO (h : f =Θ[l] g) : f =O[l] g := h.1

lemma IsTheta.isBigO_symm (h : f =Θ[l] g) : g =O[l] f := h.2

/-- The Landau notation `f =o[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by an arbitrarily small constant
multiple of `‖g‖`. In other words, `‖f‖ / ‖g‖` tends to `0` along `l`, modulo division by zero
issues that are avoided by this definition. -/
irreducible_def IsLittleO (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f g

@[inherit_doc]
notation:100 f " =o[" l "] " g:100 => IsLittleO l f g

/-- Definition of `IsLittleO` in terms of `IsBigOWith`. -/
theorem isLittleO_iff_forall_isBigOWith : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f g := by
  rw [IsLittleO_def]

alias ⟨IsLittleO.forall_isBigOWith, IsLittleO.of_isBigOWith⟩ := isLittleO_iff_forall_isBigOWith

/-- Definition of `IsLittleO` in terms of filters. -/
theorem isLittleO_iff : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  simp only [IsLittleO_def, IsBigOWith_def]

alias ⟨IsLittleO.bound, IsLittleO.of_bound⟩ := isLittleO_iff

theorem IsLittleO.def (h : f =o[l] g) (hc : 0 < c) : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isLittleO_iff.1 h hc

theorem IsLittleO.def' (h : f =o[l] g) (hc : 0 < c) : IsBigOWith c l f g :=
  isBigOWith_iff.2 <| isLittleO_iff.1 h hc

theorem IsLittleO.eventuallyLE (h : f =o[l] g) : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖ := by
  simpa using h.def zero_lt_one

theorem IsLittleO.eventuallyLT_norm_of_eventually_pos (h : f =o[l] g) (hg : ∀ᶠ x in l, 0 < ‖g x‖) :
    ∀ᶠ x in l, ‖f x‖ < ‖g x‖ := by
  refine ((h.def (show 0 < 2⁻¹ by simp)).and hg).mono fun x ⟨hx₁, hx₂⟩ ↦ hx₁.trans_lt ?_
  rw [mul_lt_iff_lt_one_left hx₂]
  norm_num

/-- Two functions `u` and `v` are said to be asymptotically equivalent along a filter `l`
  (denoted as `u ~[l] v` in the `Asymptotics` namespace)
  when `u x - v x = o(v x)` as `x` converges along `l`. -/
def IsEquivalent (l : Filter α) (u v : α → E') :=
  (u - v) =o[l] v

@[inherit_doc] scoped notation:50 u " ~[" l:50 "] " v:50 => Asymptotics.IsEquivalent l u v

end Defs

/-! ### Conversions -/


theorem IsBigOWith.isBigO (h : IsBigOWith c l f g) : f =O[l] g := by rw [IsBigO_def]; exact ⟨c, h⟩

theorem IsLittleO.isBigOWith (hgf : f =o[l] g) : IsBigOWith 1 l f g :=
  hgf.def' zero_lt_one

theorem IsLittleO.isBigO (hgf : f =o[l] g) : f =O[l] g :=
  hgf.isBigOWith.isBigO

theorem IsBigO.isBigOWith : f =O[l] g → ∃ c : ℝ, IsBigOWith c l f g :=
  isBigO_iff_isBigOWith.1

theorem IsBigOWith.weaken (h : IsBigOWith c l f g') (hc : c ≤ c') : IsBigOWith c' l f g' :=
  IsBigOWith.of_bound <|
    mem_of_superset h.bound fun x hx =>
      calc
        ‖f x‖ ≤ c * ‖g' x‖ := hx
        _ ≤ _ := by gcongr

theorem IsBigOWith.exists_pos (h : IsBigOWith c l f g') :
    ∃ c' > 0, IsBigOWith c' l f g' :=
  ⟨max c 1, lt_of_lt_of_le zero_lt_one (le_max_right c 1), h.weaken <| le_max_left c 1⟩

theorem IsBigO.exists_pos (h : f =O[l] g') : ∃ c > 0, IsBigOWith c l f g' :=
  let ⟨_c, hc⟩ := h.isBigOWith
  hc.exists_pos

theorem IsBigOWith.exists_nonneg (h : IsBigOWith c l f g') :
    ∃ c' ≥ 0, IsBigOWith c' l f g' :=
  let ⟨c, cpos, hc⟩ := h.exists_pos
  ⟨c, le_of_lt cpos, hc⟩

theorem IsBigO.exists_nonneg (h : f =O[l] g') : ∃ c ≥ 0, IsBigOWith c l f g' :=
  let ⟨_c, hc⟩ := h.isBigOWith
  hc.exists_nonneg

/-- `f = O(g)` if and only if `IsBigOWith c f g` for all sufficiently large `c`. -/
theorem isBigO_iff_eventually_isBigOWith : f =O[l] g' ↔ ∀ᶠ c in atTop, IsBigOWith c l f g' :=
  isBigO_iff_isBigOWith.trans
    ⟨fun ⟨c, hc⟩ => mem_atTop_sets.2 ⟨c, fun _c' hc' => hc.weaken hc'⟩, fun h => h.exists⟩

/-- `f = O(g)` if and only if `∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖` for all sufficiently large `c`. -/
theorem isBigO_iff_eventually : f =O[l] g' ↔ ∀ᶠ c in atTop, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g' x‖ :=
  isBigO_iff_eventually_isBigOWith.trans <| by simp only [IsBigOWith_def]

theorem IsBigO.exists_mem_basis {ι} {p : ι → Prop} {s : ι → Set α} (h : f =O[l] g')
    (hb : l.HasBasis p s) :
    ∃ c > 0, ∃ i : ι, p i ∧ ∀ x ∈ s i, ‖f x‖ ≤ c * ‖g' x‖ :=
  flip Exists.imp h.exists_pos fun c h => by
    simpa only [isBigOWith_iff, hb.eventually_iff, exists_prop] using h

theorem isBigOWith_inv (hc : 0 < c) : IsBigOWith c⁻¹ l f g ↔ ∀ᶠ x in l, c * ‖f x‖ ≤ ‖g x‖ := by
  simp only [IsBigOWith_def, ← div_eq_inv_mul, le_div_iff₀' hc]

-- We prove this lemma with strange assumptions to get two lemmas below automatically
theorem isLittleO_iff_nat_mul_le_aux (h₀ : (∀ x, 0 ≤ ‖f x‖) ∨ ∀ x, 0 ≤ ‖g x‖) :
    f =o[l] g ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f x‖ ≤ ‖g x‖ := by
  constructor
  · rintro H (_ | n)
    · refine (H.def one_pos).mono fun x h₀' => ?_
      rw [Nat.cast_zero, zero_mul]
      refine h₀.elim (fun hf => (hf x).trans ?_) fun hg => hg x
      rwa [one_mul] at h₀'
    · have : (0 : ℝ) < n.succ := Nat.cast_pos.2 n.succ_pos
      exact (isBigOWith_inv this).1 (H.def' <| inv_pos.2 this)
  · refine fun H => isLittleO_iff.2 fun ε ε0 => ?_
    rcases exists_nat_gt ε⁻¹ with ⟨n, hn⟩
    have hn₀ : (0 : ℝ) < n := (inv_pos.2 ε0).trans hn
    refine ((isBigOWith_inv hn₀).2 (H n)).bound.mono fun x hfg => ?_
    refine hfg.trans (mul_le_mul_of_nonneg_right (inv_le_of_inv_le₀ ε0 hn.le) ?_)
    refine h₀.elim (fun hf => nonneg_of_mul_nonneg_right ((hf x).trans hfg) ?_) fun h => h x
    exact inv_pos.2 hn₀

theorem isLittleO_iff_nat_mul_le : f =o[l] g' ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f x‖ ≤ ‖g' x‖ :=
  isLittleO_iff_nat_mul_le_aux (Or.inr fun _x => norm_nonneg _)

theorem isLittleO_iff_nat_mul_le' : f' =o[l] g ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f' x‖ ≤ ‖g x‖ :=
  isLittleO_iff_nat_mul_le_aux (Or.inl fun _x => norm_nonneg _)

/-! ### Subsingleton -/


@[nontriviality]
theorem isLittleO_of_subsingleton [Subsingleton E'] : f' =o[l] g' :=
  IsLittleO.of_bound fun c hc => by simp [Subsingleton.elim (f' _) 0, mul_nonneg hc.le]

@[nontriviality]
theorem isBigO_of_subsingleton [Subsingleton E'] : f' =O[l] g' :=
  isLittleO_of_subsingleton.isBigO

section congr

variable {f₁ f₂ : α → E} {g₁ g₂ : α → F}

/-! ### Congruence -/


theorem isBigOWith_congr (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    IsBigOWith c₁ l f₁ g₁ ↔ IsBigOWith c₂ l f₂ g₂ := by
  simp only [IsBigOWith_def]
  subst c₂
  apply Filter.eventually_congr
  filter_upwards [hf, hg] with _ e₁ e₂
  rw [e₁, e₂]

theorem IsBigOWith.congr' (h : IsBigOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂)
    (hg : g₁ =ᶠ[l] g₂) : IsBigOWith c₂ l f₂ g₂ :=
  (isBigOWith_congr hc hf hg).mp h

theorem IsBigOWith.congr (h : IsBigOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : ∀ x, f₁ x = f₂ x)
    (hg : ∀ x, g₁ x = g₂ x) : IsBigOWith c₂ l f₂ g₂ :=
  h.congr' hc (univ_mem' hf) (univ_mem' hg)

theorem IsBigOWith.congr_left (h : IsBigOWith c l f₁ g) (hf : ∀ x, f₁ x = f₂ x) :
    IsBigOWith c l f₂ g :=
  h.congr rfl hf fun _ => rfl

theorem IsBigOWith.congr_right (h : IsBigOWith c l f g₁) (hg : ∀ x, g₁ x = g₂ x) :
    IsBigOWith c l f g₂ :=
  h.congr rfl (fun _ => rfl) hg

theorem IsBigOWith.congr_const (h : IsBigOWith c₁ l f g) (hc : c₁ = c₂) : IsBigOWith c₂ l f g :=
  h.congr hc (fun _ => rfl) fun _ => rfl

theorem isBigO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =O[l] g₁ ↔ f₂ =O[l] g₂ := by
  simp only [IsBigO_def]
  exact exists_congr fun c => isBigOWith_congr rfl hf hg

theorem IsBigO.congr' (h : f₁ =O[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =O[l] g₂ :=
  (isBigO_congr hf hg).mp h

theorem IsBigO.congr (h : f₁ =O[l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    f₂ =O[l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)

theorem IsBigO.congr_left (h : f₁ =O[l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =O[l] g :=
  h.congr hf fun _ => rfl

theorem IsBigO.congr_right (h : f =O[l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =O[l] g₂ :=
  h.congr (fun _ => rfl) hg

theorem isLittleO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =o[l] g₁ ↔ f₂ =o[l] g₂ := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun c _hc => isBigOWith_congr (Eq.refl c) hf hg

theorem IsLittleO.congr' (h : f₁ =o[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =o[l] g₂ :=
  (isLittleO_congr hf hg).mp h

theorem IsLittleO.congr (h : f₁ =o[l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    f₂ =o[l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)

theorem IsLittleO.congr_left (h : f₁ =o[l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =o[l] g :=
  h.congr hf fun _ => rfl

theorem IsLittleO.congr_right (h : f =o[l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =o[l] g₂ :=
  h.congr (fun _ => rfl) hg

@[trans]
theorem _root_.Filter.EventuallyEq.trans_isBigO {f₁ f₂ : α → E} {g : α → F} (hf : f₁ =ᶠ[l] f₂)
    (h : f₂ =O[l] g) : f₁ =O[l] g :=
  h.congr' hf.symm EventuallyEq.rfl

instance transEventuallyEqIsBigO :
    @Trans (α → E) (α → E) (α → F) (· =ᶠ[l] ·) (· =O[l] ·) (· =O[l] ·) where
  trans := Filter.EventuallyEq.trans_isBigO

@[trans]
theorem _root_.Filter.EventuallyEq.trans_isLittleO {f₁ f₂ : α → E} {g : α → F} (hf : f₁ =ᶠ[l] f₂)
    (h : f₂ =o[l] g) : f₁ =o[l] g :=
  h.congr' hf.symm EventuallyEq.rfl

instance transEventuallyEqIsLittleO :
    @Trans (α → E) (α → E) (α → F) (· =ᶠ[l] ·) (· =o[l] ·) (· =o[l] ·) where
  trans := Filter.EventuallyEq.trans_isLittleO

@[trans]
theorem IsBigO.trans_eventuallyEq {f : α → E} {g₁ g₂ : α → F} (h : f =O[l] g₁) (hg : g₁ =ᶠ[l] g₂) :
    f =O[l] g₂ :=
  h.congr' EventuallyEq.rfl hg

instance transIsBigOEventuallyEq :
    @Trans (α → E) (α → F) (α → F) (· =O[l] ·) (· =ᶠ[l] ·) (· =O[l] ·) where
  trans := IsBigO.trans_eventuallyEq

@[trans]
theorem IsLittleO.trans_eventuallyEq {f : α → E} {g₁ g₂ : α → F} (h : f =o[l] g₁)
    (hg : g₁ =ᶠ[l] g₂) : f =o[l] g₂ :=
  h.congr' EventuallyEq.rfl hg

instance transIsLittleOEventuallyEq :
    @Trans (α → E) (α → F) (α → F) (· =o[l] ·) (· =ᶠ[l] ·) (· =o[l] ·) where
  trans := IsLittleO.trans_eventuallyEq

end congr

/-! ### Filter operations and transitivity -/


theorem IsBigOWith.comp_tendsto (hcfg : IsBigOWith c l f g) {k : β → α} {l' : Filter β}
    (hk : Tendsto k l' l) : IsBigOWith c l' (f ∘ k) (g ∘ k) :=
  IsBigOWith.of_bound <| hk hcfg.bound

theorem IsBigO.comp_tendsto (hfg : f =O[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) :
    (f ∘ k) =O[l'] (g ∘ k) :=
  isBigO_iff_isBigOWith.2 <| hfg.isBigOWith.imp fun _c h => h.comp_tendsto hk

lemma IsBigO.comp_neg_int {f : ℤ → E} {g : ℤ → F} (hf : f =O[cofinite] g) :
    (fun n => f (-n)) =O[cofinite] fun n => g (-n) := by
  rw [← Equiv.neg_apply]
  exact hf.comp_tendsto (Equiv.neg ℤ).injective.tendsto_cofinite

theorem IsLittleO.comp_tendsto (hfg : f =o[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) :
    (f ∘ k) =o[l'] (g ∘ k) :=
  IsLittleO.of_isBigOWith fun _c cpos => (hfg.forall_isBigOWith cpos).comp_tendsto hk

@[simp]
theorem isBigOWith_map {k : β → α} {l : Filter β} :
    IsBigOWith c (map k l) f g ↔ IsBigOWith c l (f ∘ k) (g ∘ k) := by
  simp only [IsBigOWith_def]
  exact eventually_map

@[simp]
theorem isBigO_map {k : β → α} {l : Filter β} : f =O[map k l] g ↔ (f ∘ k) =O[l] (g ∘ k) := by
  simp only [IsBigO_def, isBigOWith_map]

@[simp]
theorem isLittleO_map {k : β → α} {l : Filter β} : f =o[map k l] g ↔ (f ∘ k) =o[l] (g ∘ k) := by
  simp only [IsLittleO_def, isBigOWith_map]

theorem IsBigOWith.mono (h : IsBigOWith c l' f g) (hl : l ≤ l') : IsBigOWith c l f g :=
  IsBigOWith.of_bound <| hl h.bound

theorem IsBigO.mono (h : f =O[l'] g) (hl : l ≤ l') : f =O[l] g :=
  isBigO_iff_isBigOWith.2 <| h.isBigOWith.imp fun _c h => h.mono hl

theorem IsLittleO.mono (h : f =o[l'] g) (hl : l ≤ l') : f =o[l] g :=
  IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).mono hl

theorem IsBigOWith.trans (hfg : IsBigOWith c l f g) (hgk : IsBigOWith c' l g k) (hc : 0 ≤ c) :
    IsBigOWith (c * c') l f k := by
  simp only [IsBigOWith_def] at *
  filter_upwards [hfg, hgk] with x hx hx'
  calc
    ‖f x‖ ≤ c * ‖g x‖ := hx
    _ ≤ c * (c' * ‖k x‖) := by gcongr
    _ = c * c' * ‖k x‖ := (mul_assoc _ _ _).symm

@[trans]
theorem IsBigO.trans {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g) (hgk : g =O[l] k) :
    f =O[l] k :=
  let ⟨_c, cnonneg, hc⟩ := hfg.exists_nonneg
  let ⟨_c', hc'⟩ := hgk.isBigOWith
  (hc.trans hc' cnonneg).isBigO

instance transIsBigOIsBigO :
    @Trans (α → E) (α → F') (α → G) (· =O[l] ·) (· =O[l] ·) (· =O[l] ·) where
  trans := IsBigO.trans

theorem IsLittleO.trans_isBigOWith (hfg : f =o[l] g) (hgk : IsBigOWith c l g k) (hc : 0 < c) :
    f =o[l] k := by
  simp only [IsLittleO_def] at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact ((hfg this).trans hgk this.le).congr_const (div_mul_cancel₀ _ hc.ne')

@[trans]
theorem IsLittleO.trans_isBigO {f : α → E} {g : α → F} {k : α → G'} (hfg : f =o[l] g)
    (hgk : g =O[l] k) : f =o[l] k :=
  let ⟨_c, cpos, hc⟩ := hgk.exists_pos
  hfg.trans_isBigOWith hc cpos

instance transIsLittleOIsBigO :
    @Trans (α → E) (α → F) (α → G') (· =o[l] ·) (· =O[l] ·) (· =o[l] ·) where
  trans := IsLittleO.trans_isBigO

theorem IsBigOWith.trans_isLittleO (hfg : IsBigOWith c l f g) (hgk : g =o[l] k) (hc : 0 < c) :
    f =o[l] k := by
  simp only [IsLittleO_def] at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact (hfg.trans (hgk this) hc.le).congr_const (mul_div_cancel₀ _ hc.ne')

@[trans]
theorem IsBigO.trans_isLittleO {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g)
    (hgk : g =o[l] k) : f =o[l] k :=
  let ⟨_c, cpos, hc⟩ := hfg.exists_pos
  hc.trans_isLittleO hgk cpos

instance transIsBigOIsLittleO :
    @Trans (α → E) (α → F') (α → G) (· =O[l] ·) (· =o[l] ·) (· =o[l] ·) where
  trans := IsBigO.trans_isLittleO

@[trans]
theorem IsLittleO.trans {f : α → E} {g : α → F} {k : α → G} (hfg : f =o[l] g) (hgk : g =o[l] k) :
    f =o[l] k :=
  hfg.trans_isBigOWith hgk.isBigOWith one_pos

instance transIsLittleOIsLittleO :
    @Trans (α → E) (α → F) (α → G) (· =o[l] ·) (· =o[l] ·) (· =o[l] ·) where
  trans := IsLittleO.trans

theorem _root_.Filter.Eventually.trans_isBigO {f : α → E} {g : α → F'} {k : α → G}
    (hfg : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖) (hgk : g =O[l] k) : f =O[l] k :=
  (IsBigO.of_bound' hfg).trans hgk

/-- See also `Asymptotics.IsBigO.of_norm_eventuallyLE`, which is the same lemma
stated using `Filter.EventuallyLE` instead of `Filter.Eventually`. -/
theorem _root_.Filter.Eventually.isBigO {f : α → E} {g : α → ℝ} {l : Filter α}
    (hfg : ∀ᶠ x in l, ‖f x‖ ≤ g x) : f =O[l] g :=
  .of_norm_eventuallyLE hfg

section

variable (l)

theorem isBigOWith_of_le' (hfg : ∀ x, ‖f x‖ ≤ c * ‖g x‖) : IsBigOWith c l f g :=
  IsBigOWith.of_bound <| univ_mem' hfg

theorem isBigOWith_of_le (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) : IsBigOWith 1 l f g :=
  isBigOWith_of_le' l fun x => by
    rw [one_mul]
    exact hfg x

theorem isBigO_of_le' (hfg : ∀ x, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g :=
  (isBigOWith_of_le' l hfg).isBigO

theorem isBigO_of_le (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) : f =O[l] g :=
  (isBigOWith_of_le l hfg).isBigO

end

theorem isBigOWith_refl (f : α → E) (l : Filter α) : IsBigOWith 1 l f f :=
  isBigOWith_of_le l fun _ => le_rfl

theorem isBigO_refl (f : α → E) (l : Filter α) : f =O[l] f :=
  (isBigOWith_refl f l).isBigO

theorem _root_.Filter.EventuallyEq.isBigO {f₁ f₂ : α → E} (hf : f₁ =ᶠ[l] f₂) : f₁ =O[l] f₂ :=
  hf.trans_isBigO (isBigO_refl _ _)

theorem IsBigOWith.trans_le (hfg : IsBigOWith c l f g) (hgk : ∀ x, ‖g x‖ ≤ ‖k x‖) (hc : 0 ≤ c) :
    IsBigOWith c l f k :=
  (hfg.trans (isBigOWith_of_le l hgk) hc).congr_const <| mul_one c

theorem IsBigO.trans_le (hfg : f =O[l] g') (hgk : ∀ x, ‖g' x‖ ≤ ‖k x‖) : f =O[l] k :=
  hfg.trans (isBigO_of_le l hgk)

theorem IsLittleO.trans_le (hfg : f =o[l] g) (hgk : ∀ x, ‖g x‖ ≤ ‖k x‖) : f =o[l] k :=
  hfg.trans_isBigOWith (isBigOWith_of_le _ hgk) zero_lt_one

theorem isLittleO_irrefl' (h : ∃ᶠ x in l, ‖f' x‖ ≠ 0) : ¬f' =o[l] f' := by
  intro ho
  rcases ((ho.bound one_half_pos).and_frequently h).exists with ⟨x, hle, hne⟩
  rw [one_div, ← div_eq_inv_mul] at hle
  exact (half_lt_self (lt_of_le_of_ne (norm_nonneg _) hne.symm)).not_ge hle

theorem isLittleO_irrefl (h : ∃ᶠ x in l, f'' x ≠ 0) : ¬f'' =o[l] f'' :=
  isLittleO_irrefl' <| h.mono fun _x => norm_ne_zero_iff.mpr

theorem IsBigO.not_isLittleO (h : f'' =O[l] g') (hf : ∃ᶠ x in l, f'' x ≠ 0) :
    ¬g' =o[l] f'' := fun h' =>
  isLittleO_irrefl hf (h.trans_isLittleO h')

theorem IsLittleO.not_isBigO (h : f'' =o[l] g') (hf : ∃ᶠ x in l, f'' x ≠ 0) :
    ¬g' =O[l] f'' := fun h' =>
  isLittleO_irrefl hf (h.trans_isBigO h')

section Bot

variable (c f g)

@[simp]
theorem isBigOWith_bot : IsBigOWith c ⊥ f g :=
  IsBigOWith.of_bound <| trivial

@[simp]
theorem isBigO_bot : f =O[⊥] g :=
  (isBigOWith_bot 1 f g).isBigO

@[simp]
theorem isLittleO_bot : f =o[⊥] g :=
  IsLittleO.of_isBigOWith fun c _ => isBigOWith_bot c f g

end Bot

@[simp]
theorem isBigOWith_pure {x} : IsBigOWith c (pure x) f g ↔ ‖f x‖ ≤ c * ‖g x‖ :=
  isBigOWith_iff

theorem IsBigOWith.sup (h : IsBigOWith c l f g) (h' : IsBigOWith c l' f g) :
    IsBigOWith c (l ⊔ l') f g :=
  IsBigOWith.of_bound <| mem_sup.2 ⟨h.bound, h'.bound⟩

theorem IsBigOWith.sup' (h : IsBigOWith c l f g') (h' : IsBigOWith c' l' f g') :
    IsBigOWith (max c c') (l ⊔ l') f g' :=
  IsBigOWith.of_bound <|
    mem_sup.2 ⟨(h.weaken <| le_max_left c c').bound, (h'.weaken <| le_max_right c c').bound⟩

theorem IsBigO.sup (h : f =O[l] g') (h' : f =O[l'] g') : f =O[l ⊔ l'] g' :=
  let ⟨_c, hc⟩ := h.isBigOWith
  let ⟨_c', hc'⟩ := h'.isBigOWith
  (hc.sup' hc').isBigO

theorem IsLittleO.sup (h : f =o[l] g) (h' : f =o[l'] g) : f =o[l ⊔ l'] g :=
  IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).sup (h'.forall_isBigOWith cpos)

@[simp]
theorem isBigO_sup : f =O[l ⊔ l'] g' ↔ f =O[l] g' ∧ f =O[l'] g' :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩

@[simp]
theorem isLittleO_sup : f =o[l ⊔ l'] g ↔ f =o[l] g ∧ f =o[l'] g :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩

theorem isBigOWith_insert [TopologicalSpace α] {x : α} {s : Set α} {C : ℝ} {g : α → E} {g' : α → F}
    (h : ‖g x‖ ≤ C * ‖g' x‖) : IsBigOWith C (𝓝[insert x s] x) g g' ↔
    IsBigOWith C (𝓝[s] x) g g' := by
  simp_rw [IsBigOWith_def, nhdsWithin_insert, eventually_sup, eventually_pure, h, true_and]

protected theorem IsBigOWith.insert [TopologicalSpace α] {x : α} {s : Set α} {C : ℝ} {g : α → E}
    {g' : α → F} (h1 : IsBigOWith C (𝓝[s] x) g g') (h2 : ‖g x‖ ≤ C * ‖g' x‖) :
    IsBigOWith C (𝓝[insert x s] x) g g' :=
  (isBigOWith_insert h2).mpr h1

theorem isLittleO_insert [TopologicalSpace α] {x : α} {s : Set α} {g : α → E'} {g' : α → F'}
    (h : g x = 0) : g =o[𝓝[insert x s] x] g' ↔ g =o[𝓝[s] x] g' := by
  simp_rw [IsLittleO_def]
  refine forall_congr' fun c => forall_congr' fun hc => ?_
  rw [isBigOWith_insert]
  rw [h, norm_zero]
  positivity

protected theorem IsLittleO.insert [TopologicalSpace α] {x : α} {s : Set α} {g : α → E'}
    {g' : α → F'} (h1 : g =o[𝓝[s] x] g') (h2 : g x = 0) : g =o[𝓝[insert x s] x] g' :=
  (isLittleO_insert h2).mpr h1

/-! ### Simplification: norm, abs -/


section NormAbs

variable {u v : α → ℝ}

@[simp]
theorem isBigOWith_norm_right : (IsBigOWith c l f fun x => ‖g' x‖) ↔ IsBigOWith c l f g' := by
  simp only [IsBigOWith_def, norm_norm]

@[simp]
theorem isBigOWith_abs_right : (IsBigOWith c l f fun x => |u x|) ↔ IsBigOWith c l f u :=
  @isBigOWith_norm_right _ _ _ _ _ _ f u l

alias ⟨IsBigOWith.of_norm_right, IsBigOWith.norm_right⟩ := isBigOWith_norm_right

alias ⟨IsBigOWith.of_abs_right, IsBigOWith.abs_right⟩ := isBigOWith_abs_right

@[simp]
theorem isBigO_norm_right : (f =O[l] fun x => ‖g' x‖) ↔ f =O[l] g' := by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_norm_right

@[simp]
theorem isBigO_abs_right : (f =O[l] fun x => |u x|) ↔ f =O[l] u :=
  @isBigO_norm_right _ _ ℝ _ _ _ _ _

alias ⟨IsBigO.of_norm_right, IsBigO.norm_right⟩ := isBigO_norm_right

alias ⟨IsBigO.of_abs_right, IsBigO.abs_right⟩ := isBigO_abs_right

@[simp]
theorem isLittleO_norm_right : (f =o[l] fun x => ‖g' x‖) ↔ f =o[l] g' := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_norm_right

@[simp]
theorem isLittleO_abs_right : (f =o[l] fun x => |u x|) ↔ f =o[l] u :=
  @isLittleO_norm_right _ _ ℝ _ _ _ _ _

alias ⟨IsLittleO.of_norm_right, IsLittleO.norm_right⟩ := isLittleO_norm_right

alias ⟨IsLittleO.of_abs_right, IsLittleO.abs_right⟩ := isLittleO_abs_right

@[simp]
theorem isBigOWith_norm_left : IsBigOWith c l (fun x => ‖f' x‖) g ↔ IsBigOWith c l f' g := by
  simp only [IsBigOWith_def, norm_norm]

@[simp]
theorem isBigOWith_abs_left : IsBigOWith c l (fun x => |u x|) g ↔ IsBigOWith c l u g :=
  @isBigOWith_norm_left _ _ _ _ _ _ g u l

alias ⟨IsBigOWith.of_norm_left, IsBigOWith.norm_left⟩ := isBigOWith_norm_left

alias ⟨IsBigOWith.of_abs_left, IsBigOWith.abs_left⟩ := isBigOWith_abs_left

@[simp]
theorem isBigO_norm_left : (fun x => ‖f' x‖) =O[l] g ↔ f' =O[l] g := by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_norm_left

@[simp]
theorem isBigO_abs_left : (fun x => |u x|) =O[l] g ↔ u =O[l] g :=
  @isBigO_norm_left _ _ _ _ _ g u l

alias ⟨IsBigO.of_norm_left, IsBigO.norm_left⟩ := isBigO_norm_left

alias ⟨IsBigO.of_abs_left, IsBigO.abs_left⟩ := isBigO_abs_left

@[simp]
theorem isLittleO_norm_left : (fun x => ‖f' x‖) =o[l] g ↔ f' =o[l] g := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_norm_left

@[simp]
theorem isLittleO_abs_left : (fun x => |u x|) =o[l] g ↔ u =o[l] g :=
  @isLittleO_norm_left _ _ _ _ _ g u l

alias ⟨IsLittleO.of_norm_left, IsLittleO.norm_left⟩ := isLittleO_norm_left

alias ⟨IsLittleO.of_abs_left, IsLittleO.abs_left⟩ := isLittleO_abs_left

theorem isBigOWith_norm_norm :
    (IsBigOWith c l (fun x => ‖f' x‖) fun x => ‖g' x‖) ↔ IsBigOWith c l f' g' :=
  isBigOWith_norm_left.trans isBigOWith_norm_right

theorem isBigOWith_abs_abs :
    (IsBigOWith c l (fun x => |u x|) fun x => |v x|) ↔ IsBigOWith c l u v :=
  isBigOWith_abs_left.trans isBigOWith_abs_right

alias ⟨IsBigOWith.of_norm_norm, IsBigOWith.norm_norm⟩ := isBigOWith_norm_norm

alias ⟨IsBigOWith.of_abs_abs, IsBigOWith.abs_abs⟩ := isBigOWith_abs_abs

theorem isBigO_norm_norm : ((fun x => ‖f' x‖) =O[l] fun x => ‖g' x‖) ↔ f' =O[l] g' :=
  isBigO_norm_left.trans isBigO_norm_right

theorem isBigO_abs_abs : ((fun x => |u x|) =O[l] fun x => |v x|) ↔ u =O[l] v :=
  isBigO_abs_left.trans isBigO_abs_right

alias ⟨IsBigO.of_norm_norm, IsBigO.norm_norm⟩ := isBigO_norm_norm

alias ⟨IsBigO.of_abs_abs, IsBigO.abs_abs⟩ := isBigO_abs_abs

theorem isLittleO_norm_norm : ((fun x => ‖f' x‖) =o[l] fun x => ‖g' x‖) ↔ f' =o[l] g' :=
  isLittleO_norm_left.trans isLittleO_norm_right

theorem isLittleO_abs_abs : ((fun x => |u x|) =o[l] fun x => |v x|) ↔ u =o[l] v :=
  isLittleO_abs_left.trans isLittleO_abs_right

alias ⟨IsLittleO.of_norm_norm, IsLittleO.norm_norm⟩ := isLittleO_norm_norm

alias ⟨IsLittleO.of_abs_abs, IsLittleO.abs_abs⟩ := isLittleO_abs_abs

end NormAbs

/-! ### Simplification: negate -/


@[simp]
theorem isBigOWith_neg_right : (IsBigOWith c l f fun x => -g' x) ↔ IsBigOWith c l f g' := by
  simp only [IsBigOWith_def, norm_neg]

alias ⟨IsBigOWith.of_neg_right, IsBigOWith.neg_right⟩ := isBigOWith_neg_right

@[simp]
theorem isBigO_neg_right : (f =O[l] fun x => -g' x) ↔ f =O[l] g' := by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_neg_right

alias ⟨IsBigO.of_neg_right, IsBigO.neg_right⟩ := isBigO_neg_right

@[simp]
theorem isLittleO_neg_right : (f =o[l] fun x => -g' x) ↔ f =o[l] g' := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_neg_right

alias ⟨IsLittleO.of_neg_right, IsLittleO.neg_right⟩ := isLittleO_neg_right

@[simp]
theorem isBigOWith_neg_left : IsBigOWith c l (fun x => -f' x) g ↔ IsBigOWith c l f' g := by
  simp only [IsBigOWith_def, norm_neg]

alias ⟨IsBigOWith.of_neg_left, IsBigOWith.neg_left⟩ := isBigOWith_neg_left

@[simp]
theorem isBigO_neg_left : (fun x => -f' x) =O[l] g ↔ f' =O[l] g := by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_neg_left

alias ⟨IsBigO.of_neg_left, IsBigO.neg_left⟩ := isBigO_neg_left

@[simp]
theorem isLittleO_neg_left : (fun x => -f' x) =o[l] g ↔ f' =o[l] g := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_neg_left

alias ⟨IsLittleO.of_neg_left, IsLittleO.neg_left⟩ := isLittleO_neg_left

/-! ### Product of functions (right) -/


theorem isBigOWith_fst_prod : IsBigOWith 1 l f' fun x => (f' x, g' x) :=
  isBigOWith_of_le l fun _x => le_max_left _ _

theorem isBigOWith_snd_prod : IsBigOWith 1 l g' fun x => (f' x, g' x) :=
  isBigOWith_of_le l fun _x => le_max_right _ _

theorem isBigO_fst_prod : f' =O[l] fun x => (f' x, g' x) :=
  isBigOWith_fst_prod.isBigO

theorem isBigO_snd_prod : g' =O[l] fun x => (f' x, g' x) :=
  isBigOWith_snd_prod.isBigO

theorem isBigO_fst_prod' {f' : α → E' × F'} : (fun x => (f' x).1) =O[l] f' := by
  simpa [IsBigO_def, IsBigOWith_def] using isBigO_fst_prod (E' := E') (F' := F')

theorem isBigO_snd_prod' {f' : α → E' × F'} : (fun x => (f' x).2) =O[l] f' := by
  simpa [IsBigO_def, IsBigOWith_def] using isBigO_snd_prod (E' := E') (F' := F')

section

variable (f' k')

theorem IsBigOWith.prod_rightl (h : IsBigOWith c l f g') (hc : 0 ≤ c) :
    IsBigOWith c l f fun x => (g' x, k' x) :=
  (h.trans isBigOWith_fst_prod hc).congr_const (mul_one c)

theorem IsBigO.prod_rightl (h : f =O[l] g') : f =O[l] fun x => (g' x, k' x) :=
  let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightl k' cnonneg).isBigO

theorem IsLittleO.prod_rightl (h : f =o[l] g') : f =o[l] fun x => (g' x, k' x) :=
  IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).prod_rightl k' cpos.le

theorem IsBigOWith.prod_rightr (h : IsBigOWith c l f g') (hc : 0 ≤ c) :
    IsBigOWith c l f fun x => (f' x, g' x) :=
  (h.trans isBigOWith_snd_prod hc).congr_const (mul_one c)

theorem IsBigO.prod_rightr (h : f =O[l] g') : f =O[l] fun x => (f' x, g' x) :=
  let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightr f' cnonneg).isBigO

theorem IsLittleO.prod_rightr (h : f =o[l] g') : f =o[l] fun x => (f' x, g' x) :=
  IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).prod_rightr f' cpos.le

end

section

variable {f : α × β → E} {g : α × β → F} {l' : Filter β}

protected theorem IsBigO.fiberwise_right :
    f =O[l ×ˢ l'] g → ∀ᶠ a in l, (f ⟨a, ·⟩) =O[l'] (g ⟨a, ·⟩) := by
  simp only [isBigO_iff, eventually_iff, mem_prod_iff]
  rintro ⟨c, t₁, ht₁, t₂, ht₂, ht⟩
  exact mem_of_superset ht₁ fun _ ha ↦ ⟨c, mem_of_superset ht₂ fun _ hb ↦ ht ⟨ha, hb⟩⟩

protected theorem IsBigO.fiberwise_left :
    f =O[l ×ˢ l'] g → ∀ᶠ b in l', (f ⟨·, b⟩) =O[l] (g ⟨·, b⟩) := by
  simp only [isBigO_iff, eventually_iff, mem_prod_iff]
  rintro ⟨c, t₁, ht₁, t₂, ht₂, ht⟩
  exact mem_of_superset ht₂ fun _ hb ↦ ⟨c, mem_of_superset ht₁ fun _ ha ↦ ht ⟨ha, hb⟩⟩

end

section

variable (l' : Filter β)

protected theorem IsBigO.comp_fst : f =O[l] g → (f ∘ Prod.fst) =O[l ×ˢ l'] (g ∘ Prod.fst) := by
  simp only [isBigO_iff, eventually_prod_iff]
  exact fun ⟨c, hc⟩ ↦ ⟨c, _, hc, fun _ ↦ True, eventually_true l', fun {_} h {_} _ ↦ h⟩

protected theorem IsBigO.comp_snd : f =O[l] g → (f ∘ Prod.snd) =O[l' ×ˢ l] (g ∘ Prod.snd) := by
  simp only [isBigO_iff, eventually_prod_iff]
  exact fun ⟨c, hc⟩ ↦ ⟨c, fun _ ↦ True, eventually_true l', _, hc, fun _ ↦ id⟩

protected theorem IsLittleO.comp_fst : f =o[l] g → (f ∘ Prod.fst) =o[l ×ˢ l'] (g ∘ Prod.fst) := by
  simp only [isLittleO_iff, eventually_prod_iff]
  exact fun h _ hc ↦ ⟨_, h hc, fun _ ↦ True, eventually_true l', fun {_} h {_} _ ↦ h⟩

protected theorem IsLittleO.comp_snd : f =o[l] g → (f ∘ Prod.snd) =o[l' ×ˢ l] (g ∘ Prod.snd) := by
  simp only [isLittleO_iff, eventually_prod_iff]
  exact fun h _ hc ↦ ⟨fun _ ↦ True, eventually_true l', _, h hc, fun _ ↦ id⟩

end

theorem IsBigOWith.prod_left_same (hf : IsBigOWith c l f' k') (hg : IsBigOWith c l g' k') :
    IsBigOWith c l (fun x => (f' x, g' x)) k' := by
  rw [isBigOWith_iff] at *; filter_upwards [hf, hg] with x using max_le

theorem IsBigOWith.prod_left (hf : IsBigOWith c l f' k') (hg : IsBigOWith c' l g' k') :
    IsBigOWith (max c c') l (fun x => (f' x, g' x)) k' :=
  (hf.weaken <| le_max_left c c').prod_left_same (hg.weaken <| le_max_right c c')

theorem IsBigOWith.prod_left_fst (h : IsBigOWith c l (fun x => (f' x, g' x)) k') :
    IsBigOWith c l f' k' :=
  (isBigOWith_fst_prod.trans h zero_le_one).congr_const <| one_mul c

theorem IsBigOWith.prod_left_snd (h : IsBigOWith c l (fun x => (f' x, g' x)) k') :
    IsBigOWith c l g' k' :=
  (isBigOWith_snd_prod.trans h zero_le_one).congr_const <| one_mul c

theorem isBigOWith_prod_left :
    IsBigOWith c l (fun x => (f' x, g' x)) k' ↔ IsBigOWith c l f' k' ∧ IsBigOWith c l g' k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left_same h.2⟩

theorem IsBigO.prod_left (hf : f' =O[l] k') (hg : g' =O[l] k') : (fun x => (f' x, g' x)) =O[l] k' :=
  let ⟨_c, hf⟩ := hf.isBigOWith
  let ⟨_c', hg⟩ := hg.isBigOWith
  (hf.prod_left hg).isBigO

theorem IsBigO.prod_left_fst : (fun x => (f' x, g' x)) =O[l] k' → f' =O[l] k' :=
  IsBigO.trans isBigO_fst_prod

theorem IsBigO.prod_left_snd : (fun x => (f' x, g' x)) =O[l] k' → g' =O[l] k' :=
  IsBigO.trans isBigO_snd_prod

@[simp]
theorem isBigO_prod_left : (fun x => (f' x, g' x)) =O[l] k' ↔ f' =O[l] k' ∧ g' =O[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left h.2⟩

theorem IsLittleO.prod_left (hf : f' =o[l] k') (hg : g' =o[l] k') :
    (fun x => (f' x, g' x)) =o[l] k' :=
  IsLittleO.of_isBigOWith fun _c hc =>
    (hf.forall_isBigOWith hc).prod_left_same (hg.forall_isBigOWith hc)

theorem IsLittleO.prod_left_fst : (fun x => (f' x, g' x)) =o[l] k' → f' =o[l] k' :=
  IsBigO.trans_isLittleO isBigO_fst_prod

theorem IsLittleO.prod_left_snd : (fun x => (f' x, g' x)) =o[l] k' → g' =o[l] k' :=
  IsBigO.trans_isLittleO isBigO_snd_prod

@[simp]
theorem isLittleO_prod_left : (fun x => (f' x, g' x)) =o[l] k' ↔ f' =o[l] k' ∧ g' =o[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left h.2⟩

theorem IsBigOWith.eq_zero_imp (h : IsBigOWith c l f'' g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  Eventually.mono h.bound fun x hx hg => norm_le_zero_iff.1 <| by simpa [hg] using hx

theorem IsBigO.eq_zero_imp (h : f'' =O[l] g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  let ⟨_C, hC⟩ := h.isBigOWith
  hC.eq_zero_imp

/-! ### Addition and subtraction -/


section add_sub

variable {f₁ f₂ : α → E'} {g₁ g₂ : α → F'}

theorem IsBigOWith.add (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g) :
    IsBigOWith (c₁ + c₂) l (fun x => f₁ x + f₂ x) g := by
  rw [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with x hx₁ hx₂ using
    calc
      ‖f₁ x + f₂ x‖ ≤ c₁ * ‖g x‖ + c₂ * ‖g x‖ := norm_add_le_of_le hx₁ hx₂
      _ = (c₁ + c₂) * ‖g x‖ := (add_mul _ _ _).symm

theorem IsBigO.add (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  let ⟨_c₁, hc₁⟩ := h₁.isBigOWith
  let ⟨_c₂, hc₂⟩ := h₂.isBigOWith
  (hc₁.add hc₂).isBigO

theorem IsLittleO.add (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g :=
  IsLittleO.of_isBigOWith fun c cpos =>
    ((h₁.forall_isBigOWith <| half_pos cpos).add (h₂.forall_isBigOWith <|
      half_pos cpos)).congr_const (add_halves c)

theorem IsBigOWith.add_add {g₁ g₂ : α → ℝ} (h₁ : IsBigOWith c₁ l f₁ g₁)
    (h₂ : IsBigOWith c₂ l f₂ g₂) :
    IsBigOWith (max c₁ c₂) l (fun x ↦ f₁ x + f₂ x) (fun x ↦ ‖g₁ x‖ + ‖g₂ x‖) := by
  rw [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  calc
    ‖f₁ x + f₂ x‖ ≤ c₁ * ‖g₁ x‖ + c₂ * ‖g₂ x‖ := norm_add_le_of_le hx₁ hx₂
    _ ≤ (max c₁ c₂) * ‖g₁ x‖ + (max c₁ c₂) * ‖g₂ x‖ := by
        gcongr <;> simp [le_max_left _ _, le_max_right _ _]
    _ = (max c₁ c₂) * ‖‖g₁ x‖ + ‖g₂ x‖‖ := by
        rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), mul_add]

theorem IsBigO.add_add {g₁ g₂ : α → ℝ} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x ↦ f₁ x + f₂ x) =O[l] fun x ↦ ‖g₁ x‖ + ‖g₂ x‖ := by
  obtain ⟨c₁, hc₁⟩ := h₁.isBigOWith
  obtain ⟨c₂, hc₂⟩ := h₂.isBigOWith
  exact (hc₁.add_add hc₂).isBigO

theorem IsLittleO.add_add (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x + f₂ x) =o[l] fun x => ‖g₁ x‖ + ‖g₂ x‖ := by
  refine (h₁.trans_le fun x => ?_).add (h₂.trans_le ?_) <;> simp [abs_of_nonneg, add_nonneg]

theorem IsBigO.add_isLittleO (h₁ : f₁ =O[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.add h₂.isBigO

theorem IsLittleO.add_isBigO (h₁ : f₁ =o[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.isBigO.add h₂

theorem IsBigOWith.add_isLittleO (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₁.add (h₂.forall_isBigOWith (sub_pos.2 hc))).congr_const (add_sub_cancel _ _)

theorem IsLittleO.add_isBigOWith (h₁ : f₁ =o[l] g) (h₂ : IsBigOWith c₁ l f₂ g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₂.add_isLittleO h₁ hc).congr_left fun _ => add_comm _ _

theorem IsBigOWith.sub (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g) :
    IsBigOWith (c₁ + c₂) l (fun x => f₁ x - f₂ x) g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

theorem IsBigOWith.sub_isLittleO (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x - f₂ x) g := by
  simpa only [sub_eq_add_neg] using h₁.add_isLittleO h₂.neg_left hc

theorem IsBigO.sub (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

theorem IsLittleO.sub (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

theorem IsBigO.add_iff_left (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g ↔ (f₁ =O[l] g) :=
  ⟨fun h ↦ h.sub h₂ |>.congr (fun _ ↦ add_sub_cancel_right _ _) (fun _ ↦ rfl), fun h ↦ h.add h₂⟩

theorem IsBigO.add_iff_right (h₁ : f₁ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g ↔ (f₂ =O[l] g) :=
  ⟨fun h ↦ h.sub h₁ |>.congr (fun _ ↦ (eq_sub_of_add_eq' rfl).symm) (fun _ ↦ rfl), fun h ↦ h₁.add h⟩

theorem IsLittleO.add_iff_left (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g ↔ (f₁ =o[l] g) :=
  ⟨fun h ↦ h.sub h₂ |>.congr (fun _ ↦ add_sub_cancel_right _ _) (fun _ ↦ rfl), fun h ↦ h.add h₂⟩

theorem IsLittleO.add_iff_right (h₁ : f₁ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g ↔ (f₂ =o[l] g) :=
  ⟨fun h ↦ h.sub h₁ |>.congr (fun _ ↦ (eq_sub_of_add_eq' rfl).symm) (fun _ ↦ rfl), fun h ↦ h₁.add h⟩

theorem IsBigO.sub_iff_left (h₂ : f₂ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g ↔ (f₁ =O[l] g) :=
  ⟨fun h ↦ h.add h₂ |>.congr (fun _ ↦ sub_add_cancel ..) (fun _ ↦ rfl), fun h ↦ h.sub h₂⟩

theorem IsBigO.sub_iff_right (h₁ : f₁ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g ↔ (f₂ =O[l] g) :=
  ⟨fun h ↦ h₁.sub h |>.congr (fun _ ↦ sub_sub_self ..) (fun _ ↦ rfl), fun h ↦ h₁.sub h⟩

theorem IsLittleO.sub_iff_left (h₂ : f₂ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g ↔ (f₁ =o[l] g) :=
  ⟨fun h ↦ h.add h₂ |>.congr (fun _ ↦ sub_add_cancel ..) (fun _ ↦ rfl), fun h ↦ h.sub h₂⟩

theorem IsLittleO.sub_iff_right (h₁ : f₁ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g ↔ (f₂ =o[l] g) :=
  ⟨fun h ↦ h₁.sub h |>.congr (fun _ ↦ sub_sub_self ..) (fun _ ↦ rfl), fun h ↦ h₁.sub h⟩

end add_sub

/-!
### Lemmas about `IsBigO (f₁ - f₂) g l` / `IsLittleO (f₁ - f₂) g l` treated as a binary relation
-/


section IsBigOOAsRel

variable {f₁ f₂ f₃ : α → E'}

theorem IsBigOWith.symm (h : IsBigOWith c l (fun x => f₁ x - f₂ x) g) :
    IsBigOWith c l (fun x => f₂ x - f₁ x) g :=
  h.neg_left.congr_left fun _x => neg_sub _ _

theorem isBigOWith_comm :
    IsBigOWith c l (fun x => f₁ x - f₂ x) g ↔ IsBigOWith c l (fun x => f₂ x - f₁ x) g :=
  ⟨IsBigOWith.symm, IsBigOWith.symm⟩

theorem IsBigO.symm (h : (fun x => f₁ x - f₂ x) =O[l] g) : (fun x => f₂ x - f₁ x) =O[l] g :=
  h.neg_left.congr_left fun _x => neg_sub _ _

theorem isBigO_comm : (fun x => f₁ x - f₂ x) =O[l] g ↔ (fun x => f₂ x - f₁ x) =O[l] g :=
  ⟨IsBigO.symm, IsBigO.symm⟩

theorem IsLittleO.symm (h : (fun x => f₁ x - f₂ x) =o[l] g) : (fun x => f₂ x - f₁ x) =o[l] g := by
  simpa only [neg_sub] using h.neg_left

theorem isLittleO_comm : (fun x => f₁ x - f₂ x) =o[l] g ↔ (fun x => f₂ x - f₁ x) =o[l] g :=
  ⟨IsLittleO.symm, IsLittleO.symm⟩

theorem IsBigOWith.triangle (h₁ : IsBigOWith c l (fun x => f₁ x - f₂ x) g)
    (h₂ : IsBigOWith c' l (fun x => f₂ x - f₃ x) g) :
    IsBigOWith (c + c') l (fun x => f₁ x - f₃ x) g :=
  (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _

theorem IsBigO.triangle (h₁ : (fun x => f₁ x - f₂ x) =O[l] g)
    (h₂ : (fun x => f₂ x - f₃ x) =O[l] g) : (fun x => f₁ x - f₃ x) =O[l] g :=
  (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _

theorem IsLittleO.triangle (h₁ : (fun x => f₁ x - f₂ x) =o[l] g)
    (h₂ : (fun x => f₂ x - f₃ x) =o[l] g) : (fun x => f₁ x - f₃ x) =o[l] g :=
  (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _

theorem IsBigO.congr_of_sub (h : (fun x => f₁ x - f₂ x) =O[l] g) : f₁ =O[l] g ↔ f₂ =O[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun _x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun _x => sub_add_cancel _ _⟩

theorem IsLittleO.congr_of_sub (h : (fun x => f₁ x - f₂ x) =o[l] g) : f₁ =o[l] g ↔ f₂ =o[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun _x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun _x => sub_add_cancel _ _⟩

end IsBigOOAsRel

/-! ### Zero, one, and other constants -/


section ZeroConst

variable (g g' l)

theorem isLittleO_zero : (fun _x => (0 : E')) =o[l] g' :=
  IsLittleO.of_bound fun c hc =>
    univ_mem' fun x => by simpa using mul_nonneg hc.le (norm_nonneg <| g' x)

theorem isBigOWith_zero (hc : 0 ≤ c) : IsBigOWith c l (fun _x => (0 : E')) g' :=
  IsBigOWith.of_bound <| univ_mem' fun x => by simpa using mul_nonneg hc (norm_nonneg <| g' x)

theorem isBigOWith_zero' : IsBigOWith 0 l (fun _x => (0 : E')) g :=
  IsBigOWith.of_bound <| univ_mem' fun x => by simp

theorem isBigO_zero : (fun _x => (0 : E')) =O[l] g :=
  isBigO_iff_isBigOWith.2 ⟨0, isBigOWith_zero' _ _⟩

theorem isBigO_refl_left : (fun x => f' x - f' x) =O[l] g' :=
  (isBigO_zero g' l).congr_left fun _x => (sub_self _).symm

theorem isLittleO_refl_left : (fun x => f' x - f' x) =o[l] g' :=
  (isLittleO_zero g' l).congr_left fun _x => (sub_self _).symm

variable {g g' l}

@[simp]
theorem isBigOWith_zero_right_iff : (IsBigOWith c l f'' fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0 := by
  simp only [IsBigOWith_def, norm_zero, mul_zero, norm_le_zero_iff, EventuallyEq, Pi.zero_apply]

@[simp]
theorem isBigO_zero_right_iff : (f'' =O[l] fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h =>
    let ⟨_c, hc⟩ := h.isBigOWith
    isBigOWith_zero_right_iff.1 hc,
    fun h => (isBigOWith_zero_right_iff.2 h : IsBigOWith 1 _ _ _).isBigO⟩

@[simp]
theorem isLittleO_zero_right_iff : (f'' =o[l] fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h => isBigO_zero_right_iff.1 h.isBigO,
   fun h => IsLittleO.of_isBigOWith fun _c _hc => isBigOWith_zero_right_iff.2 h⟩

theorem isBigOWith_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) :
    IsBigOWith (‖c‖ / ‖c'‖) l (fun _x : α => c) fun _x => c' := by
  simp only [IsBigOWith_def]
  apply univ_mem'
  intro x
  rw [mem_setOf, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hc')]

theorem isBigO_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) :
    (fun _x : α => c) =O[l] fun _x => c' :=
  (isBigOWith_const_const c hc' l).isBigO

@[simp]
theorem isBigO_const_const_iff {c : E''} {c' : F''} (l : Filter α) [l.NeBot] :
    ((fun _x : α => c) =O[l] fun _x => c') ↔ c' = 0 → c = 0 := by
  rcases eq_or_ne c' 0 with (rfl | hc')
  · simp [EventuallyEq]
  · simp [hc', isBigO_const_const _ hc']

@[simp]
theorem isBigO_pure {x} : f'' =O[pure x] g'' ↔ g'' x = 0 → f'' x = 0 :=
  calc
    f'' =O[pure x] g'' ↔ (fun _y : α => f'' x) =O[pure x] fun _ => g'' x := isBigO_congr rfl rfl
    _ ↔ g'' x = 0 → f'' x = 0 := isBigO_const_const_iff _

end ZeroConst

/-! ### Multiplication by a constant -/

theorem isBigOWith_const_mul_self (c : R) (f : α → R) (l : Filter α) :
    IsBigOWith ‖c‖ l (fun x => c * f x) f :=
  isBigOWith_of_le' _ fun _x => norm_mul_le _ _

theorem isBigO_const_mul_self (c : R) (f : α → R) (l : Filter α) : (fun x => c * f x) =O[l] f :=
  (isBigOWith_const_mul_self c f l).isBigO

theorem IsBigOWith.const_mul_left {f : α → R} (h : IsBigOWith c l f g) (c' : R) :
    IsBigOWith (‖c'‖ * c) l (fun x => c' * f x) g :=
  (isBigOWith_const_mul_self c' f l).trans h (norm_nonneg c')

theorem IsBigO.const_mul_left {f : α → R} (h : f =O[l] g) (c' : R) : (fun x => c' * f x) =O[l] g :=
  let ⟨_c, hc⟩ := h.isBigOWith
  (hc.const_mul_left c').isBigO

theorem isBigOWith_self_const_mul' (u : Rˣ) (f : α → R) (l : Filter α) :
    IsBigOWith ‖(↑u⁻¹ : R)‖ l f fun x => ↑u * f x :=
  (isBigOWith_const_mul_self ↑u⁻¹ (fun x ↦ ↑u * f x) l).congr_left
    fun x ↦ u.inv_mul_cancel_left (f x)

theorem isBigOWith_self_const_mul {c : S} (hc : c ≠ 0) (f : α → S) (l : Filter α) :
    IsBigOWith ‖c‖⁻¹ l f fun x ↦ c * f x := by
  simp [IsBigOWith, inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr hc)]

theorem isBigO_self_const_mul' {c : R} (hc : IsUnit c) (f : α → R) (l : Filter α) :
    f =O[l] fun x => c * f x :=
  let ⟨u, hu⟩ := hc
  hu ▸ (isBigOWith_self_const_mul' u f l).isBigO

theorem isBigO_self_const_mul {c : S} (hc : c ≠ 0) (f : α → S) (l : Filter α) :
    f =O[l] fun x ↦ c * f x :=
  (isBigOWith_self_const_mul hc f l).isBigO

theorem isBigO_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) :
    (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  ⟨(isBigO_self_const_mul' hc f l).trans, fun h => h.const_mul_left c⟩

theorem isBigO_const_mul_left_iff {f : α → S} {c : S} (hc : c ≠ 0) :
    (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  ⟨(isBigO_self_const_mul hc f l).trans, (isBigO_const_mul_self c f l).trans⟩

theorem IsLittleO.const_mul_left {f : α → R} (h : f =o[l] g) (c : R) : (fun x => c * f x) =o[l] g :=
  (isBigO_const_mul_self c f l).trans_isLittleO h

theorem isLittleO_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) :
    (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  ⟨(isBigO_self_const_mul' hc f l).trans_isLittleO, fun h => h.const_mul_left c⟩

theorem isLittleO_const_mul_left_iff {f : α → S} {c : S} (hc : c ≠ 0) :
    (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  ⟨(isBigO_self_const_mul hc f l).trans_isLittleO, (isBigO_const_mul_self c f l).trans_isLittleO⟩

theorem IsBigOWith.of_const_mul_right {g : α → R} {c : R} (hc' : 0 ≤ c')
    (h : IsBigOWith c' l f fun x => c * g x) : IsBigOWith (c' * ‖c‖) l f g :=
  h.trans (isBigOWith_const_mul_self c g l) hc'

theorem IsBigO.of_const_mul_right {g : α → R} {c : R} (h : f =O[l] fun x => c * g x) : f =O[l] g :=
  let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.of_const_mul_right cnonneg).isBigO

theorem IsBigOWith.const_mul_right' {g : α → R} {u : Rˣ} {c' : ℝ} (hc' : 0 ≤ c')
    (h : IsBigOWith c' l f g) : IsBigOWith (c' * ‖(↑u⁻¹ : R)‖) l f fun x => ↑u * g x :=
  h.trans (isBigOWith_self_const_mul' _ _ _) hc'

theorem IsBigOWith.const_mul_right {g : α → S} {c : S} (hc : c ≠ 0) {c' : ℝ} (hc' : 0 ≤ c')
    (h : IsBigOWith c' l f g) : IsBigOWith (c' * ‖c‖⁻¹) l f fun x => c * g x :=
  h.trans (isBigOWith_self_const_mul hc g l) hc'

theorem IsBigO.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : f =O[l] g) :
    f =O[l] fun x => c * g x :=
  h.trans (isBigO_self_const_mul' hc g l)

theorem IsBigO.const_mul_right {g : α → S} {c : S} (hc : c ≠ 0) (h : f =O[l] g) :
    f =O[l] fun x => c * g x :=
  match h.exists_nonneg with
  | ⟨_, hd, hd'⟩ => (hd'.const_mul_right hc hd).isBigO

theorem isBigO_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) :
    (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩

theorem isBigO_const_mul_right_iff {g : α → S} {c : S} (hc : c ≠ 0) :
    (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  ⟨fun h ↦ h.of_const_mul_right, fun h ↦ h.const_mul_right hc⟩

theorem IsLittleO.of_const_mul_right {g : α → R} {c : R} (h : f =o[l] fun x => c * g x) :
    f =o[l] g :=
  h.trans_isBigO (isBigO_const_mul_self c g l)

theorem IsLittleO.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : f =o[l] g) :
    f =o[l] fun x => c * g x :=
  h.trans_isBigO (isBigO_self_const_mul' hc g l)

theorem IsLittleO.const_mul_right {g : α → S} {c : S} (hc : c ≠ 0) (h : f =o[l] g) :
    f =o[l] fun x => c * g x :=
  h.trans_isBigO <| isBigO_self_const_mul hc g l

theorem isLittleO_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) :
    (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩

theorem isLittleO_const_mul_right_iff {g : α → S} {c : S} (hc : c ≠ 0) :
    (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  ⟨fun h ↦ h.of_const_mul_right, fun h ↦ h.trans_isBigO (isBigO_self_const_mul hc g l)⟩

/-! ### Multiplication -/

theorem IsBigOWith.mul {f₁ f₂ : α → R} {g₁ g₂ : α → S} {c₁ c₂ : ℝ} (h₁ : IsBigOWith c₁ l f₁ g₁)
    (h₂ : IsBigOWith c₂ l f₂ g₂) :
    IsBigOWith (c₁ * c₂) l (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x := by
  simp only [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with _ hx₁ hx₂
  apply le_trans (norm_mul_le _ _)
  convert mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_trans (norm_nonneg _) hx₁) using 1
  rw [norm_mul, mul_mul_mul_comm]

theorem IsBigO.mul {f₁ f₂ : α → R} {g₁ g₂ : α → S} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x => f₁ x * f₂ x) =O[l] fun x => g₁ x * g₂ x :=
  let ⟨_c, hc⟩ := h₁.isBigOWith
  let ⟨_c', hc'⟩ := h₂.isBigOWith
  (hc.mul hc').isBigO

theorem IsBigO.mul_isLittleO {f₁ f₂ : α → R} {g₁ g₂ : α → S} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x := by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩
  exact (hc'.mul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel₀ _ (ne_of_gt c'pos))

theorem IsLittleO.mul_isBigO {f₁ f₂ : α → R} {g₁ g₂ : α → S} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x ↦ f₁ x * f₂ x) =o[l] fun x ↦ g₁ x * g₂ x := by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩
  exact ((h₁ (div_pos cpos c'pos)).mul hc').congr_const (div_mul_cancel₀ _ (ne_of_gt c'pos))

theorem IsLittleO.mul {f₁ f₂ : α → R} {g₁ g₂ : α → S} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x ↦ f₁ x * f₂ x) =o[l] fun x ↦ g₁ x * g₂ x :=
  h₁.mul_isBigO h₂.isBigO

theorem IsBigOWith.pow' [NormOneClass S] {f : α → R} {g : α → S} (h : IsBigOWith c l f g) :
    ∀ n : ℕ, IsBigOWith (Nat.casesOn n ‖(1 : R)‖ fun n ↦ c ^ (n + 1))
      l (fun x => f x ^ n) fun x => g x ^ n
  | 0 => by
    have : Nontrivial S := NormOneClass.nontrivial
    simpa using isBigOWith_const_const (1 : R) (one_ne_zero' S) l
  | 1 => by simpa
  | n + 2 => by simpa [pow_succ] using (IsBigOWith.pow' h (n + 1)).mul h

theorem IsBigOWith.pow [NormOneClass R] [NormOneClass S]
    {f : α → R} {g : α → S} (h : IsBigOWith c l f g) :
    ∀ n : ℕ, IsBigOWith (c ^ n) l (fun x => f x ^ n) fun x => g x ^ n
  | 0 => by simpa using h.pow' 0
  | n + 1 => h.pow' (n + 1)

theorem IsBigOWith.of_pow [NormOneClass S] {n : ℕ} {f : α → S} {g : α → R}
    (h : IsBigOWith c l (f ^ n) (g ^ n)) (hn : n ≠ 0) (hc : c ≤ c' ^ n) (hc' : 0 ≤ c') :
    IsBigOWith c' l f g :=
  IsBigOWith.of_bound <| (h.weaken hc).bound.mono fun x hx ↦
    le_of_pow_le_pow_left₀ hn (by positivity) <|
      calc
        ‖f x‖ ^ n = ‖f x ^ n‖ := (norm_pow _ _).symm
        _ ≤ c' ^ n * ‖g x ^ n‖ := hx
        _ ≤ c' ^ n * ‖g x‖ ^ n := by gcongr; exact norm_pow_le' _ hn.bot_lt
        _ = (c' * ‖g x‖) ^ n := (mul_pow _ _ _).symm

theorem IsBigO.pow [NormOneClass S] {f : α → R} {g : α → S} (h : f =O[l] g) (n : ℕ) :
    (fun x => f x ^ n) =O[l] fun x => g x ^ n :=
  let ⟨_C, hC⟩ := h.isBigOWith
  isBigO_iff_isBigOWith.2 ⟨_, hC.pow' n⟩

theorem IsLittleO.pow {f : α → R} {g : α → S} (h : f =o[l] g) {n : ℕ} (hn : 0 < n) :
    (fun x => f x ^ n) =o[l] fun x => g x ^ n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'; clear hn
  induction n with
  | zero => simpa only [pow_one]
  | succ n ihn => convert ihn.mul h <;> simp [pow_succ]

theorem IsLittleO.of_pow [NormOneClass S] {f : α → S} {g : α → R} {n : ℕ}
    (h : (f ^ n) =o[l] (g ^ n)) (hn : n ≠ 0) : f =o[l] g :=
  IsLittleO.of_isBigOWith fun _c hc => (h.def' <| pow_pos hc _).of_pow hn le_rfl hc.le

/-! ### Inverse -/

theorem IsBigOWith.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : IsBigOWith c l f g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : IsBigOWith c l (fun x => (g x)⁻¹) fun x => (f x)⁻¹ := by
  refine IsBigOWith.of_bound (h.bound.mp (h₀.mono fun x h₀ hle => ?_))
  rcases eq_or_ne (f x) 0 with hx | hx
  · simp only [hx, h₀ hx, inv_zero, norm_zero, mul_zero, le_rfl]
  · have hc : 0 < c := pos_of_mul_pos_left ((norm_pos_iff.2 hx).trans_le hle) (norm_nonneg _)
    replace hle := inv_anti₀ (norm_pos_iff.2 hx) hle
    simpa only [norm_inv, mul_inv, ← div_eq_inv_mul, div_le_iff₀ hc] using hle

theorem IsBigO.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =O[l] g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : (fun x => (g x)⁻¹) =O[l] fun x => (f x)⁻¹ :=
  let ⟨_c, hc⟩ := h.isBigOWith
  (hc.inv_rev h₀).isBigO

theorem IsLittleO.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =o[l] g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : (fun x => (g x)⁻¹) =o[l] fun x => (f x)⁻¹ :=
  IsLittleO.of_isBigOWith fun _c hc => (h.def' hc).inv_rev h₀

/-! ### Sum -/

section Sum

variable {ι : Type*} {A : ι → α → E'} {C : ι → ℝ} {s : Finset ι}

theorem IsBigOWith.sum (h : ∀ i ∈ s, IsBigOWith (C i) l (A i) g) :
    IsBigOWith (∑ i ∈ s, C i) l (fun x => ∑ i ∈ s, A i x) g := by
  induction s using Finset.cons_induction with
  | empty => simp only [isBigOWith_zero', Finset.sum_empty]
  | cons i s is IH =>
    simp only [Finset.sum_cons, Finset.forall_mem_cons] at h ⊢
    exact h.1.add (IH h.2)

theorem IsBigO.sum (h : ∀ i ∈ s, A i =O[l] g) : (fun x => ∑ i ∈ s, A i x) =O[l] g := by
  simp only [IsBigO_def] at *
  choose! C hC using h
  exact ⟨_, IsBigOWith.sum hC⟩

theorem IsLittleO.sum (h : ∀ i ∈ s, A i =o[l] g') : (fun x => ∑ i ∈ s, A i x) =o[l] g' := by
  simp only [← Finset.sum_apply]
  exact Finset.sum_induction A (· =o[l] g') (fun _ _ ↦ .add) (isLittleO_zero ..) h

variable {B : ι → α → ℝ}

/-- If each term `A i` of a sum `IsBigO` of `B i`, then the sum of the `A i` `IsBigO` of the sum
of the norms of the `B i`. -/
theorem IsBigOWith.sum_congr
    (hAB : ∀ i ∈ s, IsBigOWith (C i) l (A i) (B i)) :
    IsBigOWith (sSup (C '' s)) l (fun H ↦ ∑ i ∈ s, A i H) (fun H ↦ ∑ i ∈ s, ‖B i H‖) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [isBigOWith_zero]
  simp only [IsBigOWith_def] at *
  filter_upwards [(eventually_all_finset s).mpr hAB]
    with x hx
  calc
    ‖∑ i ∈ s, A i x‖ ≤ ∑ i ∈ s, ‖A i x‖ := norm_sum_le ..
    _ ≤ ∑ i ∈ s, C i * ‖B i x‖ := Finset.sum_le_sum (fun j hj ↦ hx j hj)
    _ ≤ ∑ i ∈ s, sSup (C '' s) * ‖B i x‖ := by
        refine Finset.sum_le_sum ?_
        intro j hj; gcongr
        rw [← s.sup'_eq_csSup_image hs, Finset.le_sup'_iff]; use j
    _ = sSup (C '' s) * ∑ i ∈ s, ‖B i x‖ := (Finset.mul_sum ..).symm
    _ = sSup (C '' s) * ‖∑ i ∈ s, ‖B i x‖‖ := by
      congr; rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))]

theorem IsBigO.sum_congr (hAB : ∀ i ∈ s, A i =O[l] B i) :
    (fun H => ∑ i ∈ s, A i H) =O[l] fun H => ∑ i ∈ s, ‖B i H‖ := by
  simp only [IsBigO_def] at *
  choose! C hC using hAB
  exact ⟨_, IsBigOWith.sum_congr hC⟩

theorem IsLittleO.sum_congr (hAB : ∀ i ∈ s, A i =o[l] B i) :
    (fun H => ∑ i ∈ s, A i H) =o[l] fun H => ∑ i ∈ s, ‖B i H‖ := by
  induction s using Finset.cons_induction with
  | empty => simp [isLittleO_zero]
  | cons i s his h =>
  simp_rw [Finset.sum_cons]
  calc (fun H => A i H + ∑ j ∈ s, A j H)
      =o[l] fun H => ‖B i H‖ + ‖∑ j ∈ s, ‖B j H‖‖ :=
          (hAB i (by simp)).add_add (h (fun j hj => hAB j (by simp [hj])))
    _ =ᶠ[l] fun H => ‖B i H‖ + ∑ j ∈ s, ‖B j H‖ := by
        refine Eventually.of_forall fun H ↦ congr_arg (‖B i H‖ + ·) ?_
        exact Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)

/-- Similar to `IsBigOWith.sum_congr` except the index set can change in the sum. This requires the
constant in `hAB` to be independent of the index `i` and also the big-O relationship to "kick in"
at the same point along the running variable. Hence the `⊤` in `⊤ ×ˢ l`. -/
theorem IsBigOWith.sum_congr' {C : ℝ} {i : α → Finset ι}
    (hAB : IsBigOWith C (⊤ ×ˢ l) A.uncurry B.uncurry) :
    IsBigOWith C l (fun H => ∑ j ∈ i H, A j H) (fun H => ∑ j ∈ i H, ‖B j H‖) := by
  simp only [IsBigOWith_def] at *
  obtain ⟨s₁, hs₁, s₂, hs₂, hbound⟩ := Filter.eventually_prod_iff.mp hAB
  filter_upwards [hs₂] with H hH
  calc
    ‖∑ j ∈ i H, A j H‖ ≤ ∑ j ∈ i H, ‖A j H‖ := norm_sum_le ..
    _ ≤ ∑ j ∈ i H, C * ‖B j H‖ :=
        Finset.sum_le_sum fun j _ => hbound (Filter.eventually_top.mp hs₁ j) hH
    _ = C * ∑ j ∈ i H, ‖B j H‖ := (Finset.mul_sum ..).symm
    _ = C * ‖∑ j ∈ i H, ‖B j H‖‖ := by
        congr; rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))]

theorem IsBigO.sum_congr' {i : α → Finset ι} (hAB : A.uncurry =O[⊤ ×ˢ l] B.uncurry) :
    (fun H => ∑ j ∈ i H, A j H) =O[l] (fun H => ∑ j ∈ i H, ‖B j H‖) := by
  simp only [IsBigO_def]
  obtain ⟨C, hC⟩ := hAB.isBigOWith
  exact ⟨C, hC.sum_congr'⟩

theorem IsLittleO.sum_congr' {i : α → Finset ι} (hAB : A.uncurry =o[⊤ ×ˢ l] B.uncurry) :
    (fun H => ∑ j ∈ i H, A j H) =o[l] (fun H => ∑ j ∈ i H, ‖B j H‖) := by
  rw [isLittleO_iff_forall_isBigOWith] at *
  intro c hc
  exact (hAB hc).sum_congr'

end Sum

/-!
### Eventually (u / v) * v = u

If `u` and `v` are linked by an `IsBigOWith` relation, then we
eventually have `(u / v) * v = u`, even if `v` vanishes.
-/

section EventuallyMulDivCancel

variable {u v : α → 𝕜}

theorem IsBigOWith.eventually_mul_div_cancel (h : IsBigOWith c l u v) : u / v * v =ᶠ[l] u :=
  Eventually.mono h.bound fun y hy => div_mul_cancel_of_imp fun hv => by simpa [hv] using hy

/-- If `u = O(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem IsBigO.eventually_mul_div_cancel (h : u =O[l] v) : u / v * v =ᶠ[l] u :=
  let ⟨_c, hc⟩ := h.isBigOWith
  hc.eventually_mul_div_cancel

/-- If `u = o(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem IsLittleO.eventually_mul_div_cancel (h : u =o[l] v) : u / v * v =ᶠ[l] u :=
  (h.forall_isBigOWith zero_lt_one).eventually_mul_div_cancel

end EventuallyMulDivCancel

end Asymptotics
