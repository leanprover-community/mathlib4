/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Asymptotics

We introduce these relations:

* `IsBigOWith c l f g` : "f is big O of g along l with constant c";
* `f =O[l] g` : "f is big O of g along l";
* `f =Θ[l] g` : "f is big O of g along l and vice versa";
* `f =o[l] g` : "f is little o of g along l";

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

@[expose] public section

assert_not_exists IsBoundedSMul Summable OpenPartialHomeomorph BoundedLENhdsClass

open Filter

namespace Asymptotics

variable {α E F E' : Type*} {c : ℝ} {f : α → E} {g : α → F} {l : Filter α}

variable [Norm E] [Norm F] [SeminormedAddGroup E']

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
theorem isBigO_iff' {g : α → E'} :
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
theorem isBigO_iff'' {g : α → E'} :
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

end Defs

end Asymptotics
