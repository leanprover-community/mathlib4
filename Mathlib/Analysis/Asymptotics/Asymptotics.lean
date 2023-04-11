/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.asymptotics.asymptotics
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.LocalHomeomorph

/-!
# Asymptotics

We introduce these relations:

* `is_O_with c l f g` : "f is big O of g along l with constant c";
* `f =O[l] g` : "f is big O of g along l";
* `f =o[l] g` : "f is little o of g along l".

Here `l` is any filter on the domain of `f` and `g`, which are assumed to be the same. The codomains
of `f` and `g` do not need to be the same; all that is needed that there is a norm associated with
these types, and it is the norm that is compared asymptotically.

The relation `is_O_with c` is introduced to factor out common algebraic arguments in the proofs of
similar properties of `is_O` and `is_o`. Usually proofs outside of this file should use `is_O`
instead.

Often the ranges of `f` and `g` will be the real numbers, in which case the norm is the absolute
value. In general, we have

  `f =O[l] g ↔ (λ x, ‖f x‖) =O[l] (λ x, ‖g x‖)`,

and similarly for `is_o`. But our setup allows us to use the notions e.g. with functions
to the integers, rationals, complex numbers, or any normed vector space without mentioning the
norm explicitly.

If `f` and `g` are functions to a normed field like the reals or complex numbers and `g` is always
nonzero, we have

  `f =o[l] g ↔ tendsto (λ x, f x / (g x)) l (𝓝 0)`.

In fact, the right-to-left direction holds without the hypothesis on `g`, and in the other direction
it suffices to assume that `f` is zero wherever `g` is. (This generalization is useful in defining
the Fréchet derivative.)
-/


open Filter Set

open Topology BigOperators Classical Filter NNReal

namespace Asymptotics

set_option linter.uppercaseLean3 false

variable {α : Type _} {β : Type _} {E : Type _} {F : Type _} {G : Type _} {E' : Type _}
  {F' : Type _} {G' : Type _} {E'' : Type _} {F'' : Type _} {G'' : Type _} {R : Type _}
  {R' : Type _} {𝕜 : Type _} {𝕜' : Type _}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']

variable [NormedField 𝕜] [NormedField 𝕜']

variable {c c' c₁ c₂ : ℝ} {f : α → E} {g : α → F} {k : α → G}

variable {f' : α → E'} {g' : α → F'} {k' : α → G'}

variable {f'' : α → E''} {g'' : α → F''} {k'' : α → G''}

variable {l l' : Filter α}

section Defs

/-! ### Definitions -/


/-- This version of the Landau notation `is_O_with C l f g` where `f` and `g` are two functions on
a type `α` and `l` is a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by `C * ‖g‖`.
In other words, `‖f‖ / ‖g‖` is eventually bounded by `C`, modulo division by zero issues that are
avoided by this definition. Probably you want to use `is_O` instead of this relation. -/
irreducible_def Is𝓞With (c : ℝ) (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖
#align asymptotics.is_O_with Asymptotics.Is𝓞With

/-- Definition of `is_O_with`. We record it in a lemma as `is_O_with` is irreducible. -/
theorem is𝓞With_iff : Is𝓞With c l f g ↔ ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by rw [Is𝓞With_def]
#align asymptotics.is_O_with_iff Asymptotics.is𝓞With_iff

alias is𝓞With_iff ↔ Is𝓞With.bound Is𝓞With.of_bound
#align asymptotics.is_O_with.bound Asymptotics.Is𝓞With.bound
#align asymptotics.is_O_with.of_bound Asymptotics.Is𝓞With.of_bound

/-- The Landau notation `f =O[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by a constant multiple of `‖g‖`.
In other words, `‖f‖ / ‖g‖` is eventually bounded, modulo division by zero issues that are avoided
by this definition. -/
irreducible_def Is𝓞 (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∃ c : ℝ, Is𝓞With c l f g
#align asymptotics.is_O Asymptotics.Is𝓞

-- mathport name: «expr =O[ ] »
@[inherit_doc]
notation:100 f " =O[" l "] " g:100 => Is𝓞 l f g

/-- Definition of `is_O` in terms of `is_O_with`. We record it in a lemma as `is_O` is
irreducible. -/
theorem is𝓞_iff_is𝓞With : f =O[l] g ↔ ∃ c : ℝ, Is𝓞With c l f g := by rw [Is𝓞_def]
#align asymptotics.is_O_iff_is_O_with Asymptotics.is𝓞_iff_is𝓞With

/-- Definition of `is_O` in terms of filters. We record it in a lemma as we will set
`is_O` to be irreducible at the end of this file. -/
theorem is𝓞_iff : f =O[l] g ↔ ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  simp only [Is𝓞_def, Is𝓞With_def]
#align asymptotics.is_O_iff Asymptotics.is𝓞_iff

theorem Is𝓞.of_bound (c : ℝ) (h : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g :=
  is𝓞_iff.2 ⟨c, h⟩
#align asymptotics.is_O.of_bound Asymptotics.Is𝓞.of_bound

theorem Is𝓞.of_bound' (h : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖) : f =O[l] g :=
  Is𝓞.of_bound 1 <| by
    simp_rw [one_mul]
    exact h
#align asymptotics.is_O.of_bound' Asymptotics.Is𝓞.of_bound'

theorem Is𝓞.bound : f =O[l] g → ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  is𝓞_iff.1
#align asymptotics.is_O.bound Asymptotics.Is𝓞.bound

/-- The Landau notation `f =o[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by an arbitrarily small constant
multiple of `‖g‖`. In other words, `‖f‖ / ‖g‖` tends to `0` along `l`, modulo division by zero
issues that are avoided by this definition. -/
irreducible_def Is𝓸 (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → Is𝓞With c l f g
#align asymptotics.is_o Asymptotics.Is𝓸

-- mathport name: «expr =o[ ] »
@[inherit_doc]
notation:100 f " =o[" l "] " g:100 => Is𝓸 l f g

/-- Definition of `is_o` in terms of `is_O_with`. We record it in a lemma as we will set
`is_o` to be irreducible at the end of this file. -/
theorem is𝓸_iff_forall_is𝓞With : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → Is𝓞With c l f g := by
  rw [Is𝓸_def]
#align asymptotics.is_o_iff_forall_is_O_with Asymptotics.is𝓸_iff_forall_is𝓞With

alias is𝓸_iff_forall_is𝓞With ↔ Is𝓸.forall_is𝓞With Is𝓸.of_is𝓞With
#align asymptotics.is_o.forall_is_O_with Asymptotics.Is𝓸.forall_is𝓞With
#align asymptotics.is_o.of_is_O_with Asymptotics.Is𝓸.of_is𝓞With

/-- Definition of `is_o` in terms of filters. We record it in a lemma as we will set
`is_o` to be irreducible at the end of this file. -/
theorem is𝓸_iff : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  simp only [Is𝓸_def, Is𝓞With_def]
#align asymptotics.is_o_iff Asymptotics.is𝓸_iff

alias is𝓸_iff ↔ Is𝓸.bound Is𝓸.of_bound
#align asymptotics.is_o.bound Asymptotics.Is𝓸.bound
#align asymptotics.is_o.of_bound Asymptotics.Is𝓸.of_bound

theorem Is𝓸.def (h : f =o[l] g) (hc : 0 < c) : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  is𝓸_iff.1 h hc
#align asymptotics.is_o.def Asymptotics.Is𝓸.def

theorem Is𝓸.def' (h : f =o[l] g) (hc : 0 < c) : Is𝓞With c l f g :=
  is𝓞With_iff.2 <| is𝓸_iff.1 h hc
#align asymptotics.is_o.def' Asymptotics.Is𝓸.def'

end Defs

/-! ### Conversions -/


theorem Is𝓞With.is𝓞 (h : Is𝓞With c l f g) : f =O[l] g := by rw [Is𝓞_def]; exact ⟨c, h⟩
#align asymptotics.is_O_with.is_O Asymptotics.Is𝓞With.is𝓞

theorem Is𝓸.is𝓞With (hgf : f =o[l] g) : Is𝓞With 1 l f g :=
  hgf.def' zero_lt_one
#align asymptotics.is_o.is_O_with Asymptotics.Is𝓸.is𝓞With

theorem Is𝓸.is𝓞 (hgf : f =o[l] g) : f =O[l] g :=
  hgf.is𝓞With.is𝓞
#align asymptotics.is_o.is_O Asymptotics.Is𝓸.is𝓞

theorem Is𝓞.is𝓞With : f =O[l] g → ∃ c : ℝ, Is𝓞With c l f g :=
  is𝓞_iff_is𝓞With.1
#align asymptotics.is_O.is_O_with Asymptotics.Is𝓞.is𝓞With

theorem Is𝓞With.weaken (h : Is𝓞With c l f g') (hc : c ≤ c') : Is𝓞With c' l f g' :=
  Is𝓞With.of_bound <|
    mem_of_superset h.bound fun x hx =>
      calc
        ‖f x‖ ≤ c * ‖g' x‖ := hx
        _ ≤ _ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)

#align asymptotics.is_O_with.weaken Asymptotics.Is𝓞With.weaken

theorem Is𝓞With.exists_pos (h : Is𝓞With c l f g') : ∃ (c' : _) (_H : 0 < c'), Is𝓞With c' l f g' :=
  ⟨max c 1, lt_of_lt_of_le zero_lt_one (le_max_right c 1), h.weaken <| le_max_left c 1⟩
#align asymptotics.is_O_with.exists_pos Asymptotics.Is𝓞With.exists_pos

theorem Is𝓞.exists_pos (h : f =O[l] g') : ∃ (c : _) (_H : 0 < c), Is𝓞With c l f g' :=
  let ⟨_c, hc⟩ := h.is𝓞With
  hc.exists_pos
#align asymptotics.is_O.exists_pos Asymptotics.Is𝓞.exists_pos

theorem Is𝓞With.exists_nonneg (h : Is𝓞With c l f g') :
    ∃ (c' : _) (_H : 0 ≤ c'), Is𝓞With c' l f g' :=
  let ⟨c, cpos, hc⟩ := h.exists_pos
  ⟨c, le_of_lt cpos, hc⟩
#align asymptotics.is_O_with.exists_nonneg Asymptotics.Is𝓞With.exists_nonneg

theorem Is𝓞.exists_nonneg (h : f =O[l] g') : ∃ (c : _) (_H : 0 ≤ c), Is𝓞With c l f g' :=
  let ⟨_c, hc⟩ := h.is𝓞With
  hc.exists_nonneg
#align asymptotics.is_O.exists_nonneg Asymptotics.Is𝓞.exists_nonneg

/-- `f = O(g)` if and only if `is_O_with c f g` for all sufficiently large `c`. -/
theorem is𝓞_iff_eventually_is𝓞With : f =O[l] g' ↔ ∀ᶠ c in atTop, Is𝓞With c l f g' :=
  is𝓞_iff_is𝓞With.trans
    ⟨fun ⟨c, hc⟩ => mem_atTop_sets.2 ⟨c, fun _c' hc' => hc.weaken hc'⟩, fun h => h.exists⟩
#align asymptotics.is_O_iff_eventually_is_O_with Asymptotics.is𝓞_iff_eventually_is𝓞With

/-- `f = O(g)` if and only if `∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖` for all sufficiently large `c`. -/
theorem is𝓞_iff_eventually : f =O[l] g' ↔ ∀ᶠ c in atTop, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g' x‖ :=
  is𝓞_iff_eventually_is𝓞With.trans <| by simp only [Is𝓞With_def]
#align asymptotics.is_O_iff_eventually Asymptotics.is𝓞_iff_eventually

theorem Is𝓞.exists_mem_basis {ι} {p : ι → Prop} {s : ι → Set α} (h : f =O[l] g')
    (hb : l.HasBasis p s) :
    ∃ (c : ℝ) (_hc : 0 < c) (i : ι) (_hi : p i), ∀ x ∈ s i, ‖f x‖ ≤ c * ‖g' x‖ :=
  flip Exists₂.imp h.exists_pos fun c _hc h => by
    simpa only [is𝓞With_iff, hb.eventually_iff, exists_prop] using h
#align asymptotics.is_O.exists_mem_basis Asymptotics.Is𝓞.exists_mem_basis

theorem is𝓞With_inv (hc : 0 < c) : Is𝓞With c⁻¹ l f g ↔ ∀ᶠ x in l, c * ‖f x‖ ≤ ‖g x‖ := by
  simp only [Is𝓞With_def, ← div_eq_inv_mul, le_div_iff' hc]
#align asymptotics.is_O_with_inv Asymptotics.is𝓞With_inv

-- We prove this lemma with strange assumptions to get two lemmas below automatically
theorem is𝓸_iff_nat_mul_le_aux (h₀ : (∀ x, 0 ≤ ‖f x‖) ∨ ∀ x, 0 ≤ ‖g x‖) :
    f =o[l] g ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f x‖ ≤ ‖g x‖ := by
  constructor
  · rintro H (_ | n)
    · refine' (H.def one_pos).mono fun x h₀' => _
      rw [Nat.cast_zero, MulZeroClass.zero_mul]
      refine' h₀.elim (fun hf => (hf x).trans _) fun hg => hg x
      rwa [one_mul] at h₀'
    · have : (0 : ℝ) < n.succ := Nat.cast_pos.2 n.succ_pos
      exact (is𝓞With_inv this).1 (H.def' <| inv_pos.2 this)
  · refine' fun H => is𝓸_iff.2 fun ε ε0 => _
    rcases exists_nat_gt ε⁻¹ with ⟨n, hn⟩
    have hn₀ : (0 : ℝ) < n := (inv_pos.2 ε0).trans hn
    refine' ((is𝓞With_inv hn₀).2 (H n)).bound.mono fun x hfg => _
    refine' hfg.trans (mul_le_mul_of_nonneg_right (inv_le_of_inv_le ε0 hn.le) _)
    refine' h₀.elim (fun hf => nonneg_of_mul_nonneg_right ((hf x).trans hfg) _) fun h => h x
    exact inv_pos.2 hn₀
#align asymptotics.is_o_iff_nat_mul_le_aux Asymptotics.is𝓸_iff_nat_mul_le_aux

theorem is𝓸_iff_nat_mul_le : f =o[l] g' ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f x‖ ≤ ‖g' x‖ :=
  is𝓸_iff_nat_mul_le_aux (Or.inr fun _x => norm_nonneg _)
#align asymptotics.is_o_iff_nat_mul_le Asymptotics.is𝓸_iff_nat_mul_le

theorem is𝓸_iff_nat_mul_le' : f' =o[l] g ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f' x‖ ≤ ‖g x‖ :=
  is𝓸_iff_nat_mul_le_aux (Or.inl fun _x => norm_nonneg _)
#align asymptotics.is_o_iff_nat_mul_le' Asymptotics.is𝓸_iff_nat_mul_le'

/-! ### Subsingleton -/


@[nontriviality]
theorem is𝓸_of_subsingleton [Subsingleton E'] : f' =o[l] g' :=
  Is𝓸.of_bound fun c hc => by simp [Subsingleton.elim (f' _) 0, mul_nonneg hc.le]
#align asymptotics.is_o_of_subsingleton Asymptotics.is𝓸_of_subsingleton

@[nontriviality]
theorem is𝓞_of_subsingleton [Subsingleton E'] : f' =O[l] g' :=
  is𝓸_of_subsingleton.is𝓞
#align asymptotics.is_O_of_subsingleton Asymptotics.is𝓞_of_subsingleton

section congr

variable {f₁ f₂ : α → E} {g₁ g₂ : α → F}

/-! ### Congruence -/


theorem is𝓞With_congr (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    Is𝓞With c₁ l f₁ g₁ ↔ Is𝓞With c₂ l f₂ g₂ := by
  simp only [Is𝓞With_def]
  subst c₂
  apply Filter.eventually_congr
  filter_upwards [hf, hg]with _ e₁ e₂
  rw [e₁, e₂]
#align asymptotics.is_O_with_congr Asymptotics.is𝓞With_congr

theorem Is𝓞With.congr' (h : Is𝓞With c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂)
    (hg : g₁ =ᶠ[l] g₂) : Is𝓞With c₂ l f₂ g₂ :=
  (is𝓞With_congr hc hf hg).mp h
#align asymptotics.is_O_with.congr' Asymptotics.Is𝓞With.congr'

theorem Is𝓞With.congr (h : Is𝓞With c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : ∀ x, f₁ x = f₂ x)
    (hg : ∀ x, g₁ x = g₂ x) : Is𝓞With c₂ l f₂ g₂ :=
  h.congr' hc (univ_mem' hf) (univ_mem' hg)
#align asymptotics.is_O_with.congr Asymptotics.Is𝓞With.congr

theorem Is𝓞With.congr_left (h : Is𝓞With c l f₁ g) (hf : ∀ x, f₁ x = f₂ x) : Is𝓞With c l f₂ g :=
  h.congr rfl hf fun _ => rfl
#align asymptotics.is_O_with.congr_left Asymptotics.Is𝓞With.congr_left

theorem Is𝓞With.congr_right (h : Is𝓞With c l f g₁) (hg : ∀ x, g₁ x = g₂ x) : Is𝓞With c l f g₂ :=
  h.congr rfl (fun _ => rfl) hg
#align asymptotics.is_O_with.congr_right Asymptotics.Is𝓞With.congr_right

theorem Is𝓞With.congr_const (h : Is𝓞With c₁ l f g) (hc : c₁ = c₂) : Is𝓞With c₂ l f g :=
  h.congr hc (fun _ => rfl) fun _ => rfl
#align asymptotics.is_O_with.congr_const Asymptotics.Is𝓞With.congr_const

theorem is𝓞_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =O[l] g₁ ↔ f₂ =O[l] g₂ := by
  simp only [Is𝓞_def]
  exact exists_congr fun c => is𝓞With_congr rfl hf hg
#align asymptotics.is_O_congr Asymptotics.is𝓞_congr

theorem Is𝓞.congr' (h : f₁ =O[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =O[l] g₂ :=
  (is𝓞_congr hf hg).mp h
#align asymptotics.is_O.congr' Asymptotics.Is𝓞.congr'

theorem Is𝓞.congr (h : f₁ =O[l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) : f₂ =O[l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)
#align asymptotics.is_O.congr Asymptotics.Is𝓞.congr

theorem Is𝓞.congr_left (h : f₁ =O[l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =O[l] g :=
  h.congr hf fun _ => rfl
#align asymptotics.is_O.congr_left Asymptotics.Is𝓞.congr_left

theorem Is𝓞.congr_right (h : f =O[l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =O[l] g₂ :=
  h.congr (fun _ => rfl) hg
#align asymptotics.is_O.congr_right Asymptotics.Is𝓞.congr_right

theorem is𝓸_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =o[l] g₁ ↔ f₂ =o[l] g₂ := by
  simp only [Is𝓸_def]
  exact forall₂_congr fun c _hc => is𝓞With_congr (Eq.refl c) hf hg
#align asymptotics.is_o_congr Asymptotics.is𝓸_congr

theorem Is𝓸.congr' (h : f₁ =o[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =o[l] g₂ :=
  (is𝓸_congr hf hg).mp h
#align asymptotics.is_o.congr' Asymptotics.Is𝓸.congr'

theorem Is𝓸.congr (h : f₁ =o[l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    f₂ =o[l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)
#align asymptotics.is_o.congr Asymptotics.Is𝓸.congr

theorem Is𝓸.congr_left (h : f₁ =o[l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =o[l] g :=
  h.congr hf fun _ => rfl
#align asymptotics.is_o.congr_left Asymptotics.Is𝓸.congr_left

theorem Is𝓸.congr_right (h : f =o[l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =o[l] g₂ :=
  h.congr (fun _ => rfl) hg
#align asymptotics.is_o.congr_right Asymptotics.Is𝓸.congr_right

@[trans]
theorem _root_.Filter.EventuallyEq.trans_is𝓞 {f₁ f₂ : α → E} {g : α → F} (hf : f₁ =ᶠ[l] f₂)
    (h : f₂ =O[l] g) : f₁ =O[l] g :=
  h.congr' hf.symm EventuallyEq.rfl
#align filter.eventually_eq.trans_is_O Filter.EventuallyEq.trans_is𝓞

instance : @Trans (α → E) (α → E) (α → F) (· =ᶠ[l] ·) (· =O[l] ·) (· =O[l] ·) where
  trans := Filter.EventuallyEq.trans_is𝓞

@[trans]
theorem _root_.Filter.EventuallyEq.trans_is𝓸 {f₁ f₂ : α → E} {g : α → F} (hf : f₁ =ᶠ[l] f₂)
    (h : f₂ =o[l] g) : f₁ =o[l] g :=
  h.congr' hf.symm EventuallyEq.rfl
#align filter.eventually_eq.trans_is_o Filter.EventuallyEq.trans_is𝓸

instance : @Trans (α → E) (α → E) (α → F) (· =ᶠ[l] ·) (· =o[l] ·) (· =o[l] ·) where
  trans := Filter.EventuallyEq.trans_is𝓸

@[trans]
theorem Is𝓞.trans_eventuallyEq {f : α → E} {g₁ g₂ : α → F} (h : f =O[l] g₁) (hg : g₁ =ᶠ[l] g₂) :
    f =O[l] g₂ :=
  h.congr' EventuallyEq.rfl hg
#align asymptotics.is_O.trans_eventually_eq Asymptotics.Is𝓞.trans_eventuallyEq

instance : @Trans (α → E) (α → F) (α → F) (· =O[l] ·) (· =ᶠ[l] ·) (· =O[l] ·) where
  trans := Is𝓞.trans_eventuallyEq

@[trans]
theorem Is𝓸.trans_eventuallyEq {f : α → E} {g₁ g₂ : α → F} (h : f =o[l] g₁) (hg : g₁ =ᶠ[l] g₂) :
    f =o[l] g₂ :=
  h.congr' EventuallyEq.rfl hg
#align asymptotics.is_o.trans_eventually_eq Asymptotics.Is𝓸.trans_eventuallyEq

instance : @Trans (α → E) (α → F) (α → F) (· =o[l] ·) (· =ᶠ[l] ·) (· =o[l] ·) where
  trans := Is𝓸.trans_eventuallyEq

end congr

/-! ### Filter operations and transitivity -/


theorem Is𝓞With.comp_tendsto (hcfg : Is𝓞With c l f g) {k : β → α} {l' : Filter β}
    (hk : Tendsto k l' l) : Is𝓞With c l' (f ∘ k) (g ∘ k) :=
  Is𝓞With.of_bound <| hk hcfg.bound
#align asymptotics.is_O_with.comp_tendsto Asymptotics.Is𝓞With.comp_tendsto

theorem Is𝓞.comp_tendsto (hfg : f =O[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) :
    (f ∘ k) =O[l'] (g ∘ k) :=
  is𝓞_iff_is𝓞With.2 <| hfg.is𝓞With.imp fun _c h => h.comp_tendsto hk
#align asymptotics.is_O.comp_tendsto Asymptotics.Is𝓞.comp_tendsto

theorem Is𝓸.comp_tendsto (hfg : f =o[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) :
    (f ∘ k) =o[l'] (g ∘ k) :=
  Is𝓸.of_is𝓞With fun _c cpos => (hfg.forall_is𝓞With cpos).comp_tendsto hk
#align asymptotics.is_o.comp_tendsto Asymptotics.Is𝓸.comp_tendsto

@[simp]
theorem is𝓞With_map {k : β → α} {l : Filter β} :
    Is𝓞With c (map k l) f g ↔ Is𝓞With c l (f ∘ k) (g ∘ k) := by
  simp only [Is𝓞With_def]
  exact eventually_map
#align asymptotics.is_O_with_map Asymptotics.is𝓞With_map

@[simp]
theorem is𝓞_map {k : β → α} {l : Filter β} : f =O[map k l] g ↔ (f ∘ k) =O[l] (g ∘ k) := by
  simp only [Is𝓞_def, is𝓞With_map]
#align asymptotics.is_O_map Asymptotics.is𝓞_map

@[simp]
theorem is𝓸_map {k : β → α} {l : Filter β} : f =o[map k l] g ↔ (f ∘ k) =o[l] (g ∘ k) := by
  simp only [Is𝓸_def, is𝓞With_map]
#align asymptotics.is_o_map Asymptotics.is𝓸_map

theorem Is𝓞With.mono (h : Is𝓞With c l' f g) (hl : l ≤ l') : Is𝓞With c l f g :=
  Is𝓞With.of_bound <| hl h.bound
#align asymptotics.is_O_with.mono Asymptotics.Is𝓞With.mono

theorem Is𝓞.mono (h : f =O[l'] g) (hl : l ≤ l') : f =O[l] g :=
  is𝓞_iff_is𝓞With.2 <| h.is𝓞With.imp fun _c h => h.mono hl
#align asymptotics.is_O.mono Asymptotics.Is𝓞.mono

theorem Is𝓸.mono (h : f =o[l'] g) (hl : l ≤ l') : f =o[l] g :=
  Is𝓸.of_is𝓞With fun _c cpos => (h.forall_is𝓞With cpos).mono hl
#align asymptotics.is_o.mono Asymptotics.Is𝓸.mono

theorem Is𝓞With.trans (hfg : Is𝓞With c l f g) (hgk : Is𝓞With c' l g k) (hc : 0 ≤ c) :
    Is𝓞With (c * c') l f k := by
  simp only [Is𝓞With_def] at *
  filter_upwards [hfg, hgk]with x hx hx'
  calc
    ‖f x‖ ≤ c * ‖g x‖ := hx
    _ ≤ c * (c' * ‖k x‖) := (mul_le_mul_of_nonneg_left hx' hc)
    _ = c * c' * ‖k x‖ := (mul_assoc _ _ _).symm

#align asymptotics.is_O_with.trans Asymptotics.Is𝓞With.trans

@[trans]
theorem Is𝓞.trans {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g) (hgk : g =O[l] k) :
    f =O[l] k :=
  let ⟨_c, cnonneg, hc⟩ := hfg.exists_nonneg
  let ⟨_c', hc'⟩ := hgk.is𝓞With
  (hc.trans hc' cnonneg).is𝓞
#align asymptotics.is_O.trans Asymptotics.Is𝓞.trans

instance : @Trans (α → E) (α → F') (α → G) (· =O[l] ·) (· =O[l] ·) (· =O[l] ·) where
  trans := Is𝓞.trans

theorem Is𝓸.trans_is𝓞With (hfg : f =o[l] g) (hgk : Is𝓞With c l g k) (hc : 0 < c) : f =o[l] k :=
  by
  simp only [Is𝓸_def] at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact ((hfg this).trans hgk this.le).congr_const (div_mul_cancel _ hc.ne')
#align asymptotics.is_o.trans_is_O_with Asymptotics.Is𝓸.trans_is𝓞With

@[trans]
theorem Is𝓸.trans_is𝓞 {f : α → E} {g : α → F} {k : α → G'} (hfg : f =o[l] g) (hgk : g =O[l] k) :
    f =o[l] k :=
  let ⟨_c, cpos, hc⟩ := hgk.exists_pos
  hfg.trans_is𝓞With hc cpos
#align asymptotics.is_o.trans_is_O Asymptotics.Is𝓸.trans_is𝓞

instance : @Trans (α → E) (α → F) (α → G') (· =o[l] ·) (· =O[l] ·) (· =o[l] ·) where
  trans := Is𝓸.trans_is𝓞

theorem Is𝓞With.trans_is𝓸 (hfg : Is𝓞With c l f g) (hgk : g =o[l] k) (hc : 0 < c) : f =o[l] k :=
  by
  simp only [Is𝓸_def] at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact (hfg.trans (hgk this) hc.le).congr_const (mul_div_cancel' _ hc.ne')
#align asymptotics.is_O_with.trans_is_o Asymptotics.Is𝓞With.trans_is𝓸

@[trans]
theorem Is𝓞.trans_is𝓸 {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g) (hgk : g =o[l] k) :
    f =o[l] k :=
  let ⟨_c, cpos, hc⟩ := hfg.exists_pos
  hc.trans_is𝓸 hgk cpos
#align asymptotics.is_O.trans_is_o Asymptotics.Is𝓞.trans_is𝓸

instance : @Trans (α → E) (α → F') (α → G) (· =O[l] ·) (· =o[l] ·) (· =o[l] ·) where
  trans := Is𝓞.trans_is𝓸

@[trans]
theorem Is𝓸.trans {f : α → E} {g : α → F} {k : α → G} (hfg : f =o[l] g) (hgk : g =o[l] k) :
    f =o[l] k :=
  hfg.trans_is𝓞With hgk.is𝓞With one_pos
#align asymptotics.is_o.trans Asymptotics.Is𝓸.trans

instance : @Trans (α → E) (α → F) (α → G) (· =o[l] ·) (· =o[l] ·) (· =o[l] ·) where
  trans := Is𝓸.trans

theorem _root_.Filter.Eventually.trans_is𝓞 {f : α → E} {g : α → F'} {k : α → G}
    (hfg : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖) (hgk : g =O[l] k) : f =O[l] k :=
  (Is𝓞.of_bound' hfg).trans hgk
#align filter.eventually.trans_is_O Filter.Eventually.trans_is𝓞

theorem _root_.Filter.Eventually.is𝓞 {f : α → E} {g : α → ℝ} {l : Filter α}
    (hfg : ∀ᶠ x in l, ‖f x‖ ≤ g x) : f =O[l] g :=
  Is𝓞.of_bound' <| hfg.mono fun _x hx => hx.trans <| Real.le_norm_self _
#align filter.eventually.is_O Filter.Eventually.is𝓞

section

variable (l)

theorem is𝓞With_of_le' (hfg : ∀ x, ‖f x‖ ≤ c * ‖g x‖) : Is𝓞With c l f g :=
  Is𝓞With.of_bound <| univ_mem' hfg
#align asymptotics.is_O_with_of_le' Asymptotics.is𝓞With_of_le'

theorem is𝓞With_of_le (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) : Is𝓞With 1 l f g :=
  is𝓞With_of_le' l fun x => by
    rw [one_mul]
    exact hfg x
#align asymptotics.is_O_with_of_le Asymptotics.is𝓞With_of_le

theorem is𝓞_of_le' (hfg : ∀ x, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g :=
  (is𝓞With_of_le' l hfg).is𝓞
#align asymptotics.is_O_of_le' Asymptotics.is𝓞_of_le'

theorem is𝓞_of_le (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) : f =O[l] g :=
  (is𝓞With_of_le l hfg).is𝓞
#align asymptotics.is_O_of_le Asymptotics.is𝓞_of_le

end

theorem is𝓞With_refl (f : α → E) (l : Filter α) : Is𝓞With 1 l f f :=
  is𝓞With_of_le l fun _ => le_rfl
#align asymptotics.is_O_with_refl Asymptotics.is𝓞With_refl

theorem is𝓞_refl (f : α → E) (l : Filter α) : f =O[l] f :=
  (is𝓞With_refl f l).is𝓞
#align asymptotics.is_O_refl Asymptotics.is𝓞_refl

theorem Is𝓞With.trans_le (hfg : Is𝓞With c l f g) (hgk : ∀ x, ‖g x‖ ≤ ‖k x‖) (hc : 0 ≤ c) :
    Is𝓞With c l f k :=
  (hfg.trans (is𝓞With_of_le l hgk) hc).congr_const <| mul_one c
#align asymptotics.is_O_with.trans_le Asymptotics.Is𝓞With.trans_le

theorem Is𝓞.trans_le (hfg : f =O[l] g') (hgk : ∀ x, ‖g' x‖ ≤ ‖k x‖) : f =O[l] k :=
  hfg.trans (is𝓞_of_le l hgk)
#align asymptotics.is_O.trans_le Asymptotics.Is𝓞.trans_le

theorem Is𝓸.trans_le (hfg : f =o[l] g) (hgk : ∀ x, ‖g x‖ ≤ ‖k x‖) : f =o[l] k :=
  hfg.trans_is𝓞With (is𝓞With_of_le _ hgk) zero_lt_one
#align asymptotics.is_o.trans_le Asymptotics.Is𝓸.trans_le

theorem is𝓸_irrefl' (h : ∃ᶠ x in l, ‖f' x‖ ≠ 0) : ¬f' =o[l] f' := by
  intro ho
  rcases((ho.bound one_half_pos).and_frequently h).exists with ⟨x, hle, hne⟩
  rw [one_div, ← div_eq_inv_mul] at hle
  exact (half_lt_self (lt_of_le_of_ne (norm_nonneg _) hne.symm)).not_le hle
#align asymptotics.is_o_irrefl' Asymptotics.is𝓸_irrefl'

theorem is𝓸_irrefl (h : ∃ᶠ x in l, f'' x ≠ 0) : ¬f'' =o[l] f'' :=
  is𝓸_irrefl' <| h.mono fun _x => norm_ne_zero_iff.mpr
#align asymptotics.is_o_irrefl Asymptotics.is𝓸_irrefl

theorem Is𝓞.not_is𝓸 (h : f'' =O[l] g') (hf : ∃ᶠ x in l, f'' x ≠ 0) : ¬g' =o[l] f'' := fun h' =>
  is𝓸_irrefl hf (h.trans_is𝓸 h')
#align asymptotics.is_O.not_is_o Asymptotics.Is𝓞.not_is𝓸

theorem Is𝓸.not_is𝓞 (h : f'' =o[l] g') (hf : ∃ᶠ x in l, f'' x ≠ 0) : ¬g' =O[l] f'' := fun h' =>
  is𝓸_irrefl hf (h.trans_is𝓞 h')
#align asymptotics.is_o.not_is_O Asymptotics.Is𝓸.not_is𝓞

section Bot

variable (c f g)

@[simp]
theorem is𝓞With_bot : Is𝓞With c ⊥ f g :=
  Is𝓞With.of_bound <| trivial
#align asymptotics.is_O_with_bot Asymptotics.is𝓞With_bot

@[simp]
theorem is𝓞_bot : f =O[⊥] g :=
  (is𝓞With_bot 1 f g).is𝓞
#align asymptotics.is_O_bot Asymptotics.is𝓞_bot

@[simp]
theorem is𝓸_bot : f =o[⊥] g :=
  Is𝓸.of_is𝓞With fun c _ => is𝓞With_bot c f g
#align asymptotics.is_o_bot Asymptotics.is𝓸_bot

end Bot

@[simp]
theorem is𝓞With_pure {x} : Is𝓞With c (pure x) f g ↔ ‖f x‖ ≤ c * ‖g x‖ :=
  is𝓞With_iff
#align asymptotics.is_O_with_pure Asymptotics.is𝓞With_pure

theorem Is𝓞With.sup (h : Is𝓞With c l f g) (h' : Is𝓞With c l' f g) : Is𝓞With c (l ⊔ l') f g :=
  Is𝓞With.of_bound <| mem_sup.2 ⟨h.bound, h'.bound⟩
#align asymptotics.is_O_with.sup Asymptotics.Is𝓞With.sup

theorem Is𝓞With.sup' (h : Is𝓞With c l f g') (h' : Is𝓞With c' l' f g') :
    Is𝓞With (max c c') (l ⊔ l') f g' :=
  Is𝓞With.of_bound <|
    mem_sup.2 ⟨(h.weaken <| le_max_left c c').bound, (h'.weaken <| le_max_right c c').bound⟩
#align asymptotics.is_O_with.sup' Asymptotics.Is𝓞With.sup'

theorem Is𝓞.sup (h : f =O[l] g') (h' : f =O[l'] g') : f =O[l ⊔ l'] g' :=
  let ⟨_c, hc⟩ := h.is𝓞With
  let ⟨_c', hc'⟩ := h'.is𝓞With
  (hc.sup' hc').is𝓞
#align asymptotics.is_O.sup Asymptotics.Is𝓞.sup

theorem Is𝓸.sup (h : f =o[l] g) (h' : f =o[l'] g) : f =o[l ⊔ l'] g :=
  Is𝓸.of_is𝓞With fun _c cpos => (h.forall_is𝓞With cpos).sup (h'.forall_is𝓞With cpos)
#align asymptotics.is_o.sup Asymptotics.Is𝓸.sup

@[simp]
theorem is𝓞_sup : f =O[l ⊔ l'] g' ↔ f =O[l] g' ∧ f =O[l'] g' :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩
#align asymptotics.is_O_sup Asymptotics.is𝓞_sup

@[simp]
theorem is𝓸_sup : f =o[l ⊔ l'] g ↔ f =o[l] g ∧ f =o[l'] g :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩
#align asymptotics.is_o_sup Asymptotics.is𝓸_sup

theorem is𝓞With_insert [TopologicalSpace α] {x : α} {s : Set α} {C : ℝ} {g : α → E} {g' : α → F}
    (h : ‖g x‖ ≤ C * ‖g' x‖) : Is𝓞With C (𝓝[insert x s] x) g g' ↔ Is𝓞With C (𝓝[s] x) g g' := by
  simp_rw [Is𝓞With_def, nhdsWithin_insert, eventually_sup, eventually_pure, h, true_and_iff]
#align asymptotics.is_O_with_insert Asymptotics.is𝓞With_insert

theorem Is𝓞With.insert [TopologicalSpace α] {x : α} {s : Set α} {C : ℝ} {g : α → E} {g' : α → F}
    (h1 : Is𝓞With C (𝓝[s] x) g g') (h2 : ‖g x‖ ≤ C * ‖g' x‖) : Is𝓞With C (𝓝[insert x s] x) g g' :=
  (is𝓞With_insert h2).mpr h1
#align asymptotics.is_O_with.insert Asymptotics.Is𝓞With.insert

theorem is𝓸_insert [TopologicalSpace α] {x : α} {s : Set α} {g : α → E'} {g' : α → F'}
    (h : g x = 0) : g =o[𝓝[insert x s] x] g' ↔ g =o[𝓝[s] x] g' := by
  simp_rw [Is𝓸_def]
  refine' forall_congr' fun c => forall_congr' fun hc => _
  rw [is𝓞With_insert]
  rw [h, norm_zero]
  exact mul_nonneg hc.le (norm_nonneg _)
#align asymptotics.is_o_insert Asymptotics.is𝓸_insert

theorem Is𝓸.insert [TopologicalSpace α] {x : α} {s : Set α} {g : α → E'} {g' : α → F'}
    (h1 : g =o[𝓝[s] x] g') (h2 : g x = 0) : g =o[𝓝[insert x s] x] g' :=
  (is𝓸_insert h2).mpr h1
#align asymptotics.is_o.insert Asymptotics.Is𝓸.insert

/-! ### Simplification : norm, abs -/


section NormAbs

variable {u v : α → ℝ}

@[simp]
theorem is𝓞With_norm_right : (Is𝓞With c l f fun x => ‖g' x‖) ↔ Is𝓞With c l f g' := by
  simp only [Is𝓞With_def, norm_norm]
#align asymptotics.is_O_with_norm_right Asymptotics.is𝓞With_norm_right

@[simp]
theorem is𝓞With_abs_right : (Is𝓞With c l f fun x => |u x|) ↔ Is𝓞With c l f u :=
  @is𝓞With_norm_right _ _ _ _ _ _ f u l
#align asymptotics.is_O_with_abs_right Asymptotics.is𝓞With_abs_right

alias is𝓞With_norm_right ↔ Is𝓞With.of_norm_right Is𝓞With.norm_right
#align asymptotics.is_O_with.of_norm_right Asymptotics.Is𝓞With.of_norm_right
#align asymptotics.is_O_with.norm_right Asymptotics.Is𝓞With.norm_right

alias is𝓞With_abs_right ↔ Is𝓞With.of_abs_right Is𝓞With.abs_right
#align asymptotics.is_O_with.of_abs_right Asymptotics.Is𝓞With.of_abs_right
#align asymptotics.is_O_with.abs_right Asymptotics.Is𝓞With.abs_right

@[simp]
theorem is𝓞_norm_right : (f =O[l] fun x => ‖g' x‖) ↔ f =O[l] g' := by
  simp only [Is𝓞_def]
  exact exists_congr fun _ => is𝓞With_norm_right
#align asymptotics.is_O_norm_right Asymptotics.is𝓞_norm_right

@[simp]
theorem is𝓞_abs_right : (f =O[l] fun x => |u x|) ↔ f =O[l] u :=
  @is𝓞_norm_right _ _ ℝ _ _ _ _ _
#align asymptotics.is_O_abs_right Asymptotics.is𝓞_abs_right

alias is𝓞_norm_right ↔ Is𝓞.of_norm_right Is𝓞.norm_right
#align asymptotics.is_O.of_norm_right Asymptotics.Is𝓞.of_norm_right
#align asymptotics.is_O.norm_right Asymptotics.Is𝓞.norm_right

alias is𝓞_abs_right ↔ Is𝓞.of_abs_right Is𝓞.abs_right
#align asymptotics.is_O.of_abs_right Asymptotics.Is𝓞.of_abs_right
#align asymptotics.is_O.abs_right Asymptotics.Is𝓞.abs_right

@[simp]
theorem is𝓸_norm_right : (f =o[l] fun x => ‖g' x‖) ↔ f =o[l] g' := by
  simp only [Is𝓸_def]
  exact forall₂_congr fun _ _ => is𝓞With_norm_right
#align asymptotics.is_o_norm_right Asymptotics.is𝓸_norm_right

@[simp]
theorem is𝓸_abs_right : (f =o[l] fun x => |u x|) ↔ f =o[l] u :=
  @is𝓸_norm_right _ _ ℝ _ _ _ _ _
#align asymptotics.is_o_abs_right Asymptotics.is𝓸_abs_right

alias is𝓸_norm_right ↔ Is𝓸.of_norm_right Is𝓸.norm_right
#align asymptotics.is_o.of_norm_right Asymptotics.Is𝓸.of_norm_right
#align asymptotics.is_o.norm_right Asymptotics.Is𝓸.norm_right

alias is𝓸_abs_right ↔ Is𝓸.of_abs_right Is𝓸.abs_right
#align asymptotics.is_o.of_abs_right Asymptotics.Is𝓸.of_abs_right
#align asymptotics.is_o.abs_right Asymptotics.Is𝓸.abs_right

@[simp]
theorem is𝓞With_norm_left : Is𝓞With c l (fun x => ‖f' x‖) g ↔ Is𝓞With c l f' g := by
  simp only [Is𝓞With_def, norm_norm]
#align asymptotics.is_O_with_norm_left Asymptotics.is𝓞With_norm_left

@[simp]
theorem is𝓞With_abs_left : Is𝓞With c l (fun x => |u x|) g ↔ Is𝓞With c l u g :=
  @is𝓞With_norm_left _ _ _ _ _ _ g u l
#align asymptotics.is_O_with_abs_left Asymptotics.is𝓞With_abs_left

alias is𝓞With_norm_left ↔ Is𝓞With.of_norm_left Is𝓞With.norm_left
#align asymptotics.is_O_with.of_norm_left Asymptotics.Is𝓞With.of_norm_left
#align asymptotics.is_O_with.norm_left Asymptotics.Is𝓞With.norm_left

alias is𝓞With_abs_left ↔ Is𝓞With.of_abs_left Is𝓞With.abs_left
#align asymptotics.is_O_with.of_abs_left Asymptotics.Is𝓞With.of_abs_left
#align asymptotics.is_O_with.abs_left Asymptotics.Is𝓞With.abs_left

@[simp]
theorem is𝓞_norm_left : (fun x => ‖f' x‖) =O[l] g ↔ f' =O[l] g := by
  simp only [Is𝓞_def]
  exact exists_congr fun _ => is𝓞With_norm_left
#align asymptotics.is_O_norm_left Asymptotics.is𝓞_norm_left

@[simp]
theorem is𝓞_abs_left : (fun x => |u x|) =O[l] g ↔ u =O[l] g :=
  @is𝓞_norm_left _ _ _ _ _ g u l
#align asymptotics.is_O_abs_left Asymptotics.is𝓞_abs_left

alias is𝓞_norm_left ↔ Is𝓞.of_norm_left Is𝓞.norm_left
#align asymptotics.is_O.of_norm_left Asymptotics.Is𝓞.of_norm_left
#align asymptotics.is_O.norm_left Asymptotics.Is𝓞.norm_left

alias is𝓞_abs_left ↔ Is𝓞.of_abs_left Is𝓞.abs_left
#align asymptotics.is_O.of_abs_left Asymptotics.Is𝓞.of_abs_left
#align asymptotics.is_O.abs_left Asymptotics.Is𝓞.abs_left

@[simp]
theorem is𝓸_norm_left : (fun x => ‖f' x‖) =o[l] g ↔ f' =o[l] g := by
  simp only [Is𝓸_def]
  exact forall₂_congr fun _ _ => is𝓞With_norm_left
#align asymptotics.is_o_norm_left Asymptotics.is𝓸_norm_left

@[simp]
theorem is𝓸_abs_left : (fun x => |u x|) =o[l] g ↔ u =o[l] g :=
  @is𝓸_norm_left _ _ _ _ _ g u l
#align asymptotics.is_o_abs_left Asymptotics.is𝓸_abs_left

alias is𝓸_norm_left ↔ Is𝓸.of_norm_left Is𝓸.norm_left
#align asymptotics.is_o.of_norm_left Asymptotics.Is𝓸.of_norm_left
#align asymptotics.is_o.norm_left Asymptotics.Is𝓸.norm_left

alias is𝓸_abs_left ↔ Is𝓸.of_abs_left Is𝓸.abs_left
#align asymptotics.is_o.of_abs_left Asymptotics.Is𝓸.of_abs_left
#align asymptotics.is_o.abs_left Asymptotics.Is𝓸.abs_left

theorem is𝓞With_norm_norm : (Is𝓞With c l (fun x => ‖f' x‖) fun x => ‖g' x‖) ↔ Is𝓞With c l f' g' :=
  is𝓞With_norm_left.trans is𝓞With_norm_right
#align asymptotics.is_O_with_norm_norm Asymptotics.is𝓞With_norm_norm

theorem is𝓞With_abs_abs : (Is𝓞With c l (fun x => |u x|) fun x => |v x|) ↔ Is𝓞With c l u v :=
  is𝓞With_abs_left.trans is𝓞With_abs_right
#align asymptotics.is_O_with_abs_abs Asymptotics.is𝓞With_abs_abs

alias is𝓞With_norm_norm ↔ Is𝓞With.of_norm_norm Is𝓞With.norm_norm
#align asymptotics.is_O_with.of_norm_norm Asymptotics.Is𝓞With.of_norm_norm
#align asymptotics.is_O_with.norm_norm Asymptotics.Is𝓞With.norm_norm

alias is𝓞With_abs_abs ↔ Is𝓞With.of_abs_abs Is𝓞With.abs_abs
#align asymptotics.is_O_with.of_abs_abs Asymptotics.Is𝓞With.of_abs_abs
#align asymptotics.is_O_with.abs_abs Asymptotics.Is𝓞With.abs_abs

theorem is𝓞_norm_norm : ((fun x => ‖f' x‖) =O[l] fun x => ‖g' x‖) ↔ f' =O[l] g' :=
  is𝓞_norm_left.trans is𝓞_norm_right
#align asymptotics.is_O_norm_norm Asymptotics.is𝓞_norm_norm

theorem is𝓞_abs_abs : ((fun x => |u x|) =O[l] fun x => |v x|) ↔ u =O[l] v :=
  is𝓞_abs_left.trans is𝓞_abs_right
#align asymptotics.is_O_abs_abs Asymptotics.is𝓞_abs_abs

alias is𝓞_norm_norm ↔ Is𝓞.of_norm_norm Is𝓞.norm_norm
#align asymptotics.is_O.of_norm_norm Asymptotics.Is𝓞.of_norm_norm
#align asymptotics.is_O.norm_norm Asymptotics.Is𝓞.norm_norm

alias is𝓞_abs_abs ↔ Is𝓞.of_abs_abs Is𝓞.abs_abs
#align asymptotics.is_O.of_abs_abs Asymptotics.Is𝓞.of_abs_abs
#align asymptotics.is_O.abs_abs Asymptotics.Is𝓞.abs_abs

theorem is𝓸_norm_norm : ((fun x => ‖f' x‖) =o[l] fun x => ‖g' x‖) ↔ f' =o[l] g' :=
  is𝓸_norm_left.trans is𝓸_norm_right
#align asymptotics.is_o_norm_norm Asymptotics.is𝓸_norm_norm

theorem is𝓸_abs_abs : ((fun x => |u x|) =o[l] fun x => |v x|) ↔ u =o[l] v :=
  is𝓸_abs_left.trans is𝓸_abs_right
#align asymptotics.is_o_abs_abs Asymptotics.is𝓸_abs_abs

alias is𝓸_norm_norm ↔ Is𝓸.of_norm_norm Is𝓸.norm_norm
#align asymptotics.is_o.of_norm_norm Asymptotics.Is𝓸.of_norm_norm
#align asymptotics.is_o.norm_norm Asymptotics.Is𝓸.norm_norm

alias is𝓸_abs_abs ↔ Is𝓸.of_abs_abs Is𝓸.abs_abs
#align asymptotics.is_o.of_abs_abs Asymptotics.Is𝓸.of_abs_abs
#align asymptotics.is_o.abs_abs Asymptotics.Is𝓸.abs_abs

end NormAbs

/-! ### Simplification: negate -/


@[simp]
theorem is𝓞With_neg_right : (Is𝓞With c l f fun x => -g' x) ↔ Is𝓞With c l f g' := by
  simp only [Is𝓞With_def, norm_neg]
#align asymptotics.is_O_with_neg_right Asymptotics.is𝓞With_neg_right

alias is𝓞With_neg_right ↔ Is𝓞With.of_neg_right Is𝓞With.neg_right
#align asymptotics.is_O_with.of_neg_right Asymptotics.Is𝓞With.of_neg_right
#align asymptotics.is_O_with.neg_right Asymptotics.Is𝓞With.neg_right

@[simp]
theorem is𝓞_neg_right : (f =O[l] fun x => -g' x) ↔ f =O[l] g' := by
  simp only [Is𝓞_def]
  exact exists_congr fun _ => is𝓞With_neg_right
#align asymptotics.is_O_neg_right Asymptotics.is𝓞_neg_right

alias is𝓞_neg_right ↔ Is𝓞.of_neg_right Is𝓞.neg_right
#align asymptotics.is_O.of_neg_right Asymptotics.Is𝓞.of_neg_right
#align asymptotics.is_O.neg_right Asymptotics.Is𝓞.neg_right

@[simp]
theorem is𝓸_neg_right : (f =o[l] fun x => -g' x) ↔ f =o[l] g' := by
  simp only [Is𝓸_def]
  exact forall₂_congr fun _ _ => is𝓞With_neg_right
#align asymptotics.is_o_neg_right Asymptotics.is𝓸_neg_right

alias is𝓸_neg_right ↔ Is𝓸.of_neg_right Is𝓸.neg_right
#align asymptotics.is_o.of_neg_right Asymptotics.Is𝓸.of_neg_right
#align asymptotics.is_o.neg_right Asymptotics.Is𝓸.neg_right

@[simp]
theorem is𝓞With_neg_left : Is𝓞With c l (fun x => -f' x) g ↔ Is𝓞With c l f' g := by
  simp only [Is𝓞With_def, norm_neg]
#align asymptotics.is_O_with_neg_left Asymptotics.is𝓞With_neg_left

alias is𝓞With_neg_left ↔ Is𝓞With.of_neg_left Is𝓞With.neg_left
#align asymptotics.is_O_with.of_neg_left Asymptotics.Is𝓞With.of_neg_left
#align asymptotics.is_O_with.neg_left Asymptotics.Is𝓞With.neg_left

@[simp]
theorem is𝓞_neg_left : (fun x => -f' x) =O[l] g ↔ f' =O[l] g := by
  simp only [Is𝓞_def]
  exact exists_congr fun _ => is𝓞With_neg_left
#align asymptotics.is_O_neg_left Asymptotics.is𝓞_neg_left

alias is𝓞_neg_left ↔ Is𝓞.of_neg_left Is𝓞.neg_left
#align asymptotics.is_O.of_neg_left Asymptotics.Is𝓞.of_neg_left
#align asymptotics.is_O.neg_left Asymptotics.Is𝓞.neg_left

@[simp]
theorem is𝓸_neg_left : (fun x => -f' x) =o[l] g ↔ f' =o[l] g := by
  simp only [Is𝓸_def]
  exact forall₂_congr fun _ _ => is𝓞With_neg_left
#align asymptotics.is_o_neg_left Asymptotics.is𝓸_neg_left

alias is𝓸_neg_left ↔ Is𝓸.of_neg_left Is𝓸.neg_left
#align asymptotics.is_o.of_neg_left Asymptotics.Is𝓸.of_neg_left
#align asymptotics.is_o.neg_left Asymptotics.Is𝓸.neg_left

/-! ### Product of functions (right) -/


theorem is𝓞With_fst_prod : Is𝓞With 1 l f' fun x => (f' x, g' x) :=
  is𝓞With_of_le l fun _x => le_max_left _ _
#align asymptotics.is_O_with_fst_prod Asymptotics.is𝓞With_fst_prod

theorem is𝓞With_snd_prod : Is𝓞With 1 l g' fun x => (f' x, g' x) :=
  is𝓞With_of_le l fun _x => le_max_right _ _
#align asymptotics.is_O_with_snd_prod Asymptotics.is𝓞With_snd_prod

theorem is𝓞_fst_prod : f' =O[l] fun x => (f' x, g' x) :=
  is𝓞With_fst_prod.is𝓞
#align asymptotics.is_O_fst_prod Asymptotics.is𝓞_fst_prod

theorem is𝓞_snd_prod : g' =O[l] fun x => (f' x, g' x) :=
  is𝓞With_snd_prod.is𝓞
#align asymptotics.is_O_snd_prod Asymptotics.is𝓞_snd_prod

theorem is𝓞_fst_prod' {f' : α → E' × F'} : (fun x => (f' x).1) =O[l] f' := by
  simpa [Is𝓞_def, Is𝓞With_def] using is𝓞_fst_prod (E' := E') (F' := F')
#align asymptotics.is_O_fst_prod' Asymptotics.is𝓞_fst_prod'

theorem is𝓞_snd_prod' {f' : α → E' × F'} : (fun x => (f' x).2) =O[l] f' := by
  simpa [Is𝓞_def, Is𝓞With_def] using is𝓞_snd_prod (E' := E') (F' := F')
#align asymptotics.is_O_snd_prod' Asymptotics.is𝓞_snd_prod'

section

variable (f' k')

theorem Is𝓞With.prod_rightl (h : Is𝓞With c l f g') (hc : 0 ≤ c) :
    Is𝓞With c l f fun x => (g' x, k' x) :=
  (h.trans is𝓞With_fst_prod hc).congr_const (mul_one c)
#align asymptotics.is_O_with.prod_rightl Asymptotics.Is𝓞With.prod_rightl

theorem Is𝓞.prod_rightl (h : f =O[l] g') : f =O[l] fun x => (g' x, k' x) :=
  let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightl k' cnonneg).is𝓞
#align asymptotics.is_O.prod_rightl Asymptotics.Is𝓞.prod_rightl

theorem Is𝓸.prod_rightl (h : f =o[l] g') : f =o[l] fun x => (g' x, k' x) :=
  Is𝓸.of_is𝓞With fun _c cpos => (h.forall_is𝓞With cpos).prod_rightl k' cpos.le
#align asymptotics.is_o.prod_rightl Asymptotics.Is𝓸.prod_rightl

theorem Is𝓞With.prod_rightr (h : Is𝓞With c l f g') (hc : 0 ≤ c) :
    Is𝓞With c l f fun x => (f' x, g' x) :=
  (h.trans is𝓞With_snd_prod hc).congr_const (mul_one c)
#align asymptotics.is_O_with.prod_rightr Asymptotics.Is𝓞With.prod_rightr

theorem Is𝓞.prod_rightr (h : f =O[l] g') : f =O[l] fun x => (f' x, g' x) :=
  let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightr f' cnonneg).is𝓞
#align asymptotics.is_O.prod_rightr Asymptotics.Is𝓞.prod_rightr

theorem Is𝓸.prod_rightr (h : f =o[l] g') : f =o[l] fun x => (f' x, g' x) :=
  Is𝓸.of_is𝓞With fun _c cpos => (h.forall_is𝓞With cpos).prod_rightr f' cpos.le
#align asymptotics.is_o.prod_rightr Asymptotics.Is𝓸.prod_rightr

end

theorem Is𝓞With.prod_left_same (hf : Is𝓞With c l f' k') (hg : Is𝓞With c l g' k') :
    Is𝓞With c l (fun x => (f' x, g' x)) k' := by
  rw [is𝓞With_iff] at *; filter_upwards [hf, hg]with x using max_le
#align asymptotics.is_O_with.prod_left_same Asymptotics.Is𝓞With.prod_left_same

theorem Is𝓞With.prod_left (hf : Is𝓞With c l f' k') (hg : Is𝓞With c' l g' k') :
    Is𝓞With (max c c') l (fun x => (f' x, g' x)) k' :=
  (hf.weaken <| le_max_left c c').prod_left_same (hg.weaken <| le_max_right c c')
#align asymptotics.is_O_with.prod_left Asymptotics.Is𝓞With.prod_left

theorem Is𝓞With.prod_left_fst (h : Is𝓞With c l (fun x => (f' x, g' x)) k') : Is𝓞With c l f' k' :=
  (is𝓞With_fst_prod.trans h zero_le_one).congr_const <| one_mul c
#align asymptotics.is_O_with.prod_left_fst Asymptotics.Is𝓞With.prod_left_fst

theorem Is𝓞With.prod_left_snd (h : Is𝓞With c l (fun x => (f' x, g' x)) k') : Is𝓞With c l g' k' :=
  (is𝓞With_snd_prod.trans h zero_le_one).congr_const <| one_mul c
#align asymptotics.is_O_with.prod_left_snd Asymptotics.Is𝓞With.prod_left_snd

theorem is𝓞With_prod_left :
    Is𝓞With c l (fun x => (f' x, g' x)) k' ↔ Is𝓞With c l f' k' ∧ Is𝓞With c l g' k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left_same h.2⟩
#align asymptotics.is_O_with_prod_left Asymptotics.is𝓞With_prod_left

theorem Is𝓞.prod_left (hf : f' =O[l] k') (hg : g' =O[l] k') : (fun x => (f' x, g' x)) =O[l] k' :=
  let ⟨_c, hf⟩ := hf.is𝓞With
  let ⟨_c', hg⟩ := hg.is𝓞With
  (hf.prod_left hg).is𝓞
#align asymptotics.is_O.prod_left Asymptotics.Is𝓞.prod_left

theorem Is𝓞.prod_left_fst : (fun x => (f' x, g' x)) =O[l] k' → f' =O[l] k' :=
  Is𝓞.trans is𝓞_fst_prod
#align asymptotics.is_O.prod_left_fst Asymptotics.Is𝓞.prod_left_fst

theorem Is𝓞.prod_left_snd : (fun x => (f' x, g' x)) =O[l] k' → g' =O[l] k' :=
  Is𝓞.trans is𝓞_snd_prod
#align asymptotics.is_O.prod_left_snd Asymptotics.Is𝓞.prod_left_snd

@[simp]
theorem is𝓞_prod_left : (fun x => (f' x, g' x)) =O[l] k' ↔ f' =O[l] k' ∧ g' =O[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left h.2⟩
#align asymptotics.is_O_prod_left Asymptotics.is𝓞_prod_left

theorem Is𝓸.prod_left (hf : f' =o[l] k') (hg : g' =o[l] k') : (fun x => (f' x, g' x)) =o[l] k' :=
  Is𝓸.of_is𝓞With fun _c hc => (hf.forall_is𝓞With hc).prod_left_same (hg.forall_is𝓞With hc)
#align asymptotics.is_o.prod_left Asymptotics.Is𝓸.prod_left

theorem Is𝓸.prod_left_fst : (fun x => (f' x, g' x)) =o[l] k' → f' =o[l] k' :=
  Is𝓞.trans_is𝓸 is𝓞_fst_prod
#align asymptotics.is_o.prod_left_fst Asymptotics.Is𝓸.prod_left_fst

theorem Is𝓸.prod_left_snd : (fun x => (f' x, g' x)) =o[l] k' → g' =o[l] k' :=
  Is𝓞.trans_is𝓸 is𝓞_snd_prod
#align asymptotics.is_o.prod_left_snd Asymptotics.Is𝓸.prod_left_snd

@[simp]
theorem is𝓸_prod_left : (fun x => (f' x, g' x)) =o[l] k' ↔ f' =o[l] k' ∧ g' =o[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left h.2⟩
#align asymptotics.is_o_prod_left Asymptotics.is𝓸_prod_left

theorem Is𝓞With.eq_zero_imp (h : Is𝓞With c l f'' g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  Eventually.mono h.bound fun x hx hg => norm_le_zero_iff.1 <| by simpa [hg] using hx
#align asymptotics.is_O_with.eq_zero_imp Asymptotics.Is𝓞With.eq_zero_imp

theorem Is𝓞.eq_zero_imp (h : f'' =O[l] g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  let ⟨_C, hC⟩ := h.is𝓞With
  hC.eq_zero_imp
#align asymptotics.is_O.eq_zero_imp Asymptotics.Is𝓞.eq_zero_imp

/-! ### Addition and subtraction -/


section add_sub

variable {f₁ f₂ : α → E'} {g₁ g₂ : α → F'}

theorem Is𝓞With.add (h₁ : Is𝓞With c₁ l f₁ g) (h₂ : Is𝓞With c₂ l f₂ g) :
    Is𝓞With (c₁ + c₂) l (fun x => f₁ x + f₂ x) g := by
  rw [Is𝓞With_def] at *;
    filter_upwards [h₁,
      h₂]with x hx₁ hx₂ using calc
        ‖f₁ x + f₂ x‖ ≤ c₁ * ‖g x‖ + c₂ * ‖g x‖ := norm_add_le_of_le hx₁ hx₂
        _ = (c₁ + c₂) * ‖g x‖ := (add_mul _ _ _).symm

#align asymptotics.is_O_with.add Asymptotics.Is𝓞With.add

theorem Is𝓞.add (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  let ⟨_c₁, hc₁⟩ := h₁.is𝓞With
  let ⟨_c₂, hc₂⟩ := h₂.is𝓞With
  (hc₁.add hc₂).is𝓞
#align asymptotics.is_O.add Asymptotics.Is𝓞.add

theorem Is𝓸.add (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g :=
  Is𝓸.of_is𝓞With fun c cpos =>
    ((h₁.forall_is𝓞With <| half_pos cpos).add (h₂.forall_is𝓞With <| half_pos cpos)).congr_const
      (add_halves c)
#align asymptotics.is_o.add Asymptotics.Is𝓸.add

theorem Is𝓸.add_add (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x + f₂ x) =o[l] fun x => ‖g₁ x‖ + ‖g₂ x‖ := by
  refine' (h₁.trans_le fun x => _).add (h₂.trans_le _) <;> simp [abs_of_nonneg, add_nonneg]
#align asymptotics.is_o.add_add Asymptotics.Is𝓸.add_add

theorem Is𝓞.add_is𝓸 (h₁ : f₁ =O[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.add h₂.is𝓞
#align asymptotics.is_O.add_is_o Asymptotics.Is𝓞.add_is𝓸

theorem Is𝓸.add_is𝓞 (h₁ : f₁ =o[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.is𝓞.add h₂
#align asymptotics.is_o.add_is_O Asymptotics.Is𝓸.add_is𝓞

theorem Is𝓞With.add_is𝓸 (h₁ : Is𝓞With c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    Is𝓞With c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₁.add (h₂.forall_is𝓞With (sub_pos.2 hc))).congr_const (add_sub_cancel'_right _ _)
#align asymptotics.is_O_with.add_is_o Asymptotics.Is𝓞With.add_is𝓸

theorem Is𝓸.add_is𝓞With (h₁ : f₁ =o[l] g) (h₂ : Is𝓞With c₁ l f₂ g) (hc : c₁ < c₂) :
    Is𝓞With c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₂.add_is𝓸 h₁ hc).congr_left fun _ => add_comm _ _
#align asymptotics.is_o.add_is_O_with Asymptotics.Is𝓸.add_is𝓞With

theorem Is𝓞With.sub (h₁ : Is𝓞With c₁ l f₁ g) (h₂ : Is𝓞With c₂ l f₂ g) :
    Is𝓞With (c₁ + c₂) l (fun x => f₁ x - f₂ x) g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left
#align asymptotics.is_O_with.sub Asymptotics.Is𝓞With.sub

theorem Is𝓞With.sub_is𝓸 (h₁ : Is𝓞With c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    Is𝓞With c₂ l (fun x => f₁ x - f₂ x) g := by
  simpa only [sub_eq_add_neg] using h₁.add_is𝓸 h₂.neg_left hc
#align asymptotics.is_O_with.sub_is_o Asymptotics.Is𝓞With.sub_is𝓸

theorem Is𝓞.sub (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left
#align asymptotics.is_O.sub Asymptotics.Is𝓞.sub

theorem Is𝓸.sub (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left
#align asymptotics.is_o.sub Asymptotics.Is𝓸.sub

end add_sub

/-! ### Lemmas about `is_O (f₁ - f₂) g l` / `is_o (f₁ - f₂) g l` treated as a binary relation -/


section Is𝓞OAsRel

variable {f₁ f₂ f₃ : α → E'}

theorem Is𝓞With.symm (h : Is𝓞With c l (fun x => f₁ x - f₂ x) g) :
    Is𝓞With c l (fun x => f₂ x - f₁ x) g :=
  h.neg_left.congr_left fun _x => neg_sub _ _
#align asymptotics.is_O_with.symm Asymptotics.Is𝓞With.symm

theorem is𝓞With_comm :
    Is𝓞With c l (fun x => f₁ x - f₂ x) g ↔ Is𝓞With c l (fun x => f₂ x - f₁ x) g :=
  ⟨Is𝓞With.symm, Is𝓞With.symm⟩
#align asymptotics.is_O_with_comm Asymptotics.is𝓞With_comm

theorem Is𝓞.symm (h : (fun x => f₁ x - f₂ x) =O[l] g) : (fun x => f₂ x - f₁ x) =O[l] g :=
  h.neg_left.congr_left fun _x => neg_sub _ _
#align asymptotics.is_O.symm Asymptotics.Is𝓞.symm

theorem is𝓞_comm : (fun x => f₁ x - f₂ x) =O[l] g ↔ (fun x => f₂ x - f₁ x) =O[l] g :=
  ⟨Is𝓞.symm, Is𝓞.symm⟩
#align asymptotics.is_O_comm Asymptotics.is𝓞_comm

theorem Is𝓸.symm (h : (fun x => f₁ x - f₂ x) =o[l] g) : (fun x => f₂ x - f₁ x) =o[l] g := by
  simpa only [neg_sub] using h.neg_left
#align asymptotics.is_o.symm Asymptotics.Is𝓸.symm

theorem is𝓸_comm : (fun x => f₁ x - f₂ x) =o[l] g ↔ (fun x => f₂ x - f₁ x) =o[l] g :=
  ⟨Is𝓸.symm, Is𝓸.symm⟩
#align asymptotics.is_o_comm Asymptotics.is𝓸_comm

theorem Is𝓞With.triangle (h₁ : Is𝓞With c l (fun x => f₁ x - f₂ x) g)
    (h₂ : Is𝓞With c' l (fun x => f₂ x - f₃ x) g) : Is𝓞With (c + c') l (fun x => f₁ x - f₃ x) g :=
  (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _
#align asymptotics.is_O_with.triangle Asymptotics.Is𝓞With.triangle

theorem Is𝓞.triangle (h₁ : (fun x => f₁ x - f₂ x) =O[l] g) (h₂ : (fun x => f₂ x - f₃ x) =O[l] g) :
    (fun x => f₁ x - f₃ x) =O[l] g :=
  (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _
#align asymptotics.is_O.triangle Asymptotics.Is𝓞.triangle

theorem Is𝓸.triangle (h₁ : (fun x => f₁ x - f₂ x) =o[l] g)
    (h₂ : (fun x => f₂ x - f₃ x) =o[l] g) : (fun x => f₁ x - f₃ x) =o[l] g :=
  (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _
#align asymptotics.is_o.triangle Asymptotics.Is𝓸.triangle

theorem Is𝓞.congr_of_sub (h : (fun x => f₁ x - f₂ x) =O[l] g) : f₁ =O[l] g ↔ f₂ =O[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun _x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun _x => sub_add_cancel _ _⟩
#align asymptotics.is_O.congr_of_sub Asymptotics.Is𝓞.congr_of_sub

theorem Is𝓸.congr_of_sub (h : (fun x => f₁ x - f₂ x) =o[l] g) : f₁ =o[l] g ↔ f₂ =o[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun _x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun _x => sub_add_cancel _ _⟩
#align asymptotics.is_o.congr_of_sub Asymptotics.Is𝓸.congr_of_sub

end Is𝓞OAsRel

/-! ### Zero, one, and other constants -/


section ZeroConst

variable (g g' l)

theorem is𝓸_zero : (fun _x => (0 : E')) =o[l] g' :=
  Is𝓸.of_bound fun c hc =>
    univ_mem' fun x => by simpa using mul_nonneg hc.le (norm_nonneg <| g' x)
#align asymptotics.is_o_zero Asymptotics.is𝓸_zero

theorem is𝓞With_zero (hc : 0 ≤ c) : Is𝓞With c l (fun _x => (0 : E')) g' :=
  Is𝓞With.of_bound <| univ_mem' fun x => by simpa using mul_nonneg hc (norm_nonneg <| g' x)
#align asymptotics.is_O_with_zero Asymptotics.is𝓞With_zero

theorem is𝓞With_zero' : Is𝓞With 0 l (fun _x => (0 : E')) g :=
  Is𝓞With.of_bound <| univ_mem' fun x => by simp
#align asymptotics.is_O_with_zero' Asymptotics.is𝓞With_zero'

theorem is𝓞_zero : (fun _x => (0 : E')) =O[l] g :=
  is𝓞_iff_is𝓞With.2 ⟨0, is𝓞With_zero' _ _⟩
#align asymptotics.is_O_zero Asymptotics.is𝓞_zero

theorem is𝓞_refl_left : (fun x => f' x - f' x) =O[l] g' :=
  (is𝓞_zero g' l).congr_left fun _x => (sub_self _).symm
#align asymptotics.is_O_refl_left Asymptotics.is𝓞_refl_left

theorem is𝓸_refl_left : (fun x => f' x - f' x) =o[l] g' :=
  (is𝓸_zero g' l).congr_left fun _x => (sub_self _).symm
#align asymptotics.is_o_refl_left Asymptotics.is𝓸_refl_left

variable {g g' l}

@[simp]
theorem is𝓞With_zero_right_iff : (Is𝓞With c l f'' fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0 := by
  simp only [Is𝓞With_def, exists_prop, true_and_iff, norm_zero, MulZeroClass.mul_zero,
    norm_le_zero_iff, EventuallyEq, Pi.zero_apply]
#align asymptotics.is_O_with_zero_right_iff Asymptotics.is𝓞With_zero_right_iff

@[simp]
theorem is𝓞_zero_right_iff : (f'' =O[l] fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h =>
    let ⟨_c, hc⟩ := h.is𝓞With
    is𝓞With_zero_right_iff.1 hc,
    fun h => (is𝓞With_zero_right_iff.2 h : Is𝓞With 1 _ _ _).is𝓞⟩
#align asymptotics.is_O_zero_right_iff Asymptotics.is𝓞_zero_right_iff

@[simp]
theorem is𝓸_zero_right_iff : (f'' =o[l] fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h => is𝓞_zero_right_iff.1 h.is𝓞, fun h =>
    Is𝓸.of_is𝓞With fun _c _hc => is𝓞With_zero_right_iff.2 h⟩
#align asymptotics.is_o_zero_right_iff Asymptotics.is𝓸_zero_right_iff

theorem is𝓞With_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) :
    Is𝓞With (‖c‖ / ‖c'‖) l (fun _x : α => c) fun _x => c' := by
  simp only [Is𝓞With_def]
  apply univ_mem'
  intro x
  simp only [mem_setOf_eq]
  rw [div_mul_cancel]
  rwa [Ne.def, norm_eq_zero]
#align asymptotics.is_O_with_const_const Asymptotics.is𝓞With_const_const

theorem is𝓞_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) :
    (fun _x : α => c) =O[l] fun _x => c' :=
  (is𝓞With_const_const c hc' l).is𝓞
#align asymptotics.is_O_const_const Asymptotics.is𝓞_const_const

@[simp]
theorem is𝓞_const_const_iff {c : E''} {c' : F''} (l : Filter α) [l.NeBot] :
    ((fun _x : α => c) =O[l] fun _x => c') ↔ c' = 0 → c = 0 := by
  rcases eq_or_ne c' 0 with (rfl | hc')
  · simp [EventuallyEq]
  · simp [hc', is𝓞_const_const _ hc']
#align asymptotics.is_O_const_const_iff Asymptotics.is𝓞_const_const_iff

@[simp]
theorem is𝓞_pure {x} : f'' =O[pure x] g'' ↔ g'' x = 0 → f'' x = 0 :=
  calc
    f'' =O[pure x] g'' ↔ (fun _y : α => f'' x) =O[pure x] fun _ => g'' x := is𝓞_congr rfl rfl
    _ ↔ g'' x = 0 → f'' x = 0 := is𝓞_const_const_iff _

#align asymptotics.is_O_pure Asymptotics.is𝓞_pure

end ZeroConst

@[simp]
theorem is𝓞With_top : Is𝓞With c ⊤ f g ↔ ∀ x, ‖f x‖ ≤ c * ‖g x‖ := by rw [Is𝓞With_def]; rfl
#align asymptotics.is_O_with_top Asymptotics.is𝓞With_top

@[simp]
theorem is𝓞_top : f =O[⊤] g ↔ ∃ C, ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by rw [is𝓞_iff]; rfl
#align asymptotics.is_O_top Asymptotics.is𝓞_top

@[simp]
theorem is𝓸_top : f'' =o[⊤] g'' ↔ ∀ x, f'' x = 0 := by
  refine' ⟨_, fun h => (is𝓸_zero g'' ⊤).congr (fun x => (h x).symm) fun x => rfl⟩
  simp only [is𝓸_iff, eventually_top]
  refine' fun h x => norm_le_zero_iff.1 _
  have : Tendsto (fun c : ℝ => c * ‖g'' x‖) (𝓝[>] 0) (𝓝 0) :=
    ((continuous_id.mul continuous_const).tendsto' _ _ (MulZeroClass.zero_mul _)).mono_left
      inf_le_left
  exact
    le_of_tendsto_of_tendsto tendsto_const_nhds this
      (eventually_nhdsWithin_iff.2 <| eventually_of_forall fun c hc => h hc x)
#align asymptotics.is_o_top Asymptotics.is𝓸_top

@[simp]
theorem is𝓞With_principal {s : Set α} : Is𝓞With c (𝓟 s) f g ↔ ∀ x ∈ s, ‖f x‖ ≤ c * ‖g x‖ := by
  rw [Is𝓞With_def]; rfl
#align asymptotics.is_O_with_principal Asymptotics.is𝓞With_principal

theorem is𝓞_principal {s : Set α} : f =O[𝓟 s] g ↔ ∃ c, ∀ x ∈ s, ‖f x‖ ≤ c * ‖g x‖ := by
  rw [is𝓞_iff]; rfl
#align asymptotics.is_O_principal Asymptotics.is𝓞_principal

section

variable (F)
variable [One F] [NormOneClass F]

theorem is𝓞With_const_one (c : E) (l : Filter α) :
    Is𝓞With ‖c‖ l (fun _x : α => c) fun _x => (1 : F) := by simp [is𝓞With_iff]
#align asymptotics.is_O_with_const_one Asymptotics.is𝓞With_const_one

theorem is𝓞_const_one (c : E) (l : Filter α) : (fun _x : α => c) =O[l] fun _x => (1 : F) :=
  (is𝓞With_const_one F c l).is𝓞
#align asymptotics.is_O_const_one Asymptotics.is𝓞_const_one

theorem is𝓸_const_iff_is𝓸_one {c : F''} (hc : c ≠ 0) :
    (f =o[l] fun _x => c) ↔ f =o[l] fun _x => (1 : F) :=
  ⟨fun h => h.trans_is𝓞With (is𝓞With_const_one _ _ _) (norm_pos_iff.2 hc), fun h =>
    h.trans_is𝓞 <| is𝓞_const_const _ hc _⟩
#align asymptotics.is_o_const_iff_is_o_one Asymptotics.is𝓸_const_iff_is𝓸_one

@[simp]
theorem is𝓸_one_iff : f' =o[l] (fun _x => 1 : α → F) ↔ Tendsto f' l (𝓝 0) := by
  simp only [is𝓸_iff, norm_one, mul_one, Metric.nhds_basis_closedBall.tendsto_right_iff,
    Metric.mem_closedBall, dist_zero_right]
#align asymptotics.is_o_one_iff Asymptotics.is𝓸_one_iff

@[simp]
theorem is𝓞_one_iff : f =O[l] (fun _x => 1 : α → F) ↔ IsBoundedUnder (· ≤ ·) l fun x => ‖f x‖ := by
  simp only [is𝓞_iff, norm_one, mul_one]
  rfl
#align asymptotics.is_O_one_iff Asymptotics.is𝓞_one_iff

alias is𝓞_one_iff ↔ _ _root_.Filter.IsBoundedUnder.is𝓞_one
#align filter.is_bounded_under.is_O_one Filter.IsBoundedUnder.is𝓞_one

@[simp]
theorem is𝓸_one_left_iff : (fun _x => 1 : α → F) =o[l] f ↔ Tendsto (fun x => ‖f x‖) l atTop :=
  calc
    (fun _x => 1 : α → F) =o[l] f ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖(1 : F)‖ ≤ ‖f x‖ :=
      is𝓸_iff_nat_mul_le_aux <| Or.inl fun _x => by simp only [norm_one, zero_le_one]
    _ ↔ ∀ n : ℕ, True → ∀ᶠ x in l, ‖f x‖ ∈ Ici (n : ℝ) := by
      simp only [norm_one, mul_one, true_imp_iff, mem_Ici]
    _ ↔ Tendsto (fun x => ‖f x‖) l atTop :=
      atTop_hasCountableBasis_of_archimedean.1.tendsto_right_iff.symm

#align asymptotics.is_o_one_left_iff Asymptotics.is𝓸_one_left_iff

theorem _root_.Filter.Tendsto.is𝓞_one {c : E'} (h : Tendsto f' l (𝓝 c)) :
    f' =O[l] (fun _x => 1 : α → F) :=
  h.norm.isBoundedUnder_le.is𝓞_one F
#align filter.tendsto.is_O_one Filter.Tendsto.is𝓞_one

theorem Is𝓞.trans_tendsto_nhds (hfg : f =O[l] g') {y : F'} (hg : Tendsto g' l (𝓝 y)) :
    f =O[l] (fun _x => 1 : α → F) :=
  hfg.trans <| hg.is𝓞_one F
#align asymptotics.is_O.trans_tendsto_nhds Asymptotics.Is𝓞.trans_tendsto_nhds

end

theorem is𝓸_const_iff {c : F''} (hc : c ≠ 0) : (f'' =o[l] fun _x => c) ↔ Tendsto f'' l (𝓝 0) :=
  (is𝓸_const_iff_is𝓸_one ℝ hc).trans (is𝓸_one_iff _)
#align asymptotics.is_o_const_iff Asymptotics.is𝓸_const_iff

theorem is𝓸_id_const {c : F''} (hc : c ≠ 0) : (fun x : E'' => x) =o[𝓝 0] fun _x => c :=
  (is𝓸_const_iff hc).mpr (continuous_id.tendsto 0)
#align asymptotics.is_o_id_const Asymptotics.is𝓸_id_const

theorem _root_.Filter.IsBoundedUnder.is𝓞_const (h : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) {c : F''}
    (hc : c ≠ 0) : f =O[l] fun _x => c :=
  (h.is𝓞_one ℝ).trans (is𝓞_const_const _ hc _)
#align filter.is_bounded_under.is_O_const Filter.IsBoundedUnder.is𝓞_const

theorem is𝓞_const_of_tendsto {y : E''} (h : Tendsto f'' l (𝓝 y)) {c : F''} (hc : c ≠ 0) :
    f'' =O[l] fun _x => c :=
  h.norm.isBoundedUnder_le.is𝓞_const hc
#align asymptotics.is_O_const_of_tendsto Asymptotics.is𝓞_const_of_tendsto

theorem Is𝓞.isBoundedUnder_le {c : F} (h : f =O[l] fun _x => c) :
    IsBoundedUnder (· ≤ ·) l (norm ∘ f) :=
  let ⟨c', hc'⟩ := h.bound
  ⟨c' * ‖c‖, eventually_map.2 hc'⟩
#align asymptotics.is_O.is_bounded_under_le Asymptotics.Is𝓞.isBoundedUnder_le

theorem is𝓞_const_of_ne {c : F''} (hc : c ≠ 0) :
    (f =O[l] fun _x => c) ↔ IsBoundedUnder (· ≤ ·) l (norm ∘ f) :=
  ⟨fun h => h.isBoundedUnder_le, fun h => h.is𝓞_const hc⟩
#align asymptotics.is_O_const_of_ne Asymptotics.is𝓞_const_of_ne

theorem is𝓞_const_iff {c : F''} :
    (f'' =O[l] fun _x => c) ↔ (c = 0 → f'' =ᶠ[l] 0) ∧ IsBoundedUnder (· ≤ ·) l fun x => ‖f'' x‖ :=
  by
  refine' ⟨fun h => ⟨fun hc => is𝓞_zero_right_iff.1 (by rwa [← hc]), h.isBoundedUnder_le⟩, _⟩
  rintro ⟨hcf, hf⟩
  rcases eq_or_ne c 0 with (hc | hc)
  exacts[(hcf hc).trans_is𝓞 (is𝓞_zero _ _), hf.is𝓞_const hc]
#align asymptotics.is_O_const_iff Asymptotics.is𝓞_const_iff

theorem is𝓞_iff_isBoundedUnder_le_div (h : ∀ᶠ x in l, g'' x ≠ 0) :
    f =O[l] g'' ↔ IsBoundedUnder (· ≤ ·) l fun x => ‖f x‖ / ‖g'' x‖ := by
  simp only [is𝓞_iff, IsBoundedUnder, IsBounded, eventually_map]
  exact
    exists_congr fun c =>
      eventually_congr <| h.mono fun x hx => (div_le_iff <| norm_pos_iff.2 hx).symm
#align asymptotics.is_O_iff_is_bounded_under_le_div Asymptotics.is𝓞_iff_isBoundedUnder_le_div

/-- `(λ x, c) =O[l] f` if and only if `f` is bounded away from zero. -/
theorem is𝓞_const_left_iff_pos_le_norm {c : E''} (hc : c ≠ 0) :
    (fun _x => c) =O[l] f' ↔ ∃ b, 0 < b ∧ ∀ᶠ x in l, b ≤ ‖f' x‖ := by
  constructor
  · intro h
    rcases h.exists_pos with ⟨C, hC₀, hC⟩
    refine' ⟨‖c‖ / C, div_pos (norm_pos_iff.2 hc) hC₀, _⟩
    exact hC.bound.mono fun x => (div_le_iff' hC₀).2
  · rintro ⟨b, hb₀, hb⟩
    refine' Is𝓞.of_bound (‖c‖ / b) (hb.mono fun x hx => _)
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact le_mul_of_one_le_right (norm_nonneg _) ((one_le_div hb₀).2 hx)
#align asymptotics.is_O_const_left_iff_pos_le_norm Asymptotics.is𝓞_const_left_iff_pos_le_norm

section

variable (𝕜)

end

theorem Is𝓞.trans_tendsto (hfg : f'' =O[l] g'') (hg : Tendsto g'' l (𝓝 0)) : Tendsto f'' l (𝓝 0) :=
  (is𝓸_one_iff ℝ).1 <| hfg.trans_is𝓸 <| (is𝓸_one_iff ℝ).2 hg
#align asymptotics.is_O.trans_tendsto Asymptotics.Is𝓞.trans_tendsto

theorem Is𝓸.trans_tendsto (hfg : f'' =o[l] g'') (hg : Tendsto g'' l (𝓝 0)) :
    Tendsto f'' l (𝓝 0) :=
  hfg.is𝓞.trans_tendsto hg
#align asymptotics.is_o.trans_tendsto Asymptotics.Is𝓸.trans_tendsto

/-! ### Multiplication by a constant -/


theorem is𝓞With_const_mul_self (c : R) (f : α → R) (l : Filter α) :
    Is𝓞With ‖c‖ l (fun x => c * f x) f :=
  is𝓞With_of_le' _ fun _x => norm_mul_le _ _
#align asymptotics.is_O_with_const_mul_self Asymptotics.is𝓞With_const_mul_self

theorem is𝓞_const_mul_self (c : R) (f : α → R) (l : Filter α) : (fun x => c * f x) =O[l] f :=
  (is𝓞With_const_mul_self c f l).is𝓞
#align asymptotics.is_O_const_mul_self Asymptotics.is𝓞_const_mul_self

theorem Is𝓞With.const_mul_left {f : α → R} (h : Is𝓞With c l f g) (c' : R) :
    Is𝓞With (‖c'‖ * c) l (fun x => c' * f x) g :=
  (is𝓞With_const_mul_self c' f l).trans h (norm_nonneg c')
#align asymptotics.is_O_with.const_mul_left Asymptotics.Is𝓞With.const_mul_left

theorem Is𝓞.const_mul_left {f : α → R} (h : f =O[l] g) (c' : R) : (fun x => c' * f x) =O[l] g :=
  let ⟨_c, hc⟩ := h.is𝓞With
  (hc.const_mul_left c').is𝓞
#align asymptotics.is_O.const_mul_left Asymptotics.Is𝓞.const_mul_left

theorem is𝓞With_self_const_mul' (u : Rˣ) (f : α → R) (l : Filter α) :
    Is𝓞With ‖(↑u⁻¹ : R)‖ l f fun x => ↑u * f x := by
  refine' (is𝓞With_const_mul_self ↑u⁻¹ _ l).congr_left _
  exact fun x => u.inv_mul_cancel_left (f x)
  -- porting note: Lean just had trouble elaborating correctly, but this fixes it.
#align asymptotics.is_O_with_self_const_mul' Asymptotics.is𝓞With_self_const_mul'

theorem is𝓞With_self_const_mul (c : 𝕜) (hc : c ≠ 0) (f : α → 𝕜) (l : Filter α) :
    Is𝓞With ‖c‖⁻¹ l f fun x => c * f x :=
  (is𝓞With_self_const_mul' (Units.mk0 c hc) f l).congr_const <| norm_inv c
#align asymptotics.is_O_with_self_const_mul Asymptotics.is𝓞With_self_const_mul

theorem is𝓞_self_const_mul' {c : R} (hc : IsUnit c) (f : α → R) (l : Filter α) :
    f =O[l] fun x => c * f x :=
  let ⟨u, hu⟩ := hc
  hu ▸ (is𝓞With_self_const_mul' u f l).is𝓞
#align asymptotics.is_O_self_const_mul' Asymptotics.is𝓞_self_const_mul'

theorem is𝓞_self_const_mul (c : 𝕜) (hc : c ≠ 0) (f : α → 𝕜) (l : Filter α) :
    f =O[l] fun x => c * f x :=
  is𝓞_self_const_mul' (IsUnit.mk0 c hc) f l
#align asymptotics.is_O_self_const_mul Asymptotics.is𝓞_self_const_mul

theorem is𝓞_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) :
    (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  ⟨(is𝓞_self_const_mul' hc f l).trans, fun h => h.const_mul_left c⟩
#align asymptotics.is_O_const_mul_left_iff' Asymptotics.is𝓞_const_mul_left_iff'

theorem is𝓞_const_mul_left_iff {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  is𝓞_const_mul_left_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_O_const_mul_left_iff Asymptotics.is𝓞_const_mul_left_iff

theorem Is𝓸.const_mul_left {f : α → R} (h : f =o[l] g) (c : R) : (fun x => c * f x) =o[l] g :=
  (is𝓞_const_mul_self c f l).trans_is𝓸 h
#align asymptotics.is_o.const_mul_left Asymptotics.Is𝓸.const_mul_left

theorem is𝓸_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) :
    (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  ⟨(is𝓞_self_const_mul' hc f l).trans_is𝓸, fun h => h.const_mul_left c⟩
#align asymptotics.is_o_const_mul_left_iff' Asymptotics.is𝓸_const_mul_left_iff'

theorem is𝓸_const_mul_left_iff {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  is𝓸_const_mul_left_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_o_const_mul_left_iff Asymptotics.is𝓸_const_mul_left_iff

theorem Is𝓞With.of_const_mul_right {g : α → R} {c : R} (hc' : 0 ≤ c')
    (h : Is𝓞With c' l f fun x => c * g x) : Is𝓞With (c' * ‖c‖) l f g :=
  h.trans (is𝓞With_const_mul_self c g l) hc'
#align asymptotics.is_O_with.of_const_mul_right Asymptotics.Is𝓞With.of_const_mul_right

theorem Is𝓞.of_const_mul_right {g : α → R} {c : R} (h : f =O[l] fun x => c * g x) : f =O[l] g :=
  let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.of_const_mul_right cnonneg).is𝓞
#align asymptotics.is_O.of_const_mul_right Asymptotics.Is𝓞.of_const_mul_right

theorem Is𝓞With.const_mul_right' {g : α → R} {u : Rˣ} {c' : ℝ} (hc' : 0 ≤ c')
    (h : Is𝓞With c' l f g) : Is𝓞With (c' * ‖(↑u⁻¹ : R)‖) l f fun x => ↑u * g x :=
  h.trans (is𝓞With_self_const_mul' _ _ _) hc'
#align asymptotics.is_O_with.const_mul_right' Asymptotics.Is𝓞With.const_mul_right'

theorem Is𝓞With.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) {c' : ℝ} (hc' : 0 ≤ c')
    (h : Is𝓞With c' l f g) : Is𝓞With (c' * ‖c‖⁻¹) l f fun x => c * g x :=
  h.trans (is𝓞With_self_const_mul c hc g l) hc'
#align asymptotics.is_O_with.const_mul_right Asymptotics.Is𝓞With.const_mul_right

theorem Is𝓞.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : f =O[l] g) :
    f =O[l] fun x => c * g x :=
  h.trans (is𝓞_self_const_mul' hc g l)
#align asymptotics.is_O.const_mul_right' Asymptotics.Is𝓞.const_mul_right'

theorem Is𝓞.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : f =O[l] g) :
    f =O[l] fun x => c * g x :=
  h.const_mul_right' <| IsUnit.mk0 c hc
#align asymptotics.is_O.const_mul_right Asymptotics.Is𝓞.const_mul_right

theorem is𝓞_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) :
    (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩
#align asymptotics.is_O_const_mul_right_iff' Asymptotics.is𝓞_const_mul_right_iff'

theorem is𝓞_const_mul_right_iff {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  is𝓞_const_mul_right_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_O_const_mul_right_iff Asymptotics.is𝓞_const_mul_right_iff

theorem Is𝓸.of_const_mul_right {g : α → R} {c : R} (h : f =o[l] fun x => c * g x) : f =o[l] g :=
  h.trans_is𝓞 (is𝓞_const_mul_self c g l)
#align asymptotics.is_o.of_const_mul_right Asymptotics.Is𝓸.of_const_mul_right

theorem Is𝓸.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : f =o[l] g) :
    f =o[l] fun x => c * g x :=
  h.trans_is𝓞 (is𝓞_self_const_mul' hc g l)
#align asymptotics.is_o.const_mul_right' Asymptotics.Is𝓸.const_mul_right'

theorem Is𝓸.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : f =o[l] g) :
    f =o[l] fun x => c * g x :=
  h.const_mul_right' <| IsUnit.mk0 c hc
#align asymptotics.is_o.const_mul_right Asymptotics.Is𝓸.const_mul_right

theorem is𝓸_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) :
    (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩
#align asymptotics.is_o_const_mul_right_iff' Asymptotics.is𝓸_const_mul_right_iff'

theorem is𝓸_const_mul_right_iff {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  is𝓸_const_mul_right_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_o_const_mul_right_iff Asymptotics.is𝓸_const_mul_right_iff

/-! ### Multiplication -/


theorem Is𝓞With.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} {c₁ c₂ : ℝ} (h₁ : Is𝓞With c₁ l f₁ g₁)
    (h₂ : Is𝓞With c₂ l f₂ g₂) : Is𝓞With (c₁ * c₂) l (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x :=
  by
  simp only [Is𝓞With_def] at *
  filter_upwards [h₁, h₂]with _ hx₁ hx₂
  apply le_trans (norm_mul_le _ _)
  convert mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_trans (norm_nonneg _) hx₁) using 1
  rw [norm_mul, mul_mul_mul_comm]
#align asymptotics.is_O_with.mul Asymptotics.Is𝓞With.mul

theorem Is𝓞.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x => f₁ x * f₂ x) =O[l] fun x => g₁ x * g₂ x :=
  let ⟨_c, hc⟩ := h₁.is𝓞With
  let ⟨_c', hc'⟩ := h₂.is𝓞With
  (hc.mul hc').is𝓞
#align asymptotics.is_O.mul Asymptotics.Is𝓞.mul

theorem Is𝓞.mul_is𝓸 {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x := by
  simp only [Is𝓸_def] at *
  intro c cpos
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩
  exact (hc'.mul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel' _ (ne_of_gt c'pos))
#align asymptotics.is_O.mul_is_o Asymptotics.Is𝓞.mul_is𝓸

theorem Is𝓸.mul_is𝓞 {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x := by
  simp only [Is𝓸_def] at *
  intro c cpos
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩
  exact ((h₁ (div_pos cpos c'pos)).mul hc').congr_const (div_mul_cancel _ (ne_of_gt c'pos))
#align asymptotics.is_o.mul_is_O Asymptotics.Is𝓸.mul_is𝓞

theorem Is𝓸.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x :=
  h₁.mul_is𝓞 h₂.is𝓞
#align asymptotics.is_o.mul Asymptotics.Is𝓸.mul

theorem Is𝓞With.pow' {f : α → R} {g : α → 𝕜} (h : Is𝓞With c l f g) :
    ∀ n : ℕ,
      Is𝓞With (Nat.casesOn n ‖(1 : R)‖ fun n => c ^ (n + 1)) l (fun x => f x ^ n) fun x => g x ^ n
  | 0 => by simpa using is𝓞With_const_const (1 : R) (one_ne_zero' 𝕜) l
  | 1 => by simpa
  | n + 2 => by simpa [pow_succ] using h.mul (Is𝓞With.pow' h (n + 1))
#align asymptotics.is_O_with.pow' Asymptotics.Is𝓞With.pow'

theorem Is𝓞With.pow [NormOneClass R] {f : α → R} {g : α → 𝕜} (h : Is𝓞With c l f g) :
    ∀ n : ℕ, Is𝓞With (c ^ n) l (fun x => f x ^ n) fun x => g x ^ n
  | 0 => by simpa using h.pow' 0
  | n + 1 => h.pow' (n + 1)
#align asymptotics.is_O_with.pow Asymptotics.Is𝓞With.pow

theorem Is𝓞With.of_pow {n : ℕ} {f : α → 𝕜} {g : α → R} (h : Is𝓞With c l (f ^ n) (g ^ n))
    (hn : n ≠ 0) (hc : c ≤ c' ^ n) (hc' : 0 ≤ c') : Is𝓞With c' l f g :=
  Is𝓞With.of_bound <|
    (h.weaken hc).bound.mono fun x hx =>
      le_of_pow_le_pow n (mul_nonneg hc' <| norm_nonneg _) hn.bot_lt <|
        calc
          ‖f x‖ ^ n = ‖f x ^ n‖ := (norm_pow _ _).symm
          _ ≤ c' ^ n * ‖g x ^ n‖ := hx
          _ ≤ c' ^ n * ‖g x‖ ^ n :=
            (mul_le_mul_of_nonneg_left (norm_pow_le' _ hn.bot_lt) (pow_nonneg hc' _))
          _ = (c' * ‖g x‖) ^ n := (mul_pow _ _ _).symm

#align asymptotics.is_O_with.of_pow Asymptotics.Is𝓞With.of_pow

theorem Is𝓞.pow {f : α → R} {g : α → 𝕜} (h : f =O[l] g) (n : ℕ) :
    (fun x => f x ^ n) =O[l] fun x => g x ^ n :=
  let ⟨_C, hC⟩ := h.is𝓞With
  is𝓞_iff_is𝓞With.2 ⟨_, hC.pow' n⟩
#align asymptotics.is_O.pow Asymptotics.Is𝓞.pow

theorem Is𝓞.of_pow {f : α → 𝕜} {g : α → R} {n : ℕ} (hn : n ≠ 0) (h : (f ^ n) =O[l] (g ^ n)) :
    f =O[l] g := by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  obtain ⟨c, hc₀, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ C ≤ c ^ n
  exact ((eventually_ge_atTop _).and <| (tendsto_pow_atTop hn).eventually_ge_atTop C).exists
  exact (hC.of_pow hn hc hc₀).is𝓞
#align asymptotics.is_O.of_pow Asymptotics.Is𝓞.of_pow

theorem Is𝓸.pow {f : α → R} {g : α → 𝕜} (h : f =o[l] g) {n : ℕ} (hn : 0 < n) :
    (fun x => f x ^ n) =o[l] fun x => g x ^ n := by
  cases' n with n; exact hn.false.elim; clear hn
  induction' n with n ihn
  · simpa only [Nat.zero_eq, ←Nat.one_eq_succ_zero, pow_one]
  · convert h.mul ihn <;> simp [pow_succ]
#align asymptotics.is_o.pow Asymptotics.Is𝓸.pow

theorem Is𝓸.of_pow {f : α → 𝕜} {g : α → R} {n : ℕ} (h : (f ^ n) =o[l] (g ^ n)) (hn : n ≠ 0) :
    f =o[l] g :=
  Is𝓸.of_is𝓞With fun _c hc => (h.def' <| pow_pos hc _).of_pow hn le_rfl hc.le
#align asymptotics.is_o.of_pow Asymptotics.Is𝓸.of_pow

/-! ### Inverse -/


theorem Is𝓞With.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : Is𝓞With c l f g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : Is𝓞With c l (fun x => (g x)⁻¹) fun x => (f x)⁻¹ := by
  refine' Is𝓞With.of_bound (h.bound.mp (h₀.mono fun x h₀ hle => _))
  cases' eq_or_ne (f x) 0 with hx hx
  · simp only [hx, h₀ hx, inv_zero, norm_zero, MulZeroClass.mul_zero]; rfl
  · have hc : 0 < c := pos_of_mul_pos_left ((norm_pos_iff.2 hx).trans_le hle) (norm_nonneg _)
    replace hle := inv_le_inv_of_le (norm_pos_iff.2 hx) hle
    simpa only [norm_inv, mul_inv, ← div_eq_inv_mul, div_le_iff hc] using hle
#align asymptotics.is_O_with.inv_rev Asymptotics.Is𝓞With.inv_rev

theorem Is𝓞.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =O[l] g) (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) :
    (fun x => (g x)⁻¹) =O[l] fun x => (f x)⁻¹ :=
  let ⟨_c, hc⟩ := h.is𝓞With
  (hc.inv_rev h₀).is𝓞
#align asymptotics.is_O.inv_rev Asymptotics.Is𝓞.inv_rev

theorem Is𝓸.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =o[l] g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : (fun x => (g x)⁻¹) =o[l] fun x => (f x)⁻¹ :=
  Is𝓸.of_is𝓞With fun _c hc => (h.def' hc).inv_rev h₀
#align asymptotics.is_o.inv_rev Asymptotics.Is𝓸.inv_rev

/-! ### Scalar multiplication -/


section SmulConst

variable [NormedSpace 𝕜 E']

theorem Is𝓞With.const_smul_left (h : Is𝓞With c l f' g) (c' : 𝕜) :
    Is𝓞With (‖c'‖ * c) l (fun x => c' • f' x) g :=
  Is𝓞With.of_norm_left <| by
    simpa only [norm_smul, _root_.norm_norm] using h.norm_left.const_mul_left ‖c'‖
    -- porting note:
#align asymptotics.is_O_with.const_smul_left Asymptotics.Is𝓞With.const_smul_left

theorem Is𝓞.const_smul_left (h : f' =O[l] g) (c : 𝕜) : (c • f') =O[l] g :=
  let ⟨_b, hb⟩ := h.is𝓞With
  (hb.const_smul_left _).is𝓞
#align asymptotics.is_O.const_smul_left Asymptotics.Is𝓞.const_smul_left

theorem Is𝓸.const_smul_left (h : f' =o[l] g) (c : 𝕜) : (c • f') =o[l] g :=
  Is𝓸.of_norm_left <| by simpa only [← norm_smul] using h.norm_left.const_mul_left ‖c‖
#align asymptotics.is_o.const_smul_left Asymptotics.Is𝓸.const_smul_left

theorem is𝓞_const_smul_left {c : 𝕜} (hc : c ≠ 0) : (fun x => c • f' x) =O[l] g ↔ f' =O[l] g := by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is𝓞_norm_left]
  simp only [norm_smul]
  rw [is𝓞_const_mul_left_iff cne0, is𝓞_norm_left]
#align asymptotics.is_O_const_smul_left Asymptotics.is𝓞_const_smul_left

theorem is𝓸_const_smul_left {c : 𝕜} (hc : c ≠ 0) : (fun x => c • f' x) =o[l] g ↔ f' =o[l] g := by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is𝓸_norm_left]
  simp only [norm_smul]
  rw [is𝓸_const_mul_left_iff cne0, is𝓸_norm_left]
#align asymptotics.is_o_const_smul_left Asymptotics.is𝓸_const_smul_left

theorem is𝓞_const_smul_right {c : 𝕜} (hc : c ≠ 0) : (f =O[l] fun x => c • f' x) ↔ f =O[l] f' := by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is𝓞_norm_right]
  simp only [norm_smul]
  rw [is𝓞_const_mul_right_iff cne0, is𝓞_norm_right]
#align asymptotics.is_O_const_smul_right Asymptotics.is𝓞_const_smul_right

theorem is𝓸_const_smul_right {c : 𝕜} (hc : c ≠ 0) : (f =o[l] fun x => c • f' x) ↔ f =o[l] f' :=
  by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is𝓸_norm_right]
  simp only [norm_smul]
  rw [is𝓸_const_mul_right_iff cne0, is𝓸_norm_right]
#align asymptotics.is_o_const_smul_right Asymptotics.is𝓸_const_smul_right

end SmulConst

section Smul

variable [NormedSpace 𝕜 E'] [NormedSpace 𝕜' F'] {k₁ : α → 𝕜} {k₂ : α → 𝕜'}

theorem Is𝓞With.smul (h₁ : Is𝓞With c l k₁ k₂) (h₂ : Is𝓞With c' l f' g') :
    Is𝓞With (c * c') l (fun x => k₁ x • f' x) fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr rfl _ _).of_norm_norm <;>
    · intros; simp only [norm_smul]
#align asymptotics.is_O_with.smul Asymptotics.Is𝓞With.smul

theorem Is𝓞.smul (h₁ : k₁ =O[l] k₂) (h₂ : f' =O[l] g') :
    (fun x => k₁ x • f' x) =O[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros; simp only [norm_smul]
#align asymptotics.is_O.smul Asymptotics.Is𝓞.smul

theorem Is𝓞.smul_is𝓸 (h₁ : k₁ =O[l] k₂) (h₂ : f' =o[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul_is𝓸 h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros; simp only [norm_smul]
#align asymptotics.is_O.smul_is_o Asymptotics.Is𝓞.smul_is𝓸

theorem Is𝓸.smul_is𝓞 (h₁ : k₁ =o[l] k₂) (h₂ : f' =O[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul_is𝓞 h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros; simp only [norm_smul]
#align asymptotics.is_o.smul_is_O Asymptotics.Is𝓸.smul_is𝓞

theorem Is𝓸.smul (h₁ : k₁ =o[l] k₂) (h₂ : f' =o[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros; simp only [norm_smul]
#align asymptotics.is_o.smul Asymptotics.Is𝓸.smul

end Smul

/-! ### Sum -/


section Sum

variable {ι : Type _} {A : ι → α → E'} {C : ι → ℝ} {s : Finset ι}

theorem Is𝓞With.sum (h : ∀ i ∈ s, Is𝓞With (C i) l (A i) g) :
    Is𝓞With (∑ i in s, C i) l (fun x => ∑ i in s, A i x) g := by
  induction' s using Finset.induction_on with i s is IH
  · simp only [is𝓞With_zero', Finset.sum_empty, forall_true_iff]
  · simp only [is, Finset.sum_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i s)).add (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))
#align asymptotics.is_O_with.sum Asymptotics.Is𝓞With.sum

theorem Is𝓞.sum (h : ∀ i ∈ s, A i =O[l] g) : (fun x => ∑ i in s, A i x) =O[l] g := by
  simp only [Is𝓞_def] at *
  choose! C hC using h
  exact ⟨_, Is𝓞With.sum hC⟩
#align asymptotics.is_O.sum Asymptotics.Is𝓞.sum

theorem Is𝓸.sum (h : ∀ i ∈ s, A i =o[l] g') : (fun x => ∑ i in s, A i x) =o[l] g' := by
  induction' s using Finset.induction_on with i s is IH
  · simp only [is𝓸_zero, Finset.sum_empty, forall_true_iff]
  · simp only [is, Finset.sum_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i s)).add (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))
#align asymptotics.is_o.sum Asymptotics.Is𝓸.sum

end Sum

/-! ### Relation between `f = o(g)` and `f / g → 0` -/


theorem Is𝓸.tendsto_div_nhds_zero {f g : α → 𝕜} (h : f =o[l] g) :
    Tendsto (fun x => f x / g x) l (𝓝 0) :=
  (is𝓸_one_iff 𝕜).mp <| by
    calc
      (fun x => f x / g x) =o[l] fun x => g x / g x := by
        simpa only [div_eq_mul_inv] using h.mul_is𝓞 (is𝓞_refl _ _)
      _ =O[l] fun _x => (1 : 𝕜) := is𝓞_of_le _ fun x => by simp [div_self_le_one]
#align asymptotics.is_o.tendsto_div_nhds_zero Asymptotics.Is𝓸.tendsto_div_nhds_zero

theorem Is𝓸.tendsto_inv_smul_nhds_zero [NormedSpace 𝕜 E'] {f : α → E'} {g : α → 𝕜} {l : Filter α}
    (h : f =o[l] g) : Tendsto (fun x => (g x)⁻¹ • f x) l (𝓝 0) := by
  simpa only [div_eq_inv_mul, ← norm_inv, ← norm_smul, ← tendsto_zero_iff_norm_tendsto_zero] using
    h.norm_norm.tendsto_div_nhds_zero
#align asymptotics.is_o.tendsto_inv_smul_nhds_zero Asymptotics.Is𝓸.tendsto_inv_smul_nhds_zero

theorem is𝓸_iff_tendsto' {f g : α → 𝕜} (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
    f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  ⟨Is𝓸.tendsto_div_nhds_zero, fun h =>
    (((is𝓸_one_iff _).mpr h).mul_is𝓞 (is𝓞_refl g l)).congr'
      (hgf.mono fun _x => div_mul_cancel_of_imp) (eventually_of_forall fun _x => one_mul _)⟩
#align asymptotics.is_o_iff_tendsto' Asymptotics.is𝓸_iff_tendsto'

theorem is𝓸_iff_tendsto {f g : α → 𝕜} (hgf : ∀ x, g x = 0 → f x = 0) :
    f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  is𝓸_iff_tendsto' (eventually_of_forall hgf)
#align asymptotics.is_o_iff_tendsto Asymptotics.is𝓸_iff_tendsto

alias is𝓸_iff_tendsto' ↔ _ is𝓸_of_tendsto'
#align asymptotics.is_o_of_tendsto' Asymptotics.is𝓸_of_tendsto'

alias is𝓸_iff_tendsto ↔ _ is𝓸_of_tendsto
#align asymptotics.is_o_of_tendsto Asymptotics.is𝓸_of_tendsto

theorem is𝓸_const_left_of_ne {c : E''} (hc : c ≠ 0) :
    (fun _x => c) =o[l] g ↔ Tendsto (fun x => ‖g x‖) l atTop := by
  simp only [← is𝓸_one_left_iff ℝ]
  exact ⟨(is𝓞_const_const (1 : ℝ) hc l).trans_is𝓸, (is𝓞_const_one ℝ c l).trans_is𝓸⟩
#align asymptotics.is_o_const_left_of_ne Asymptotics.is𝓸_const_left_of_ne

@[simp]
theorem is𝓸_const_left {c : E''} :
    (fun _x => c) =o[l] g'' ↔ c = 0 ∨ Tendsto (norm ∘ g'') l atTop := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp only [is𝓸_zero, eq_self_iff_true, true_or_iff]
  · simp only [hc, false_or_iff, is𝓸_const_left_of_ne hc]; rfl
#align asymptotics.is_o_const_left Asymptotics.is𝓸_const_left

@[simp 1001] -- porting note: increase priority so that this triggers before `is𝓸_const_left`
theorem is𝓸_const_const_iff [NeBot l] {d : E''} {c : F''} :
    ((fun _x => d) =o[l] fun _x => c) ↔ d = 0 := by
  have : ¬Tendsto (Function.const α ‖c‖) l atTop :=
    not_tendsto_atTop_of_tendsto_nhds tendsto_const_nhds
  simp only [is𝓸_const_left, or_iff_left_iff_imp]
  exact fun h => (this h).elim
#align asymptotics.is_o_const_const_iff Asymptotics.is𝓸_const_const_iff

@[simp]
theorem is𝓸_pure {x} : f'' =o[pure x] g'' ↔ f'' x = 0 :=
  calc
    f'' =o[pure x] g'' ↔ (fun _y : α => f'' x) =o[pure x] fun _ => g'' x := is𝓸_congr rfl rfl
    _ ↔ f'' x = 0 := is𝓸_const_const_iff

#align asymptotics.is_o_pure Asymptotics.is𝓸_pure

theorem is𝓸_const_id_comap_norm_atTop (c : F'') : (fun _x : E'' => c) =o[comap norm atTop] id :=
  is𝓸_const_left.2 <| Or.inr tendsto_comap
#align asymptotics.is_o_const_id_comap_norm_at_top Asymptotics.is𝓸_const_id_comap_norm_atTop

theorem is𝓸_const_id_atTop (c : E'') : (fun _x : ℝ => c) =o[atTop] id :=
  is𝓸_const_left.2 <| Or.inr tendsto_abs_atTop_atTop
#align asymptotics.is_o_const_id_at_top Asymptotics.is𝓸_const_id_atTop

theorem is𝓸_const_id_atBot (c : E'') : (fun _x : ℝ => c) =o[atBot] id :=
  is𝓸_const_left.2 <| Or.inr tendsto_abs_atBot_atTop
#align asymptotics.is_o_const_id_at_bot Asymptotics.is𝓸_const_id_atBot

/-!
### Eventually (u / v) * v = u

If `u` and `v` are linked by an `is_O_with` relation, then we
eventually have `(u / v) * v = u`, even if `v` vanishes.
-/


section EventuallyMulDivCancel

variable {u v : α → 𝕜}

theorem Is𝓞With.eventually_mul_div_cancel (h : Is𝓞With c l u v) : u / v * v =ᶠ[l] u :=
  Eventually.mono h.bound fun y hy => div_mul_cancel_of_imp fun hv => by simpa [hv] using hy
#align asymptotics.is_O_with.eventually_mul_div_cancel Asymptotics.Is𝓞With.eventually_mul_div_cancel

/-- If `u = O(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem Is𝓞.eventually_mul_div_cancel (h : u =O[l] v) : u / v * v =ᶠ[l] u :=
  let ⟨_c, hc⟩ := h.is𝓞With
  hc.eventually_mul_div_cancel
#align asymptotics.is_O.eventually_mul_div_cancel Asymptotics.Is𝓞.eventually_mul_div_cancel

/-- If `u = o(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem Is𝓸.eventually_mul_div_cancel (h : u =o[l] v) : u / v * v =ᶠ[l] u :=
  (h.forall_is𝓞With zero_lt_one).eventually_mul_div_cancel
#align asymptotics.is_o.eventually_mul_div_cancel Asymptotics.Is𝓸.eventually_mul_div_cancel

end EventuallyMulDivCancel

/-! ### Equivalent definitions of the form `∃ φ, u =ᶠ[l] φ * v` in a `normed_field`. -/


section ExistsMulEq

variable {u v : α → 𝕜}

/-- If `‖φ‖` is eventually bounded by `c`, and `u =ᶠ[l] φ * v`, then we have `is_O_with c u v l`.
    This does not require any assumptions on `c`, which is why we keep this version along with
    `is_O_with_iff_exists_eq_mul`. -/
theorem is𝓞With_of_eq_mul (φ : α → 𝕜) (hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c) (h : u =ᶠ[l] φ * v) :
    Is𝓞With c l u v := by
  simp only [Is𝓞With_def]
  refine' h.symm.rw (fun x a => ‖a‖ ≤ c * ‖v x‖) (hφ.mono fun x hx => _)
  simp only [norm_mul, Pi.mul_apply]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
#align asymptotics.is_O_with_of_eq_mul Asymptotics.is𝓞With_of_eq_mul

theorem is𝓞With_iff_exists_eq_mul (hc : 0 ≤ c) :
    Is𝓞With c l u v ↔ ∃ (φ : α → 𝕜)(_hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c), u =ᶠ[l] φ * v := by
  constructor
  · intro h
    use fun x => u x / v x
    refine' ⟨Eventually.mono h.bound fun y hy => _, h.eventually_mul_div_cancel.symm⟩
    simpa using div_le_of_nonneg_of_le_mul (norm_nonneg _) hc hy
  · rintro ⟨φ, hφ, h⟩
    exact is𝓞With_of_eq_mul φ hφ h
#align asymptotics.is_O_with_iff_exists_eq_mul Asymptotics.is𝓞With_iff_exists_eq_mul

theorem Is𝓞With.exists_eq_mul (h : Is𝓞With c l u v) (hc : 0 ≤ c) :
    ∃ (φ : α → 𝕜)(_hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c), u =ᶠ[l] φ * v :=
  (is𝓞With_iff_exists_eq_mul hc).mp h
#align asymptotics.is_O_with.exists_eq_mul Asymptotics.Is𝓞With.exists_eq_mul

theorem is𝓞_iff_exists_eq_mul :
    u =O[l] v ↔ ∃ (φ : α → 𝕜)(_hφ : l.IsBoundedUnder (· ≤ ·) (norm ∘ φ)), u =ᶠ[l] φ * v := by
  constructor
  · rintro h
    rcases h.exists_nonneg with ⟨c, hnnc, hc⟩
    rcases hc.exists_eq_mul hnnc with ⟨φ, hφ, huvφ⟩
    exact ⟨φ, ⟨c, hφ⟩, huvφ⟩
  · rintro ⟨φ, ⟨c, hφ⟩, huvφ⟩
    exact is𝓞_iff_is𝓞With.2 ⟨c, is𝓞With_of_eq_mul φ hφ huvφ⟩
#align asymptotics.is_O_iff_exists_eq_mul Asymptotics.is𝓞_iff_exists_eq_mul

alias is𝓞_iff_exists_eq_mul ↔ Is𝓞.exists_eq_mul _
#align asymptotics.is_O.exists_eq_mul Asymptotics.Is𝓞.exists_eq_mul

theorem is𝓸_iff_exists_eq_mul :
    u =o[l] v ↔ ∃ (φ : α → 𝕜)(_hφ : Tendsto φ l (𝓝 0)), u =ᶠ[l] φ * v := by
  constructor
  · exact fun h => ⟨fun x => u x / v x, h.tendsto_div_nhds_zero, h.eventually_mul_div_cancel.symm⟩
  · simp only [Is𝓸_def]
    rintro ⟨φ, hφ, huvφ⟩ c hpos
    rw [NormedAddCommGroup.tendsto_nhds_zero] at hφ
    exact is𝓞With_of_eq_mul _ ((hφ c hpos).mono fun x => le_of_lt) huvφ
#align asymptotics.is_o_iff_exists_eq_mul Asymptotics.is𝓸_iff_exists_eq_mul

alias is𝓸_iff_exists_eq_mul ↔ Is𝓸.exists_eq_mul _
#align asymptotics.is_o.exists_eq_mul Asymptotics.Is𝓸.exists_eq_mul

end ExistsMulEq

/-! ### Miscellanous lemmas -/


theorem div_isBoundedUnder_of_is𝓞 {α : Type _} {l : Filter α} {f g : α → 𝕜} (h : f =O[l] g) :
    IsBoundedUnder (· ≤ ·) l fun x => ‖f x / g x‖ := by
  obtain ⟨c, h₀, hc⟩ := h.exists_nonneg
  refine' ⟨c, eventually_map.2 (hc.bound.mono fun x hx => _)⟩
  rw [norm_div]
  exact div_le_of_nonneg_of_le_mul (norm_nonneg _) h₀ hx
#align asymptotics.div_is_bounded_under_of_is_O Asymptotics.div_isBoundedUnder_of_is𝓞

theorem is𝓞_iff_div_isBoundedUnder {α : Type _} {l : Filter α} {f g : α → 𝕜}
    (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
    f =O[l] g ↔ IsBoundedUnder (· ≤ ·) l fun x => ‖f x / g x‖ := by
  refine' ⟨div_isBoundedUnder_of_is𝓞, fun h => _⟩
  obtain ⟨c, hc⟩ := h
  simp only [eventually_map, norm_div] at hc
  refine' Is𝓞.of_bound c (hc.mp <| hgf.mono fun x hx₁ hx₂ => _)
  by_cases hgx : g x = 0
  · simp [hx₁ hgx, hgx]
  · exact (div_le_iff (norm_pos_iff.2 hgx)).mp hx₂
#align asymptotics.is_O_iff_div_is_bounded_under Asymptotics.is𝓞_iff_div_isBoundedUnder

theorem is𝓞_of_div_tendsto_nhds {α : Type _} {l : Filter α} {f g : α → 𝕜}
    (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) (c : 𝕜) (H : Filter.Tendsto (f / g) l (𝓝 c)) : f =O[l] g :=
  (is𝓞_iff_div_isBoundedUnder hgf).2 <| H.norm.isBoundedUnder_le
#align asymptotics.is_O_of_div_tendsto_nhds Asymptotics.is𝓞_of_div_tendsto_nhds

theorem Is𝓸.tendsto_zero_of_tendsto {α E 𝕜 : Type _} [NormedAddCommGroup E] [NormedField 𝕜]
    {u : α → E} {v : α → 𝕜} {l : Filter α} {y : 𝕜} (huv : u =o[l] v) (hv : Tendsto v l (𝓝 y)) :
    Tendsto u l (𝓝 0) := by
  suffices h : u =o[l] fun _x => (1 : 𝕜)
  · rwa [is𝓸_one_iff] at h
  exact huv.trans_is𝓞 (hv.is𝓞_one 𝕜)
#align asymptotics.is_o.tendsto_zero_of_tendsto Asymptotics.Is𝓸.tendsto_zero_of_tendsto

theorem is𝓸_pow_pow {m n : ℕ} (h : m < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x ^ m := by
  rcases lt_iff_exists_add.1 h with ⟨p, hp0 : 0 < p, rfl⟩
  suffices (fun x : 𝕜 => x ^ m * x ^ p) =o[𝓝 0] fun x => x ^ m * 1 ^ p by
    simpa only [pow_add, one_pow, mul_one]
  exact Is𝓞.mul_is𝓸 (is𝓞_refl _ _) (Is𝓸.pow ((is𝓸_one_iff _).2 tendsto_id) hp0)
#align asymptotics.is_o_pow_pow Asymptotics.is𝓸_pow_pow

theorem is𝓸_norm_pow_norm_pow {m n : ℕ} (h : m < n) :
    (fun x : E' => ‖x‖ ^ n) =o[𝓝 0] fun x => ‖x‖ ^ m :=
  (is𝓸_pow_pow h).comp_tendsto tendsto_norm_zero
#align asymptotics.is_o_norm_pow_norm_pow Asymptotics.is𝓸_norm_pow_norm_pow

theorem is𝓸_pow_id {n : ℕ} (h : 1 < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x := by
  convert is𝓸_pow_pow h (𝕜 := 𝕜)
  simp only [pow_one]
#align asymptotics.is_o_pow_id Asymptotics.is𝓸_pow_id

theorem is𝓸_norm_pow_id {n : ℕ} (h : 1 < n) : (fun x : E' => ‖x‖ ^ n) =o[𝓝 0] fun x => x := by
  have := @is𝓸_norm_pow_norm_pow E' _ _ _ h
  simp only [pow_one] at this
  exact is𝓸_norm_right.mp this
#align asymptotics.is_o_norm_pow_id Asymptotics.is𝓸_norm_pow_id

theorem Is𝓞.eq_zero_of_norm_pow_within {f : E'' → F''} {s : Set E''} {x₀ : E''} {n : ℕ}
    (h : f =O[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ n) (hx₀ : x₀ ∈ s) (hn : 0 < n) : f x₀ = 0 :=
  mem_of_mem_nhdsWithin hx₀ h.eq_zero_imp <| by simp_rw [sub_self, norm_zero, zero_pow hn]
#align asymptotics.is_O.eq_zero_of_norm_pow_within Asymptotics.Is𝓞.eq_zero_of_norm_pow_within

theorem Is𝓞.eq_zero_of_norm_pow {f : E'' → F''} {x₀ : E''} {n : ℕ}
    (h : f =O[𝓝 x₀] fun x => ‖x - x₀‖ ^ n) (hn : 0 < n) : f x₀ = 0 := by
  rw [← nhdsWithin_univ] at h
  exact h.eq_zero_of_norm_pow_within (mem_univ _) hn
#align asymptotics.is_O.eq_zero_of_norm_pow Asymptotics.Is𝓞.eq_zero_of_norm_pow

theorem is𝓸_pow_sub_pow_sub (x₀ : E') {n m : ℕ} (h : n < m) :
    (fun x => ‖x - x₀‖ ^ m) =o[𝓝 x₀] fun x => ‖x - x₀‖ ^ n :=
  haveI : Tendsto (fun x => ‖x - x₀‖) (𝓝 x₀) (𝓝 0) := by
    apply tendsto_norm_zero.comp
    rw [← sub_self x₀]
    exact tendsto_id.sub tendsto_const_nhds
  (is𝓸_pow_pow h).comp_tendsto this
#align asymptotics.is_o_pow_sub_pow_sub Asymptotics.is𝓸_pow_sub_pow_sub

theorem is𝓸_pow_sub_sub (x₀ : E') {m : ℕ} (h : 1 < m) :
    (fun x => ‖x - x₀‖ ^ m) =o[𝓝 x₀] fun x => x - x₀ := by
  simpa only [is𝓸_norm_right, pow_one] using is𝓸_pow_sub_pow_sub x₀ h
#align asymptotics.is_o_pow_sub_sub Asymptotics.is𝓸_pow_sub_sub

theorem Is𝓞With.right_le_sub_of_lt_1 {f₁ f₂ : α → E'} (h : Is𝓞With c l f₁ f₂) (hc : c < 1) :
    Is𝓞With (1 / (1 - c)) l f₂ fun x => f₂ x - f₁ x :=
  Is𝓞With.of_bound <|
    mem_of_superset h.bound fun x hx => by
      simp only [mem_setOf_eq] at hx⊢
      rw [mul_comm, one_div, ← div_eq_mul_inv, _root_.le_div_iff, mul_sub, mul_one, mul_comm]
      · exact le_trans (sub_le_sub_left hx _) (norm_sub_norm_le _ _)
      · exact sub_pos.2 hc
#align asymptotics.is_O_with.right_le_sub_of_lt_1 Asymptotics.Is𝓞With.right_le_sub_of_lt_1

theorem Is𝓞With.right_le_add_of_lt_1 {f₁ f₂ : α → E'} (h : Is𝓞With c l f₁ f₂) (hc : c < 1) :
    Is𝓞With (1 / (1 - c)) l f₂ fun x => f₁ x + f₂ x :=
  (h.neg_right.right_le_sub_of_lt_1 hc).neg_right.of_neg_left.congr rfl (fun x => rfl) fun x => by
    rw [neg_sub, sub_neg_eq_add]
#align asymptotics.is_O_with.right_le_add_of_lt_1 Asymptotics.Is𝓞With.right_le_add_of_lt_1

theorem Is𝓸.right_is𝓞_sub {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) : f₂ =O[l] fun x => f₂ x - f₁ x :=
  ((h.def' one_half_pos).right_le_sub_of_lt_1 one_half_lt_one).is𝓞
#align asymptotics.is_o.right_is_O_sub Asymptotics.Is𝓸.right_is𝓞_sub

theorem Is𝓸.right_is𝓞_add {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) : f₂ =O[l] fun x => f₁ x + f₂ x :=
  ((h.def' one_half_pos).right_le_add_of_lt_1 one_half_lt_one).is𝓞
#align asymptotics.is_o.right_is_O_add Asymptotics.Is𝓸.right_is𝓞_add

/-- If `f x = O(g x)` along `cofinite`, then there exists a positive constant `C` such that
`‖f x‖ ≤ C * ‖g x‖` whenever `g x ≠ 0`. -/
theorem bound_of_is𝓞_cofinite (h : f =O[cofinite] g'') :
    ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖ := by
  rcases h.exists_pos with ⟨C, C₀, hC⟩
  rw [Is𝓞With_def, eventually_cofinite] at hC
  rcases (hC.toFinset.image fun x => ‖f x‖ / ‖g'' x‖).exists_le with ⟨C', hC'⟩
  have : ∀ x, C * ‖g'' x‖ < ‖f x‖ → ‖f x‖ / ‖g'' x‖ ≤ C' := by simpa using hC'
  refine' ⟨max C C', lt_max_iff.2 (Or.inl C₀), fun x h₀ => _⟩
  rw [max_mul_of_nonneg _ _ (norm_nonneg _), le_max_iff, or_iff_not_imp_left, not_le]
  exact fun hx => (div_le_iff (norm_pos_iff.2 h₀)).1 (this _ hx)
#align asymptotics.bound_of_is_O_cofinite Asymptotics.bound_of_is𝓞_cofinite

theorem is𝓞_cofinite_iff (h : ∀ x, g'' x = 0 → f'' x = 0) :
    f'' =O[cofinite] g'' ↔ ∃ C, ∀ x, ‖f'' x‖ ≤ C * ‖g'' x‖ :=
  ⟨fun h' =>
    let ⟨C, _C₀, hC⟩ := bound_of_is𝓞_cofinite h'
    ⟨C, fun x => if hx : g'' x = 0 then by simp [h _ hx, hx] else hC hx⟩,
    fun h => (is𝓞_top.2 h).mono le_top⟩
#align asymptotics.is_O_cofinite_iff Asymptotics.is𝓞_cofinite_iff

theorem bound_of_is𝓞_nat_atTop {f : ℕ → E} {g'' : ℕ → E''} (h : f =O[atTop] g'') :
    ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖ :=
  bound_of_is𝓞_cofinite <| by rwa [Nat.cofinite_eq_atTop]
#align asymptotics.bound_of_is_O_nat_at_top Asymptotics.bound_of_is𝓞_nat_atTop

theorem is𝓞_nat_atTop_iff {f : ℕ → E''} {g : ℕ → F''} (h : ∀ x, g x = 0 → f x = 0) :
    f =O[atTop] g ↔ ∃ C, ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by
  rw [← Nat.cofinite_eq_atTop, is𝓞_cofinite_iff h]
#align asymptotics.is_O_nat_at_top_iff Asymptotics.is𝓞_nat_atTop_iff

theorem is𝓞_one_nat_atTop_iff {f : ℕ → E''} :
    f =O[atTop] (fun _n => 1 : ℕ → ℝ) ↔ ∃ C, ∀ n, ‖f n‖ ≤ C :=
  Iff.trans (is𝓞_nat_atTop_iff fun n h => (one_ne_zero h).elim) <| by simp only [norm_one, mul_one]
#align asymptotics.is_O_one_nat_at_top_iff Asymptotics.is𝓞_one_nat_atTop_iff

theorem is𝓞With_pi {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} {C : ℝ} (hC : 0 ≤ C) :
    Is𝓞With C l f g' ↔ ∀ i, Is𝓞With C l (fun x => f x i) g' := by
  have : ∀ x, 0 ≤ C * ‖g' x‖ := fun x => mul_nonneg hC (norm_nonneg _)
  simp only [is𝓞With_iff, pi_norm_le_iff_of_nonneg (this _), eventually_all]
#align asymptotics.is_O_with_pi Asymptotics.is𝓞With_pi

@[simp]
theorem is𝓞_pi {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} : f =O[l] g' ↔ ∀ i, (fun x => f x i) =O[l] g' := by
  simp only [is𝓞_iff_eventually_is𝓞With, ← eventually_all]
  exact eventually_congr (eventually_atTop.2 ⟨0, fun c => is𝓞With_pi⟩)
#align asymptotics.is_O_pi Asymptotics.is𝓞_pi

@[simp]
theorem is𝓸_pi {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} : f =o[l] g' ↔ ∀ i, (fun x => f x i) =o[l] g' := by
  simp (config := { contextual := true }) only [Is𝓸_def, is𝓞With_pi, le_of_lt]
  exact ⟨fun h i c hc => h hc i, fun h c hc i => h i hc⟩
#align asymptotics.is_o_pi Asymptotics.is𝓸_pi

end Asymptotics

open Asymptotics

theorem summable_of_is𝓞 {ι E} [NormedAddCommGroup E] [CompleteSpace E] {f : ι → E} {g : ι → ℝ}
    (hg : Summable g) (h : f =O[cofinite] g) : Summable f :=
  let ⟨C, hC⟩ := h.is𝓞With
  summable_of_norm_bounded_eventually (fun x => C * ‖g x‖) (hg.abs.mul_left _) hC.bound
set_option linter.uppercaseLean3 false in
#align summable_of_is_O summable_of_is𝓞

theorem summable_of_is𝓞_nat {E} [NormedAddCommGroup E] [CompleteSpace E] {f : ℕ → E} {g : ℕ → ℝ}
    (hg : Summable g) (h : f =O[atTop] g) : Summable f :=
  summable_of_is𝓞 hg <| Nat.cofinite_eq_atTop.symm ▸ h
set_option linter.uppercaseLean3 false in
#align summable_of_is_O_nat summable_of_is𝓞_nat

namespace LocalHomeomorph

variable {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

variable {E : Type _} [Norm E] {F : Type _} [Norm F]

/-- Transfer `is_O_with` over a `local_homeomorph`. -/
theorem is𝓞With_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E} {g : β → F}
    {C : ℝ} : Is𝓞With C (𝓝 b) f g ↔ Is𝓞With C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
  ⟨fun h =>
    h.comp_tendsto <| by
      have := e.continuousAt (e.map_target hb)
      rwa [ContinuousAt, e.rightInvOn hb] at this,
    fun h =>
    (h.comp_tendsto (e.continuousAt_symm hb)).congr' rfl
      ((e.eventually_right_inverse hb).mono fun x hx => congr_arg f hx)
      ((e.eventually_right_inverse hb).mono fun x hx => congr_arg g hx)⟩
set_option linter.uppercaseLean3 false in
#align local_homeomorph.is_O_with_congr LocalHomeomorph.is𝓞With_congr

/-- Transfer `is_O` over a `local_homeomorph`. -/
theorem is𝓞_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E} {g : β → F} :
    f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [Is𝓞_def]
  exact exists_congr fun C => e.is𝓞With_congr hb
set_option linter.uppercaseLean3 false in
#align local_homeomorph.is_O_congr LocalHomeomorph.is𝓞_congr

/-- Transfer `is_o` over a `local_homeomorph`. -/
theorem is𝓸_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E} {g : β → F} :
    f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [Is𝓸_def]
  exact forall₂_congr fun c _hc => e.is𝓞With_congr hb
set_option linter.uppercaseLean3 false in
#align local_homeomorph.is_o_congr LocalHomeomorph.is𝓸_congr

end LocalHomeomorph

namespace Homeomorph

variable {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

variable {E : Type _} [Norm E] {F : Type _} [Norm F]

open Asymptotics

/-- Transfer `is_O_with` over a `homeomorph`. -/
theorem is𝓞With_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} {C : ℝ} :
    Is𝓞With C (𝓝 b) f g ↔ Is𝓞With C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
  e.toLocalHomeomorph.is𝓞With_congr trivial
set_option linter.uppercaseLean3 false in
#align homeomorph.is_O_with_congr Homeomorph.is𝓞With_congr

/-- Transfer `is_O` over a `homeomorph`. -/
theorem is𝓞_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} :
    f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [Is𝓞_def]
  exact exists_congr fun C => e.is𝓞With_congr
set_option linter.uppercaseLean3 false in
#align homeomorph.is_O_congr Homeomorph.is𝓞_congr

/-- Transfer `is_o` over a `homeomorph`. -/
theorem is𝓸_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} :
    f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [Is𝓸_def]
  exact forall₂_congr fun c _hc => e.is𝓞With_congr
#align homeomorph.is_o_congr Homeomorph.is𝓸_congr

end Homeomorph
