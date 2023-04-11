/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.asymptotics.asymptotics
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.InfiniteSum
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Topology.Algebra.Order.LiminfLimsup
import Mathbin.Topology.LocalHomeomorph

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
irreducible_def IsOWith (c : ℝ) (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖
#align asymptotics.is_O_with Asymptotics.IsOWith

/-- Definition of `is_O_with`. We record it in a lemma as `is_O_with` is irreducible. -/
theorem isOWith_iff : IsOWith c l f g ↔ ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by rw [is_O_with]
#align asymptotics.is_O_with_iff Asymptotics.isOWith_iff

alias is_O_with_iff ↔ is_O_with.bound is_O_with.of_bound
#align asymptotics.is_O_with.bound Asymptotics.IsOWith.bound
#align asymptotics.is_O_with.of_bound Asymptotics.IsOWith.of_bound

/-- The Landau notation `f =O[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by a constant multiple of `‖g‖`.
In other words, `‖f‖ / ‖g‖` is eventually bounded, modulo division by zero issues that are avoided
by this definition. -/
irreducible_def IsO (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∃ c : ℝ, IsOWith c l f g
#align asymptotics.is_O Asymptotics.IsO

-- mathport name: «expr =O[ ] »
notation:100 f " =O[" l "] " g:100 => IsO l f g

/-- Definition of `is_O` in terms of `is_O_with`. We record it in a lemma as `is_O` is
irreducible. -/
theorem isO_iff_isOWith : f =O[l] g ↔ ∃ c : ℝ, IsOWith c l f g := by rw [is_O]
#align asymptotics.is_O_iff_is_O_with Asymptotics.isO_iff_isOWith

/-- Definition of `is_O` in terms of filters. We record it in a lemma as we will set
`is_O` to be irreducible at the end of this file. -/
theorem isO_iff : f =O[l] g ↔ ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  simp only [is_O, is_O_with]
#align asymptotics.is_O_iff Asymptotics.isO_iff

theorem IsO.of_bound (c : ℝ) (h : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g :=
  isO_iff.2 ⟨c, h⟩
#align asymptotics.is_O.of_bound Asymptotics.IsO.of_bound

theorem IsO.of_bound' (h : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖) : f =O[l] g :=
  IsO.of_bound 1 <| by
    simp_rw [one_mul]
    exact h
#align asymptotics.is_O.of_bound' Asymptotics.IsO.of_bound'

theorem IsO.bound : f =O[l] g → ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isO_iff.1
#align asymptotics.is_O.bound Asymptotics.IsO.bound

/-- The Landau notation `f =o[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by an arbitrarily small constant
multiple of `‖g‖`. In other words, `‖f‖ / ‖g‖` tends to `0` along `l`, modulo division by zero
issues that are avoided by this definition. -/
irreducible_def IsOCat (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → IsOWith c l f g
#align asymptotics.is_o Asymptotics.IsOCat

-- mathport name: «expr =o[ ] »
notation:100 f " =o[" l "] " g:100 => IsOCat l f g

/-- Definition of `is_o` in terms of `is_O_with`. We record it in a lemma as we will set
`is_o` to be irreducible at the end of this file. -/
theorem isOCat_iff_forall_isOWith : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → IsOWith c l f g := by rw [is_o]
#align asymptotics.is_o_iff_forall_is_O_with Asymptotics.isOCat_iff_forall_isOWith

alias is_o_iff_forall_is_O_with ↔ is_o.forall_is_O_with is_o.of_is_O_with
#align asymptotics.is_o.forall_is_O_with Asymptotics.IsOCat.forall_isOWith
#align asymptotics.is_o.of_is_O_with Asymptotics.IsOCat.of_isOWith

/-- Definition of `is_o` in terms of filters. We record it in a lemma as we will set
`is_o` to be irreducible at the end of this file. -/
theorem isOCat_iff : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  simp only [is_o, is_O_with]
#align asymptotics.is_o_iff Asymptotics.isOCat_iff

alias is_o_iff ↔ is_o.bound is_o.of_bound
#align asymptotics.is_o.bound Asymptotics.IsOCat.bound
#align asymptotics.is_o.of_bound Asymptotics.IsOCat.of_bound

theorem IsOCat.def (h : f =o[l] g) (hc : 0 < c) : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isOCat_iff.1 h hc
#align asymptotics.is_o.def Asymptotics.IsOCat.def

theorem IsOCat.def' (h : f =o[l] g) (hc : 0 < c) : IsOWith c l f g :=
  isOWith_iff.2 <| isOCat_iff.1 h hc
#align asymptotics.is_o.def' Asymptotics.IsOCat.def'

end Defs

/-! ### Conversions -/


theorem IsOWith.isO (h : IsOWith c l f g) : f =O[l] g := by rw [is_O] <;> exact ⟨c, h⟩
#align asymptotics.is_O_with.is_O Asymptotics.IsOWith.isO

theorem IsOCat.isOWith (hgf : f =o[l] g) : IsOWith 1 l f g :=
  hgf.def' zero_lt_one
#align asymptotics.is_o.is_O_with Asymptotics.IsOCat.isOWith

theorem IsOCat.isO (hgf : f =o[l] g) : f =O[l] g :=
  hgf.IsOWith.IsO
#align asymptotics.is_o.is_O Asymptotics.IsOCat.isO

theorem IsO.isOWith : f =O[l] g → ∃ c : ℝ, IsOWith c l f g :=
  isO_iff_isOWith.1
#align asymptotics.is_O.is_O_with Asymptotics.IsO.isOWith

theorem IsOWith.weaken (h : IsOWith c l f g') (hc : c ≤ c') : IsOWith c' l f g' :=
  IsOWith.of_bound <|
    mem_of_superset h.bound fun x hx =>
      calc
        ‖f x‖ ≤ c * ‖g' x‖ := hx
        _ ≤ _ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
        
#align asymptotics.is_O_with.weaken Asymptotics.IsOWith.weaken

theorem IsOWith.exists_pos (h : IsOWith c l f g') : ∃ (c' : _)(H : 0 < c'), IsOWith c' l f g' :=
  ⟨max c 1, lt_of_lt_of_le zero_lt_one (le_max_right c 1), h.weaken <| le_max_left c 1⟩
#align asymptotics.is_O_with.exists_pos Asymptotics.IsOWith.exists_pos

theorem IsO.exists_pos (h : f =O[l] g') : ∃ (c : _)(H : 0 < c), IsOWith c l f g' :=
  let ⟨c, hc⟩ := h.IsOWith
  hc.exists_pos
#align asymptotics.is_O.exists_pos Asymptotics.IsO.exists_pos

theorem IsOWith.exists_nonneg (h : IsOWith c l f g') : ∃ (c' : _)(H : 0 ≤ c'), IsOWith c' l f g' :=
  let ⟨c, cpos, hc⟩ := h.exists_pos
  ⟨c, le_of_lt cpos, hc⟩
#align asymptotics.is_O_with.exists_nonneg Asymptotics.IsOWith.exists_nonneg

theorem IsO.exists_nonneg (h : f =O[l] g') : ∃ (c : _)(H : 0 ≤ c), IsOWith c l f g' :=
  let ⟨c, hc⟩ := h.IsOWith
  hc.exists_nonneg
#align asymptotics.is_O.exists_nonneg Asymptotics.IsO.exists_nonneg

/-- `f = O(g)` if and only if `is_O_with c f g` for all sufficiently large `c`. -/
theorem isO_iff_eventually_isOWith : f =O[l] g' ↔ ∀ᶠ c in atTop, IsOWith c l f g' :=
  isO_iff_isOWith.trans
    ⟨fun ⟨c, hc⟩ => mem_atTop_sets.2 ⟨c, fun c' hc' => hc.weaken hc'⟩, fun h => h.exists⟩
#align asymptotics.is_O_iff_eventually_is_O_with Asymptotics.isO_iff_eventually_isOWith

/-- `f = O(g)` if and only if `∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖` for all sufficiently large `c`. -/
theorem isO_iff_eventually : f =O[l] g' ↔ ∀ᶠ c in atTop, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g' x‖ :=
  isO_iff_eventually_isOWith.trans <| by simp only [is_O_with]
#align asymptotics.is_O_iff_eventually Asymptotics.isO_iff_eventually

theorem IsO.exists_mem_basis {ι} {p : ι → Prop} {s : ι → Set α} (h : f =O[l] g')
    (hb : l.HasBasis p s) : ∃ (c : ℝ)(hc : 0 < c)(i : ι)(hi : p i), ∀ x ∈ s i, ‖f x‖ ≤ c * ‖g' x‖ :=
  flip Exists₂.imp h.exists_pos fun c hc h => by
    simpa only [is_O_with_iff, hb.eventually_iff, exists_prop] using h
#align asymptotics.is_O.exists_mem_basis Asymptotics.IsO.exists_mem_basis

theorem isOWith_inv (hc : 0 < c) : IsOWith c⁻¹ l f g ↔ ∀ᶠ x in l, c * ‖f x‖ ≤ ‖g x‖ := by
  simp only [is_O_with, ← div_eq_inv_mul, le_div_iff' hc]
#align asymptotics.is_O_with_inv Asymptotics.isOWith_inv

-- We prove this lemma with strange assumptions to get two lemmas below automatically
theorem isOCat_iff_nat_mul_le_aux (h₀ : (∀ x, 0 ≤ ‖f x‖) ∨ ∀ x, 0 ≤ ‖g x‖) :
    f =o[l] g ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f x‖ ≤ ‖g x‖ :=
  by
  constructor
  · rintro H (_ | n)
    · refine' (H.def one_pos).mono fun x h₀' => _
      rw [Nat.cast_zero, MulZeroClass.zero_mul]
      refine' h₀.elim (fun hf => (hf x).trans _) fun hg => hg x
      rwa [one_mul] at h₀'
    · have : (0 : ℝ) < n.succ := Nat.cast_pos.2 n.succ_pos
      exact (is_O_with_inv this).1 (H.def' <| inv_pos.2 this)
  · refine' fun H => is_o_iff.2 fun ε ε0 => _
    rcases exists_nat_gt ε⁻¹ with ⟨n, hn⟩
    have hn₀ : (0 : ℝ) < n := (inv_pos.2 ε0).trans hn
    refine' ((is_O_with_inv hn₀).2 (H n)).bound.mono fun x hfg => _
    refine' hfg.trans (mul_le_mul_of_nonneg_right (inv_le_of_inv_le ε0 hn.le) _)
    refine' h₀.elim (fun hf => nonneg_of_mul_nonneg_right ((hf x).trans hfg) _) fun h => h x
    exact inv_pos.2 hn₀
#align asymptotics.is_o_iff_nat_mul_le_aux Asymptotics.isOCat_iff_nat_mul_le_aux

theorem isOCat_iff_nat_mul_le : f =o[l] g' ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f x‖ ≤ ‖g' x‖ :=
  isOCat_iff_nat_mul_le_aux (Or.inr fun x => norm_nonneg _)
#align asymptotics.is_o_iff_nat_mul_le Asymptotics.isOCat_iff_nat_mul_le

theorem isOCat_iff_nat_mul_le' : f' =o[l] g ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f' x‖ ≤ ‖g x‖ :=
  isOCat_iff_nat_mul_le_aux (Or.inl fun x => norm_nonneg _)
#align asymptotics.is_o_iff_nat_mul_le' Asymptotics.isOCat_iff_nat_mul_le'

/-! ### Subsingleton -/


@[nontriviality]
theorem isOCat_of_subsingleton [Subsingleton E'] : f' =o[l] g' :=
  IsOCat.of_bound fun c hc => by simp [Subsingleton.elim (f' _) 0, mul_nonneg hc.le]
#align asymptotics.is_o_of_subsingleton Asymptotics.isOCat_of_subsingleton

@[nontriviality]
theorem isO_of_subsingleton [Subsingleton E'] : f' =O[l] g' :=
  isOCat_of_subsingleton.IsO
#align asymptotics.is_O_of_subsingleton Asymptotics.isO_of_subsingleton

section congr

variable {f₁ f₂ : α → E} {g₁ g₂ : α → F}

/-! ### Congruence -/


theorem isOWith_congr (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    IsOWith c₁ l f₁ g₁ ↔ IsOWith c₂ l f₂ g₂ :=
  by
  unfold is_O_with
  subst c₂
  apply Filter.eventually_congr
  filter_upwards [hf, hg]with _ e₁ e₂
  rw [e₁, e₂]
#align asymptotics.is_O_with_congr Asymptotics.isOWith_congr

theorem IsOWith.congr' (h : IsOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂)
    (hg : g₁ =ᶠ[l] g₂) : IsOWith c₂ l f₂ g₂ :=
  (isOWith_congr hc hf hg).mp h
#align asymptotics.is_O_with.congr' Asymptotics.IsOWith.congr'

theorem IsOWith.congr (h : IsOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : ∀ x, f₁ x = f₂ x)
    (hg : ∀ x, g₁ x = g₂ x) : IsOWith c₂ l f₂ g₂ :=
  h.congr' hc (univ_mem' hf) (univ_mem' hg)
#align asymptotics.is_O_with.congr Asymptotics.IsOWith.congr

theorem IsOWith.congr_left (h : IsOWith c l f₁ g) (hf : ∀ x, f₁ x = f₂ x) : IsOWith c l f₂ g :=
  h.congr rfl hf fun _ => rfl
#align asymptotics.is_O_with.congr_left Asymptotics.IsOWith.congr_left

theorem IsOWith.congr_right (h : IsOWith c l f g₁) (hg : ∀ x, g₁ x = g₂ x) : IsOWith c l f g₂ :=
  h.congr rfl (fun _ => rfl) hg
#align asymptotics.is_O_with.congr_right Asymptotics.IsOWith.congr_right

theorem IsOWith.congr_const (h : IsOWith c₁ l f g) (hc : c₁ = c₂) : IsOWith c₂ l f g :=
  h.congr hc (fun _ => rfl) fun _ => rfl
#align asymptotics.is_O_with.congr_const Asymptotics.IsOWith.congr_const

theorem isO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =O[l] g₁ ↔ f₂ =O[l] g₂ :=
  by
  unfold is_O
  exact exists_congr fun c => is_O_with_congr rfl hf hg
#align asymptotics.is_O_congr Asymptotics.isO_congr

theorem IsO.congr' (h : f₁ =O[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =O[l] g₂ :=
  (isO_congr hf hg).mp h
#align asymptotics.is_O.congr' Asymptotics.IsO.congr'

theorem IsO.congr (h : f₁ =O[l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) : f₂ =O[l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)
#align asymptotics.is_O.congr Asymptotics.IsO.congr

theorem IsO.congr_left (h : f₁ =O[l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =O[l] g :=
  h.congr hf fun _ => rfl
#align asymptotics.is_O.congr_left Asymptotics.IsO.congr_left

theorem IsO.congr_right (h : f =O[l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =O[l] g₂ :=
  h.congr (fun _ => rfl) hg
#align asymptotics.is_O.congr_right Asymptotics.IsO.congr_right

theorem isOCat_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =o[l] g₁ ↔ f₂ =o[l] g₂ :=
  by
  unfold is_o
  exact forall₂_congr fun c hc => is_O_with_congr (Eq.refl c) hf hg
#align asymptotics.is_o_congr Asymptotics.isOCat_congr

theorem IsOCat.congr' (h : f₁ =o[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =o[l] g₂ :=
  (isOCat_congr hf hg).mp h
#align asymptotics.is_o.congr' Asymptotics.IsOCat.congr'

theorem IsOCat.congr (h : f₁ =o[l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    f₂ =o[l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)
#align asymptotics.is_o.congr Asymptotics.IsOCat.congr

theorem IsOCat.congr_left (h : f₁ =o[l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =o[l] g :=
  h.congr hf fun _ => rfl
#align asymptotics.is_o.congr_left Asymptotics.IsOCat.congr_left

theorem IsOCat.congr_right (h : f =o[l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =o[l] g₂ :=
  h.congr (fun _ => rfl) hg
#align asymptotics.is_o.congr_right Asymptotics.IsOCat.congr_right

@[trans]
theorem Filter.EventuallyEq.trans_isO {f₁ f₂ : α → E} {g : α → F} (hf : f₁ =ᶠ[l] f₂)
    (h : f₂ =O[l] g) : f₁ =O[l] g :=
  h.congr' hf.symm EventuallyEq.rfl
#align filter.eventually_eq.trans_is_O Filter.EventuallyEq.trans_isO

@[trans]
theorem Filter.EventuallyEq.trans_isOCat {f₁ f₂ : α → E} {g : α → F} (hf : f₁ =ᶠ[l] f₂)
    (h : f₂ =o[l] g) : f₁ =o[l] g :=
  h.congr' hf.symm EventuallyEq.rfl
#align filter.eventually_eq.trans_is_o Filter.EventuallyEq.trans_isOCat

@[trans]
theorem IsO.trans_eventuallyEq {f : α → E} {g₁ g₂ : α → F} (h : f =O[l] g₁) (hg : g₁ =ᶠ[l] g₂) :
    f =O[l] g₂ :=
  h.congr' EventuallyEq.rfl hg
#align asymptotics.is_O.trans_eventually_eq Asymptotics.IsO.trans_eventuallyEq

@[trans]
theorem IsOCat.trans_eventuallyEq {f : α → E} {g₁ g₂ : α → F} (h : f =o[l] g₁) (hg : g₁ =ᶠ[l] g₂) :
    f =o[l] g₂ :=
  h.congr' EventuallyEq.rfl hg
#align asymptotics.is_o.trans_eventually_eq Asymptotics.IsOCat.trans_eventuallyEq

end congr

/-! ### Filter operations and transitivity -/


theorem IsOWith.comp_tendsto (hcfg : IsOWith c l f g) {k : β → α} {l' : Filter β}
    (hk : Tendsto k l' l) : IsOWith c l' (f ∘ k) (g ∘ k) :=
  IsOWith.of_bound <| hk hcfg.bound
#align asymptotics.is_O_with.comp_tendsto Asymptotics.IsOWith.comp_tendsto

theorem IsO.comp_tendsto (hfg : f =O[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) :
    (f ∘ k) =O[l'] (g ∘ k) :=
  isO_iff_isOWith.2 <| hfg.IsOWith.imp fun c h => h.comp_tendsto hk
#align asymptotics.is_O.comp_tendsto Asymptotics.IsO.comp_tendsto

theorem IsOCat.comp_tendsto (hfg : f =o[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) :
    (f ∘ k) =o[l'] (g ∘ k) :=
  IsOCat.of_isOWith fun c cpos => (hfg.forall_isOWith cpos).comp_tendsto hk
#align asymptotics.is_o.comp_tendsto Asymptotics.IsOCat.comp_tendsto

@[simp]
theorem isOWith_map {k : β → α} {l : Filter β} :
    IsOWith c (map k l) f g ↔ IsOWith c l (f ∘ k) (g ∘ k) :=
  by
  unfold is_O_with
  exact eventually_map
#align asymptotics.is_O_with_map Asymptotics.isOWith_map

@[simp]
theorem isO_map {k : β → α} {l : Filter β} : f =O[map k l] g ↔ (f ∘ k) =O[l] (g ∘ k) := by
  simp only [is_O, is_O_with_map]
#align asymptotics.is_O_map Asymptotics.isO_map

@[simp]
theorem isOCat_map {k : β → α} {l : Filter β} : f =o[map k l] g ↔ (f ∘ k) =o[l] (g ∘ k) := by
  simp only [is_o, is_O_with_map]
#align asymptotics.is_o_map Asymptotics.isOCat_map

theorem IsOWith.mono (h : IsOWith c l' f g) (hl : l ≤ l') : IsOWith c l f g :=
  IsOWith.of_bound <| hl h.bound
#align asymptotics.is_O_with.mono Asymptotics.IsOWith.mono

theorem IsO.mono (h : f =O[l'] g) (hl : l ≤ l') : f =O[l] g :=
  isO_iff_isOWith.2 <| h.IsOWith.imp fun c h => h.mono hl
#align asymptotics.is_O.mono Asymptotics.IsO.mono

theorem IsOCat.mono (h : f =o[l'] g) (hl : l ≤ l') : f =o[l] g :=
  IsOCat.of_isOWith fun c cpos => (h.forall_isOWith cpos).mono hl
#align asymptotics.is_o.mono Asymptotics.IsOCat.mono

theorem IsOWith.trans (hfg : IsOWith c l f g) (hgk : IsOWith c' l g k) (hc : 0 ≤ c) :
    IsOWith (c * c') l f k := by
  unfold is_O_with at *
  filter_upwards [hfg, hgk]with x hx hx'
  calc
    ‖f x‖ ≤ c * ‖g x‖ := hx
    _ ≤ c * (c' * ‖k x‖) := (mul_le_mul_of_nonneg_left hx' hc)
    _ = c * c' * ‖k x‖ := (mul_assoc _ _ _).symm
    
#align asymptotics.is_O_with.trans Asymptotics.IsOWith.trans

@[trans]
theorem IsO.trans {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g) (hgk : g =O[l] k) :
    f =O[l] k :=
  let ⟨c, cnonneg, hc⟩ := hfg.exists_nonneg
  let ⟨c', hc'⟩ := hgk.IsOWith
  (hc.trans hc' cnonneg).IsO
#align asymptotics.is_O.trans Asymptotics.IsO.trans

theorem IsOCat.trans_isOWith (hfg : f =o[l] g) (hgk : IsOWith c l g k) (hc : 0 < c) : f =o[l] k :=
  by
  unfold is_o at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact ((hfg this).trans hgk this.le).congr_const (div_mul_cancel _ hc.ne')
#align asymptotics.is_o.trans_is_O_with Asymptotics.IsOCat.trans_isOWith

@[trans]
theorem IsOCat.trans_isO {f : α → E} {g : α → F} {k : α → G'} (hfg : f =o[l] g) (hgk : g =O[l] k) :
    f =o[l] k :=
  let ⟨c, cpos, hc⟩ := hgk.exists_pos
  hfg.trans_isOWith hc cpos
#align asymptotics.is_o.trans_is_O Asymptotics.IsOCat.trans_isO

theorem IsOWith.trans_isOCat (hfg : IsOWith c l f g) (hgk : g =o[l] k) (hc : 0 < c) : f =o[l] k :=
  by
  unfold is_o at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact (hfg.trans (hgk this) hc.le).congr_const (mul_div_cancel' _ hc.ne')
#align asymptotics.is_O_with.trans_is_o Asymptotics.IsOWith.trans_isOCat

@[trans]
theorem IsO.trans_isOCat {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g) (hgk : g =o[l] k) :
    f =o[l] k :=
  let ⟨c, cpos, hc⟩ := hfg.exists_pos
  hc.trans_isOCat hgk cpos
#align asymptotics.is_O.trans_is_o Asymptotics.IsO.trans_isOCat

@[trans]
theorem IsOCat.trans {f : α → E} {g : α → F} {k : α → G} (hfg : f =o[l] g) (hgk : g =o[l] k) :
    f =o[l] k :=
  hfg.trans_isOWith hgk.IsOWith one_pos
#align asymptotics.is_o.trans Asymptotics.IsOCat.trans

theorem Filter.Eventually.trans_isO {f : α → E} {g : α → F'} {k : α → G}
    (hfg : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖) (hgk : g =O[l] k) : f =O[l] k :=
  (IsO.of_bound' hfg).trans hgk
#align filter.eventually.trans_is_O Filter.Eventually.trans_isO

theorem Filter.Eventually.isO {f : α → E} {g : α → ℝ} {l : Filter α}
    (hfg : ∀ᶠ x in l, ‖f x‖ ≤ g x) : f =O[l] g :=
  IsO.of_bound' <| hfg.mono fun x hx => hx.trans <| Real.le_norm_self _
#align filter.eventually.is_O Filter.Eventually.isO

section

variable (l)

theorem isOWith_of_le' (hfg : ∀ x, ‖f x‖ ≤ c * ‖g x‖) : IsOWith c l f g :=
  IsOWith.of_bound <| univ_mem' hfg
#align asymptotics.is_O_with_of_le' Asymptotics.isOWith_of_le'

theorem isOWith_of_le (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) : IsOWith 1 l f g :=
  isOWith_of_le' l fun x => by
    rw [one_mul]
    exact hfg x
#align asymptotics.is_O_with_of_le Asymptotics.isOWith_of_le

theorem isO_of_le' (hfg : ∀ x, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g :=
  (isOWith_of_le' l hfg).IsO
#align asymptotics.is_O_of_le' Asymptotics.isO_of_le'

theorem isO_of_le (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) : f =O[l] g :=
  (isOWith_of_le l hfg).IsO
#align asymptotics.is_O_of_le Asymptotics.isO_of_le

end

theorem isOWith_refl (f : α → E) (l : Filter α) : IsOWith 1 l f f :=
  isOWith_of_le l fun _ => le_rfl
#align asymptotics.is_O_with_refl Asymptotics.isOWith_refl

theorem isO_refl (f : α → E) (l : Filter α) : f =O[l] f :=
  (isOWith_refl f l).IsO
#align asymptotics.is_O_refl Asymptotics.isO_refl

theorem IsOWith.trans_le (hfg : IsOWith c l f g) (hgk : ∀ x, ‖g x‖ ≤ ‖k x‖) (hc : 0 ≤ c) :
    IsOWith c l f k :=
  (hfg.trans (isOWith_of_le l hgk) hc).congr_const <| mul_one c
#align asymptotics.is_O_with.trans_le Asymptotics.IsOWith.trans_le

theorem IsO.trans_le (hfg : f =O[l] g') (hgk : ∀ x, ‖g' x‖ ≤ ‖k x‖) : f =O[l] k :=
  hfg.trans (isO_of_le l hgk)
#align asymptotics.is_O.trans_le Asymptotics.IsO.trans_le

theorem IsOCat.trans_le (hfg : f =o[l] g) (hgk : ∀ x, ‖g x‖ ≤ ‖k x‖) : f =o[l] k :=
  hfg.trans_isOWith (isOWith_of_le _ hgk) zero_lt_one
#align asymptotics.is_o.trans_le Asymptotics.IsOCat.trans_le

theorem isOCat_irrefl' (h : ∃ᶠ x in l, ‖f' x‖ ≠ 0) : ¬f' =o[l] f' :=
  by
  intro ho
  rcases((ho.bound one_half_pos).and_frequently h).exists with ⟨x, hle, hne⟩
  rw [one_div, ← div_eq_inv_mul] at hle
  exact (half_lt_self (lt_of_le_of_ne (norm_nonneg _) hne.symm)).not_le hle
#align asymptotics.is_o_irrefl' Asymptotics.isOCat_irrefl'

theorem isOCat_irrefl (h : ∃ᶠ x in l, f'' x ≠ 0) : ¬f'' =o[l] f'' :=
  isOCat_irrefl' <| h.mono fun x => norm_ne_zero_iff.mpr
#align asymptotics.is_o_irrefl Asymptotics.isOCat_irrefl

theorem IsO.not_isOCat (h : f'' =O[l] g') (hf : ∃ᶠ x in l, f'' x ≠ 0) : ¬g' =o[l] f'' := fun h' =>
  isOCat_irrefl hf (h.trans_isOCat h')
#align asymptotics.is_O.not_is_o Asymptotics.IsO.not_isOCat

theorem IsOCat.not_isO (h : f'' =o[l] g') (hf : ∃ᶠ x in l, f'' x ≠ 0) : ¬g' =O[l] f'' := fun h' =>
  isOCat_irrefl hf (h.trans_isO h')
#align asymptotics.is_o.not_is_O Asymptotics.IsOCat.not_isO

section Bot

variable (c f g)

@[simp]
theorem isOWith_bot : IsOWith c ⊥ f g :=
  IsOWith.of_bound <| trivial
#align asymptotics.is_O_with_bot Asymptotics.isOWith_bot

@[simp]
theorem isO_bot : f =O[⊥] g :=
  (isOWith_bot 1 f g).IsO
#align asymptotics.is_O_bot Asymptotics.isO_bot

@[simp]
theorem isOCat_bot : f =o[⊥] g :=
  IsOCat.of_isOWith fun c _ => isOWith_bot c f g
#align asymptotics.is_o_bot Asymptotics.isOCat_bot

end Bot

@[simp]
theorem isOWith_pure {x} : IsOWith c (pure x) f g ↔ ‖f x‖ ≤ c * ‖g x‖ :=
  isOWith_iff
#align asymptotics.is_O_with_pure Asymptotics.isOWith_pure

theorem IsOWith.sup (h : IsOWith c l f g) (h' : IsOWith c l' f g) : IsOWith c (l ⊔ l') f g :=
  IsOWith.of_bound <| mem_sup.2 ⟨h.bound, h'.bound⟩
#align asymptotics.is_O_with.sup Asymptotics.IsOWith.sup

theorem IsOWith.sup' (h : IsOWith c l f g') (h' : IsOWith c' l' f g') :
    IsOWith (max c c') (l ⊔ l') f g' :=
  IsOWith.of_bound <|
    mem_sup.2 ⟨(h.weaken <| le_max_left c c').bound, (h'.weaken <| le_max_right c c').bound⟩
#align asymptotics.is_O_with.sup' Asymptotics.IsOWith.sup'

theorem IsO.sup (h : f =O[l] g') (h' : f =O[l'] g') : f =O[l ⊔ l'] g' :=
  let ⟨c, hc⟩ := h.IsOWith
  let ⟨c', hc'⟩ := h'.IsOWith
  (hc.sup' hc').IsO
#align asymptotics.is_O.sup Asymptotics.IsO.sup

theorem IsOCat.sup (h : f =o[l] g) (h' : f =o[l'] g) : f =o[l ⊔ l'] g :=
  IsOCat.of_isOWith fun c cpos => (h.forall_isOWith cpos).sup (h'.forall_isOWith cpos)
#align asymptotics.is_o.sup Asymptotics.IsOCat.sup

@[simp]
theorem isO_sup : f =O[l ⊔ l'] g' ↔ f =O[l] g' ∧ f =O[l'] g' :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩
#align asymptotics.is_O_sup Asymptotics.isO_sup

@[simp]
theorem isOCat_sup : f =o[l ⊔ l'] g ↔ f =o[l] g ∧ f =o[l'] g :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩
#align asymptotics.is_o_sup Asymptotics.isOCat_sup

theorem isOWith_insert [TopologicalSpace α] {x : α} {s : Set α} {C : ℝ} {g : α → E} {g' : α → F}
    (h : ‖g x‖ ≤ C * ‖g' x‖) : IsOWith C (𝓝[insert x s] x) g g' ↔ IsOWith C (𝓝[s] x) g g' := by
  simp_rw [is_O_with, nhdsWithin_insert, eventually_sup, eventually_pure, h, true_and_iff]
#align asymptotics.is_O_with_insert Asymptotics.isOWith_insert

theorem IsOWith.insert [TopologicalSpace α] {x : α} {s : Set α} {C : ℝ} {g : α → E} {g' : α → F}
    (h1 : IsOWith C (𝓝[s] x) g g') (h2 : ‖g x‖ ≤ C * ‖g' x‖) : IsOWith C (𝓝[insert x s] x) g g' :=
  (isOWith_insert h2).mpr h1
#align asymptotics.is_O_with.insert Asymptotics.IsOWith.insert

theorem isOCat_insert [TopologicalSpace α] {x : α} {s : Set α} {g : α → E'} {g' : α → F'}
    (h : g x = 0) : g =o[𝓝[insert x s] x] g' ↔ g =o[𝓝[s] x] g' :=
  by
  simp_rw [is_o]
  refine' forall_congr' fun c => forall_congr' fun hc => _
  rw [is_O_with_insert]
  rw [h, norm_zero]
  exact mul_nonneg hc.le (norm_nonneg _)
#align asymptotics.is_o_insert Asymptotics.isOCat_insert

theorem IsOCat.insert [TopologicalSpace α] {x : α} {s : Set α} {g : α → E'} {g' : α → F'}
    (h1 : g =o[𝓝[s] x] g') (h2 : g x = 0) : g =o[𝓝[insert x s] x] g' :=
  (isOCat_insert h2).mpr h1
#align asymptotics.is_o.insert Asymptotics.IsOCat.insert

/-! ### Simplification : norm, abs -/


section NormAbs

variable {u v : α → ℝ}

@[simp]
theorem isOWith_norm_right : (IsOWith c l f fun x => ‖g' x‖) ↔ IsOWith c l f g' := by
  simp only [is_O_with, norm_norm]
#align asymptotics.is_O_with_norm_right Asymptotics.isOWith_norm_right

@[simp]
theorem isOWith_abs_right : (IsOWith c l f fun x => |u x|) ↔ IsOWith c l f u :=
  @isOWith_norm_right _ _ _ _ _ _ f u l
#align asymptotics.is_O_with_abs_right Asymptotics.isOWith_abs_right

alias is_O_with_norm_right ↔ is_O_with.of_norm_right is_O_with.norm_right
#align asymptotics.is_O_with.of_norm_right Asymptotics.IsOWith.of_norm_right
#align asymptotics.is_O_with.norm_right Asymptotics.IsOWith.norm_right

alias is_O_with_abs_right ↔ is_O_with.of_abs_right is_O_with.abs_right
#align asymptotics.is_O_with.of_abs_right Asymptotics.IsOWith.of_abs_right
#align asymptotics.is_O_with.abs_right Asymptotics.IsOWith.abs_right

@[simp]
theorem isO_norm_right : (f =O[l] fun x => ‖g' x‖) ↔ f =O[l] g' :=
  by
  unfold is_O
  exact exists_congr fun _ => is_O_with_norm_right
#align asymptotics.is_O_norm_right Asymptotics.isO_norm_right

@[simp]
theorem isO_abs_right : (f =O[l] fun x => |u x|) ↔ f =O[l] u :=
  @isO_norm_right _ _ ℝ _ _ _ _ _
#align asymptotics.is_O_abs_right Asymptotics.isO_abs_right

alias is_O_norm_right ↔ is_O.of_norm_right is_O.norm_right
#align asymptotics.is_O.of_norm_right Asymptotics.IsO.of_norm_right
#align asymptotics.is_O.norm_right Asymptotics.IsO.norm_right

alias is_O_abs_right ↔ is_O.of_abs_right is_O.abs_right
#align asymptotics.is_O.of_abs_right Asymptotics.IsO.of_abs_right
#align asymptotics.is_O.abs_right Asymptotics.IsO.abs_right

@[simp]
theorem isOCat_norm_right : (f =o[l] fun x => ‖g' x‖) ↔ f =o[l] g' :=
  by
  unfold is_o
  exact forall₂_congr fun _ _ => is_O_with_norm_right
#align asymptotics.is_o_norm_right Asymptotics.isOCat_norm_right

@[simp]
theorem isOCat_abs_right : (f =o[l] fun x => |u x|) ↔ f =o[l] u :=
  @isOCat_norm_right _ _ ℝ _ _ _ _ _
#align asymptotics.is_o_abs_right Asymptotics.isOCat_abs_right

alias is_o_norm_right ↔ is_o.of_norm_right is_o.norm_right
#align asymptotics.is_o.of_norm_right Asymptotics.IsOCat.of_norm_right
#align asymptotics.is_o.norm_right Asymptotics.IsOCat.norm_right

alias is_o_abs_right ↔ is_o.of_abs_right is_o.abs_right
#align asymptotics.is_o.of_abs_right Asymptotics.IsOCat.of_abs_right
#align asymptotics.is_o.abs_right Asymptotics.IsOCat.abs_right

@[simp]
theorem isOWith_norm_left : IsOWith c l (fun x => ‖f' x‖) g ↔ IsOWith c l f' g := by
  simp only [is_O_with, norm_norm]
#align asymptotics.is_O_with_norm_left Asymptotics.isOWith_norm_left

@[simp]
theorem isOWith_abs_left : IsOWith c l (fun x => |u x|) g ↔ IsOWith c l u g :=
  @isOWith_norm_left _ _ _ _ _ _ g u l
#align asymptotics.is_O_with_abs_left Asymptotics.isOWith_abs_left

alias is_O_with_norm_left ↔ is_O_with.of_norm_left is_O_with.norm_left
#align asymptotics.is_O_with.of_norm_left Asymptotics.IsOWith.of_norm_left
#align asymptotics.is_O_with.norm_left Asymptotics.IsOWith.norm_left

alias is_O_with_abs_left ↔ is_O_with.of_abs_left is_O_with.abs_left
#align asymptotics.is_O_with.of_abs_left Asymptotics.IsOWith.of_abs_left
#align asymptotics.is_O_with.abs_left Asymptotics.IsOWith.abs_left

@[simp]
theorem isO_norm_left : (fun x => ‖f' x‖) =O[l] g ↔ f' =O[l] g :=
  by
  unfold is_O
  exact exists_congr fun _ => is_O_with_norm_left
#align asymptotics.is_O_norm_left Asymptotics.isO_norm_left

@[simp]
theorem isO_abs_left : (fun x => |u x|) =O[l] g ↔ u =O[l] g :=
  @isO_norm_left _ _ _ _ _ g u l
#align asymptotics.is_O_abs_left Asymptotics.isO_abs_left

alias is_O_norm_left ↔ is_O.of_norm_left is_O.norm_left
#align asymptotics.is_O.of_norm_left Asymptotics.IsO.of_norm_left
#align asymptotics.is_O.norm_left Asymptotics.IsO.norm_left

alias is_O_abs_left ↔ is_O.of_abs_left is_O.abs_left
#align asymptotics.is_O.of_abs_left Asymptotics.IsO.of_abs_left
#align asymptotics.is_O.abs_left Asymptotics.IsO.abs_left

@[simp]
theorem isOCat_norm_left : (fun x => ‖f' x‖) =o[l] g ↔ f' =o[l] g :=
  by
  unfold is_o
  exact forall₂_congr fun _ _ => is_O_with_norm_left
#align asymptotics.is_o_norm_left Asymptotics.isOCat_norm_left

@[simp]
theorem isOCat_abs_left : (fun x => |u x|) =o[l] g ↔ u =o[l] g :=
  @isOCat_norm_left _ _ _ _ _ g u l
#align asymptotics.is_o_abs_left Asymptotics.isOCat_abs_left

alias is_o_norm_left ↔ is_o.of_norm_left is_o.norm_left
#align asymptotics.is_o.of_norm_left Asymptotics.IsOCat.of_norm_left
#align asymptotics.is_o.norm_left Asymptotics.IsOCat.norm_left

alias is_o_abs_left ↔ is_o.of_abs_left is_o.abs_left
#align asymptotics.is_o.of_abs_left Asymptotics.IsOCat.of_abs_left
#align asymptotics.is_o.abs_left Asymptotics.IsOCat.abs_left

theorem isOWith_norm_norm : (IsOWith c l (fun x => ‖f' x‖) fun x => ‖g' x‖) ↔ IsOWith c l f' g' :=
  isOWith_norm_left.trans isOWith_norm_right
#align asymptotics.is_O_with_norm_norm Asymptotics.isOWith_norm_norm

theorem isOWith_abs_abs : (IsOWith c l (fun x => |u x|) fun x => |v x|) ↔ IsOWith c l u v :=
  isOWith_abs_left.trans isOWith_abs_right
#align asymptotics.is_O_with_abs_abs Asymptotics.isOWith_abs_abs

alias is_O_with_norm_norm ↔ is_O_with.of_norm_norm is_O_with.norm_norm
#align asymptotics.is_O_with.of_norm_norm Asymptotics.IsOWith.of_norm_norm
#align asymptotics.is_O_with.norm_norm Asymptotics.IsOWith.norm_norm

alias is_O_with_abs_abs ↔ is_O_with.of_abs_abs is_O_with.abs_abs
#align asymptotics.is_O_with.of_abs_abs Asymptotics.IsOWith.of_abs_abs
#align asymptotics.is_O_with.abs_abs Asymptotics.IsOWith.abs_abs

theorem isO_norm_norm : ((fun x => ‖f' x‖) =O[l] fun x => ‖g' x‖) ↔ f' =O[l] g' :=
  isO_norm_left.trans isO_norm_right
#align asymptotics.is_O_norm_norm Asymptotics.isO_norm_norm

theorem isO_abs_abs : ((fun x => |u x|) =O[l] fun x => |v x|) ↔ u =O[l] v :=
  isO_abs_left.trans isO_abs_right
#align asymptotics.is_O_abs_abs Asymptotics.isO_abs_abs

alias is_O_norm_norm ↔ is_O.of_norm_norm is_O.norm_norm
#align asymptotics.is_O.of_norm_norm Asymptotics.IsO.of_norm_norm
#align asymptotics.is_O.norm_norm Asymptotics.IsO.norm_norm

alias is_O_abs_abs ↔ is_O.of_abs_abs is_O.abs_abs
#align asymptotics.is_O.of_abs_abs Asymptotics.IsO.of_abs_abs
#align asymptotics.is_O.abs_abs Asymptotics.IsO.abs_abs

theorem isOCat_norm_norm : ((fun x => ‖f' x‖) =o[l] fun x => ‖g' x‖) ↔ f' =o[l] g' :=
  isOCat_norm_left.trans isOCat_norm_right
#align asymptotics.is_o_norm_norm Asymptotics.isOCat_norm_norm

theorem isOCat_abs_abs : ((fun x => |u x|) =o[l] fun x => |v x|) ↔ u =o[l] v :=
  isOCat_abs_left.trans isOCat_abs_right
#align asymptotics.is_o_abs_abs Asymptotics.isOCat_abs_abs

alias is_o_norm_norm ↔ is_o.of_norm_norm is_o.norm_norm
#align asymptotics.is_o.of_norm_norm Asymptotics.IsOCat.of_norm_norm
#align asymptotics.is_o.norm_norm Asymptotics.IsOCat.norm_norm

alias is_o_abs_abs ↔ is_o.of_abs_abs is_o.abs_abs
#align asymptotics.is_o.of_abs_abs Asymptotics.IsOCat.of_abs_abs
#align asymptotics.is_o.abs_abs Asymptotics.IsOCat.abs_abs

end NormAbs

/-! ### Simplification: negate -/


@[simp]
theorem isOWith_neg_right : (IsOWith c l f fun x => -g' x) ↔ IsOWith c l f g' := by
  simp only [is_O_with, norm_neg]
#align asymptotics.is_O_with_neg_right Asymptotics.isOWith_neg_right

alias is_O_with_neg_right ↔ is_O_with.of_neg_right is_O_with.neg_right
#align asymptotics.is_O_with.of_neg_right Asymptotics.IsOWith.of_neg_right
#align asymptotics.is_O_with.neg_right Asymptotics.IsOWith.neg_right

@[simp]
theorem isO_neg_right : (f =O[l] fun x => -g' x) ↔ f =O[l] g' :=
  by
  unfold is_O
  exact exists_congr fun _ => is_O_with_neg_right
#align asymptotics.is_O_neg_right Asymptotics.isO_neg_right

alias is_O_neg_right ↔ is_O.of_neg_right is_O.neg_right
#align asymptotics.is_O.of_neg_right Asymptotics.IsO.of_neg_right
#align asymptotics.is_O.neg_right Asymptotics.IsO.neg_right

@[simp]
theorem isOCat_neg_right : (f =o[l] fun x => -g' x) ↔ f =o[l] g' :=
  by
  unfold is_o
  exact forall₂_congr fun _ _ => is_O_with_neg_right
#align asymptotics.is_o_neg_right Asymptotics.isOCat_neg_right

alias is_o_neg_right ↔ is_o.of_neg_right is_o.neg_right
#align asymptotics.is_o.of_neg_right Asymptotics.IsOCat.of_neg_right
#align asymptotics.is_o.neg_right Asymptotics.IsOCat.neg_right

@[simp]
theorem isOWith_neg_left : IsOWith c l (fun x => -f' x) g ↔ IsOWith c l f' g := by
  simp only [is_O_with, norm_neg]
#align asymptotics.is_O_with_neg_left Asymptotics.isOWith_neg_left

alias is_O_with_neg_left ↔ is_O_with.of_neg_left is_O_with.neg_left
#align asymptotics.is_O_with.of_neg_left Asymptotics.IsOWith.of_neg_left
#align asymptotics.is_O_with.neg_left Asymptotics.IsOWith.neg_left

@[simp]
theorem isO_neg_left : (fun x => -f' x) =O[l] g ↔ f' =O[l] g :=
  by
  unfold is_O
  exact exists_congr fun _ => is_O_with_neg_left
#align asymptotics.is_O_neg_left Asymptotics.isO_neg_left

alias is_O_neg_left ↔ is_O.of_neg_left is_O.neg_left
#align asymptotics.is_O.of_neg_left Asymptotics.IsO.of_neg_left
#align asymptotics.is_O.neg_left Asymptotics.IsO.neg_left

@[simp]
theorem isOCat_neg_left : (fun x => -f' x) =o[l] g ↔ f' =o[l] g :=
  by
  unfold is_o
  exact forall₂_congr fun _ _ => is_O_with_neg_left
#align asymptotics.is_o_neg_left Asymptotics.isOCat_neg_left

alias is_o_neg_left ↔ is_o.of_neg_right is_o.neg_left
#align asymptotics.is_o.of_neg_right Asymptotics.IsOCat.of_neg_right
#align asymptotics.is_o.neg_left Asymptotics.IsOCat.neg_left

/-! ### Product of functions (right) -/


theorem isOWith_fst_prod : IsOWith 1 l f' fun x => (f' x, g' x) :=
  isOWith_of_le l fun x => le_max_left _ _
#align asymptotics.is_O_with_fst_prod Asymptotics.isOWith_fst_prod

theorem isOWith_snd_prod : IsOWith 1 l g' fun x => (f' x, g' x) :=
  isOWith_of_le l fun x => le_max_right _ _
#align asymptotics.is_O_with_snd_prod Asymptotics.isOWith_snd_prod

theorem isO_fst_prod : f' =O[l] fun x => (f' x, g' x) :=
  isOWith_fst_prod.IsO
#align asymptotics.is_O_fst_prod Asymptotics.isO_fst_prod

theorem isO_snd_prod : g' =O[l] fun x => (f' x, g' x) :=
  isOWith_snd_prod.IsO
#align asymptotics.is_O_snd_prod Asymptotics.isO_snd_prod

theorem isO_fst_prod' {f' : α → E' × F'} : (fun x => (f' x).1) =O[l] f' := by
  simpa [is_O, is_O_with] using is_O_fst_prod
#align asymptotics.is_O_fst_prod' Asymptotics.isO_fst_prod'

theorem isO_snd_prod' {f' : α → E' × F'} : (fun x => (f' x).2) =O[l] f' := by
  simpa [is_O, is_O_with] using is_O_snd_prod
#align asymptotics.is_O_snd_prod' Asymptotics.isO_snd_prod'

section

variable (f' k')

theorem IsOWith.prod_rightl (h : IsOWith c l f g') (hc : 0 ≤ c) :
    IsOWith c l f fun x => (g' x, k' x) :=
  (h.trans isOWith_fst_prod hc).congr_const (mul_one c)
#align asymptotics.is_O_with.prod_rightl Asymptotics.IsOWith.prod_rightl

theorem IsO.prod_rightl (h : f =O[l] g') : f =O[l] fun x => (g' x, k' x) :=
  let ⟨c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightl k' cnonneg).IsO
#align asymptotics.is_O.prod_rightl Asymptotics.IsO.prod_rightl

theorem IsOCat.prod_rightl (h : f =o[l] g') : f =o[l] fun x => (g' x, k' x) :=
  IsOCat.of_isOWith fun c cpos => (h.forall_isOWith cpos).prod_rightl k' cpos.le
#align asymptotics.is_o.prod_rightl Asymptotics.IsOCat.prod_rightl

theorem IsOWith.prod_rightr (h : IsOWith c l f g') (hc : 0 ≤ c) :
    IsOWith c l f fun x => (f' x, g' x) :=
  (h.trans isOWith_snd_prod hc).congr_const (mul_one c)
#align asymptotics.is_O_with.prod_rightr Asymptotics.IsOWith.prod_rightr

theorem IsO.prod_rightr (h : f =O[l] g') : f =O[l] fun x => (f' x, g' x) :=
  let ⟨c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightr f' cnonneg).IsO
#align asymptotics.is_O.prod_rightr Asymptotics.IsO.prod_rightr

theorem IsOCat.prod_rightr (h : f =o[l] g') : f =o[l] fun x => (f' x, g' x) :=
  IsOCat.of_isOWith fun c cpos => (h.forall_isOWith cpos).prod_rightr f' cpos.le
#align asymptotics.is_o.prod_rightr Asymptotics.IsOCat.prod_rightr

end

theorem IsOWith.prod_left_same (hf : IsOWith c l f' k') (hg : IsOWith c l g' k') :
    IsOWith c l (fun x => (f' x, g' x)) k' := by
  rw [is_O_with_iff] at * <;> filter_upwards [hf, hg]with x using max_le
#align asymptotics.is_O_with.prod_left_same Asymptotics.IsOWith.prod_left_same

theorem IsOWith.prod_left (hf : IsOWith c l f' k') (hg : IsOWith c' l g' k') :
    IsOWith (max c c') l (fun x => (f' x, g' x)) k' :=
  (hf.weaken <| le_max_left c c').prod_left_same (hg.weaken <| le_max_right c c')
#align asymptotics.is_O_with.prod_left Asymptotics.IsOWith.prod_left

theorem IsOWith.prod_left_fst (h : IsOWith c l (fun x => (f' x, g' x)) k') : IsOWith c l f' k' :=
  (isOWith_fst_prod.trans h zero_le_one).congr_const <| one_mul c
#align asymptotics.is_O_with.prod_left_fst Asymptotics.IsOWith.prod_left_fst

theorem IsOWith.prod_left_snd (h : IsOWith c l (fun x => (f' x, g' x)) k') : IsOWith c l g' k' :=
  (isOWith_snd_prod.trans h zero_le_one).congr_const <| one_mul c
#align asymptotics.is_O_with.prod_left_snd Asymptotics.IsOWith.prod_left_snd

theorem isOWith_prod_left :
    IsOWith c l (fun x => (f' x, g' x)) k' ↔ IsOWith c l f' k' ∧ IsOWith c l g' k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left_same h.2⟩
#align asymptotics.is_O_with_prod_left Asymptotics.isOWith_prod_left

theorem IsO.prod_left (hf : f' =O[l] k') (hg : g' =O[l] k') : (fun x => (f' x, g' x)) =O[l] k' :=
  let ⟨c, hf⟩ := hf.IsOWith
  let ⟨c', hg⟩ := hg.IsOWith
  (hf.prodLeft hg).IsO
#align asymptotics.is_O.prod_left Asymptotics.IsO.prod_left

theorem IsO.prod_left_fst : (fun x => (f' x, g' x)) =O[l] k' → f' =O[l] k' :=
  IsO.trans isO_fst_prod
#align asymptotics.is_O.prod_left_fst Asymptotics.IsO.prod_left_fst

theorem IsO.prod_left_snd : (fun x => (f' x, g' x)) =O[l] k' → g' =O[l] k' :=
  IsO.trans isO_snd_prod
#align asymptotics.is_O.prod_left_snd Asymptotics.IsO.prod_left_snd

@[simp]
theorem isO_prod_left : (fun x => (f' x, g' x)) =O[l] k' ↔ f' =O[l] k' ∧ g' =O[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prodLeft h.2⟩
#align asymptotics.is_O_prod_left Asymptotics.isO_prod_left

theorem IsOCat.prod_left (hf : f' =o[l] k') (hg : g' =o[l] k') : (fun x => (f' x, g' x)) =o[l] k' :=
  IsOCat.of_isOWith fun c hc => (hf.forall_isOWith hc).prod_left_same (hg.forall_isOWith hc)
#align asymptotics.is_o.prod_left Asymptotics.IsOCat.prod_left

theorem IsOCat.prod_left_fst : (fun x => (f' x, g' x)) =o[l] k' → f' =o[l] k' :=
  IsO.trans_isOCat isO_fst_prod
#align asymptotics.is_o.prod_left_fst Asymptotics.IsOCat.prod_left_fst

theorem IsOCat.prod_left_snd : (fun x => (f' x, g' x)) =o[l] k' → g' =o[l] k' :=
  IsO.trans_isOCat isO_snd_prod
#align asymptotics.is_o.prod_left_snd Asymptotics.IsOCat.prod_left_snd

@[simp]
theorem isOCat_prod_left : (fun x => (f' x, g' x)) =o[l] k' ↔ f' =o[l] k' ∧ g' =o[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prodLeft h.2⟩
#align asymptotics.is_o_prod_left Asymptotics.isOCat_prod_left

theorem IsOWith.eq_zero_imp (h : IsOWith c l f'' g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  Eventually.mono h.bound fun x hx hg => norm_le_zero_iff.1 <| by simpa [hg] using hx
#align asymptotics.is_O_with.eq_zero_imp Asymptotics.IsOWith.eq_zero_imp

theorem IsO.eq_zero_imp (h : f'' =O[l] g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  let ⟨C, hC⟩ := h.IsOWith
  hC.eq_zero_imp
#align asymptotics.is_O.eq_zero_imp Asymptotics.IsO.eq_zero_imp

/-! ### Addition and subtraction -/


section add_sub

variable {f₁ f₂ : α → E'} {g₁ g₂ : α → F'}

theorem IsOWith.add (h₁ : IsOWith c₁ l f₁ g) (h₂ : IsOWith c₂ l f₂ g) :
    IsOWith (c₁ + c₂) l (fun x => f₁ x + f₂ x) g := by
  rw [is_O_with] at * <;>
    filter_upwards [h₁,
      h₂]with x hx₁ hx₂ using calc
        ‖f₁ x + f₂ x‖ ≤ c₁ * ‖g x‖ + c₂ * ‖g x‖ := norm_add_le_of_le hx₁ hx₂
        _ = (c₁ + c₂) * ‖g x‖ := (add_mul _ _ _).symm
        
#align asymptotics.is_O_with.add Asymptotics.IsOWith.add

theorem IsO.add (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  let ⟨c₁, hc₁⟩ := h₁.IsOWith
  let ⟨c₂, hc₂⟩ := h₂.IsOWith
  (hc₁.add hc₂).IsO
#align asymptotics.is_O.add Asymptotics.IsO.add

theorem IsOCat.add (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g :=
  IsOCat.of_isOWith fun c cpos =>
    ((h₁.forall_isOWith <| half_pos cpos).add (h₂.forall_isOWith <| half_pos cpos)).congr_const
      (add_halves c)
#align asymptotics.is_o.add Asymptotics.IsOCat.add

theorem IsOCat.add_add (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x + f₂ x) =o[l] fun x => ‖g₁ x‖ + ‖g₂ x‖ := by
  refine' (h₁.trans_le fun x => _).add (h₂.trans_le _) <;> simp [abs_of_nonneg, add_nonneg]
#align asymptotics.is_o.add_add Asymptotics.IsOCat.add_add

theorem IsO.add_isOCat (h₁ : f₁ =O[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.add h₂.IsO
#align asymptotics.is_O.add_is_o Asymptotics.IsO.add_isOCat

theorem IsOCat.add_isO (h₁ : f₁ =o[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.IsO.add h₂
#align asymptotics.is_o.add_is_O Asymptotics.IsOCat.add_isO

theorem IsOWith.add_isOCat (h₁ : IsOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    IsOWith c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₁.add (h₂.forall_isOWith (sub_pos.2 hc))).congr_const (add_sub_cancel'_right _ _)
#align asymptotics.is_O_with.add_is_o Asymptotics.IsOWith.add_isOCat

theorem IsOCat.add_isOWith (h₁ : f₁ =o[l] g) (h₂ : IsOWith c₁ l f₂ g) (hc : c₁ < c₂) :
    IsOWith c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₂.add_isOCat h₁ hc).congr_left fun _ => add_comm _ _
#align asymptotics.is_o.add_is_O_with Asymptotics.IsOCat.add_isOWith

theorem IsOWith.sub (h₁ : IsOWith c₁ l f₁ g) (h₂ : IsOWith c₂ l f₂ g) :
    IsOWith (c₁ + c₂) l (fun x => f₁ x - f₂ x) g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left
#align asymptotics.is_O_with.sub Asymptotics.IsOWith.sub

theorem IsOWith.sub_isOCat (h₁ : IsOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    IsOWith c₂ l (fun x => f₁ x - f₂ x) g := by
  simpa only [sub_eq_add_neg] using h₁.add_is_o h₂.neg_left hc
#align asymptotics.is_O_with.sub_is_o Asymptotics.IsOWith.sub_isOCat

theorem IsO.sub (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left
#align asymptotics.is_O.sub Asymptotics.IsO.sub

theorem IsOCat.sub (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left
#align asymptotics.is_o.sub Asymptotics.IsOCat.sub

end add_sub

/-! ### Lemmas about `is_O (f₁ - f₂) g l` / `is_o (f₁ - f₂) g l` treated as a binary relation -/


section IsOOAsRel

variable {f₁ f₂ f₃ : α → E'}

theorem IsOWith.symm (h : IsOWith c l (fun x => f₁ x - f₂ x) g) :
    IsOWith c l (fun x => f₂ x - f₁ x) g :=
  h.neg_left.congr_left fun x => neg_sub _ _
#align asymptotics.is_O_with.symm Asymptotics.IsOWith.symm

theorem isOWith_comm :
    IsOWith c l (fun x => f₁ x - f₂ x) g ↔ IsOWith c l (fun x => f₂ x - f₁ x) g :=
  ⟨IsOWith.symm, IsOWith.symm⟩
#align asymptotics.is_O_with_comm Asymptotics.isOWith_comm

theorem IsO.symm (h : (fun x => f₁ x - f₂ x) =O[l] g) : (fun x => f₂ x - f₁ x) =O[l] g :=
  h.neg_left.congr_left fun x => neg_sub _ _
#align asymptotics.is_O.symm Asymptotics.IsO.symm

theorem isO_comm : (fun x => f₁ x - f₂ x) =O[l] g ↔ (fun x => f₂ x - f₁ x) =O[l] g :=
  ⟨IsO.symm, IsO.symm⟩
#align asymptotics.is_O_comm Asymptotics.isO_comm

theorem IsOCat.symm (h : (fun x => f₁ x - f₂ x) =o[l] g) : (fun x => f₂ x - f₁ x) =o[l] g := by
  simpa only [neg_sub] using h.neg_left
#align asymptotics.is_o.symm Asymptotics.IsOCat.symm

theorem isOCat_comm : (fun x => f₁ x - f₂ x) =o[l] g ↔ (fun x => f₂ x - f₁ x) =o[l] g :=
  ⟨IsOCat.symm, IsOCat.symm⟩
#align asymptotics.is_o_comm Asymptotics.isOCat_comm

theorem IsOWith.triangle (h₁ : IsOWith c l (fun x => f₁ x - f₂ x) g)
    (h₂ : IsOWith c' l (fun x => f₂ x - f₃ x) g) : IsOWith (c + c') l (fun x => f₁ x - f₃ x) g :=
  (h₁.add h₂).congr_left fun x => sub_add_sub_cancel _ _ _
#align asymptotics.is_O_with.triangle Asymptotics.IsOWith.triangle

theorem IsO.triangle (h₁ : (fun x => f₁ x - f₂ x) =O[l] g) (h₂ : (fun x => f₂ x - f₃ x) =O[l] g) :
    (fun x => f₁ x - f₃ x) =O[l] g :=
  (h₁.add h₂).congr_left fun x => sub_add_sub_cancel _ _ _
#align asymptotics.is_O.triangle Asymptotics.IsO.triangle

theorem IsOCat.triangle (h₁ : (fun x => f₁ x - f₂ x) =o[l] g)
    (h₂ : (fun x => f₂ x - f₃ x) =o[l] g) : (fun x => f₁ x - f₃ x) =o[l] g :=
  (h₁.add h₂).congr_left fun x => sub_add_sub_cancel _ _ _
#align asymptotics.is_o.triangle Asymptotics.IsOCat.triangle

theorem IsO.congr_of_sub (h : (fun x => f₁ x - f₂ x) =O[l] g) : f₁ =O[l] g ↔ f₂ =O[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun x => sub_add_cancel _ _⟩
#align asymptotics.is_O.congr_of_sub Asymptotics.IsO.congr_of_sub

theorem IsOCat.congr_of_sub (h : (fun x => f₁ x - f₂ x) =o[l] g) : f₁ =o[l] g ↔ f₂ =o[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun x => sub_add_cancel _ _⟩
#align asymptotics.is_o.congr_of_sub Asymptotics.IsOCat.congr_of_sub

end IsOOAsRel

/-! ### Zero, one, and other constants -/


section ZeroConst

variable (g g' l)

theorem isOCat_zero : (fun x => (0 : E')) =o[l] g' :=
  IsOCat.of_bound fun c hc =>
    univ_mem' fun x => by simpa using mul_nonneg hc.le (norm_nonneg <| g' x)
#align asymptotics.is_o_zero Asymptotics.isOCat_zero

theorem isOWith_zero (hc : 0 ≤ c) : IsOWith c l (fun x => (0 : E')) g' :=
  IsOWith.of_bound <| univ_mem' fun x => by simpa using mul_nonneg hc (norm_nonneg <| g' x)
#align asymptotics.is_O_with_zero Asymptotics.isOWith_zero

theorem isOWith_zero' : IsOWith 0 l (fun x => (0 : E')) g :=
  IsOWith.of_bound <| univ_mem' fun x => by simp
#align asymptotics.is_O_with_zero' Asymptotics.isOWith_zero'

theorem isO_zero : (fun x => (0 : E')) =O[l] g :=
  isO_iff_isOWith.2 ⟨0, isOWith_zero' _ _⟩
#align asymptotics.is_O_zero Asymptotics.isO_zero

theorem isO_refl_left : (fun x => f' x - f' x) =O[l] g' :=
  (isO_zero g' l).congr_left fun x => (sub_self _).symm
#align asymptotics.is_O_refl_left Asymptotics.isO_refl_left

theorem isOCat_refl_left : (fun x => f' x - f' x) =o[l] g' :=
  (isOCat_zero g' l).congr_left fun x => (sub_self _).symm
#align asymptotics.is_o_refl_left Asymptotics.isOCat_refl_left

variable {g g' l}

@[simp]
theorem isOWith_zero_right_iff : (IsOWith c l f'' fun x => (0 : F')) ↔ f'' =ᶠ[l] 0 := by
  simp only [is_O_with, exists_prop, true_and_iff, norm_zero, MulZeroClass.mul_zero,
    norm_le_zero_iff, eventually_eq, Pi.zero_apply]
#align asymptotics.is_O_with_zero_right_iff Asymptotics.isOWith_zero_right_iff

@[simp]
theorem isO_zero_right_iff : (f'' =O[l] fun x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h =>
    let ⟨c, hc⟩ := h.IsOWith
    isOWith_zero_right_iff.1 hc,
    fun h => (isOWith_zero_right_iff.2 h : IsOWith 1 _ _ _).IsO⟩
#align asymptotics.is_O_zero_right_iff Asymptotics.isO_zero_right_iff

@[simp]
theorem isOCat_zero_right_iff : (f'' =o[l] fun x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h => isO_zero_right_iff.1 h.IsO, fun h =>
    IsOCat.of_isOWith fun c hc => isOWith_zero_right_iff.2 h⟩
#align asymptotics.is_o_zero_right_iff Asymptotics.isOCat_zero_right_iff

theorem isOWith_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) :
    IsOWith (‖c‖ / ‖c'‖) l (fun x : α => c) fun x => c' :=
  by
  unfold is_O_with
  apply univ_mem'
  intro x
  rw [mem_set_of_eq, div_mul_cancel]
  rwa [Ne.def, norm_eq_zero]
#align asymptotics.is_O_with_const_const Asymptotics.isOWith_const_const

theorem isO_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) :
    (fun x : α => c) =O[l] fun x => c' :=
  (isOWith_const_const c hc' l).IsO
#align asymptotics.is_O_const_const Asymptotics.isO_const_const

@[simp]
theorem isO_const_const_iff {c : E''} {c' : F''} (l : Filter α) [l.ne_bot] :
    ((fun x : α => c) =O[l] fun x => c') ↔ c' = 0 → c = 0 :=
  by
  rcases eq_or_ne c' 0 with (rfl | hc')
  · simp [eventually_eq]
  · simp [hc', is_O_const_const _ hc']
#align asymptotics.is_O_const_const_iff Asymptotics.isO_const_const_iff

@[simp]
theorem isO_pure {x} : f'' =O[pure x] g'' ↔ g'' x = 0 → f'' x = 0 :=
  calc
    f'' =O[pure x] g'' ↔ (fun y : α => f'' x) =O[pure x] fun _ => g'' x := isO_congr rfl rfl
    _ ↔ g'' x = 0 → f'' x = 0 := isO_const_const_iff _
    
#align asymptotics.is_O_pure Asymptotics.isO_pure

end ZeroConst

@[simp]
theorem isOWith_top : IsOWith c ⊤ f g ↔ ∀ x, ‖f x‖ ≤ c * ‖g x‖ := by rw [is_O_with] <;> rfl
#align asymptotics.is_O_with_top Asymptotics.isOWith_top

@[simp]
theorem isO_top : f =O[⊤] g ↔ ∃ C, ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by rw [is_O_iff] <;> rfl
#align asymptotics.is_O_top Asymptotics.isO_top

@[simp]
theorem isOCat_top : f'' =o[⊤] g'' ↔ ∀ x, f'' x = 0 :=
  by
  refine' ⟨_, fun h => (is_o_zero g'' ⊤).congr (fun x => (h x).symm) fun x => rfl⟩
  simp only [is_o_iff, eventually_top]
  refine' fun h x => norm_le_zero_iff.1 _
  have : tendsto (fun c : ℝ => c * ‖g'' x‖) (𝓝[>] 0) (𝓝 0) :=
    ((continuous_id.mul continuous_const).tendsto' _ _ (MulZeroClass.zero_mul _)).mono_left
      inf_le_left
  exact
    le_of_tendsto_of_tendsto tendsto_const_nhds this
      (eventually_nhdsWithin_iff.2 <| eventually_of_forall fun c hc => h hc x)
#align asymptotics.is_o_top Asymptotics.isOCat_top

@[simp]
theorem isOWith_principal {s : Set α} : IsOWith c (𝓟 s) f g ↔ ∀ x ∈ s, ‖f x‖ ≤ c * ‖g x‖ := by
  rw [is_O_with] <;> rfl
#align asymptotics.is_O_with_principal Asymptotics.isOWith_principal

theorem isO_principal {s : Set α} : f =O[𝓟 s] g ↔ ∃ c, ∀ x ∈ s, ‖f x‖ ≤ c * ‖g x‖ := by
  rw [is_O_iff] <;> rfl
#align asymptotics.is_O_principal Asymptotics.isO_principal

section

variable (F) [One F] [NormOneClass F]

theorem isOWith_const_one (c : E) (l : Filter α) :
    IsOWith ‖c‖ l (fun x : α => c) fun x => (1 : F) := by simp [is_O_with_iff]
#align asymptotics.is_O_with_const_one Asymptotics.isOWith_const_one

theorem isO_const_one (c : E) (l : Filter α) : (fun x : α => c) =O[l] fun x => (1 : F) :=
  (isOWith_const_one F c l).IsO
#align asymptotics.is_O_const_one Asymptotics.isO_const_one

theorem isOCat_const_iff_isOCat_one {c : F''} (hc : c ≠ 0) :
    (f =o[l] fun x => c) ↔ f =o[l] fun x => (1 : F) :=
  ⟨fun h => h.trans_isOWith (isOWith_const_one _ _ _) (norm_pos_iff.2 hc), fun h =>
    h.trans_isO <| isO_const_const _ hc _⟩
#align asymptotics.is_o_const_iff_is_o_one Asymptotics.isOCat_const_iff_isOCat_one

@[simp]
theorem isOCat_one_iff : f' =o[l] (fun x => 1 : α → F) ↔ Tendsto f' l (𝓝 0) := by
  simp only [is_o_iff, norm_one, mul_one, metric.nhds_basis_closed_ball.tendsto_right_iff,
    Metric.mem_closedBall, dist_zero_right]
#align asymptotics.is_o_one_iff Asymptotics.isOCat_one_iff

@[simp]
theorem isO_one_iff : f =O[l] (fun x => 1 : α → F) ↔ IsBoundedUnder (· ≤ ·) l fun x => ‖f x‖ :=
  by
  simp only [is_O_iff, norm_one, mul_one]
  rfl
#align asymptotics.is_O_one_iff Asymptotics.isO_one_iff

alias is_O_one_iff ↔ _ _root_.filter.is_bounded_under.is_O_one
#align filter.is_bounded_under.is_O_one Filter.IsBoundedUnder.isO_one

@[simp]
theorem isOCat_one_left_iff : (fun x => 1 : α → F) =o[l] f ↔ Tendsto (fun x => ‖f x‖) l atTop :=
  calc
    (fun x => 1 : α → F) =o[l] f ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖(1 : F)‖ ≤ ‖f x‖ :=
      isOCat_iff_nat_mul_le_aux <| Or.inl fun x => by simp only [norm_one, zero_le_one]
    _ ↔ ∀ n : ℕ, True → ∀ᶠ x in l, ‖f x‖ ∈ Ici (n : ℝ) := by
      simp only [norm_one, mul_one, true_imp_iff, mem_Ici]
    _ ↔ Tendsto (fun x => ‖f x‖) l atTop :=
      atTop_hasCountableBasis_of_archimedean.1.tendsto_right_iff.symm
    
#align asymptotics.is_o_one_left_iff Asymptotics.isOCat_one_left_iff

theorem Filter.Tendsto.isO_one {c : E'} (h : Tendsto f' l (𝓝 c)) : f' =O[l] (fun x => 1 : α → F) :=
  h.norm.isBoundedUnder_le.isO_one F
#align filter.tendsto.is_O_one Filter.Tendsto.isO_one

theorem IsO.trans_tendsto_nhds (hfg : f =O[l] g') {y : F'} (hg : Tendsto g' l (𝓝 y)) :
    f =O[l] (fun x => 1 : α → F) :=
  hfg.trans <| hg.isO_one F
#align asymptotics.is_O.trans_tendsto_nhds Asymptotics.IsO.trans_tendsto_nhds

end

theorem isOCat_const_iff {c : F''} (hc : c ≠ 0) : (f'' =o[l] fun x => c) ↔ Tendsto f'' l (𝓝 0) :=
  (isOCat_const_iff_isOCat_one ℝ hc).trans (isOCat_one_iff _)
#align asymptotics.is_o_const_iff Asymptotics.isOCat_const_iff

theorem isOCat_id_const {c : F''} (hc : c ≠ 0) : (fun x : E'' => x) =o[𝓝 0] fun x => c :=
  (isOCat_const_iff hc).mpr (continuous_id.Tendsto 0)
#align asymptotics.is_o_id_const Asymptotics.isOCat_id_const

theorem Filter.IsBoundedUnder.isO_const (h : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) {c : F''}
    (hc : c ≠ 0) : f =O[l] fun x => c :=
  (h.isO_one ℝ).trans (isO_const_const _ hc _)
#align filter.is_bounded_under.is_O_const Filter.IsBoundedUnder.isO_const

theorem isO_const_of_tendsto {y : E''} (h : Tendsto f'' l (𝓝 y)) {c : F''} (hc : c ≠ 0) :
    f'' =O[l] fun x => c :=
  h.norm.isBoundedUnder_le.isO_const hc
#align asymptotics.is_O_const_of_tendsto Asymptotics.isO_const_of_tendsto

theorem IsO.isBoundedUnder_le {c : F} (h : f =O[l] fun x => c) :
    IsBoundedUnder (· ≤ ·) l (norm ∘ f) :=
  let ⟨c', hc'⟩ := h.bound
  ⟨c' * ‖c‖, eventually_map.2 hc'⟩
#align asymptotics.is_O.is_bounded_under_le Asymptotics.IsO.isBoundedUnder_le

theorem isO_const_of_ne {c : F''} (hc : c ≠ 0) :
    (f =O[l] fun x => c) ↔ IsBoundedUnder (· ≤ ·) l (norm ∘ f) :=
  ⟨fun h => h.isBoundedUnder_le, fun h => h.isO_const hc⟩
#align asymptotics.is_O_const_of_ne Asymptotics.isO_const_of_ne

theorem isO_const_iff {c : F''} :
    (f'' =O[l] fun x => c) ↔ (c = 0 → f'' =ᶠ[l] 0) ∧ IsBoundedUnder (· ≤ ·) l fun x => ‖f'' x‖ :=
  by
  refine' ⟨fun h => ⟨fun hc => is_O_zero_right_iff.1 (by rwa [← hc]), h.isBoundedUnder_le⟩, _⟩
  rintro ⟨hcf, hf⟩
  rcases eq_or_ne c 0 with (hc | hc)
  exacts[(hcf hc).trans_isO (is_O_zero _ _), hf.is_O_const hc]
#align asymptotics.is_O_const_iff Asymptotics.isO_const_iff

theorem isO_iff_isBoundedUnder_le_div (h : ∀ᶠ x in l, g'' x ≠ 0) :
    f =O[l] g'' ↔ IsBoundedUnder (· ≤ ·) l fun x => ‖f x‖ / ‖g'' x‖ :=
  by
  simp only [is_O_iff, is_bounded_under, is_bounded, eventually_map]
  exact
    exists_congr fun c =>
      eventually_congr <| h.mono fun x hx => (div_le_iff <| norm_pos_iff.2 hx).symm
#align asymptotics.is_O_iff_is_bounded_under_le_div Asymptotics.isO_iff_isBoundedUnder_le_div

/-- `(λ x, c) =O[l] f` if and only if `f` is bounded away from zero. -/
theorem isO_const_left_iff_pos_le_norm {c : E''} (hc : c ≠ 0) :
    (fun x => c) =O[l] f' ↔ ∃ b, 0 < b ∧ ∀ᶠ x in l, b ≤ ‖f' x‖ :=
  by
  constructor
  · intro h
    rcases h.exists_pos with ⟨C, hC₀, hC⟩
    refine' ⟨‖c‖ / C, div_pos (norm_pos_iff.2 hc) hC₀, _⟩
    exact hC.bound.mono fun x => (div_le_iff' hC₀).2
  · rintro ⟨b, hb₀, hb⟩
    refine' is_O.of_bound (‖c‖ / b) (hb.mono fun x hx => _)
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact le_mul_of_one_le_right (norm_nonneg _) ((one_le_div hb₀).2 hx)
#align asymptotics.is_O_const_left_iff_pos_le_norm Asymptotics.isO_const_left_iff_pos_le_norm

section

variable (𝕜)

end

theorem IsO.trans_tendsto (hfg : f'' =O[l] g'') (hg : Tendsto g'' l (𝓝 0)) : Tendsto f'' l (𝓝 0) :=
  (isOCat_one_iff ℝ).1 <| hfg.trans_isOCat <| (isOCat_one_iff ℝ).2 hg
#align asymptotics.is_O.trans_tendsto Asymptotics.IsO.trans_tendsto

theorem IsOCat.trans_tendsto (hfg : f'' =o[l] g'') (hg : Tendsto g'' l (𝓝 0)) :
    Tendsto f'' l (𝓝 0) :=
  hfg.IsO.trans_tendsto hg
#align asymptotics.is_o.trans_tendsto Asymptotics.IsOCat.trans_tendsto

/-! ### Multiplication by a constant -/


theorem isOWith_const_mul_self (c : R) (f : α → R) (l : Filter α) :
    IsOWith ‖c‖ l (fun x => c * f x) f :=
  isOWith_of_le' _ fun x => norm_mul_le _ _
#align asymptotics.is_O_with_const_mul_self Asymptotics.isOWith_const_mul_self

theorem isO_const_mul_self (c : R) (f : α → R) (l : Filter α) : (fun x => c * f x) =O[l] f :=
  (isOWith_const_mul_self c f l).IsO
#align asymptotics.is_O_const_mul_self Asymptotics.isO_const_mul_self

theorem IsOWith.const_mul_left {f : α → R} (h : IsOWith c l f g) (c' : R) :
    IsOWith (‖c'‖ * c) l (fun x => c' * f x) g :=
  (isOWith_const_mul_self c' f l).trans h (norm_nonneg c')
#align asymptotics.is_O_with.const_mul_left Asymptotics.IsOWith.const_mul_left

theorem IsO.const_mul_left {f : α → R} (h : f =O[l] g) (c' : R) : (fun x => c' * f x) =O[l] g :=
  let ⟨c, hc⟩ := h.IsOWith
  (hc.const_mul_left c').IsO
#align asymptotics.is_O.const_mul_left Asymptotics.IsO.const_mul_left

theorem isOWith_self_const_mul' (u : Rˣ) (f : α → R) (l : Filter α) :
    IsOWith ‖(↑u⁻¹ : R)‖ l f fun x => ↑u * f x :=
  (isOWith_const_mul_self ↑u⁻¹ _ l).congr_left fun x => u.inv_mul_cancel_left (f x)
#align asymptotics.is_O_with_self_const_mul' Asymptotics.isOWith_self_const_mul'

theorem isOWith_self_const_mul (c : 𝕜) (hc : c ≠ 0) (f : α → 𝕜) (l : Filter α) :
    IsOWith ‖c‖⁻¹ l f fun x => c * f x :=
  (isOWith_self_const_mul' (Units.mk0 c hc) f l).congr_const <| norm_inv c
#align asymptotics.is_O_with_self_const_mul Asymptotics.isOWith_self_const_mul

theorem isO_self_const_mul' {c : R} (hc : IsUnit c) (f : α → R) (l : Filter α) :
    f =O[l] fun x => c * f x :=
  let ⟨u, hu⟩ := hc
  hu ▸ (isOWith_self_const_mul' u f l).IsO
#align asymptotics.is_O_self_const_mul' Asymptotics.isO_self_const_mul'

theorem isO_self_const_mul (c : 𝕜) (hc : c ≠ 0) (f : α → 𝕜) (l : Filter α) :
    f =O[l] fun x => c * f x :=
  isO_self_const_mul' (IsUnit.mk0 c hc) f l
#align asymptotics.is_O_self_const_mul Asymptotics.isO_self_const_mul

theorem isO_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) :
    (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  ⟨(isO_self_const_mul' hc f l).trans, fun h => h.const_mul_left c⟩
#align asymptotics.is_O_const_mul_left_iff' Asymptotics.isO_const_mul_left_iff'

theorem isO_const_mul_left_iff {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  isO_const_mul_left_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_O_const_mul_left_iff Asymptotics.isO_const_mul_left_iff

theorem IsOCat.const_mul_left {f : α → R} (h : f =o[l] g) (c : R) : (fun x => c * f x) =o[l] g :=
  (isO_const_mul_self c f l).trans_isOCat h
#align asymptotics.is_o.const_mul_left Asymptotics.IsOCat.const_mul_left

theorem isOCat_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) :
    (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  ⟨(isO_self_const_mul' hc f l).trans_isOCat, fun h => h.const_mul_left c⟩
#align asymptotics.is_o_const_mul_left_iff' Asymptotics.isOCat_const_mul_left_iff'

theorem isOCat_const_mul_left_iff {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  isOCat_const_mul_left_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_o_const_mul_left_iff Asymptotics.isOCat_const_mul_left_iff

theorem IsOWith.of_const_mul_right {g : α → R} {c : R} (hc' : 0 ≤ c')
    (h : IsOWith c' l f fun x => c * g x) : IsOWith (c' * ‖c‖) l f g :=
  h.trans (isOWith_const_mul_self c g l) hc'
#align asymptotics.is_O_with.of_const_mul_right Asymptotics.IsOWith.of_const_mul_right

theorem IsO.of_const_mul_right {g : α → R} {c : R} (h : f =O[l] fun x => c * g x) : f =O[l] g :=
  let ⟨c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.of_const_mul_right cnonneg).IsO
#align asymptotics.is_O.of_const_mul_right Asymptotics.IsO.of_const_mul_right

theorem IsOWith.const_mul_right' {g : α → R} {u : Rˣ} {c' : ℝ} (hc' : 0 ≤ c')
    (h : IsOWith c' l f g) : IsOWith (c' * ‖(↑u⁻¹ : R)‖) l f fun x => ↑u * g x :=
  h.trans (isOWith_self_const_mul' _ _ _) hc'
#align asymptotics.is_O_with.const_mul_right' Asymptotics.IsOWith.const_mul_right'

theorem IsOWith.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) {c' : ℝ} (hc' : 0 ≤ c')
    (h : IsOWith c' l f g) : IsOWith (c' * ‖c‖⁻¹) l f fun x => c * g x :=
  h.trans (isOWith_self_const_mul c hc g l) hc'
#align asymptotics.is_O_with.const_mul_right Asymptotics.IsOWith.const_mul_right

theorem IsO.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : f =O[l] g) :
    f =O[l] fun x => c * g x :=
  h.trans (isO_self_const_mul' hc g l)
#align asymptotics.is_O.const_mul_right' Asymptotics.IsO.const_mul_right'

theorem IsO.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : f =O[l] g) :
    f =O[l] fun x => c * g x :=
  h.const_mul_right' <| IsUnit.mk0 c hc
#align asymptotics.is_O.const_mul_right Asymptotics.IsO.const_mul_right

theorem isO_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) :
    (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩
#align asymptotics.is_O_const_mul_right_iff' Asymptotics.isO_const_mul_right_iff'

theorem isO_const_mul_right_iff {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  isO_const_mul_right_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_O_const_mul_right_iff Asymptotics.isO_const_mul_right_iff

theorem IsOCat.of_const_mul_right {g : α → R} {c : R} (h : f =o[l] fun x => c * g x) : f =o[l] g :=
  h.trans_isO (isO_const_mul_self c g l)
#align asymptotics.is_o.of_const_mul_right Asymptotics.IsOCat.of_const_mul_right

theorem IsOCat.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : f =o[l] g) :
    f =o[l] fun x => c * g x :=
  h.trans_isO (isO_self_const_mul' hc g l)
#align asymptotics.is_o.const_mul_right' Asymptotics.IsOCat.const_mul_right'

theorem IsOCat.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : f =o[l] g) :
    f =o[l] fun x => c * g x :=
  h.const_mul_right' <| IsUnit.mk0 c hc
#align asymptotics.is_o.const_mul_right Asymptotics.IsOCat.const_mul_right

theorem isOCat_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) :
    (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩
#align asymptotics.is_o_const_mul_right_iff' Asymptotics.isOCat_const_mul_right_iff'

theorem isOCat_const_mul_right_iff {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  isOCat_const_mul_right_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_o_const_mul_right_iff Asymptotics.isOCat_const_mul_right_iff

/-! ### Multiplication -/


theorem IsOWith.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} {c₁ c₂ : ℝ} (h₁ : IsOWith c₁ l f₁ g₁)
    (h₂ : IsOWith c₂ l f₂ g₂) : IsOWith (c₁ * c₂) l (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x :=
  by
  unfold is_O_with at *
  filter_upwards [h₁, h₂]with _ hx₁ hx₂
  apply le_trans (norm_mul_le _ _)
  convert mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_trans (norm_nonneg _) hx₁) using 1
  rw [norm_mul, mul_mul_mul_comm]
#align asymptotics.is_O_with.mul Asymptotics.IsOWith.mul

theorem IsO.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x => f₁ x * f₂ x) =O[l] fun x => g₁ x * g₂ x :=
  let ⟨c, hc⟩ := h₁.IsOWith
  let ⟨c', hc'⟩ := h₂.IsOWith
  (hc.mul hc').IsO
#align asymptotics.is_O.mul Asymptotics.IsO.mul

theorem IsO.mul_isOCat {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x :=
  by
  unfold is_o at *
  intro c cpos
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩
  exact (hc'.mul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel' _ (ne_of_gt c'pos))
#align asymptotics.is_O.mul_is_o Asymptotics.IsO.mul_isOCat

theorem IsOCat.mul_isO {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x :=
  by
  unfold is_o at *
  intro c cpos
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩
  exact ((h₁ (div_pos cpos c'pos)).mul hc').congr_const (div_mul_cancel _ (ne_of_gt c'pos))
#align asymptotics.is_o.mul_is_O Asymptotics.IsOCat.mul_isO

theorem IsOCat.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x :=
  h₁.mul_isO h₂.IsO
#align asymptotics.is_o.mul Asymptotics.IsOCat.mul

theorem IsOWith.pow' {f : α → R} {g : α → 𝕜} (h : IsOWith c l f g) :
    ∀ n : ℕ,
      IsOWith (Nat.casesOn n ‖(1 : R)‖ fun n => c ^ (n + 1)) l (fun x => f x ^ n) fun x => g x ^ n
  | 0 => by simpa using is_O_with_const_const (1 : R) (one_ne_zero' 𝕜) l
  | 1 => by simpa
  | n + 2 => by simpa [pow_succ] using h.mul (is_O_with.pow' (n + 1))
#align asymptotics.is_O_with.pow' Asymptotics.IsOWith.pow'

theorem IsOWith.pow [NormOneClass R] {f : α → R} {g : α → 𝕜} (h : IsOWith c l f g) :
    ∀ n : ℕ, IsOWith (c ^ n) l (fun x => f x ^ n) fun x => g x ^ n
  | 0 => by simpa using h.pow' 0
  | n + 1 => h.pow' (n + 1)
#align asymptotics.is_O_with.pow Asymptotics.IsOWith.pow

theorem IsOWith.of_pow {n : ℕ} {f : α → 𝕜} {g : α → R} (h : IsOWith c l (f ^ n) (g ^ n))
    (hn : n ≠ 0) (hc : c ≤ c' ^ n) (hc' : 0 ≤ c') : IsOWith c' l f g :=
  IsOWith.of_bound <|
    (h.weaken hc).bound.mono fun x hx =>
      le_of_pow_le_pow n (mul_nonneg hc' <| norm_nonneg _) hn.bot_lt <|
        calc
          ‖f x‖ ^ n = ‖f x ^ n‖ := (norm_pow _ _).symm
          _ ≤ c' ^ n * ‖g x ^ n‖ := hx
          _ ≤ c' ^ n * ‖g x‖ ^ n :=
            (mul_le_mul_of_nonneg_left (norm_pow_le' _ hn.bot_lt) (pow_nonneg hc' _))
          _ = (c' * ‖g x‖) ^ n := (mul_pow _ _ _).symm
          
#align asymptotics.is_O_with.of_pow Asymptotics.IsOWith.of_pow

theorem IsO.pow {f : α → R} {g : α → 𝕜} (h : f =O[l] g) (n : ℕ) :
    (fun x => f x ^ n) =O[l] fun x => g x ^ n :=
  let ⟨C, hC⟩ := h.IsOWith
  isO_iff_isOWith.2 ⟨_, hC.pow' n⟩
#align asymptotics.is_O.pow Asymptotics.IsO.pow

theorem IsO.of_pow {f : α → 𝕜} {g : α → R} {n : ℕ} (hn : n ≠ 0) (h : (f ^ n) =O[l] (g ^ n)) :
    f =O[l] g := by
  rcases h.exists_pos with ⟨C, hC₀, hC⟩
  obtain ⟨c, hc₀, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ C ≤ c ^ n
  exact ((eventually_ge_at_top _).And <| (tendsto_pow_at_top hn).eventually_ge_atTop C).exists
  exact (hC.of_pow hn hc hc₀).IsO
#align asymptotics.is_O.of_pow Asymptotics.IsO.of_pow

theorem IsOCat.pow {f : α → R} {g : α → 𝕜} (h : f =o[l] g) {n : ℕ} (hn : 0 < n) :
    (fun x => f x ^ n) =o[l] fun x => g x ^ n :=
  by
  cases n; exact hn.false.elim; clear hn
  induction' n with n ihn; · simpa only [pow_one]
  convert h.mul ihn <;> simp [pow_succ]
#align asymptotics.is_o.pow Asymptotics.IsOCat.pow

theorem IsOCat.of_pow {f : α → 𝕜} {g : α → R} {n : ℕ} (h : (f ^ n) =o[l] (g ^ n)) (hn : n ≠ 0) :
    f =o[l] g :=
  IsOCat.of_isOWith fun c hc => (h.def' <| pow_pos hc _).ofPow hn le_rfl hc.le
#align asymptotics.is_o.of_pow Asymptotics.IsOCat.of_pow

/-! ### Inverse -/


theorem IsOWith.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : IsOWith c l f g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : IsOWith c l (fun x => (g x)⁻¹) fun x => (f x)⁻¹ :=
  by
  refine' is_O_with.of_bound (h.bound.mp (h₀.mono fun x h₀ hle => _))
  cases' eq_or_ne (f x) 0 with hx hx
  · simp only [hx, h₀ hx, inv_zero, norm_zero, MulZeroClass.mul_zero]
  · have hc : 0 < c := pos_of_mul_pos_left ((norm_pos_iff.2 hx).trans_le hle) (norm_nonneg _)
    replace hle := inv_le_inv_of_le (norm_pos_iff.2 hx) hle
    simpa only [norm_inv, mul_inv, ← div_eq_inv_mul, div_le_iff hc] using hle
#align asymptotics.is_O_with.inv_rev Asymptotics.IsOWith.inv_rev

theorem IsO.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =O[l] g) (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) :
    (fun x => (g x)⁻¹) =O[l] fun x => (f x)⁻¹ :=
  let ⟨c, hc⟩ := h.IsOWith
  (hc.inv_rev h₀).IsO
#align asymptotics.is_O.inv_rev Asymptotics.IsO.inv_rev

theorem IsOCat.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =o[l] g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : (fun x => (g x)⁻¹) =o[l] fun x => (f x)⁻¹ :=
  IsOCat.of_isOWith fun c hc => (h.def' hc).inv_rev h₀
#align asymptotics.is_o.inv_rev Asymptotics.IsOCat.inv_rev

/-! ### Scalar multiplication -/


section SmulConst

variable [NormedSpace 𝕜 E']

theorem IsOWith.const_smul_left (h : IsOWith c l f' g) (c' : 𝕜) :
    IsOWith (‖c'‖ * c) l (fun x => c' • f' x) g :=
  IsOWith.of_norm_left <| by
    simpa only [← norm_smul, norm_norm] using h.norm_left.const_mul_left ‖c'‖
#align asymptotics.is_O_with.const_smul_left Asymptotics.IsOWith.const_smul_left

theorem IsO.const_smul_left (h : f' =O[l] g) (c : 𝕜) : (c • f') =O[l] g :=
  let ⟨b, hb⟩ := h.IsOWith
  (hb.const_smul_left _).IsO
#align asymptotics.is_O.const_smul_left Asymptotics.IsO.const_smul_left

theorem IsOCat.const_smul_left (h : f' =o[l] g) (c : 𝕜) : (c • f') =o[l] g :=
  IsOCat.of_norm_left <| by simpa only [← norm_smul] using h.norm_left.const_mul_left ‖c‖
#align asymptotics.is_o.const_smul_left Asymptotics.IsOCat.const_smul_left

theorem isO_const_smul_left {c : 𝕜} (hc : c ≠ 0) : (fun x => c • f' x) =O[l] g ↔ f' =O[l] g :=
  by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_O_norm_left]
  simp only [norm_smul]
  rw [is_O_const_mul_left_iff cne0, is_O_norm_left]
#align asymptotics.is_O_const_smul_left Asymptotics.isO_const_smul_left

theorem isOCat_const_smul_left {c : 𝕜} (hc : c ≠ 0) : (fun x => c • f' x) =o[l] g ↔ f' =o[l] g :=
  by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_o_norm_left]
  simp only [norm_smul]
  rw [is_o_const_mul_left_iff cne0, is_o_norm_left]
#align asymptotics.is_o_const_smul_left Asymptotics.isOCat_const_smul_left

theorem isO_const_smul_right {c : 𝕜} (hc : c ≠ 0) : (f =O[l] fun x => c • f' x) ↔ f =O[l] f' :=
  by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_O_norm_right]
  simp only [norm_smul]
  rw [is_O_const_mul_right_iff cne0, is_O_norm_right]
#align asymptotics.is_O_const_smul_right Asymptotics.isO_const_smul_right

theorem isOCat_const_smul_right {c : 𝕜} (hc : c ≠ 0) : (f =o[l] fun x => c • f' x) ↔ f =o[l] f' :=
  by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_o_norm_right]
  simp only [norm_smul]
  rw [is_o_const_mul_right_iff cne0, is_o_norm_right]
#align asymptotics.is_o_const_smul_right Asymptotics.isOCat_const_smul_right

end SmulConst

section Smul

variable [NormedSpace 𝕜 E'] [NormedSpace 𝕜' F'] {k₁ : α → 𝕜} {k₂ : α → 𝕜'}

theorem IsOWith.smul (h₁ : IsOWith c l k₁ k₂) (h₂ : IsOWith c' l f' g') :
    IsOWith (c * c') l (fun x => k₁ x • f' x) fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr rfl _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
#align asymptotics.is_O_with.smul Asymptotics.IsOWith.smul

theorem IsO.smul (h₁ : k₁ =O[l] k₂) (h₂ : f' =O[l] g') :
    (fun x => k₁ x • f' x) =O[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
#align asymptotics.is_O.smul Asymptotics.IsO.smul

theorem IsO.smul_isOCat (h₁ : k₁ =O[l] k₂) (h₂ : f' =o[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul_is_o h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
#align asymptotics.is_O.smul_is_o Asymptotics.IsO.smul_isOCat

theorem IsOCat.smul_isO (h₁ : k₁ =o[l] k₂) (h₂ : f' =O[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul_is_O h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
#align asymptotics.is_o.smul_is_O Asymptotics.IsOCat.smul_isO

theorem IsOCat.smul (h₁ : k₁ =o[l] k₂) (h₂ : f' =o[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [norm_smul]
#align asymptotics.is_o.smul Asymptotics.IsOCat.smul

end Smul

/-! ### Sum -/


section Sum

variable {ι : Type _} {A : ι → α → E'} {C : ι → ℝ} {s : Finset ι}

theorem IsOWith.sum (h : ∀ i ∈ s, IsOWith (C i) l (A i) g) :
    IsOWith (∑ i in s, C i) l (fun x => ∑ i in s, A i x) g :=
  by
  induction' s using Finset.induction_on with i s is IH
  · simp only [is_O_with_zero', Finset.sum_empty, forall_true_iff]
  · simp only [is, Finset.sum_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i s)).add (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))
#align asymptotics.is_O_with.sum Asymptotics.IsOWith.sum

theorem IsO.sum (h : ∀ i ∈ s, A i =O[l] g) : (fun x => ∑ i in s, A i x) =O[l] g :=
  by
  unfold is_O at *
  choose! C hC using h
  exact ⟨_, is_O_with.sum hC⟩
#align asymptotics.is_O.sum Asymptotics.IsO.sum

theorem IsOCat.sum (h : ∀ i ∈ s, A i =o[l] g') : (fun x => ∑ i in s, A i x) =o[l] g' :=
  by
  induction' s using Finset.induction_on with i s is IH
  · simp only [is_o_zero, Finset.sum_empty, forall_true_iff]
  · simp only [is, Finset.sum_insert, not_false_iff]
    exact (h _ (Finset.mem_insert_self i s)).add (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))
#align asymptotics.is_o.sum Asymptotics.IsOCat.sum

end Sum

/-! ### Relation between `f = o(g)` and `f / g → 0` -/


theorem IsOCat.tendsto_div_nhds_zero {f g : α → 𝕜} (h : f =o[l] g) :
    Tendsto (fun x => f x / g x) l (𝓝 0) :=
  (isOCat_one_iff 𝕜).mp <|
    calc
      (fun x => f x / g x) =o[l] fun x => g x / g x := by
        simpa only [div_eq_mul_inv] using h.mul_is_O (is_O_refl _ _)
      _ =O[l] fun x => (1 : 𝕜) := isO_of_le _ fun x => by simp [div_self_le_one]
      
#align asymptotics.is_o.tendsto_div_nhds_zero Asymptotics.IsOCat.tendsto_div_nhds_zero

theorem IsOCat.tendsto_inv_smul_nhds_zero [NormedSpace 𝕜 E'] {f : α → E'} {g : α → 𝕜} {l : Filter α}
    (h : f =o[l] g) : Tendsto (fun x => (g x)⁻¹ • f x) l (𝓝 0) := by
  simpa only [div_eq_inv_mul, ← norm_inv, ← norm_smul, ← tendsto_zero_iff_norm_tendsto_zero] using
    h.norm_norm.tendsto_div_nhds_zero
#align asymptotics.is_o.tendsto_inv_smul_nhds_zero Asymptotics.IsOCat.tendsto_inv_smul_nhds_zero

theorem isOCat_iff_tendsto' {f g : α → 𝕜} (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
    f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  ⟨IsOCat.tendsto_div_nhds_zero, fun h =>
    (((isOCat_one_iff _).mpr h).mul_isO (isO_refl g l)).congr'
      (hgf.mono fun x => div_mul_cancel_of_imp) (eventually_of_forall fun x => one_mul _)⟩
#align asymptotics.is_o_iff_tendsto' Asymptotics.isOCat_iff_tendsto'

theorem isOCat_iff_tendsto {f g : α → 𝕜} (hgf : ∀ x, g x = 0 → f x = 0) :
    f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  isOCat_iff_tendsto' (eventually_of_forall hgf)
#align asymptotics.is_o_iff_tendsto Asymptotics.isOCat_iff_tendsto

alias is_o_iff_tendsto' ↔ _ is_o_of_tendsto'
#align asymptotics.is_o_of_tendsto' Asymptotics.isOCat_of_tendsto'

alias is_o_iff_tendsto ↔ _ is_o_of_tendsto
#align asymptotics.is_o_of_tendsto Asymptotics.isOCat_of_tendsto

theorem isOCat_const_left_of_ne {c : E''} (hc : c ≠ 0) :
    (fun x => c) =o[l] g ↔ Tendsto (fun x => ‖g x‖) l atTop :=
  by
  simp only [← is_o_one_left_iff ℝ]
  exact ⟨(is_O_const_const (1 : ℝ) hc l).trans_isOCat, (is_O_const_one ℝ c l).trans_isOCat⟩
#align asymptotics.is_o_const_left_of_ne Asymptotics.isOCat_const_left_of_ne

@[simp]
theorem isOCat_const_left {c : E''} :
    (fun x => c) =o[l] g'' ↔ c = 0 ∨ Tendsto (norm ∘ g'') l atTop :=
  by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp only [is_o_zero, eq_self_iff_true, true_or_iff]
  · simp only [hc, false_or_iff, is_o_const_left_of_ne hc]
#align asymptotics.is_o_const_left Asymptotics.isOCat_const_left

@[simp]
theorem isOCat_const_const_iff [NeBot l] {d : E''} {c : F''} :
    ((fun x => d) =o[l] fun x => c) ↔ d = 0 :=
  by
  have : ¬Tendsto (Function.const α ‖c‖) l atTop :=
    not_tendsto_atTop_of_tendsto_nhds tendsto_const_nhds
  simp [Function.const, this]
#align asymptotics.is_o_const_const_iff Asymptotics.isOCat_const_const_iff

@[simp]
theorem isOCat_pure {x} : f'' =o[pure x] g'' ↔ f'' x = 0 :=
  calc
    f'' =o[pure x] g'' ↔ (fun y : α => f'' x) =o[pure x] fun _ => g'' x := isOCat_congr rfl rfl
    _ ↔ f'' x = 0 := isOCat_const_const_iff
    
#align asymptotics.is_o_pure Asymptotics.isOCat_pure

theorem isOCat_const_id_comap_norm_atTop (c : F'') : (fun x : E'' => c) =o[comap norm atTop] id :=
  isOCat_const_left.2 <| Or.inr tendsto_comap
#align asymptotics.is_o_const_id_comap_norm_at_top Asymptotics.isOCat_const_id_comap_norm_atTop

theorem isOCat_const_id_atTop (c : E'') : (fun x : ℝ => c) =o[atTop] id :=
  isOCat_const_left.2 <| Or.inr tendsto_abs_atTop_atTop
#align asymptotics.is_o_const_id_at_top Asymptotics.isOCat_const_id_atTop

theorem isOCat_const_id_atBot (c : E'') : (fun x : ℝ => c) =o[atBot] id :=
  isOCat_const_left.2 <| Or.inr tendsto_abs_atBot_atTop
#align asymptotics.is_o_const_id_at_bot Asymptotics.isOCat_const_id_atBot

/-!
### Eventually (u / v) * v = u

If `u` and `v` are linked by an `is_O_with` relation, then we
eventually have `(u / v) * v = u`, even if `v` vanishes.
-/


section EventuallyMulDivCancel

variable {u v : α → 𝕜}

theorem IsOWith.eventually_mul_div_cancel (h : IsOWith c l u v) : u / v * v =ᶠ[l] u :=
  Eventually.mono h.bound fun y hy => div_mul_cancel_of_imp fun hv => by simpa [hv] using hy
#align asymptotics.is_O_with.eventually_mul_div_cancel Asymptotics.IsOWith.eventually_mul_div_cancel

/-- If `u = O(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem IsO.eventually_mul_div_cancel (h : u =O[l] v) : u / v * v =ᶠ[l] u :=
  let ⟨c, hc⟩ := h.IsOWith
  hc.eventually_mul_div_cancel
#align asymptotics.is_O.eventually_mul_div_cancel Asymptotics.IsO.eventually_mul_div_cancel

/-- If `u = o(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem IsOCat.eventually_mul_div_cancel (h : u =o[l] v) : u / v * v =ᶠ[l] u :=
  (h.forall_isOWith zero_lt_one).eventually_mul_div_cancel
#align asymptotics.is_o.eventually_mul_div_cancel Asymptotics.IsOCat.eventually_mul_div_cancel

end EventuallyMulDivCancel

/-! ### Equivalent definitions of the form `∃ φ, u =ᶠ[l] φ * v` in a `normed_field`. -/


section ExistsMulEq

variable {u v : α → 𝕜}

/-- If `‖φ‖` is eventually bounded by `c`, and `u =ᶠ[l] φ * v`, then we have `is_O_with c u v l`.
    This does not require any assumptions on `c`, which is why we keep this version along with
    `is_O_with_iff_exists_eq_mul`. -/
theorem isOWith_of_eq_mul (φ : α → 𝕜) (hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c) (h : u =ᶠ[l] φ * v) :
    IsOWith c l u v := by
  unfold is_O_with
  refine' h.symm.rw (fun x a => ‖a‖ ≤ c * ‖v x‖) (hφ.mono fun x hx => _)
  simp only [norm_mul, Pi.mul_apply]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
#align asymptotics.is_O_with_of_eq_mul Asymptotics.isOWith_of_eq_mul

theorem isOWith_iff_exists_eq_mul (hc : 0 ≤ c) :
    IsOWith c l u v ↔ ∃ (φ : α → 𝕜)(hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c), u =ᶠ[l] φ * v :=
  by
  constructor
  · intro h
    use fun x => u x / v x
    refine' ⟨eventually.mono h.bound fun y hy => _, h.eventually_mul_div_cancel.symm⟩
    simpa using div_le_of_nonneg_of_le_mul (norm_nonneg _) hc hy
  · rintro ⟨φ, hφ, h⟩
    exact is_O_with_of_eq_mul φ hφ h
#align asymptotics.is_O_with_iff_exists_eq_mul Asymptotics.isOWith_iff_exists_eq_mul

theorem IsOWith.exists_eq_mul (h : IsOWith c l u v) (hc : 0 ≤ c) :
    ∃ (φ : α → 𝕜)(hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c), u =ᶠ[l] φ * v :=
  (isOWith_iff_exists_eq_mul hc).mp h
#align asymptotics.is_O_with.exists_eq_mul Asymptotics.IsOWith.exists_eq_mul

theorem isO_iff_exists_eq_mul :
    u =O[l] v ↔ ∃ (φ : α → 𝕜)(hφ : l.IsBoundedUnder (· ≤ ·) (norm ∘ φ)), u =ᶠ[l] φ * v :=
  by
  constructor
  · rintro h
    rcases h.exists_nonneg with ⟨c, hnnc, hc⟩
    rcases hc.exists_eq_mul hnnc with ⟨φ, hφ, huvφ⟩
    exact ⟨φ, ⟨c, hφ⟩, huvφ⟩
  · rintro ⟨φ, ⟨c, hφ⟩, huvφ⟩
    exact is_O_iff_is_O_with.2 ⟨c, is_O_with_of_eq_mul φ hφ huvφ⟩
#align asymptotics.is_O_iff_exists_eq_mul Asymptotics.isO_iff_exists_eq_mul

alias is_O_iff_exists_eq_mul ↔ is_O.exists_eq_mul _
#align asymptotics.is_O.exists_eq_mul Asymptotics.IsO.exists_eq_mul

theorem isOCat_iff_exists_eq_mul :
    u =o[l] v ↔ ∃ (φ : α → 𝕜)(hφ : Tendsto φ l (𝓝 0)), u =ᶠ[l] φ * v :=
  by
  constructor
  · exact fun h => ⟨fun x => u x / v x, h.tendsto_div_nhds_zero, h.eventually_mul_div_cancel.symm⟩
  · unfold is_o
    rintro ⟨φ, hφ, huvφ⟩ c hpos
    rw [NormedAddCommGroup.tendsto_nhds_zero] at hφ
    exact is_O_with_of_eq_mul _ ((hφ c hpos).mono fun x => le_of_lt) huvφ
#align asymptotics.is_o_iff_exists_eq_mul Asymptotics.isOCat_iff_exists_eq_mul

alias is_o_iff_exists_eq_mul ↔ is_o.exists_eq_mul _
#align asymptotics.is_o.exists_eq_mul Asymptotics.IsOCat.exists_eq_mul

end ExistsMulEq

/-! ### Miscellanous lemmas -/


theorem div_isBoundedUnder_of_isO {α : Type _} {l : Filter α} {f g : α → 𝕜} (h : f =O[l] g) :
    IsBoundedUnder (· ≤ ·) l fun x => ‖f x / g x‖ :=
  by
  obtain ⟨c, h₀, hc⟩ := h.exists_nonneg
  refine' ⟨c, eventually_map.2 (hc.bound.mono fun x hx => _)⟩
  rw [norm_div]
  exact div_le_of_nonneg_of_le_mul (norm_nonneg _) h₀ hx
#align asymptotics.div_is_bounded_under_of_is_O Asymptotics.div_isBoundedUnder_of_isO

theorem isO_iff_div_isBoundedUnder {α : Type _} {l : Filter α} {f g : α → 𝕜}
    (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
    f =O[l] g ↔ IsBoundedUnder (· ≤ ·) l fun x => ‖f x / g x‖ :=
  by
  refine' ⟨div_is_bounded_under_of_is_O, fun h => _⟩
  obtain ⟨c, hc⟩ := h
  simp only [eventually_map, norm_div] at hc
  refine' is_O.of_bound c (hc.mp <| hgf.mono fun x hx₁ hx₂ => _)
  by_cases hgx : g x = 0
  · simp [hx₁ hgx, hgx]
  · exact (div_le_iff (norm_pos_iff.2 hgx)).mp hx₂
#align asymptotics.is_O_iff_div_is_bounded_under Asymptotics.isO_iff_div_isBoundedUnder

theorem isO_of_div_tendsto_nhds {α : Type _} {l : Filter α} {f g : α → 𝕜}
    (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) (c : 𝕜) (H : Filter.Tendsto (f / g) l (𝓝 c)) : f =O[l] g :=
  (isO_iff_div_isBoundedUnder hgf).2 <| H.norm.isBoundedUnder_le
#align asymptotics.is_O_of_div_tendsto_nhds Asymptotics.isO_of_div_tendsto_nhds

theorem IsOCat.tendsto_zero_of_tendsto {α E 𝕜 : Type _} [NormedAddCommGroup E] [NormedField 𝕜]
    {u : α → E} {v : α → 𝕜} {l : Filter α} {y : 𝕜} (huv : u =o[l] v) (hv : Tendsto v l (𝓝 y)) :
    Tendsto u l (𝓝 0) := by
  suffices h : u =o[l] fun x => (1 : 𝕜)
  · rwa [is_o_one_iff] at h
  exact huv.trans_is_O (hv.is_O_one 𝕜)
#align asymptotics.is_o.tendsto_zero_of_tendsto Asymptotics.IsOCat.tendsto_zero_of_tendsto

theorem isOCat_pow_pow {m n : ℕ} (h : m < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x ^ m :=
  by
  rcases lt_iff_exists_add.1 h with ⟨p, hp0 : 0 < p, rfl⟩
  suffices (fun x : 𝕜 => x ^ m * x ^ p) =o[𝓝 0] fun x => x ^ m * 1 ^ p by
    simpa only [pow_add, one_pow, mul_one]
  exact is_O.mul_is_o (is_O_refl _ _) (is_o.pow ((is_o_one_iff _).2 tendsto_id) hp0)
#align asymptotics.is_o_pow_pow Asymptotics.isOCat_pow_pow

theorem isOCat_norm_pow_norm_pow {m n : ℕ} (h : m < n) :
    (fun x : E' => ‖x‖ ^ n) =o[𝓝 0] fun x => ‖x‖ ^ m :=
  (isOCat_pow_pow h).comp_tendsto tendsto_norm_zero
#align asymptotics.is_o_norm_pow_norm_pow Asymptotics.isOCat_norm_pow_norm_pow

theorem isOCat_pow_id {n : ℕ} (h : 1 < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x :=
  by
  convert is_o_pow_pow h
  simp only [pow_one]
#align asymptotics.is_o_pow_id Asymptotics.isOCat_pow_id

theorem isOCat_norm_pow_id {n : ℕ} (h : 1 < n) : (fun x : E' => ‖x‖ ^ n) =o[𝓝 0] fun x => x := by
  simpa only [pow_one, is_o_norm_right] using @is_o_norm_pow_norm_pow E' _ _ _ h
#align asymptotics.is_o_norm_pow_id Asymptotics.isOCat_norm_pow_id

theorem IsO.eq_zero_of_norm_pow_within {f : E'' → F''} {s : Set E''} {x₀ : E''} {n : ℕ}
    (h : f =O[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ n) (hx₀ : x₀ ∈ s) (hn : 0 < n) : f x₀ = 0 :=
  mem_of_mem_nhdsWithin hx₀ h.eq_zero_imp <| by simp_rw [sub_self, norm_zero, zero_pow hn]
#align asymptotics.is_O.eq_zero_of_norm_pow_within Asymptotics.IsO.eq_zero_of_norm_pow_within

theorem IsO.eq_zero_of_norm_pow {f : E'' → F''} {x₀ : E''} {n : ℕ}
    (h : f =O[𝓝 x₀] fun x => ‖x - x₀‖ ^ n) (hn : 0 < n) : f x₀ = 0 :=
  by
  rw [← nhdsWithin_univ] at h
  exact h.eq_zero_of_norm_pow_within (mem_univ _) hn
#align asymptotics.is_O.eq_zero_of_norm_pow Asymptotics.IsO.eq_zero_of_norm_pow

theorem isOCat_pow_sub_pow_sub (x₀ : E') {n m : ℕ} (h : n < m) :
    (fun x => ‖x - x₀‖ ^ m) =o[𝓝 x₀] fun x => ‖x - x₀‖ ^ n :=
  haveI : tendsto (fun x => ‖x - x₀‖) (𝓝 x₀) (𝓝 0) :=
    by
    apply tendsto_norm_zero.comp
    rw [← sub_self x₀]
    exact tendsto_id.sub tendsto_const_nhds
  (is_o_pow_pow h).comp_tendsto this
#align asymptotics.is_o_pow_sub_pow_sub Asymptotics.isOCat_pow_sub_pow_sub

theorem isOCat_pow_sub_sub (x₀ : E') {m : ℕ} (h : 1 < m) :
    (fun x => ‖x - x₀‖ ^ m) =o[𝓝 x₀] fun x => x - x₀ := by
  simpa only [is_o_norm_right, pow_one] using is_o_pow_sub_pow_sub x₀ h
#align asymptotics.is_o_pow_sub_sub Asymptotics.isOCat_pow_sub_sub

theorem IsOWith.right_le_sub_of_lt_1 {f₁ f₂ : α → E'} (h : IsOWith c l f₁ f₂) (hc : c < 1) :
    IsOWith (1 / (1 - c)) l f₂ fun x => f₂ x - f₁ x :=
  IsOWith.of_bound <|
    mem_of_superset h.bound fun x hx =>
      by
      simp only [mem_set_of_eq] at hx⊢
      rw [mul_comm, one_div, ← div_eq_mul_inv, le_div_iff, mul_sub, mul_one, mul_comm]
      · exact le_trans (sub_le_sub_left hx _) (norm_sub_norm_le _ _)
      · exact sub_pos.2 hc
#align asymptotics.is_O_with.right_le_sub_of_lt_1 Asymptotics.IsOWith.right_le_sub_of_lt_1

theorem IsOWith.right_le_add_of_lt_1 {f₁ f₂ : α → E'} (h : IsOWith c l f₁ f₂) (hc : c < 1) :
    IsOWith (1 / (1 - c)) l f₂ fun x => f₁ x + f₂ x :=
  (h.neg_right.right_le_sub_of_lt_1 hc).neg_right.of_neg_left.congr rfl (fun x => rfl) fun x => by
    rw [neg_sub, sub_neg_eq_add]
#align asymptotics.is_O_with.right_le_add_of_lt_1 Asymptotics.IsOWith.right_le_add_of_lt_1

theorem IsOCat.right_isO_sub {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) : f₂ =O[l] fun x => f₂ x - f₁ x :=
  ((h.def' one_half_pos).right_le_sub_of_lt_1 one_half_lt_one).IsO
#align asymptotics.is_o.right_is_O_sub Asymptotics.IsOCat.right_isO_sub

theorem IsOCat.right_isO_add {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) : f₂ =O[l] fun x => f₁ x + f₂ x :=
  ((h.def' one_half_pos).right_le_add_of_lt_1 one_half_lt_one).IsO
#align asymptotics.is_o.right_is_O_add Asymptotics.IsOCat.right_isO_add

/-- If `f x = O(g x)` along `cofinite`, then there exists a positive constant `C` such that
`‖f x‖ ≤ C * ‖g x‖` whenever `g x ≠ 0`. -/
theorem bound_of_isO_cofinite (h : f =O[cofinite] g'') :
    ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖ :=
  by
  rcases h.exists_pos with ⟨C, C₀, hC⟩
  rw [is_O_with, eventually_cofinite] at hC
  rcases(hC.to_finset.image fun x => ‖f x‖ / ‖g'' x‖).exists_le with ⟨C', hC'⟩
  have : ∀ x, C * ‖g'' x‖ < ‖f x‖ → ‖f x‖ / ‖g'' x‖ ≤ C' := by simpa using hC'
  refine' ⟨max C C', lt_max_iff.2 (Or.inl C₀), fun x h₀ => _⟩
  rw [max_mul_of_nonneg _ _ (norm_nonneg _), le_max_iff, or_iff_not_imp_left, not_le]
  exact fun hx => (div_le_iff (norm_pos_iff.2 h₀)).1 (this _ hx)
#align asymptotics.bound_of_is_O_cofinite Asymptotics.bound_of_isO_cofinite

theorem isO_cofinite_iff (h : ∀ x, g'' x = 0 → f'' x = 0) :
    f'' =O[cofinite] g'' ↔ ∃ C, ∀ x, ‖f'' x‖ ≤ C * ‖g'' x‖ :=
  ⟨fun h' =>
    let ⟨C, C₀, hC⟩ := bound_of_isO_cofinite h'
    ⟨C, fun x => if hx : g'' x = 0 then by simp [h _ hx, hx] else hC hx⟩,
    fun h => (isO_top.2 h).mono le_top⟩
#align asymptotics.is_O_cofinite_iff Asymptotics.isO_cofinite_iff

theorem bound_of_isO_nat_atTop {f : ℕ → E} {g'' : ℕ → E''} (h : f =O[atTop] g'') :
    ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖ :=
  bound_of_isO_cofinite <| by rwa [Nat.cofinite_eq_atTop]
#align asymptotics.bound_of_is_O_nat_at_top Asymptotics.bound_of_isO_nat_atTop

theorem isO_nat_atTop_iff {f : ℕ → E''} {g : ℕ → F''} (h : ∀ x, g x = 0 → f x = 0) :
    f =O[atTop] g ↔ ∃ C, ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by
  rw [← Nat.cofinite_eq_atTop, is_O_cofinite_iff h]
#align asymptotics.is_O_nat_at_top_iff Asymptotics.isO_nat_atTop_iff

theorem isO_one_nat_atTop_iff {f : ℕ → E''} :
    f =O[atTop] (fun n => 1 : ℕ → ℝ) ↔ ∃ C, ∀ n, ‖f n‖ ≤ C :=
  Iff.trans (isO_nat_atTop_iff fun n h => (one_ne_zero h).elim) <| by simp only [norm_one, mul_one]
#align asymptotics.is_O_one_nat_at_top_iff Asymptotics.isO_one_nat_atTop_iff

theorem isOWith_pi {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} {C : ℝ} (hC : 0 ≤ C) :
    IsOWith C l f g' ↔ ∀ i, IsOWith C l (fun x => f x i) g' :=
  by
  have : ∀ x, 0 ≤ C * ‖g' x‖ := fun x => mul_nonneg hC (norm_nonneg _)
  simp only [is_O_with_iff, pi_norm_le_iff_of_nonneg (this _), eventually_all]
#align asymptotics.is_O_with_pi Asymptotics.isOWith_pi

@[simp]
theorem isO_pi {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} : f =O[l] g' ↔ ∀ i, (fun x => f x i) =O[l] g' :=
  by
  simp only [is_O_iff_eventually_is_O_with, ← eventually_all]
  exact eventually_congr (eventually_at_top.2 ⟨0, fun c => is_O_with_pi⟩)
#align asymptotics.is_O_pi Asymptotics.isO_pi

@[simp]
theorem isOCat_pi {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} : f =o[l] g' ↔ ∀ i, (fun x => f x i) =o[l] g' :=
  by
  simp (config := { contextual := true }) only [is_o, is_O_with_pi, le_of_lt]
  exact ⟨fun h i c hc => h hc i, fun h c hc i => h i hc⟩
#align asymptotics.is_o_pi Asymptotics.isOCat_pi

end Asymptotics

open Asymptotics

theorem summable_of_isO {ι E} [NormedAddCommGroup E] [CompleteSpace E] {f : ι → E} {g : ι → ℝ}
    (hg : Summable g) (h : f =O[cofinite] g) : Summable f :=
  let ⟨C, hC⟩ := h.IsOWith
  summable_of_norm_bounded_eventually (fun x => C * ‖g x‖) (hg.abs.mul_left _) hC.bound
#align summable_of_is_O summable_of_isO

theorem summable_of_isO_nat {E} [NormedAddCommGroup E] [CompleteSpace E] {f : ℕ → E} {g : ℕ → ℝ}
    (hg : Summable g) (h : f =O[atTop] g) : Summable f :=
  summable_of_isO hg <| Nat.cofinite_eq_atTop.symm ▸ h
#align summable_of_is_O_nat summable_of_isO_nat

namespace LocalHomeomorph

variable {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

variable {E : Type _} [Norm E] {F : Type _} [Norm F]

/-- Transfer `is_O_with` over a `local_homeomorph`. -/
theorem isOWith_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E} {g : β → F}
    {C : ℝ} : IsOWith C (𝓝 b) f g ↔ IsOWith C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
  ⟨fun h =>
    h.comp_tendsto <| by
      convert e.continuous_at (e.map_target hb)
      exact (e.right_inv hb).symm,
    fun h =>
    (h.comp_tendsto (e.continuousAt_symm hb)).congr' rfl
      ((e.eventually_right_inverse hb).mono fun x hx => congr_arg f hx)
      ((e.eventually_right_inverse hb).mono fun x hx => congr_arg g hx)⟩
#align local_homeomorph.is_O_with_congr LocalHomeomorph.isOWith_congr

/-- Transfer `is_O` over a `local_homeomorph`. -/
theorem isO_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E} {g : β → F} :
    f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) :=
  by
  unfold is_O
  exact exists_congr fun C => e.is_O_with_congr hb
#align local_homeomorph.is_O_congr LocalHomeomorph.isO_congr

/-- Transfer `is_o` over a `local_homeomorph`. -/
theorem isOCat_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E} {g : β → F} :
    f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) :=
  by
  unfold is_o
  exact forall₂_congr fun c hc => e.is_O_with_congr hb
#align local_homeomorph.is_o_congr LocalHomeomorph.isOCat_congr

end LocalHomeomorph

namespace Homeomorph

variable {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

variable {E : Type _} [Norm E] {F : Type _} [Norm F]

open Asymptotics

/-- Transfer `is_O_with` over a `homeomorph`. -/
theorem isOWith_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} {C : ℝ} :
    IsOWith C (𝓝 b) f g ↔ IsOWith C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
  e.toLocalHomeomorph.isOWith_congr trivial
#align homeomorph.is_O_with_congr Homeomorph.isOWith_congr

/-- Transfer `is_O` over a `homeomorph`. -/
theorem isO_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} :
    f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) :=
  by
  unfold is_O
  exact exists_congr fun C => e.is_O_with_congr
#align homeomorph.is_O_congr Homeomorph.isO_congr

/-- Transfer `is_o` over a `homeomorph`. -/
theorem isOCat_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} :
    f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) :=
  by
  unfold is_o
  exact forall₂_congr fun c hc => e.is_O_with_congr
#align homeomorph.is_o_congr Homeomorph.isOCat_congr

end Homeomorph

