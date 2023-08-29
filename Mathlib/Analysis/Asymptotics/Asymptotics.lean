/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.LocalHomeomorph

#align_import analysis.asymptotics.asymptotics from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Asymptotics

We introduce these relations:

* `IsBigOWith c l f g` : "f is big O of g along l with constant c";
* `f =O[l] g` : "f is big O of g along l";
* `f =o[l] g` : "f is little o of g along l".

Here `l` is any filter on the domain of `f` and `g`, which are assumed to be the same. The codomains
of `f` and `g` do not need to be the same; all that is needed that there is a norm associated with
these types, and it is the norm that is compared asymptotically.

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
-/


open Filter Set

open Topology BigOperators Classical Filter NNReal

namespace Asymptotics

set_option linter.uppercaseLean3 false

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {E''' : Type*}
  {R : Type*} {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedAddGroup E''']
  [SeminormedRing R']

variable [NormedField 𝕜] [NormedField 𝕜']

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
#align asymptotics.is_O_with Asymptotics.IsBigOWith

/-- Definition of `IsBigOWith`. We record it in a lemma as `IsBigOWith` is irreducible. -/
theorem isBigOWith_iff : IsBigOWith c l f g ↔ ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by rw [IsBigOWith_def]
                                                                                 -- 🎉 no goals
#align asymptotics.is_O_with_iff Asymptotics.isBigOWith_iff

alias ⟨IsBigOWith.bound, IsBigOWith.of_bound⟩ := isBigOWith_iff
#align asymptotics.is_O_with.bound Asymptotics.IsBigOWith.bound
#align asymptotics.is_O_with.of_bound Asymptotics.IsBigOWith.of_bound

/-- The Landau notation `f =O[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by a constant multiple of `‖g‖`.
In other words, `‖f‖ / ‖g‖` is eventually bounded, modulo division by zero issues that are avoided
by this definition. -/
irreducible_def IsBigO (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∃ c : ℝ, IsBigOWith c l f g
#align asymptotics.is_O Asymptotics.IsBigO

@[inherit_doc]
notation:100 f " =O[" l "] " g:100 => IsBigO l f g

/-- Definition of `IsBigO` in terms of `IsBigOWith`. We record it in a lemma as `IsBigO` is
irreducible. -/
theorem isBigO_iff_isBigOWith : f =O[l] g ↔ ∃ c : ℝ, IsBigOWith c l f g := by rw [IsBigO_def]
                                                                              -- 🎉 no goals
#align asymptotics.is_O_iff_is_O_with Asymptotics.isBigO_iff_isBigOWith

/-- Definition of `IsBigO` in terms of filters. -/
theorem isBigO_iff : f =O[l] g ↔ ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  simp only [IsBigO_def, IsBigOWith_def]
  -- 🎉 no goals
#align asymptotics.is_O_iff Asymptotics.isBigO_iff

/-- Definition of `IsBigO` in terms of filters, with a positive constant. -/
theorem isBigO_iff' {g : α → E'''} :
    f =O[l] g ↔ ∃ c > 0, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  refine ⟨fun h => ?mp, fun h => ?mpr⟩
  -- ⊢ ∃ c, c > 0 ∧ ∀ᶠ (x : α) in l, ‖f x‖ ≤ c * ‖g x‖
  case mp =>
    rw [isBigO_iff] at h
    obtain ⟨c, hc⟩ := h
    refine' ⟨max c 1, zero_lt_one.trans_le (le_max_right _ _), _⟩
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
  -- ⊢ ∃ c, c > 0 ∧ ∀ᶠ (x : α) in l, c * ‖f x‖ ≤ ‖g x‖
  case mp =>
    rw [isBigO_iff'] at h
    obtain ⟨c, ⟨hc_pos, hc⟩⟩ := h
    refine ⟨c⁻¹, ⟨by positivity, ?_⟩⟩
    filter_upwards [hc] with x hx
    rwa [inv_mul_le_iff (by positivity)]
  case mpr =>
    rw [isBigO_iff']
    obtain ⟨c, ⟨hc_pos, hc⟩⟩ := h
    refine ⟨c⁻¹, ⟨by positivity, ?_⟩⟩
    filter_upwards [hc] with x hx
    rwa [←inv_inv c, inv_mul_le_iff (by positivity)] at hx

theorem IsBigO.of_bound (c : ℝ) (h : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g :=
  isBigO_iff.2 ⟨c, h⟩
#align asymptotics.is_O.of_bound Asymptotics.IsBigO.of_bound

theorem IsBigO.of_bound' (h : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖) : f =O[l] g :=
  IsBigO.of_bound 1 <| by
    simp_rw [one_mul]
    -- ⊢ ∀ᶠ (x : α) in l, ‖f x‖ ≤ ‖g x‖
    exact h
    -- 🎉 no goals
#align asymptotics.is_O.of_bound' Asymptotics.IsBigO.of_bound'

theorem IsBigO.bound : f =O[l] g → ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isBigO_iff.1
#align asymptotics.is_O.bound Asymptotics.IsBigO.bound

/-- The Landau notation `f =o[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by an arbitrarily small constant
multiple of `‖g‖`. In other words, `‖f‖ / ‖g‖` tends to `0` along `l`, modulo division by zero
issues that are avoided by this definition. -/
irreducible_def IsLittleO (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f g
#align asymptotics.is_o Asymptotics.IsLittleO

@[inherit_doc]
notation:100 f " =o[" l "] " g:100 => IsLittleO l f g

/-- Definition of `IsLittleO` in terms of `IsBigOWith`. -/
theorem isLittleO_iff_forall_isBigOWith : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f g := by
  rw [IsLittleO_def]
  -- 🎉 no goals
#align asymptotics.is_o_iff_forall_is_O_with Asymptotics.isLittleO_iff_forall_isBigOWith

alias ⟨IsLittleO.forall_isBigOWith, IsLittleO.of_isBigOWith⟩ := isLittleO_iff_forall_isBigOWith
#align asymptotics.is_o.forall_is_O_with Asymptotics.IsLittleO.forall_isBigOWith
#align asymptotics.is_o.of_is_O_with Asymptotics.IsLittleO.of_isBigOWith

/-- Definition of `IsLittleO` in terms of filters. -/
theorem isLittleO_iff : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by
  simp only [IsLittleO_def, IsBigOWith_def]
  -- 🎉 no goals
#align asymptotics.is_o_iff Asymptotics.isLittleO_iff

alias ⟨IsLittleO.bound, IsLittleO.of_bound⟩ := isLittleO_iff
#align asymptotics.is_o.bound Asymptotics.IsLittleO.bound
#align asymptotics.is_o.of_bound Asymptotics.IsLittleO.of_bound

theorem IsLittleO.def (h : f =o[l] g) (hc : 0 < c) : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isLittleO_iff.1 h hc
#align asymptotics.is_o.def Asymptotics.IsLittleO.def

theorem IsLittleO.def' (h : f =o[l] g) (hc : 0 < c) : IsBigOWith c l f g :=
  isBigOWith_iff.2 <| isLittleO_iff.1 h hc
#align asymptotics.is_o.def' Asymptotics.IsLittleO.def'

theorem IsLittleO.eventuallyLE (h : f =o[l] g) : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖ := by
  simpa using h.def zero_lt_one
  -- 🎉 no goals

end Defs

/-! ### Conversions -/


theorem IsBigOWith.isBigO (h : IsBigOWith c l f g) : f =O[l] g := by rw [IsBigO_def]; exact ⟨c, h⟩
                                                                     -- ⊢ ∃ c, IsBigOWith c l f g
                                                                                      -- 🎉 no goals
#align asymptotics.is_O_with.is_O Asymptotics.IsBigOWith.isBigO

theorem IsLittleO.isBigOWith (hgf : f =o[l] g) : IsBigOWith 1 l f g :=
  hgf.def' zero_lt_one
#align asymptotics.is_o.is_O_with Asymptotics.IsLittleO.isBigOWith

theorem IsLittleO.isBigO (hgf : f =o[l] g) : f =O[l] g :=
  hgf.isBigOWith.isBigO
#align asymptotics.is_o.is_O Asymptotics.IsLittleO.isBigO

theorem IsBigO.isBigOWith : f =O[l] g → ∃ c : ℝ, IsBigOWith c l f g :=
  isBigO_iff_isBigOWith.1
#align asymptotics.is_O.is_O_with Asymptotics.IsBigO.isBigOWith

theorem IsBigOWith.weaken (h : IsBigOWith c l f g') (hc : c ≤ c') : IsBigOWith c' l f g' :=
  IsBigOWith.of_bound <|
    mem_of_superset h.bound fun x hx =>
      calc
        ‖f x‖ ≤ c * ‖g' x‖ := hx
        _ ≤ _ := by gcongr
                    -- 🎉 no goals
#align asymptotics.is_O_with.weaken Asymptotics.IsBigOWith.weaken

theorem IsBigOWith.exists_pos (h : IsBigOWith c l f g') :
    ∃ (c' : _) (_H : 0 < c'), IsBigOWith c' l f g' :=
  ⟨max c 1, lt_of_lt_of_le zero_lt_one (le_max_right c 1), h.weaken <| le_max_left c 1⟩
#align asymptotics.is_O_with.exists_pos Asymptotics.IsBigOWith.exists_pos

theorem IsBigO.exists_pos (h : f =O[l] g') : ∃ (c : _) (_H : 0 < c), IsBigOWith c l f g' :=
  let ⟨_c, hc⟩ := h.isBigOWith
  hc.exists_pos
#align asymptotics.is_O.exists_pos Asymptotics.IsBigO.exists_pos

theorem IsBigOWith.exists_nonneg (h : IsBigOWith c l f g') :
    ∃ (c' : _) (_H : 0 ≤ c'), IsBigOWith c' l f g' :=
  let ⟨c, cpos, hc⟩ := h.exists_pos
  ⟨c, le_of_lt cpos, hc⟩
#align asymptotics.is_O_with.exists_nonneg Asymptotics.IsBigOWith.exists_nonneg

theorem IsBigO.exists_nonneg (h : f =O[l] g') : ∃ (c : _) (_H : 0 ≤ c), IsBigOWith c l f g' :=
  let ⟨_c, hc⟩ := h.isBigOWith
  hc.exists_nonneg
#align asymptotics.is_O.exists_nonneg Asymptotics.IsBigO.exists_nonneg

/-- `f = O(g)` if and only if `IsBigOWith c f g` for all sufficiently large `c`. -/
theorem isBigO_iff_eventually_isBigOWith : f =O[l] g' ↔ ∀ᶠ c in atTop, IsBigOWith c l f g' :=
  isBigO_iff_isBigOWith.trans
    ⟨fun ⟨c, hc⟩ => mem_atTop_sets.2 ⟨c, fun _c' hc' => hc.weaken hc'⟩, fun h => h.exists⟩
#align asymptotics.is_O_iff_eventually_is_O_with Asymptotics.isBigO_iff_eventually_isBigOWith

/-- `f = O(g)` if and only if `∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖` for all sufficiently large `c`. -/
theorem isBigO_iff_eventually : f =O[l] g' ↔ ∀ᶠ c in atTop, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g' x‖ :=
  isBigO_iff_eventually_isBigOWith.trans <| by simp only [IsBigOWith_def]
                                               -- 🎉 no goals
#align asymptotics.is_O_iff_eventually Asymptotics.isBigO_iff_eventually

theorem IsBigO.exists_mem_basis {ι} {p : ι → Prop} {s : ι → Set α} (h : f =O[l] g')
    (hb : l.HasBasis p s) :
    ∃ (c : ℝ) (_hc : 0 < c) (i : ι) (_hi : p i), ∀ x ∈ s i, ‖f x‖ ≤ c * ‖g' x‖ :=
  flip Exists₂.imp h.exists_pos fun c _hc h => by
    simpa only [isBigOWith_iff, hb.eventually_iff, exists_prop] using h
    -- 🎉 no goals
#align asymptotics.is_O.exists_mem_basis Asymptotics.IsBigO.exists_mem_basis

theorem isBigOWith_inv (hc : 0 < c) : IsBigOWith c⁻¹ l f g ↔ ∀ᶠ x in l, c * ‖f x‖ ≤ ‖g x‖ := by
  simp only [IsBigOWith_def, ← div_eq_inv_mul, le_div_iff' hc]
  -- 🎉 no goals
#align asymptotics.is_O_with_inv Asymptotics.isBigOWith_inv

-- We prove this lemma with strange assumptions to get two lemmas below automatically
theorem isLittleO_iff_nat_mul_le_aux (h₀ : (∀ x, 0 ≤ ‖f x‖) ∨ ∀ x, 0 ≤ ‖g x‖) :
    f =o[l] g ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f x‖ ≤ ‖g x‖ := by
  constructor
  -- ⊢ f =o[l] g → ∀ (n : ℕ), ∀ᶠ (x : α) in l, ↑n * ‖f x‖ ≤ ‖g x‖
  · rintro H (_ | n)
    -- ⊢ ∀ᶠ (x : α) in l, ↑Nat.zero * ‖f x‖ ≤ ‖g x‖
    · refine' (H.def one_pos).mono fun x h₀' => _
      -- ⊢ ↑Nat.zero * ‖f x‖ ≤ ‖g x‖
      rw [Nat.cast_zero, zero_mul]
      -- ⊢ 0 ≤ ‖g x‖
      refine' h₀.elim (fun hf => (hf x).trans _) fun hg => hg x
      -- ⊢ ‖f x‖ ≤ ‖g x‖
      rwa [one_mul] at h₀'
      -- 🎉 no goals
    · have : (0 : ℝ) < n.succ := Nat.cast_pos.2 n.succ_pos
      -- ⊢ ∀ᶠ (x : α) in l, ↑(Nat.succ n) * ‖f x‖ ≤ ‖g x‖
      exact (isBigOWith_inv this).1 (H.def' <| inv_pos.2 this)
      -- 🎉 no goals
  · refine' fun H => isLittleO_iff.2 fun ε ε0 => _
    -- ⊢ ∀ᶠ (x : α) in l, ‖f x‖ ≤ ε * ‖g x‖
    rcases exists_nat_gt ε⁻¹ with ⟨n, hn⟩
    -- ⊢ ∀ᶠ (x : α) in l, ‖f x‖ ≤ ε * ‖g x‖
    have hn₀ : (0 : ℝ) < n := (inv_pos.2 ε0).trans hn
    -- ⊢ ∀ᶠ (x : α) in l, ‖f x‖ ≤ ε * ‖g x‖
    refine' ((isBigOWith_inv hn₀).2 (H n)).bound.mono fun x hfg => _
    -- ⊢ ‖f x‖ ≤ ε * ‖g x‖
    refine' hfg.trans (mul_le_mul_of_nonneg_right (inv_le_of_inv_le ε0 hn.le) _)
    -- ⊢ 0 ≤ ‖g x‖
    refine' h₀.elim (fun hf => nonneg_of_mul_nonneg_right ((hf x).trans hfg) _) fun h => h x
    -- ⊢ 0 < (↑n)⁻¹
    exact inv_pos.2 hn₀
    -- 🎉 no goals
#align asymptotics.is_o_iff_nat_mul_le_aux Asymptotics.isLittleO_iff_nat_mul_le_aux

theorem isLittleO_iff_nat_mul_le : f =o[l] g' ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f x‖ ≤ ‖g' x‖ :=
  isLittleO_iff_nat_mul_le_aux (Or.inr fun _x => norm_nonneg _)
#align asymptotics.is_o_iff_nat_mul_le Asymptotics.isLittleO_iff_nat_mul_le

theorem isLittleO_iff_nat_mul_le' : f' =o[l] g ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f' x‖ ≤ ‖g x‖ :=
  isLittleO_iff_nat_mul_le_aux (Or.inl fun _x => norm_nonneg _)
#align asymptotics.is_o_iff_nat_mul_le' Asymptotics.isLittleO_iff_nat_mul_le'

/-! ### Subsingleton -/


@[nontriviality]
theorem isLittleO_of_subsingleton [Subsingleton E'] : f' =o[l] g' :=
  IsLittleO.of_bound fun c hc => by simp [Subsingleton.elim (f' _) 0, mul_nonneg hc.le]
                                    -- 🎉 no goals
#align asymptotics.is_o_of_subsingleton Asymptotics.isLittleO_of_subsingleton

@[nontriviality]
theorem isBigO_of_subsingleton [Subsingleton E'] : f' =O[l] g' :=
  isLittleO_of_subsingleton.isBigO
#align asymptotics.is_O_of_subsingleton Asymptotics.isBigO_of_subsingleton

section congr

variable {f₁ f₂ : α → E} {g₁ g₂ : α → F}

/-! ### Congruence -/


theorem isBigOWith_congr (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    IsBigOWith c₁ l f₁ g₁ ↔ IsBigOWith c₂ l f₂ g₂ := by
  simp only [IsBigOWith_def]
  -- ⊢ (∀ᶠ (x : α) in l, ‖f₁ x‖ ≤ c₁ * ‖g₁ x‖) ↔ ∀ᶠ (x : α) in l, ‖f₂ x‖ ≤ c₂ * ‖g₂ …
  subst c₂
  -- ⊢ (∀ᶠ (x : α) in l, ‖f₁ x‖ ≤ c₁ * ‖g₁ x‖) ↔ ∀ᶠ (x : α) in l, ‖f₂ x‖ ≤ c₁ * ‖g₂ …
  apply Filter.eventually_congr
  -- ⊢ ∀ᶠ (x : α) in l, ‖f₁ x‖ ≤ c₁ * ‖g₁ x‖ ↔ ‖f₂ x‖ ≤ c₁ * ‖g₂ x‖
  filter_upwards [hf, hg]with _ e₁ e₂
  -- ⊢ ‖f₁ a✝‖ ≤ c₁ * ‖g₁ a✝‖ ↔ ‖f₂ a✝‖ ≤ c₁ * ‖g₂ a✝‖
  rw [e₁, e₂]
  -- 🎉 no goals
#align asymptotics.is_O_with_congr Asymptotics.isBigOWith_congr

theorem IsBigOWith.congr' (h : IsBigOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂)
    (hg : g₁ =ᶠ[l] g₂) : IsBigOWith c₂ l f₂ g₂ :=
  (isBigOWith_congr hc hf hg).mp h
#align asymptotics.is_O_with.congr' Asymptotics.IsBigOWith.congr'

theorem IsBigOWith.congr (h : IsBigOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : ∀ x, f₁ x = f₂ x)
    (hg : ∀ x, g₁ x = g₂ x) : IsBigOWith c₂ l f₂ g₂ :=
  h.congr' hc (univ_mem' hf) (univ_mem' hg)
#align asymptotics.is_O_with.congr Asymptotics.IsBigOWith.congr

theorem IsBigOWith.congr_left (h : IsBigOWith c l f₁ g) (hf : ∀ x, f₁ x = f₂ x) :
    IsBigOWith c l f₂ g :=
  h.congr rfl hf fun _ => rfl
#align asymptotics.is_O_with.congr_left Asymptotics.IsBigOWith.congr_left

theorem IsBigOWith.congr_right (h : IsBigOWith c l f g₁) (hg : ∀ x, g₁ x = g₂ x) :
    IsBigOWith c l f g₂ :=
  h.congr rfl (fun _ => rfl) hg
#align asymptotics.is_O_with.congr_right Asymptotics.IsBigOWith.congr_right

theorem IsBigOWith.congr_const (h : IsBigOWith c₁ l f g) (hc : c₁ = c₂) : IsBigOWith c₂ l f g :=
  h.congr hc (fun _ => rfl) fun _ => rfl
#align asymptotics.is_O_with.congr_const Asymptotics.IsBigOWith.congr_const

theorem isBigO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =O[l] g₁ ↔ f₂ =O[l] g₂ := by
  simp only [IsBigO_def]
  -- ⊢ (∃ c, IsBigOWith c l f₁ g₁) ↔ ∃ c, IsBigOWith c l f₂ g₂
  exact exists_congr fun c => isBigOWith_congr rfl hf hg
  -- 🎉 no goals
#align asymptotics.is_O_congr Asymptotics.isBigO_congr

theorem IsBigO.congr' (h : f₁ =O[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =O[l] g₂ :=
  (isBigO_congr hf hg).mp h
#align asymptotics.is_O.congr' Asymptotics.IsBigO.congr'

theorem IsBigO.congr (h : f₁ =O[l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    f₂ =O[l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)
#align asymptotics.is_O.congr Asymptotics.IsBigO.congr

theorem IsBigO.congr_left (h : f₁ =O[l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =O[l] g :=
  h.congr hf fun _ => rfl
#align asymptotics.is_O.congr_left Asymptotics.IsBigO.congr_left

theorem IsBigO.congr_right (h : f =O[l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =O[l] g₂ :=
  h.congr (fun _ => rfl) hg
#align asymptotics.is_O.congr_right Asymptotics.IsBigO.congr_right

theorem isLittleO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =o[l] g₁ ↔ f₂ =o[l] g₂ := by
  simp only [IsLittleO_def]
  -- ⊢ (∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f₁ g₁) ↔ ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c  …
  exact forall₂_congr fun c _hc => isBigOWith_congr (Eq.refl c) hf hg
  -- 🎉 no goals
#align asymptotics.is_o_congr Asymptotics.isLittleO_congr

theorem IsLittleO.congr' (h : f₁ =o[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =o[l] g₂ :=
  (isLittleO_congr hf hg).mp h
#align asymptotics.is_o.congr' Asymptotics.IsLittleO.congr'

theorem IsLittleO.congr (h : f₁ =o[l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    f₂ =o[l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)
#align asymptotics.is_o.congr Asymptotics.IsLittleO.congr

theorem IsLittleO.congr_left (h : f₁ =o[l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =o[l] g :=
  h.congr hf fun _ => rfl
#align asymptotics.is_o.congr_left Asymptotics.IsLittleO.congr_left

theorem IsLittleO.congr_right (h : f =o[l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =o[l] g₂ :=
  h.congr (fun _ => rfl) hg
#align asymptotics.is_o.congr_right Asymptotics.IsLittleO.congr_right

@[trans]
theorem _root_.Filter.EventuallyEq.trans_isBigO {f₁ f₂ : α → E} {g : α → F} (hf : f₁ =ᶠ[l] f₂)
    (h : f₂ =O[l] g) : f₁ =O[l] g :=
  h.congr' hf.symm EventuallyEq.rfl
#align filter.eventually_eq.trans_is_O Filter.EventuallyEq.trans_isBigO

instance transEventuallyEqIsBigO :
    @Trans (α → E) (α → E) (α → F) (· =ᶠ[l] ·) (· =O[l] ·) (· =O[l] ·) where
  trans := Filter.EventuallyEq.trans_isBigO

@[trans]
theorem _root_.Filter.EventuallyEq.trans_isLittleO {f₁ f₂ : α → E} {g : α → F} (hf : f₁ =ᶠ[l] f₂)
    (h : f₂ =o[l] g) : f₁ =o[l] g :=
  h.congr' hf.symm EventuallyEq.rfl
#align filter.eventually_eq.trans_is_o Filter.EventuallyEq.trans_isLittleO

instance transEventuallyEqIsLittleO :
    @Trans (α → E) (α → E) (α → F) (· =ᶠ[l] ·) (· =o[l] ·) (· =o[l] ·) where
  trans := Filter.EventuallyEq.trans_isLittleO

@[trans]
theorem IsBigO.trans_eventuallyEq {f : α → E} {g₁ g₂ : α → F} (h : f =O[l] g₁) (hg : g₁ =ᶠ[l] g₂) :
    f =O[l] g₂ :=
  h.congr' EventuallyEq.rfl hg
#align asymptotics.is_O.trans_eventually_eq Asymptotics.IsBigO.trans_eventuallyEq

instance transIsBigOEventuallyEq :
    @Trans (α → E) (α → F) (α → F) (· =O[l] ·) (· =ᶠ[l] ·) (· =O[l] ·) where
  trans := IsBigO.trans_eventuallyEq

@[trans]
theorem IsLittleO.trans_eventuallyEq {f : α → E} {g₁ g₂ : α → F} (h : f =o[l] g₁)
    (hg : g₁ =ᶠ[l] g₂) : f =o[l] g₂ :=
  h.congr' EventuallyEq.rfl hg
#align asymptotics.is_o.trans_eventually_eq Asymptotics.IsLittleO.trans_eventuallyEq

instance transIsLittleOEventuallyEq :
    @Trans (α → E) (α → F) (α → F) (· =o[l] ·) (· =ᶠ[l] ·) (· =o[l] ·) where
  trans := IsLittleO.trans_eventuallyEq

end congr

/-! ### Filter operations and transitivity -/


theorem IsBigOWith.comp_tendsto (hcfg : IsBigOWith c l f g) {k : β → α} {l' : Filter β}
    (hk : Tendsto k l' l) : IsBigOWith c l' (f ∘ k) (g ∘ k) :=
  IsBigOWith.of_bound <| hk hcfg.bound
#align asymptotics.is_O_with.comp_tendsto Asymptotics.IsBigOWith.comp_tendsto

theorem IsBigO.comp_tendsto (hfg : f =O[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) :
    (f ∘ k) =O[l'] (g ∘ k) :=
  isBigO_iff_isBigOWith.2 <| hfg.isBigOWith.imp fun _c h => h.comp_tendsto hk
#align asymptotics.is_O.comp_tendsto Asymptotics.IsBigO.comp_tendsto

theorem IsLittleO.comp_tendsto (hfg : f =o[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) :
    (f ∘ k) =o[l'] (g ∘ k) :=
  IsLittleO.of_isBigOWith fun _c cpos => (hfg.forall_isBigOWith cpos).comp_tendsto hk
#align asymptotics.is_o.comp_tendsto Asymptotics.IsLittleO.comp_tendsto

@[simp]
theorem isBigOWith_map {k : β → α} {l : Filter β} :
    IsBigOWith c (map k l) f g ↔ IsBigOWith c l (f ∘ k) (g ∘ k) := by
  simp only [IsBigOWith_def]
  -- ⊢ (∀ᶠ (x : α) in map k l, ‖f x‖ ≤ c * ‖g x‖) ↔ ∀ᶠ (x : β) in l, ‖(f ∘ k) x‖ ≤  …
  exact eventually_map
  -- 🎉 no goals
#align asymptotics.is_O_with_map Asymptotics.isBigOWith_map

@[simp]
theorem isBigO_map {k : β → α} {l : Filter β} : f =O[map k l] g ↔ (f ∘ k) =O[l] (g ∘ k) := by
  simp only [IsBigO_def, isBigOWith_map]
  -- 🎉 no goals
#align asymptotics.is_O_map Asymptotics.isBigO_map

@[simp]
theorem isLittleO_map {k : β → α} {l : Filter β} : f =o[map k l] g ↔ (f ∘ k) =o[l] (g ∘ k) := by
  simp only [IsLittleO_def, isBigOWith_map]
  -- 🎉 no goals
#align asymptotics.is_o_map Asymptotics.isLittleO_map

theorem IsBigOWith.mono (h : IsBigOWith c l' f g) (hl : l ≤ l') : IsBigOWith c l f g :=
  IsBigOWith.of_bound <| hl h.bound
#align asymptotics.is_O_with.mono Asymptotics.IsBigOWith.mono

theorem IsBigO.mono (h : f =O[l'] g) (hl : l ≤ l') : f =O[l] g :=
  isBigO_iff_isBigOWith.2 <| h.isBigOWith.imp fun _c h => h.mono hl
#align asymptotics.is_O.mono Asymptotics.IsBigO.mono

theorem IsLittleO.mono (h : f =o[l'] g) (hl : l ≤ l') : f =o[l] g :=
  IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).mono hl
#align asymptotics.is_o.mono Asymptotics.IsLittleO.mono

theorem IsBigOWith.trans (hfg : IsBigOWith c l f g) (hgk : IsBigOWith c' l g k) (hc : 0 ≤ c) :
    IsBigOWith (c * c') l f k := by
  simp only [IsBigOWith_def] at *
  -- ⊢ ∀ᶠ (x : α) in l, ‖f x‖ ≤ c * c' * ‖k x‖
  filter_upwards [hfg, hgk]with x hx hx'
  -- ⊢ ‖f x‖ ≤ c * c' * ‖k x‖
  calc
    ‖f x‖ ≤ c * ‖g x‖ := hx
    _ ≤ c * (c' * ‖k x‖) := by gcongr
    _ = c * c' * ‖k x‖ := (mul_assoc _ _ _).symm
#align asymptotics.is_O_with.trans Asymptotics.IsBigOWith.trans

@[trans]
theorem IsBigO.trans {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g) (hgk : g =O[l] k) :
    f =O[l] k :=
  let ⟨_c, cnonneg, hc⟩ := hfg.exists_nonneg
  let ⟨_c', hc'⟩ := hgk.isBigOWith
  (hc.trans hc' cnonneg).isBigO
#align asymptotics.is_O.trans Asymptotics.IsBigO.trans

instance transIsBigOIsBigO :
    @Trans (α → E) (α → F') (α → G) (· =O[l] ·) (· =O[l] ·) (· =O[l] ·) where
  trans := IsBigO.trans

theorem IsLittleO.trans_isBigOWith (hfg : f =o[l] g) (hgk : IsBigOWith c l g k) (hc : 0 < c) :
    f =o[l] k := by
  simp only [IsLittleO_def] at *
  -- ⊢ ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f k
  intro c' c'pos
  -- ⊢ IsBigOWith c' l f k
  have : 0 < c' / c := div_pos c'pos hc
  -- ⊢ IsBigOWith c' l f k
  exact ((hfg this).trans hgk this.le).congr_const (div_mul_cancel _ hc.ne')
  -- 🎉 no goals
#align asymptotics.is_o.trans_is_O_with Asymptotics.IsLittleO.trans_isBigOWith

@[trans]
theorem IsLittleO.trans_isBigO {f : α → E} {g : α → F} {k : α → G'} (hfg : f =o[l] g)
    (hgk : g =O[l] k) : f =o[l] k :=
  let ⟨_c, cpos, hc⟩ := hgk.exists_pos
  hfg.trans_isBigOWith hc cpos
#align asymptotics.is_o.trans_is_O Asymptotics.IsLittleO.trans_isBigO

instance transIsLittleOIsBigO :
    @Trans (α → E) (α → F) (α → G') (· =o[l] ·) (· =O[l] ·) (· =o[l] ·) where
  trans := IsLittleO.trans_isBigO

theorem IsBigOWith.trans_isLittleO (hfg : IsBigOWith c l f g) (hgk : g =o[l] k) (hc : 0 < c) :
    f =o[l] k := by
  simp only [IsLittleO_def] at *
  -- ⊢ ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f k
  intro c' c'pos
  -- ⊢ IsBigOWith c' l f k
  have : 0 < c' / c := div_pos c'pos hc
  -- ⊢ IsBigOWith c' l f k
  exact (hfg.trans (hgk this) hc.le).congr_const (mul_div_cancel' _ hc.ne')
  -- 🎉 no goals
#align asymptotics.is_O_with.trans_is_o Asymptotics.IsBigOWith.trans_isLittleO

@[trans]
theorem IsBigO.trans_isLittleO {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g)
    (hgk : g =o[l] k) : f =o[l] k :=
  let ⟨_c, cpos, hc⟩ := hfg.exists_pos
  hc.trans_isLittleO hgk cpos
#align asymptotics.is_O.trans_is_o Asymptotics.IsBigO.trans_isLittleO

instance transIsBigOIsLittleO :
    @Trans (α → E) (α → F') (α → G) (· =O[l] ·) (· =o[l] ·) (· =o[l] ·) where
  trans := IsBigO.trans_isLittleO

@[trans]
theorem IsLittleO.trans {f : α → E} {g : α → F} {k : α → G} (hfg : f =o[l] g) (hgk : g =o[l] k) :
    f =o[l] k :=
  hfg.trans_isBigOWith hgk.isBigOWith one_pos
#align asymptotics.is_o.trans Asymptotics.IsLittleO.trans

instance transIsLittleOIsLittleO :
    @Trans (α → E) (α → F) (α → G) (· =o[l] ·) (· =o[l] ·) (· =o[l] ·) where
  trans := IsLittleO.trans

theorem _root_.Filter.Eventually.trans_isBigO {f : α → E} {g : α → F'} {k : α → G}
    (hfg : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖) (hgk : g =O[l] k) : f =O[l] k :=
  (IsBigO.of_bound' hfg).trans hgk
#align filter.eventually.trans_is_O Filter.Eventually.trans_isBigO

theorem _root_.Filter.Eventually.isBigO {f : α → E} {g : α → ℝ} {l : Filter α}
    (hfg : ∀ᶠ x in l, ‖f x‖ ≤ g x) : f =O[l] g :=
  IsBigO.of_bound' <| hfg.mono fun _x hx => hx.trans <| Real.le_norm_self _
#align filter.eventually.is_O Filter.Eventually.isBigO

section

variable (l)

theorem isBigOWith_of_le' (hfg : ∀ x, ‖f x‖ ≤ c * ‖g x‖) : IsBigOWith c l f g :=
  IsBigOWith.of_bound <| univ_mem' hfg
#align asymptotics.is_O_with_of_le' Asymptotics.isBigOWith_of_le'

theorem isBigOWith_of_le (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) : IsBigOWith 1 l f g :=
  isBigOWith_of_le' l fun x => by
    rw [one_mul]
    -- ⊢ ‖f x‖ ≤ ‖g x‖
    exact hfg x
    -- 🎉 no goals
#align asymptotics.is_O_with_of_le Asymptotics.isBigOWith_of_le

theorem isBigO_of_le' (hfg : ∀ x, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g :=
  (isBigOWith_of_le' l hfg).isBigO
#align asymptotics.is_O_of_le' Asymptotics.isBigO_of_le'

theorem isBigO_of_le (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) : f =O[l] g :=
  (isBigOWith_of_le l hfg).isBigO
#align asymptotics.is_O_of_le Asymptotics.isBigO_of_le

end

theorem isBigOWith_refl (f : α → E) (l : Filter α) : IsBigOWith 1 l f f :=
  isBigOWith_of_le l fun _ => le_rfl
#align asymptotics.is_O_with_refl Asymptotics.isBigOWith_refl

theorem isBigO_refl (f : α → E) (l : Filter α) : f =O[l] f :=
  (isBigOWith_refl f l).isBigO
#align asymptotics.is_O_refl Asymptotics.isBigO_refl

theorem IsBigOWith.trans_le (hfg : IsBigOWith c l f g) (hgk : ∀ x, ‖g x‖ ≤ ‖k x‖) (hc : 0 ≤ c) :
    IsBigOWith c l f k :=
  (hfg.trans (isBigOWith_of_le l hgk) hc).congr_const <| mul_one c
#align asymptotics.is_O_with.trans_le Asymptotics.IsBigOWith.trans_le

theorem IsBigO.trans_le (hfg : f =O[l] g') (hgk : ∀ x, ‖g' x‖ ≤ ‖k x‖) : f =O[l] k :=
  hfg.trans (isBigO_of_le l hgk)
#align asymptotics.is_O.trans_le Asymptotics.IsBigO.trans_le

theorem IsLittleO.trans_le (hfg : f =o[l] g) (hgk : ∀ x, ‖g x‖ ≤ ‖k x‖) : f =o[l] k :=
  hfg.trans_isBigOWith (isBigOWith_of_le _ hgk) zero_lt_one
#align asymptotics.is_o.trans_le Asymptotics.IsLittleO.trans_le

theorem isLittleO_irrefl' (h : ∃ᶠ x in l, ‖f' x‖ ≠ 0) : ¬f' =o[l] f' := by
  intro ho
  -- ⊢ False
  rcases((ho.bound one_half_pos).and_frequently h).exists with ⟨x, hle, hne⟩
  -- ⊢ False
  rw [one_div, ← div_eq_inv_mul] at hle
  -- ⊢ False
  exact (half_lt_self (lt_of_le_of_ne (norm_nonneg _) hne.symm)).not_le hle
  -- 🎉 no goals
#align asymptotics.is_o_irrefl' Asymptotics.isLittleO_irrefl'

theorem isLittleO_irrefl (h : ∃ᶠ x in l, f'' x ≠ 0) : ¬f'' =o[l] f'' :=
  isLittleO_irrefl' <| h.mono fun _x => norm_ne_zero_iff.mpr
#align asymptotics.is_o_irrefl Asymptotics.isLittleO_irrefl

theorem IsBigO.not_isLittleO (h : f'' =O[l] g') (hf : ∃ᶠ x in l, f'' x ≠ 0) :
    ¬g' =o[l] f'' := fun h' =>
  isLittleO_irrefl hf (h.trans_isLittleO h')
#align asymptotics.is_O.not_is_o Asymptotics.IsBigO.not_isLittleO

theorem IsLittleO.not_isBigO (h : f'' =o[l] g') (hf : ∃ᶠ x in l, f'' x ≠ 0) :
    ¬g' =O[l] f'' := fun h' =>
  isLittleO_irrefl hf (h.trans_isBigO h')
#align asymptotics.is_o.not_is_O Asymptotics.IsLittleO.not_isBigO

section Bot

variable (c f g)

@[simp]
theorem isBigOWith_bot : IsBigOWith c ⊥ f g :=
  IsBigOWith.of_bound <| trivial
#align asymptotics.is_O_with_bot Asymptotics.isBigOWith_bot

@[simp]
theorem isBigO_bot : f =O[⊥] g :=
  (isBigOWith_bot 1 f g).isBigO
#align asymptotics.is_O_bot Asymptotics.isBigO_bot

@[simp]
theorem isLittleO_bot : f =o[⊥] g :=
  IsLittleO.of_isBigOWith fun c _ => isBigOWith_bot c f g
#align asymptotics.is_o_bot Asymptotics.isLittleO_bot

end Bot

@[simp]
theorem isBigOWith_pure {x} : IsBigOWith c (pure x) f g ↔ ‖f x‖ ≤ c * ‖g x‖ :=
  isBigOWith_iff
#align asymptotics.is_O_with_pure Asymptotics.isBigOWith_pure

theorem IsBigOWith.sup (h : IsBigOWith c l f g) (h' : IsBigOWith c l' f g) :
    IsBigOWith c (l ⊔ l') f g :=
  IsBigOWith.of_bound <| mem_sup.2 ⟨h.bound, h'.bound⟩
#align asymptotics.is_O_with.sup Asymptotics.IsBigOWith.sup

theorem IsBigOWith.sup' (h : IsBigOWith c l f g') (h' : IsBigOWith c' l' f g') :
    IsBigOWith (max c c') (l ⊔ l') f g' :=
  IsBigOWith.of_bound <|
    mem_sup.2 ⟨(h.weaken <| le_max_left c c').bound, (h'.weaken <| le_max_right c c').bound⟩
#align asymptotics.is_O_with.sup' Asymptotics.IsBigOWith.sup'

theorem IsBigO.sup (h : f =O[l] g') (h' : f =O[l'] g') : f =O[l ⊔ l'] g' :=
  let ⟨_c, hc⟩ := h.isBigOWith
  let ⟨_c', hc'⟩ := h'.isBigOWith
  (hc.sup' hc').isBigO
#align asymptotics.is_O.sup Asymptotics.IsBigO.sup

theorem IsLittleO.sup (h : f =o[l] g) (h' : f =o[l'] g) : f =o[l ⊔ l'] g :=
  IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).sup (h'.forall_isBigOWith cpos)
#align asymptotics.is_o.sup Asymptotics.IsLittleO.sup

@[simp]
theorem isBigO_sup : f =O[l ⊔ l'] g' ↔ f =O[l] g' ∧ f =O[l'] g' :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩
#align asymptotics.is_O_sup Asymptotics.isBigO_sup

@[simp]
theorem isLittleO_sup : f =o[l ⊔ l'] g ↔ f =o[l] g ∧ f =o[l'] g :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩
#align asymptotics.is_o_sup Asymptotics.isLittleO_sup

theorem isBigOWith_insert [TopologicalSpace α] {x : α} {s : Set α} {C : ℝ} {g : α → E} {g' : α → F}
    (h : ‖g x‖ ≤ C * ‖g' x‖) : IsBigOWith C (𝓝[insert x s] x) g g' ↔
    IsBigOWith C (𝓝[s] x) g g' := by
  simp_rw [IsBigOWith_def, nhdsWithin_insert, eventually_sup, eventually_pure, h, true_and_iff]
  -- 🎉 no goals
#align asymptotics.is_O_with_insert Asymptotics.isBigOWith_insert

protected theorem IsBigOWith.insert [TopologicalSpace α] {x : α} {s : Set α} {C : ℝ} {g : α → E}
    {g' : α → F} (h1 : IsBigOWith C (𝓝[s] x) g g') (h2 : ‖g x‖ ≤ C * ‖g' x‖) :
    IsBigOWith C (𝓝[insert x s] x) g g' :=
  (isBigOWith_insert h2).mpr h1
#align asymptotics.is_O_with.insert Asymptotics.IsBigOWith.insert

theorem isLittleO_insert [TopologicalSpace α] {x : α} {s : Set α} {g : α → E'} {g' : α → F'}
    (h : g x = 0) : g =o[𝓝[insert x s] x] g' ↔ g =o[𝓝[s] x] g' := by
  simp_rw [IsLittleO_def]
  -- ⊢ (∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c (𝓝[insert x s] x) g g') ↔ ∀ ⦃c : ℝ⦄, 0 < c  …
  refine' forall_congr' fun c => forall_congr' fun hc => _
  -- ⊢ IsBigOWith c (𝓝[insert x s] x) g g' ↔ IsBigOWith c (𝓝[s] x) g g'
  rw [isBigOWith_insert]
  -- ⊢ ‖g x‖ ≤ c * ‖g' x‖
  rw [h, norm_zero]
  -- ⊢ 0 ≤ c * ‖g' x‖
  exact mul_nonneg hc.le (norm_nonneg _)
  -- 🎉 no goals
#align asymptotics.is_o_insert Asymptotics.isLittleO_insert

protected theorem IsLittleO.insert [TopologicalSpace α] {x : α} {s : Set α} {g : α → E'}
    {g' : α → F'} (h1 : g =o[𝓝[s] x] g') (h2 : g x = 0) : g =o[𝓝[insert x s] x] g' :=
  (isLittleO_insert h2).mpr h1
#align asymptotics.is_o.insert Asymptotics.IsLittleO.insert

/-! ### Simplification : norm, abs -/


section NormAbs

variable {u v : α → ℝ}

@[simp]
theorem isBigOWith_norm_right : (IsBigOWith c l f fun x => ‖g' x‖) ↔ IsBigOWith c l f g' := by
  simp only [IsBigOWith_def, norm_norm]
  -- 🎉 no goals
#align asymptotics.is_O_with_norm_right Asymptotics.isBigOWith_norm_right

@[simp]
theorem isBigOWith_abs_right : (IsBigOWith c l f fun x => |u x|) ↔ IsBigOWith c l f u :=
  @isBigOWith_norm_right _ _ _ _ _ _ f u l
#align asymptotics.is_O_with_abs_right Asymptotics.isBigOWith_abs_right

alias ⟨IsBigOWith.of_norm_right, IsBigOWith.norm_right⟩ := isBigOWith_norm_right
#align asymptotics.is_O_with.of_norm_right Asymptotics.IsBigOWith.of_norm_right
#align asymptotics.is_O_with.norm_right Asymptotics.IsBigOWith.norm_right

alias ⟨IsBigOWith.of_abs_right, IsBigOWith.abs_right⟩ := isBigOWith_abs_right
#align asymptotics.is_O_with.of_abs_right Asymptotics.IsBigOWith.of_abs_right
#align asymptotics.is_O_with.abs_right Asymptotics.IsBigOWith.abs_right

@[simp]
theorem isBigO_norm_right : (f =O[l] fun x => ‖g' x‖) ↔ f =O[l] g' := by
  simp only [IsBigO_def]
  -- ⊢ (∃ c, IsBigOWith c l f fun x => ‖g' x‖) ↔ ∃ c, IsBigOWith c l f g'
  exact exists_congr fun _ => isBigOWith_norm_right
  -- 🎉 no goals
#align asymptotics.is_O_norm_right Asymptotics.isBigO_norm_right

@[simp]
theorem isBigO_abs_right : (f =O[l] fun x => |u x|) ↔ f =O[l] u :=
  @isBigO_norm_right _ _ ℝ _ _ _ _ _
#align asymptotics.is_O_abs_right Asymptotics.isBigO_abs_right

alias ⟨IsBigO.of_norm_right, IsBigO.norm_right⟩ := isBigO_norm_right
#align asymptotics.is_O.of_norm_right Asymptotics.IsBigO.of_norm_right
#align asymptotics.is_O.norm_right Asymptotics.IsBigO.norm_right

alias ⟨IsBigO.of_abs_right, IsBigO.abs_right⟩ := isBigO_abs_right
#align asymptotics.is_O.of_abs_right Asymptotics.IsBigO.of_abs_right
#align asymptotics.is_O.abs_right Asymptotics.IsBigO.abs_right

@[simp]
theorem isLittleO_norm_right : (f =o[l] fun x => ‖g' x‖) ↔ f =o[l] g' := by
  simp only [IsLittleO_def]
  -- ⊢ (∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f fun x => ‖g' x‖) ↔ ∀ ⦃c : ℝ⦄, 0 < c → I …
  exact forall₂_congr fun _ _ => isBigOWith_norm_right
  -- 🎉 no goals
#align asymptotics.is_o_norm_right Asymptotics.isLittleO_norm_right

@[simp]
theorem isLittleO_abs_right : (f =o[l] fun x => |u x|) ↔ f =o[l] u :=
  @isLittleO_norm_right _ _ ℝ _ _ _ _ _
#align asymptotics.is_o_abs_right Asymptotics.isLittleO_abs_right

alias ⟨IsLittleO.of_norm_right, IsLittleO.norm_right⟩ := isLittleO_norm_right
#align asymptotics.is_o.of_norm_right Asymptotics.IsLittleO.of_norm_right
#align asymptotics.is_o.norm_right Asymptotics.IsLittleO.norm_right

alias ⟨IsLittleO.of_abs_right, IsLittleO.abs_right⟩ := isLittleO_abs_right
#align asymptotics.is_o.of_abs_right Asymptotics.IsLittleO.of_abs_right
#align asymptotics.is_o.abs_right Asymptotics.IsLittleO.abs_right

@[simp]
theorem isBigOWith_norm_left : IsBigOWith c l (fun x => ‖f' x‖) g ↔ IsBigOWith c l f' g := by
  simp only [IsBigOWith_def, norm_norm]
  -- 🎉 no goals
#align asymptotics.is_O_with_norm_left Asymptotics.isBigOWith_norm_left

@[simp]
theorem isBigOWith_abs_left : IsBigOWith c l (fun x => |u x|) g ↔ IsBigOWith c l u g :=
  @isBigOWith_norm_left _ _ _ _ _ _ g u l
#align asymptotics.is_O_with_abs_left Asymptotics.isBigOWith_abs_left

alias ⟨IsBigOWith.of_norm_left, IsBigOWith.norm_left⟩ := isBigOWith_norm_left
#align asymptotics.is_O_with.of_norm_left Asymptotics.IsBigOWith.of_norm_left
#align asymptotics.is_O_with.norm_left Asymptotics.IsBigOWith.norm_left

alias ⟨IsBigOWith.of_abs_left, IsBigOWith.abs_left⟩ := isBigOWith_abs_left
#align asymptotics.is_O_with.of_abs_left Asymptotics.IsBigOWith.of_abs_left
#align asymptotics.is_O_with.abs_left Asymptotics.IsBigOWith.abs_left

@[simp]
theorem isBigO_norm_left : (fun x => ‖f' x‖) =O[l] g ↔ f' =O[l] g := by
  simp only [IsBigO_def]
  -- ⊢ (∃ c, IsBigOWith c l (fun x => ‖f' x‖) g) ↔ ∃ c, IsBigOWith c l f' g
  exact exists_congr fun _ => isBigOWith_norm_left
  -- 🎉 no goals
#align asymptotics.is_O_norm_left Asymptotics.isBigO_norm_left

@[simp]
theorem isBigO_abs_left : (fun x => |u x|) =O[l] g ↔ u =O[l] g :=
  @isBigO_norm_left _ _ _ _ _ g u l
#align asymptotics.is_O_abs_left Asymptotics.isBigO_abs_left

alias ⟨IsBigO.of_norm_left, IsBigO.norm_left⟩ := isBigO_norm_left
#align asymptotics.is_O.of_norm_left Asymptotics.IsBigO.of_norm_left
#align asymptotics.is_O.norm_left Asymptotics.IsBigO.norm_left

alias ⟨IsBigO.of_abs_left, IsBigO.abs_left⟩ := isBigO_abs_left
#align asymptotics.is_O.of_abs_left Asymptotics.IsBigO.of_abs_left
#align asymptotics.is_O.abs_left Asymptotics.IsBigO.abs_left

@[simp]
theorem isLittleO_norm_left : (fun x => ‖f' x‖) =o[l] g ↔ f' =o[l] g := by
  simp only [IsLittleO_def]
  -- ⊢ (∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l (fun x => ‖f' x‖) g) ↔ ∀ ⦃c : ℝ⦄, 0 < c → …
  exact forall₂_congr fun _ _ => isBigOWith_norm_left
  -- 🎉 no goals
#align asymptotics.is_o_norm_left Asymptotics.isLittleO_norm_left

@[simp]
theorem isLittleO_abs_left : (fun x => |u x|) =o[l] g ↔ u =o[l] g :=
  @isLittleO_norm_left _ _ _ _ _ g u l
#align asymptotics.is_o_abs_left Asymptotics.isLittleO_abs_left

alias ⟨IsLittleO.of_norm_left, IsLittleO.norm_left⟩ := isLittleO_norm_left
#align asymptotics.is_o.of_norm_left Asymptotics.IsLittleO.of_norm_left
#align asymptotics.is_o.norm_left Asymptotics.IsLittleO.norm_left

alias ⟨IsLittleO.of_abs_left, IsLittleO.abs_left⟩ := isLittleO_abs_left
#align asymptotics.is_o.of_abs_left Asymptotics.IsLittleO.of_abs_left
#align asymptotics.is_o.abs_left Asymptotics.IsLittleO.abs_left

theorem isBigOWith_norm_norm :
    (IsBigOWith c l (fun x => ‖f' x‖) fun x => ‖g' x‖) ↔ IsBigOWith c l f' g' :=
  isBigOWith_norm_left.trans isBigOWith_norm_right
#align asymptotics.is_O_with_norm_norm Asymptotics.isBigOWith_norm_norm

theorem isBigOWith_abs_abs :
    (IsBigOWith c l (fun x => |u x|) fun x => |v x|) ↔ IsBigOWith c l u v :=
  isBigOWith_abs_left.trans isBigOWith_abs_right
#align asymptotics.is_O_with_abs_abs Asymptotics.isBigOWith_abs_abs

alias ⟨IsBigOWith.of_norm_norm, IsBigOWith.norm_norm⟩ := isBigOWith_norm_norm
#align asymptotics.is_O_with.of_norm_norm Asymptotics.IsBigOWith.of_norm_norm
#align asymptotics.is_O_with.norm_norm Asymptotics.IsBigOWith.norm_norm

alias ⟨IsBigOWith.of_abs_abs, IsBigOWith.abs_abs⟩ := isBigOWith_abs_abs
#align asymptotics.is_O_with.of_abs_abs Asymptotics.IsBigOWith.of_abs_abs
#align asymptotics.is_O_with.abs_abs Asymptotics.IsBigOWith.abs_abs

theorem isBigO_norm_norm : ((fun x => ‖f' x‖) =O[l] fun x => ‖g' x‖) ↔ f' =O[l] g' :=
  isBigO_norm_left.trans isBigO_norm_right
#align asymptotics.is_O_norm_norm Asymptotics.isBigO_norm_norm

theorem isBigO_abs_abs : ((fun x => |u x|) =O[l] fun x => |v x|) ↔ u =O[l] v :=
  isBigO_abs_left.trans isBigO_abs_right
#align asymptotics.is_O_abs_abs Asymptotics.isBigO_abs_abs

alias ⟨IsBigO.of_norm_norm, IsBigO.norm_norm⟩ := isBigO_norm_norm
#align asymptotics.is_O.of_norm_norm Asymptotics.IsBigO.of_norm_norm
#align asymptotics.is_O.norm_norm Asymptotics.IsBigO.norm_norm

alias ⟨IsBigO.of_abs_abs, IsBigO.abs_abs⟩ := isBigO_abs_abs
#align asymptotics.is_O.of_abs_abs Asymptotics.IsBigO.of_abs_abs
#align asymptotics.is_O.abs_abs Asymptotics.IsBigO.abs_abs

theorem isLittleO_norm_norm : ((fun x => ‖f' x‖) =o[l] fun x => ‖g' x‖) ↔ f' =o[l] g' :=
  isLittleO_norm_left.trans isLittleO_norm_right
#align asymptotics.is_o_norm_norm Asymptotics.isLittleO_norm_norm

theorem isLittleO_abs_abs : ((fun x => |u x|) =o[l] fun x => |v x|) ↔ u =o[l] v :=
  isLittleO_abs_left.trans isLittleO_abs_right
#align asymptotics.is_o_abs_abs Asymptotics.isLittleO_abs_abs

alias ⟨IsLittleO.of_norm_norm, IsLittleO.norm_norm⟩ := isLittleO_norm_norm
#align asymptotics.is_o.of_norm_norm Asymptotics.IsLittleO.of_norm_norm
#align asymptotics.is_o.norm_norm Asymptotics.IsLittleO.norm_norm

alias ⟨IsLittleO.of_abs_abs, IsLittleO.abs_abs⟩ := isLittleO_abs_abs
#align asymptotics.is_o.of_abs_abs Asymptotics.IsLittleO.of_abs_abs
#align asymptotics.is_o.abs_abs Asymptotics.IsLittleO.abs_abs

end NormAbs

/-! ### Simplification: negate -/


@[simp]
theorem isBigOWith_neg_right : (IsBigOWith c l f fun x => -g' x) ↔ IsBigOWith c l f g' := by
  simp only [IsBigOWith_def, norm_neg]
  -- 🎉 no goals
#align asymptotics.is_O_with_neg_right Asymptotics.isBigOWith_neg_right

alias ⟨IsBigOWith.of_neg_right, IsBigOWith.neg_right⟩ := isBigOWith_neg_right
#align asymptotics.is_O_with.of_neg_right Asymptotics.IsBigOWith.of_neg_right
#align asymptotics.is_O_with.neg_right Asymptotics.IsBigOWith.neg_right

@[simp]
theorem isBigO_neg_right : (f =O[l] fun x => -g' x) ↔ f =O[l] g' := by
  simp only [IsBigO_def]
  -- ⊢ (∃ c, IsBigOWith c l f fun x => -g' x) ↔ ∃ c, IsBigOWith c l f g'
  exact exists_congr fun _ => isBigOWith_neg_right
  -- 🎉 no goals
#align asymptotics.is_O_neg_right Asymptotics.isBigO_neg_right

alias ⟨IsBigO.of_neg_right, IsBigO.neg_right⟩ := isBigO_neg_right
#align asymptotics.is_O.of_neg_right Asymptotics.IsBigO.of_neg_right
#align asymptotics.is_O.neg_right Asymptotics.IsBigO.neg_right

@[simp]
theorem isLittleO_neg_right : (f =o[l] fun x => -g' x) ↔ f =o[l] g' := by
  simp only [IsLittleO_def]
  -- ⊢ (∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l f fun x => -g' x) ↔ ∀ ⦃c : ℝ⦄, 0 < c → Is …
  exact forall₂_congr fun _ _ => isBigOWith_neg_right
  -- 🎉 no goals
#align asymptotics.is_o_neg_right Asymptotics.isLittleO_neg_right

alias ⟨IsLittleO.of_neg_right, IsLittleO.neg_right⟩ := isLittleO_neg_right
#align asymptotics.is_o.of_neg_right Asymptotics.IsLittleO.of_neg_right
#align asymptotics.is_o.neg_right Asymptotics.IsLittleO.neg_right

@[simp]
theorem isBigOWith_neg_left : IsBigOWith c l (fun x => -f' x) g ↔ IsBigOWith c l f' g := by
  simp only [IsBigOWith_def, norm_neg]
  -- 🎉 no goals
#align asymptotics.is_O_with_neg_left Asymptotics.isBigOWith_neg_left

alias ⟨IsBigOWith.of_neg_left, IsBigOWith.neg_left⟩ := isBigOWith_neg_left
#align asymptotics.is_O_with.of_neg_left Asymptotics.IsBigOWith.of_neg_left
#align asymptotics.is_O_with.neg_left Asymptotics.IsBigOWith.neg_left

@[simp]
theorem isBigO_neg_left : (fun x => -f' x) =O[l] g ↔ f' =O[l] g := by
  simp only [IsBigO_def]
  -- ⊢ (∃ c, IsBigOWith c l (fun x => -f' x) g) ↔ ∃ c, IsBigOWith c l f' g
  exact exists_congr fun _ => isBigOWith_neg_left
  -- 🎉 no goals
#align asymptotics.is_O_neg_left Asymptotics.isBigO_neg_left

alias ⟨IsBigO.of_neg_left, IsBigO.neg_left⟩ := isBigO_neg_left
#align asymptotics.is_O.of_neg_left Asymptotics.IsBigO.of_neg_left
#align asymptotics.is_O.neg_left Asymptotics.IsBigO.neg_left

@[simp]
theorem isLittleO_neg_left : (fun x => -f' x) =o[l] g ↔ f' =o[l] g := by
  simp only [IsLittleO_def]
  -- ⊢ (∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l (fun x => -f' x) g) ↔ ∀ ⦃c : ℝ⦄, 0 < c →  …
  exact forall₂_congr fun _ _ => isBigOWith_neg_left
  -- 🎉 no goals
#align asymptotics.is_o_neg_left Asymptotics.isLittleO_neg_left

alias ⟨IsLittleO.of_neg_left, IsLittleO.neg_left⟩ := isLittleO_neg_left
#align asymptotics.is_o.of_neg_left Asymptotics.IsLittleO.of_neg_left
#align asymptotics.is_o.neg_left Asymptotics.IsLittleO.neg_left

/-! ### Product of functions (right) -/


theorem isBigOWith_fst_prod : IsBigOWith 1 l f' fun x => (f' x, g' x) :=
  isBigOWith_of_le l fun _x => le_max_left _ _
#align asymptotics.is_O_with_fst_prod Asymptotics.isBigOWith_fst_prod

theorem isBigOWith_snd_prod : IsBigOWith 1 l g' fun x => (f' x, g' x) :=
  isBigOWith_of_le l fun _x => le_max_right _ _
#align asymptotics.is_O_with_snd_prod Asymptotics.isBigOWith_snd_prod

theorem isBigO_fst_prod : f' =O[l] fun x => (f' x, g' x) :=
  isBigOWith_fst_prod.isBigO
#align asymptotics.is_O_fst_prod Asymptotics.isBigO_fst_prod

theorem isBigO_snd_prod : g' =O[l] fun x => (f' x, g' x) :=
  isBigOWith_snd_prod.isBigO
#align asymptotics.is_O_snd_prod Asymptotics.isBigO_snd_prod

theorem isBigO_fst_prod' {f' : α → E' × F'} : (fun x => (f' x).1) =O[l] f' := by
  simpa [IsBigO_def, IsBigOWith_def] using isBigO_fst_prod (E' := E') (F' := F')
  -- 🎉 no goals
#align asymptotics.is_O_fst_prod' Asymptotics.isBigO_fst_prod'

theorem isBigO_snd_prod' {f' : α → E' × F'} : (fun x => (f' x).2) =O[l] f' := by
  simpa [IsBigO_def, IsBigOWith_def] using isBigO_snd_prod (E' := E') (F' := F')
  -- 🎉 no goals
#align asymptotics.is_O_snd_prod' Asymptotics.isBigO_snd_prod'

section

variable (f' k')

theorem IsBigOWith.prod_rightl (h : IsBigOWith c l f g') (hc : 0 ≤ c) :
    IsBigOWith c l f fun x => (g' x, k' x) :=
  (h.trans isBigOWith_fst_prod hc).congr_const (mul_one c)
#align asymptotics.is_O_with.prod_rightl Asymptotics.IsBigOWith.prod_rightl

theorem IsBigO.prod_rightl (h : f =O[l] g') : f =O[l] fun x => (g' x, k' x) :=
  let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightl k' cnonneg).isBigO
#align asymptotics.is_O.prod_rightl Asymptotics.IsBigO.prod_rightl

theorem IsLittleO.prod_rightl (h : f =o[l] g') : f =o[l] fun x => (g' x, k' x) :=
  IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).prod_rightl k' cpos.le
#align asymptotics.is_o.prod_rightl Asymptotics.IsLittleO.prod_rightl

theorem IsBigOWith.prod_rightr (h : IsBigOWith c l f g') (hc : 0 ≤ c) :
    IsBigOWith c l f fun x => (f' x, g' x) :=
  (h.trans isBigOWith_snd_prod hc).congr_const (mul_one c)
#align asymptotics.is_O_with.prod_rightr Asymptotics.IsBigOWith.prod_rightr

theorem IsBigO.prod_rightr (h : f =O[l] g') : f =O[l] fun x => (f' x, g' x) :=
  let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightr f' cnonneg).isBigO
#align asymptotics.is_O.prod_rightr Asymptotics.IsBigO.prod_rightr

theorem IsLittleO.prod_rightr (h : f =o[l] g') : f =o[l] fun x => (f' x, g' x) :=
  IsLittleO.of_isBigOWith fun _c cpos => (h.forall_isBigOWith cpos).prod_rightr f' cpos.le
#align asymptotics.is_o.prod_rightr Asymptotics.IsLittleO.prod_rightr

end

theorem IsBigOWith.prod_left_same (hf : IsBigOWith c l f' k') (hg : IsBigOWith c l g' k') :
    IsBigOWith c l (fun x => (f' x, g' x)) k' := by
  rw [isBigOWith_iff] at *; filter_upwards [hf, hg]with x using max_le
  -- ⊢ ∀ᶠ (x : α) in l, ‖(f' x, g' x)‖ ≤ c * ‖k' x‖
                            -- 🎉 no goals
#align asymptotics.is_O_with.prod_left_same Asymptotics.IsBigOWith.prod_left_same

theorem IsBigOWith.prod_left (hf : IsBigOWith c l f' k') (hg : IsBigOWith c' l g' k') :
    IsBigOWith (max c c') l (fun x => (f' x, g' x)) k' :=
  (hf.weaken <| le_max_left c c').prod_left_same (hg.weaken <| le_max_right c c')
#align asymptotics.is_O_with.prod_left Asymptotics.IsBigOWith.prod_left

theorem IsBigOWith.prod_left_fst (h : IsBigOWith c l (fun x => (f' x, g' x)) k') :
    IsBigOWith c l f' k' :=
  (isBigOWith_fst_prod.trans h zero_le_one).congr_const <| one_mul c
#align asymptotics.is_O_with.prod_left_fst Asymptotics.IsBigOWith.prod_left_fst

theorem IsBigOWith.prod_left_snd (h : IsBigOWith c l (fun x => (f' x, g' x)) k') :
    IsBigOWith c l g' k' :=
  (isBigOWith_snd_prod.trans h zero_le_one).congr_const <| one_mul c
#align asymptotics.is_O_with.prod_left_snd Asymptotics.IsBigOWith.prod_left_snd

theorem isBigOWith_prod_left :
    IsBigOWith c l (fun x => (f' x, g' x)) k' ↔ IsBigOWith c l f' k' ∧ IsBigOWith c l g' k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left_same h.2⟩
#align asymptotics.is_O_with_prod_left Asymptotics.isBigOWith_prod_left

theorem IsBigO.prod_left (hf : f' =O[l] k') (hg : g' =O[l] k') : (fun x => (f' x, g' x)) =O[l] k' :=
  let ⟨_c, hf⟩ := hf.isBigOWith
  let ⟨_c', hg⟩ := hg.isBigOWith
  (hf.prod_left hg).isBigO
#align asymptotics.is_O.prod_left Asymptotics.IsBigO.prod_left

theorem IsBigO.prod_left_fst : (fun x => (f' x, g' x)) =O[l] k' → f' =O[l] k' :=
  IsBigO.trans isBigO_fst_prod
#align asymptotics.is_O.prod_left_fst Asymptotics.IsBigO.prod_left_fst

theorem IsBigO.prod_left_snd : (fun x => (f' x, g' x)) =O[l] k' → g' =O[l] k' :=
  IsBigO.trans isBigO_snd_prod
#align asymptotics.is_O.prod_left_snd Asymptotics.IsBigO.prod_left_snd

@[simp]
theorem isBigO_prod_left : (fun x => (f' x, g' x)) =O[l] k' ↔ f' =O[l] k' ∧ g' =O[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left h.2⟩
#align asymptotics.is_O_prod_left Asymptotics.isBigO_prod_left

theorem IsLittleO.prod_left (hf : f' =o[l] k') (hg : g' =o[l] k') :
    (fun x => (f' x, g' x)) =o[l] k' :=
  IsLittleO.of_isBigOWith fun _c hc =>
    (hf.forall_isBigOWith hc).prod_left_same (hg.forall_isBigOWith hc)
#align asymptotics.is_o.prod_left Asymptotics.IsLittleO.prod_left

theorem IsLittleO.prod_left_fst : (fun x => (f' x, g' x)) =o[l] k' → f' =o[l] k' :=
  IsBigO.trans_isLittleO isBigO_fst_prod
#align asymptotics.is_o.prod_left_fst Asymptotics.IsLittleO.prod_left_fst

theorem IsLittleO.prod_left_snd : (fun x => (f' x, g' x)) =o[l] k' → g' =o[l] k' :=
  IsBigO.trans_isLittleO isBigO_snd_prod
#align asymptotics.is_o.prod_left_snd Asymptotics.IsLittleO.prod_left_snd

@[simp]
theorem isLittleO_prod_left : (fun x => (f' x, g' x)) =o[l] k' ↔ f' =o[l] k' ∧ g' =o[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left h.2⟩
#align asymptotics.is_o_prod_left Asymptotics.isLittleO_prod_left

theorem IsBigOWith.eq_zero_imp (h : IsBigOWith c l f'' g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  Eventually.mono h.bound fun x hx hg => norm_le_zero_iff.1 <| by simpa [hg] using hx
                                                                  -- 🎉 no goals
#align asymptotics.is_O_with.eq_zero_imp Asymptotics.IsBigOWith.eq_zero_imp

theorem IsBigO.eq_zero_imp (h : f'' =O[l] g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  let ⟨_C, hC⟩ := h.isBigOWith
  hC.eq_zero_imp
#align asymptotics.is_O.eq_zero_imp Asymptotics.IsBigO.eq_zero_imp

/-! ### Addition and subtraction -/


section add_sub

variable {f₁ f₂ : α → E'} {g₁ g₂ : α → F'}

theorem IsBigOWith.add (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g) :
    IsBigOWith (c₁ + c₂) l (fun x => f₁ x + f₂ x) g := by
  rw [IsBigOWith_def] at *;
  -- ⊢ ∀ᶠ (x : α) in l, ‖f₁ x + f₂ x‖ ≤ (c₁ + c₂) * ‖g x‖
    filter_upwards [h₁,
      h₂]with x hx₁ hx₂ using calc
        ‖f₁ x + f₂ x‖ ≤ c₁ * ‖g x‖ + c₂ * ‖g x‖ := norm_add_le_of_le hx₁ hx₂
        _ = (c₁ + c₂) * ‖g x‖ := (add_mul _ _ _).symm
#align asymptotics.is_O_with.add Asymptotics.IsBigOWith.add

theorem IsBigO.add (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  let ⟨_c₁, hc₁⟩ := h₁.isBigOWith
  let ⟨_c₂, hc₂⟩ := h₂.isBigOWith
  (hc₁.add hc₂).isBigO
#align asymptotics.is_O.add Asymptotics.IsBigO.add

theorem IsLittleO.add (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g :=
  IsLittleO.of_isBigOWith fun c cpos =>
    ((h₁.forall_isBigOWith <| half_pos cpos).add (h₂.forall_isBigOWith <|
      half_pos cpos)).congr_const (add_halves c)
#align asymptotics.is_o.add Asymptotics.IsLittleO.add

theorem IsLittleO.add_add (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x + f₂ x) =o[l] fun x => ‖g₁ x‖ + ‖g₂ x‖ := by
  refine' (h₁.trans_le fun x => _).add (h₂.trans_le _) <;> simp [abs_of_nonneg, add_nonneg]
  -- ⊢ ‖g₁ x‖ ≤ ‖‖g₁ x‖ + ‖g₂ x‖‖
                                                           -- 🎉 no goals
                                                           -- 🎉 no goals
#align asymptotics.is_o.add_add Asymptotics.IsLittleO.add_add

theorem IsBigO.add_isLittleO (h₁ : f₁ =O[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.add h₂.isBigO
#align asymptotics.is_O.add_is_o Asymptotics.IsBigO.add_isLittleO

theorem IsLittleO.add_isBigO (h₁ : f₁ =o[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.isBigO.add h₂
#align asymptotics.is_o.add_is_O Asymptotics.IsLittleO.add_isBigO

theorem IsBigOWith.add_isLittleO (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₁.add (h₂.forall_isBigOWith (sub_pos.2 hc))).congr_const (add_sub_cancel'_right _ _)
#align asymptotics.is_O_with.add_is_o Asymptotics.IsBigOWith.add_isLittleO

theorem IsLittleO.add_isBigOWith (h₁ : f₁ =o[l] g) (h₂ : IsBigOWith c₁ l f₂ g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₂.add_isLittleO h₁ hc).congr_left fun _ => add_comm _ _
#align asymptotics.is_o.add_is_O_with Asymptotics.IsLittleO.add_isBigOWith

theorem IsBigOWith.sub (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g) :
    IsBigOWith (c₁ + c₂) l (fun x => f₁ x - f₂ x) g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left
  -- 🎉 no goals
#align asymptotics.is_O_with.sub Asymptotics.IsBigOWith.sub

theorem IsBigOWith.sub_isLittleO (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x - f₂ x) g := by
  simpa only [sub_eq_add_neg] using h₁.add_isLittleO h₂.neg_left hc
  -- 🎉 no goals
#align asymptotics.is_O_with.sub_is_o Asymptotics.IsBigOWith.sub_isLittleO

theorem IsBigO.sub (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left
  -- 🎉 no goals
#align asymptotics.is_O.sub Asymptotics.IsBigO.sub

theorem IsLittleO.sub (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left
  -- 🎉 no goals
#align asymptotics.is_o.sub Asymptotics.IsLittleO.sub

end add_sub

/-!
### Lemmas about `IsBigO (f₁ - f₂) g l` / `IsLittleO (f₁ - f₂) g l` treated as a binary relation
-/


section IsBigOOAsRel

variable {f₁ f₂ f₃ : α → E'}

theorem IsBigOWith.symm (h : IsBigOWith c l (fun x => f₁ x - f₂ x) g) :
    IsBigOWith c l (fun x => f₂ x - f₁ x) g :=
  h.neg_left.congr_left fun _x => neg_sub _ _
#align asymptotics.is_O_with.symm Asymptotics.IsBigOWith.symm

theorem isBigOWith_comm :
    IsBigOWith c l (fun x => f₁ x - f₂ x) g ↔ IsBigOWith c l (fun x => f₂ x - f₁ x) g :=
  ⟨IsBigOWith.symm, IsBigOWith.symm⟩
#align asymptotics.is_O_with_comm Asymptotics.isBigOWith_comm

theorem IsBigO.symm (h : (fun x => f₁ x - f₂ x) =O[l] g) : (fun x => f₂ x - f₁ x) =O[l] g :=
  h.neg_left.congr_left fun _x => neg_sub _ _
#align asymptotics.is_O.symm Asymptotics.IsBigO.symm

theorem isBigO_comm : (fun x => f₁ x - f₂ x) =O[l] g ↔ (fun x => f₂ x - f₁ x) =O[l] g :=
  ⟨IsBigO.symm, IsBigO.symm⟩
#align asymptotics.is_O_comm Asymptotics.isBigO_comm

theorem IsLittleO.symm (h : (fun x => f₁ x - f₂ x) =o[l] g) : (fun x => f₂ x - f₁ x) =o[l] g := by
  simpa only [neg_sub] using h.neg_left
  -- 🎉 no goals
#align asymptotics.is_o.symm Asymptotics.IsLittleO.symm

theorem isLittleO_comm : (fun x => f₁ x - f₂ x) =o[l] g ↔ (fun x => f₂ x - f₁ x) =o[l] g :=
  ⟨IsLittleO.symm, IsLittleO.symm⟩
#align asymptotics.is_o_comm Asymptotics.isLittleO_comm

theorem IsBigOWith.triangle (h₁ : IsBigOWith c l (fun x => f₁ x - f₂ x) g)
    (h₂ : IsBigOWith c' l (fun x => f₂ x - f₃ x) g) :
    IsBigOWith (c + c') l (fun x => f₁ x - f₃ x) g :=
  (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _
#align asymptotics.is_O_with.triangle Asymptotics.IsBigOWith.triangle

theorem IsBigO.triangle (h₁ : (fun x => f₁ x - f₂ x) =O[l] g)
    (h₂ : (fun x => f₂ x - f₃ x) =O[l] g) : (fun x => f₁ x - f₃ x) =O[l] g :=
  (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _
#align asymptotics.is_O.triangle Asymptotics.IsBigO.triangle

theorem IsLittleO.triangle (h₁ : (fun x => f₁ x - f₂ x) =o[l] g)
    (h₂ : (fun x => f₂ x - f₃ x) =o[l] g) : (fun x => f₁ x - f₃ x) =o[l] g :=
  (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _
#align asymptotics.is_o.triangle Asymptotics.IsLittleO.triangle

theorem IsBigO.congr_of_sub (h : (fun x => f₁ x - f₂ x) =O[l] g) : f₁ =O[l] g ↔ f₂ =O[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun _x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun _x => sub_add_cancel _ _⟩
#align asymptotics.is_O.congr_of_sub Asymptotics.IsBigO.congr_of_sub

theorem IsLittleO.congr_of_sub (h : (fun x => f₁ x - f₂ x) =o[l] g) : f₁ =o[l] g ↔ f₂ =o[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun _x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun _x => sub_add_cancel _ _⟩
#align asymptotics.is_o.congr_of_sub Asymptotics.IsLittleO.congr_of_sub

end IsBigOOAsRel

/-! ### Zero, one, and other constants -/


section ZeroConst

variable (g g' l)

theorem isLittleO_zero : (fun _x => (0 : E')) =o[l] g' :=
  IsLittleO.of_bound fun c hc =>
    univ_mem' fun x => by simpa using mul_nonneg hc.le (norm_nonneg <| g' x)
                          -- 🎉 no goals
#align asymptotics.is_o_zero Asymptotics.isLittleO_zero

theorem isBigOWith_zero (hc : 0 ≤ c) : IsBigOWith c l (fun _x => (0 : E')) g' :=
  IsBigOWith.of_bound <| univ_mem' fun x => by simpa using mul_nonneg hc (norm_nonneg <| g' x)
                                               -- 🎉 no goals
#align asymptotics.is_O_with_zero Asymptotics.isBigOWith_zero

theorem isBigOWith_zero' : IsBigOWith 0 l (fun _x => (0 : E')) g :=
  IsBigOWith.of_bound <| univ_mem' fun x => by simp
                                               -- 🎉 no goals
#align asymptotics.is_O_with_zero' Asymptotics.isBigOWith_zero'

theorem isBigO_zero : (fun _x => (0 : E')) =O[l] g :=
  isBigO_iff_isBigOWith.2 ⟨0, isBigOWith_zero' _ _⟩
#align asymptotics.is_O_zero Asymptotics.isBigO_zero

theorem isBigO_refl_left : (fun x => f' x - f' x) =O[l] g' :=
  (isBigO_zero g' l).congr_left fun _x => (sub_self _).symm
#align asymptotics.is_O_refl_left Asymptotics.isBigO_refl_left

theorem isLittleO_refl_left : (fun x => f' x - f' x) =o[l] g' :=
  (isLittleO_zero g' l).congr_left fun _x => (sub_self _).symm
#align asymptotics.is_o_refl_left Asymptotics.isLittleO_refl_left

variable {g g' l}

@[simp]
theorem isBigOWith_zero_right_iff : (IsBigOWith c l f'' fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0 := by
  simp only [IsBigOWith_def, exists_prop, true_and_iff, norm_zero, mul_zero,
    norm_le_zero_iff, EventuallyEq, Pi.zero_apply]
#align asymptotics.is_O_with_zero_right_iff Asymptotics.isBigOWith_zero_right_iff

@[simp]
theorem isBigO_zero_right_iff : (f'' =O[l] fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h =>
    let ⟨_c, hc⟩ := h.isBigOWith
    isBigOWith_zero_right_iff.1 hc,
    fun h => (isBigOWith_zero_right_iff.2 h : IsBigOWith 1 _ _ _).isBigO⟩
#align asymptotics.is_O_zero_right_iff Asymptotics.isBigO_zero_right_iff

@[simp]
theorem isLittleO_zero_right_iff : (f'' =o[l] fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h => isBigO_zero_right_iff.1 h.isBigO, fun h =>
    IsLittleO.of_isBigOWith fun _c _hc => isBigOWith_zero_right_iff.2 h⟩
#align asymptotics.is_o_zero_right_iff Asymptotics.isLittleO_zero_right_iff

theorem isBigOWith_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) :
    IsBigOWith (‖c‖ / ‖c'‖) l (fun _x : α => c) fun _x => c' := by
  simp only [IsBigOWith_def]
  -- ⊢ ∀ᶠ (x : α) in l, ‖c‖ ≤ ‖c‖ / ‖c'‖ * ‖c'‖
  apply univ_mem'
  -- ⊢ ∀ (a : α), a ∈ {x | (fun x => ‖c‖ ≤ ‖c‖ / ‖c'‖ * ‖c'‖) x}
  intro x
  -- ⊢ x ∈ {x | (fun x => ‖c‖ ≤ ‖c‖ / ‖c'‖ * ‖c'‖) x}
  simp only [mem_setOf_eq]
  -- ⊢ ‖c‖ ≤ ‖c‖ / ‖c'‖ * ‖c'‖
  rw [div_mul_cancel]
  -- ⊢ ‖c'‖ ≠ 0
  rwa [Ne.def, norm_eq_zero]
  -- 🎉 no goals
#align asymptotics.is_O_with_const_const Asymptotics.isBigOWith_const_const

theorem isBigO_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) :
    (fun _x : α => c) =O[l] fun _x => c' :=
  (isBigOWith_const_const c hc' l).isBigO
#align asymptotics.is_O_const_const Asymptotics.isBigO_const_const

@[simp]
theorem isBigO_const_const_iff {c : E''} {c' : F''} (l : Filter α) [l.NeBot] :
    ((fun _x : α => c) =O[l] fun _x => c') ↔ c' = 0 → c = 0 := by
  rcases eq_or_ne c' 0 with (rfl | hc')
  -- ⊢ ((fun _x => c) =O[l] fun _x => 0) ↔ 0 = 0 → c = 0
  · simp [EventuallyEq]
    -- 🎉 no goals
  · simp [hc', isBigO_const_const _ hc']
    -- 🎉 no goals
#align asymptotics.is_O_const_const_iff Asymptotics.isBigO_const_const_iff

@[simp]
theorem isBigO_pure {x} : f'' =O[pure x] g'' ↔ g'' x = 0 → f'' x = 0 :=
  calc
    f'' =O[pure x] g'' ↔ (fun _y : α => f'' x) =O[pure x] fun _ => g'' x := isBigO_congr rfl rfl
    _ ↔ g'' x = 0 → f'' x = 0 := isBigO_const_const_iff _
#align asymptotics.is_O_pure Asymptotics.isBigO_pure

end ZeroConst

@[simp]
theorem isBigOWith_top : IsBigOWith c ⊤ f g ↔ ∀ x, ‖f x‖ ≤ c * ‖g x‖ := by rw [IsBigOWith_def]; rfl
                                                                           -- ⊢ (∀ᶠ (x : α) in ⊤, ‖f x‖ ≤ c * ‖g x‖) ↔ ∀ (x : α), ‖f x‖ ≤ c * ‖g x‖
                                                                                                -- 🎉 no goals
#align asymptotics.is_O_with_top Asymptotics.isBigOWith_top

@[simp]
theorem isBigO_top : f =O[⊤] g ↔ ∃ C, ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by rw [isBigO_iff]; rfl
                                                                   -- ⊢ (∃ c, ∀ᶠ (x : α) in ⊤, ‖f x‖ ≤ c * ‖g x‖) ↔ ∃ C, ∀ (x : α), ‖f x‖ ≤ C * ‖g x‖
                                                                                    -- 🎉 no goals
#align asymptotics.is_O_top Asymptotics.isBigO_top

@[simp]
theorem isLittleO_top : f'' =o[⊤] g'' ↔ ∀ x, f'' x = 0 := by
  refine' ⟨_, fun h => (isLittleO_zero g'' ⊤).congr (fun x => (h x).symm) fun x => rfl⟩
  -- ⊢ f'' =o[⊤] g'' → ∀ (x : α), f'' x = 0
  simp only [isLittleO_iff, eventually_top]
  -- ⊢ (∀ ⦃c : ℝ⦄, 0 < c → ∀ (x : α), ‖f'' x‖ ≤ c * ‖g'' x‖) → ∀ (x : α), f'' x = 0
  refine' fun h x => norm_le_zero_iff.1 _
  -- ⊢ ‖f'' x‖ ≤ 0
  have : Tendsto (fun c : ℝ => c * ‖g'' x‖) (𝓝[>] 0) (𝓝 0) :=
    ((continuous_id.mul continuous_const).tendsto' _ _ (zero_mul _)).mono_left
      inf_le_left
  exact
    le_of_tendsto_of_tendsto tendsto_const_nhds this
      (eventually_nhdsWithin_iff.2 <| eventually_of_forall fun c hc => h hc x)
#align asymptotics.is_o_top Asymptotics.isLittleO_top

@[simp]
theorem isBigOWith_principal {s : Set α} : IsBigOWith c (𝓟 s) f g ↔ ∀ x ∈ s, ‖f x‖ ≤ c * ‖g x‖ :=
  by rw [IsBigOWith_def]; rfl
     -- ⊢ (∀ᶠ (x : α) in 𝓟 s, ‖f x‖ ≤ c * ‖g x‖) ↔ ∀ (x : α), x ∈ s → ‖f x‖ ≤ c * ‖g x‖
                          -- 🎉 no goals
#align asymptotics.is_O_with_principal Asymptotics.isBigOWith_principal

theorem isBigO_principal {s : Set α} : f =O[𝓟 s] g ↔ ∃ c, ∀ x ∈ s, ‖f x‖ ≤ c * ‖g x‖ := by
  rw [isBigO_iff]; rfl
  -- ⊢ (∃ c, ∀ᶠ (x : α) in 𝓟 s, ‖f x‖ ≤ c * ‖g x‖) ↔ ∃ c, ∀ (x : α), x ∈ s → ‖f x‖  …
                   -- 🎉 no goals
#align asymptotics.is_O_principal Asymptotics.isBigO_principal

section

variable (F)
variable [One F] [NormOneClass F]

theorem isBigOWith_const_one (c : E) (l : Filter α) :
    IsBigOWith ‖c‖ l (fun _x : α => c) fun _x => (1 : F) := by simp [isBigOWith_iff]
                                                               -- 🎉 no goals
#align asymptotics.is_O_with_const_one Asymptotics.isBigOWith_const_one

theorem isBigO_const_one (c : E) (l : Filter α) : (fun _x : α => c) =O[l] fun _x => (1 : F) :=
  (isBigOWith_const_one F c l).isBigO
#align asymptotics.is_O_const_one Asymptotics.isBigO_const_one

theorem isLittleO_const_iff_isLittleO_one {c : F''} (hc : c ≠ 0) :
    (f =o[l] fun _x => c) ↔ f =o[l] fun _x => (1 : F) :=
  ⟨fun h => h.trans_isBigOWith (isBigOWith_const_one _ _ _) (norm_pos_iff.2 hc), fun h =>
    h.trans_isBigO <| isBigO_const_const _ hc _⟩
#align asymptotics.is_o_const_iff_is_o_one Asymptotics.isLittleO_const_iff_isLittleO_one

@[simp]
theorem isLittleO_one_iff : f' =o[l] (fun _x => 1 : α → F) ↔ Tendsto f' l (𝓝 0) := by
  simp only [isLittleO_iff, norm_one, mul_one, Metric.nhds_basis_closedBall.tendsto_right_iff,
    Metric.mem_closedBall, dist_zero_right]
#align asymptotics.is_o_one_iff Asymptotics.isLittleO_one_iff

@[simp]
theorem isBigO_one_iff : f =O[l] (fun _x => 1 : α → F) ↔
    IsBoundedUnder (· ≤ ·) l fun x => ‖f x‖ := by
  simp only [isBigO_iff, norm_one, mul_one]
  -- ⊢ (∃ c, ∀ᶠ (x : α) in l, ‖f x‖ ≤ c) ↔ IsBoundedUnder (fun x x_1 => x ≤ x_1) l  …
  rfl
  -- 🎉 no goals
#align asymptotics.is_O_one_iff Asymptotics.isBigO_one_iff

alias ⟨_, _root_.Filter.IsBoundedUnder.isBigO_one⟩ := isBigO_one_iff
#align filter.is_bounded_under.is_O_one Filter.IsBoundedUnder.isBigO_one

@[simp]
theorem isLittleO_one_left_iff : (fun _x => 1 : α → F) =o[l] f ↔ Tendsto (fun x => ‖f x‖) l atTop :=
  calc
    (fun _x => 1 : α → F) =o[l] f ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖(1 : F)‖ ≤ ‖f x‖ :=
      isLittleO_iff_nat_mul_le_aux <| Or.inl fun _x => by simp only [norm_one, zero_le_one]
                                                          -- 🎉 no goals
    _ ↔ ∀ n : ℕ, True → ∀ᶠ x in l, ‖f x‖ ∈ Ici (n : ℝ) := by
      simp only [norm_one, mul_one, true_imp_iff, mem_Ici]
      -- 🎉 no goals
    _ ↔ Tendsto (fun x => ‖f x‖) l atTop :=
      atTop_hasCountableBasis_of_archimedean.1.tendsto_right_iff.symm
#align asymptotics.is_o_one_left_iff Asymptotics.isLittleO_one_left_iff

theorem _root_.Filter.Tendsto.isBigO_one {c : E'} (h : Tendsto f' l (𝓝 c)) :
    f' =O[l] (fun _x => 1 : α → F) :=
  h.norm.isBoundedUnder_le.isBigO_one F
#align filter.tendsto.is_O_one Filter.Tendsto.isBigO_one

theorem IsBigO.trans_tendsto_nhds (hfg : f =O[l] g') {y : F'} (hg : Tendsto g' l (𝓝 y)) :
    f =O[l] (fun _x => 1 : α → F) :=
  hfg.trans <| hg.isBigO_one F
#align asymptotics.is_O.trans_tendsto_nhds Asymptotics.IsBigO.trans_tendsto_nhds

end

theorem isLittleO_const_iff {c : F''} (hc : c ≠ 0) :
    (f'' =o[l] fun _x => c) ↔ Tendsto f'' l (𝓝 0) :=
  (isLittleO_const_iff_isLittleO_one ℝ hc).trans (isLittleO_one_iff _)
#align asymptotics.is_o_const_iff Asymptotics.isLittleO_const_iff

theorem isLittleO_id_const {c : F''} (hc : c ≠ 0) : (fun x : E'' => x) =o[𝓝 0] fun _x => c :=
  (isLittleO_const_iff hc).mpr (continuous_id.tendsto 0)
#align asymptotics.is_o_id_const Asymptotics.isLittleO_id_const

theorem _root_.Filter.IsBoundedUnder.isBigO_const (h : IsBoundedUnder (· ≤ ·) l (norm ∘ f))
    {c : F''} (hc : c ≠ 0) : f =O[l] fun _x => c :=
  (h.isBigO_one ℝ).trans (isBigO_const_const _ hc _)
#align filter.is_bounded_under.is_O_const Filter.IsBoundedUnder.isBigO_const

theorem isBigO_const_of_tendsto {y : E''} (h : Tendsto f'' l (𝓝 y)) {c : F''} (hc : c ≠ 0) :
    f'' =O[l] fun _x => c :=
  h.norm.isBoundedUnder_le.isBigO_const hc
#align asymptotics.is_O_const_of_tendsto Asymptotics.isBigO_const_of_tendsto

theorem IsBigO.isBoundedUnder_le {c : F} (h : f =O[l] fun _x => c) :
    IsBoundedUnder (· ≤ ·) l (norm ∘ f) :=
  let ⟨c', hc'⟩ := h.bound
  ⟨c' * ‖c‖, eventually_map.2 hc'⟩
#align asymptotics.is_O.is_bounded_under_le Asymptotics.IsBigO.isBoundedUnder_le

theorem isBigO_const_of_ne {c : F''} (hc : c ≠ 0) :
    (f =O[l] fun _x => c) ↔ IsBoundedUnder (· ≤ ·) l (norm ∘ f) :=
  ⟨fun h => h.isBoundedUnder_le, fun h => h.isBigO_const hc⟩
#align asymptotics.is_O_const_of_ne Asymptotics.isBigO_const_of_ne

theorem isBigO_const_iff {c : F''} : (f'' =O[l] fun _x => c) ↔
    (c = 0 → f'' =ᶠ[l] 0) ∧ IsBoundedUnder (· ≤ ·) l fun x => ‖f'' x‖ := by
  refine' ⟨fun h => ⟨fun hc => isBigO_zero_right_iff.1 (by rwa [← hc]), h.isBoundedUnder_le⟩, _⟩
  -- ⊢ ((c = 0 → f'' =ᶠ[l] 0) ∧ IsBoundedUnder (fun x x_1 => x ≤ x_1) l fun x => ‖f …
  rintro ⟨hcf, hf⟩
  -- ⊢ f'' =O[l] fun _x => c
  rcases eq_or_ne c 0 with (hc | hc)
  -- ⊢ f'' =O[l] fun _x => c
  exacts [(hcf hc).trans_isBigO (isBigO_zero _ _), hf.isBigO_const hc]
  -- 🎉 no goals
#align asymptotics.is_O_const_iff Asymptotics.isBigO_const_iff

theorem isBigO_iff_isBoundedUnder_le_div (h : ∀ᶠ x in l, g'' x ≠ 0) :
    f =O[l] g'' ↔ IsBoundedUnder (· ≤ ·) l fun x => ‖f x‖ / ‖g'' x‖ := by
  simp only [isBigO_iff, IsBoundedUnder, IsBounded, eventually_map]
  -- ⊢ (∃ c, ∀ᶠ (x : α) in l, ‖f x‖ ≤ c * ‖g'' x‖) ↔ ∃ b, ∀ᶠ (a : α) in l, ‖f a‖ /  …
  exact
    exists_congr fun c =>
      eventually_congr <| h.mono fun x hx => (div_le_iff <| norm_pos_iff.2 hx).symm
#align asymptotics.is_O_iff_is_bounded_under_le_div Asymptotics.isBigO_iff_isBoundedUnder_le_div

/-- `(fun x ↦ c) =O[l] f` if and only if `f` is bounded away from zero. -/
theorem isBigO_const_left_iff_pos_le_norm {c : E''} (hc : c ≠ 0) :
    (fun _x => c) =O[l] f' ↔ ∃ b, 0 < b ∧ ∀ᶠ x in l, b ≤ ‖f' x‖ := by
  constructor
  -- ⊢ (fun _x => c) =O[l] f' → ∃ b, 0 < b ∧ ∀ᶠ (x : α) in l, b ≤ ‖f' x‖
  · intro h
    -- ⊢ ∃ b, 0 < b ∧ ∀ᶠ (x : α) in l, b ≤ ‖f' x‖
    rcases h.exists_pos with ⟨C, hC₀, hC⟩
    -- ⊢ ∃ b, 0 < b ∧ ∀ᶠ (x : α) in l, b ≤ ‖f' x‖
    refine' ⟨‖c‖ / C, div_pos (norm_pos_iff.2 hc) hC₀, _⟩
    -- ⊢ ∀ᶠ (x : α) in l, ‖c‖ / C ≤ ‖f' x‖
    exact hC.bound.mono fun x => (div_le_iff' hC₀).2
    -- 🎉 no goals
  · rintro ⟨b, hb₀, hb⟩
    -- ⊢ (fun _x => c) =O[l] f'
    refine' IsBigO.of_bound (‖c‖ / b) (hb.mono fun x hx => _)
    -- ⊢ ‖c‖ ≤ ‖c‖ / b * ‖f' x‖
    rw [div_mul_eq_mul_div, mul_div_assoc]
    -- ⊢ ‖c‖ ≤ ‖c‖ * (‖f' x‖ / b)
    exact le_mul_of_one_le_right (norm_nonneg _) ((one_le_div hb₀).2 hx)
    -- 🎉 no goals
#align asymptotics.is_O_const_left_iff_pos_le_norm Asymptotics.isBigO_const_left_iff_pos_le_norm

section

variable (𝕜)

end

theorem IsBigO.trans_tendsto (hfg : f'' =O[l] g'') (hg : Tendsto g'' l (𝓝 0)) :
    Tendsto f'' l (𝓝 0) :=
  (isLittleO_one_iff ℝ).1 <| hfg.trans_isLittleO <| (isLittleO_one_iff ℝ).2 hg
#align asymptotics.is_O.trans_tendsto Asymptotics.IsBigO.trans_tendsto

theorem IsLittleO.trans_tendsto (hfg : f'' =o[l] g'') (hg : Tendsto g'' l (𝓝 0)) :
    Tendsto f'' l (𝓝 0) :=
  hfg.isBigO.trans_tendsto hg
#align asymptotics.is_o.trans_tendsto Asymptotics.IsLittleO.trans_tendsto

/-! ### Multiplication by a constant -/


theorem isBigOWith_const_mul_self (c : R) (f : α → R) (l : Filter α) :
    IsBigOWith ‖c‖ l (fun x => c * f x) f :=
  isBigOWith_of_le' _ fun _x => norm_mul_le _ _
#align asymptotics.is_O_with_const_mul_self Asymptotics.isBigOWith_const_mul_self

theorem isBigO_const_mul_self (c : R) (f : α → R) (l : Filter α) : (fun x => c * f x) =O[l] f :=
  (isBigOWith_const_mul_self c f l).isBigO
#align asymptotics.is_O_const_mul_self Asymptotics.isBigO_const_mul_self

theorem IsBigOWith.const_mul_left {f : α → R} (h : IsBigOWith c l f g) (c' : R) :
    IsBigOWith (‖c'‖ * c) l (fun x => c' * f x) g :=
  (isBigOWith_const_mul_self c' f l).trans h (norm_nonneg c')
#align asymptotics.is_O_with.const_mul_left Asymptotics.IsBigOWith.const_mul_left

theorem IsBigO.const_mul_left {f : α → R} (h : f =O[l] g) (c' : R) : (fun x => c' * f x) =O[l] g :=
  let ⟨_c, hc⟩ := h.isBigOWith
  (hc.const_mul_left c').isBigO
#align asymptotics.is_O.const_mul_left Asymptotics.IsBigO.const_mul_left

theorem isBigOWith_self_const_mul' (u : Rˣ) (f : α → R) (l : Filter α) :
    IsBigOWith ‖(↑u⁻¹ : R)‖ l f fun x => ↑u * f x := by
  refine' (isBigOWith_const_mul_self ↑u⁻¹ _ l).congr_left _
  -- ⊢ ∀ (x : α), ↑u⁻¹ * (↑u * f x) = f x
  exact fun x => u.inv_mul_cancel_left (f x)
  -- 🎉 no goals
  -- porting note: Lean just had trouble elaborating correctly, but this fixes it.
#align asymptotics.is_O_with_self_const_mul' Asymptotics.isBigOWith_self_const_mul'

theorem isBigOWith_self_const_mul (c : 𝕜) (hc : c ≠ 0) (f : α → 𝕜) (l : Filter α) :
    IsBigOWith ‖c‖⁻¹ l f fun x => c * f x :=
  (isBigOWith_self_const_mul' (Units.mk0 c hc) f l).congr_const <| norm_inv c
#align asymptotics.is_O_with_self_const_mul Asymptotics.isBigOWith_self_const_mul

theorem isBigO_self_const_mul' {c : R} (hc : IsUnit c) (f : α → R) (l : Filter α) :
    f =O[l] fun x => c * f x :=
  let ⟨u, hu⟩ := hc
  hu ▸ (isBigOWith_self_const_mul' u f l).isBigO
#align asymptotics.is_O_self_const_mul' Asymptotics.isBigO_self_const_mul'

theorem isBigO_self_const_mul (c : 𝕜) (hc : c ≠ 0) (f : α → 𝕜) (l : Filter α) :
    f =O[l] fun x => c * f x :=
  isBigO_self_const_mul' (IsUnit.mk0 c hc) f l
#align asymptotics.is_O_self_const_mul Asymptotics.isBigO_self_const_mul

theorem isBigO_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) :
    (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  ⟨(isBigO_self_const_mul' hc f l).trans, fun h => h.const_mul_left c⟩
#align asymptotics.is_O_const_mul_left_iff' Asymptotics.isBigO_const_mul_left_iff'

theorem isBigO_const_mul_left_iff {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  isBigO_const_mul_left_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_O_const_mul_left_iff Asymptotics.isBigO_const_mul_left_iff

theorem IsLittleO.const_mul_left {f : α → R} (h : f =o[l] g) (c : R) : (fun x => c * f x) =o[l] g :=
  (isBigO_const_mul_self c f l).trans_isLittleO h
#align asymptotics.is_o.const_mul_left Asymptotics.IsLittleO.const_mul_left

theorem isLittleO_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) :
    (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  ⟨(isBigO_self_const_mul' hc f l).trans_isLittleO, fun h => h.const_mul_left c⟩
#align asymptotics.is_o_const_mul_left_iff' Asymptotics.isLittleO_const_mul_left_iff'

theorem isLittleO_const_mul_left_iff {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  isLittleO_const_mul_left_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_o_const_mul_left_iff Asymptotics.isLittleO_const_mul_left_iff

theorem IsBigOWith.of_const_mul_right {g : α → R} {c : R} (hc' : 0 ≤ c')
    (h : IsBigOWith c' l f fun x => c * g x) : IsBigOWith (c' * ‖c‖) l f g :=
  h.trans (isBigOWith_const_mul_self c g l) hc'
#align asymptotics.is_O_with.of_const_mul_right Asymptotics.IsBigOWith.of_const_mul_right

theorem IsBigO.of_const_mul_right {g : α → R} {c : R} (h : f =O[l] fun x => c * g x) : f =O[l] g :=
  let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.of_const_mul_right cnonneg).isBigO
#align asymptotics.is_O.of_const_mul_right Asymptotics.IsBigO.of_const_mul_right

theorem IsBigOWith.const_mul_right' {g : α → R} {u : Rˣ} {c' : ℝ} (hc' : 0 ≤ c')
    (h : IsBigOWith c' l f g) : IsBigOWith (c' * ‖(↑u⁻¹ : R)‖) l f fun x => ↑u * g x :=
  h.trans (isBigOWith_self_const_mul' _ _ _) hc'
#align asymptotics.is_O_with.const_mul_right' Asymptotics.IsBigOWith.const_mul_right'

theorem IsBigOWith.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) {c' : ℝ} (hc' : 0 ≤ c')
    (h : IsBigOWith c' l f g) : IsBigOWith (c' * ‖c‖⁻¹) l f fun x => c * g x :=
  h.trans (isBigOWith_self_const_mul c hc g l) hc'
#align asymptotics.is_O_with.const_mul_right Asymptotics.IsBigOWith.const_mul_right

theorem IsBigO.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : f =O[l] g) :
    f =O[l] fun x => c * g x :=
  h.trans (isBigO_self_const_mul' hc g l)
#align asymptotics.is_O.const_mul_right' Asymptotics.IsBigO.const_mul_right'

theorem IsBigO.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : f =O[l] g) :
    f =O[l] fun x => c * g x :=
  h.const_mul_right' <| IsUnit.mk0 c hc
#align asymptotics.is_O.const_mul_right Asymptotics.IsBigO.const_mul_right

theorem isBigO_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) :
    (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩
#align asymptotics.is_O_const_mul_right_iff' Asymptotics.isBigO_const_mul_right_iff'

theorem isBigO_const_mul_right_iff {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  isBigO_const_mul_right_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_O_const_mul_right_iff Asymptotics.isBigO_const_mul_right_iff

theorem IsLittleO.of_const_mul_right {g : α → R} {c : R} (h : f =o[l] fun x => c * g x) :
    f =o[l] g :=
  h.trans_isBigO (isBigO_const_mul_self c g l)
#align asymptotics.is_o.of_const_mul_right Asymptotics.IsLittleO.of_const_mul_right

theorem IsLittleO.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : f =o[l] g) :
    f =o[l] fun x => c * g x :=
  h.trans_isBigO (isBigO_self_const_mul' hc g l)
#align asymptotics.is_o.const_mul_right' Asymptotics.IsLittleO.const_mul_right'

theorem IsLittleO.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : f =o[l] g) :
    f =o[l] fun x => c * g x :=
  h.const_mul_right' <| IsUnit.mk0 c hc
#align asymptotics.is_o.const_mul_right Asymptotics.IsLittleO.const_mul_right

theorem isLittleO_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) :
    (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩
#align asymptotics.is_o_const_mul_right_iff' Asymptotics.isLittleO_const_mul_right_iff'

theorem isLittleO_const_mul_right_iff {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
    (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  isLittleO_const_mul_right_iff' <| IsUnit.mk0 c hc
#align asymptotics.is_o_const_mul_right_iff Asymptotics.isLittleO_const_mul_right_iff

/-! ### Multiplication -/


theorem IsBigOWith.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} {c₁ c₂ : ℝ} (h₁ : IsBigOWith c₁ l f₁ g₁)
    (h₂ : IsBigOWith c₂ l f₂ g₂) :
    IsBigOWith (c₁ * c₂) l (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x := by
  simp only [IsBigOWith_def] at *
  -- ⊢ ∀ᶠ (x : α) in l, ‖f₁ x * f₂ x‖ ≤ c₁ * c₂ * ‖g₁ x * g₂ x‖
  filter_upwards [h₁, h₂]with _ hx₁ hx₂
  -- ⊢ ‖f₁ a✝ * f₂ a✝‖ ≤ c₁ * c₂ * ‖g₁ a✝ * g₂ a✝‖
  apply le_trans (norm_mul_le _ _)
  -- ⊢ ‖f₁ a✝‖ * ‖f₂ a✝‖ ≤ c₁ * c₂ * ‖g₁ a✝ * g₂ a✝‖
  convert mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_trans (norm_nonneg _) hx₁) using 1
  -- ⊢ c₁ * c₂ * ‖g₁ a✝ * g₂ a✝‖ = c₁ * ‖g₁ a✝‖ * (c₂ * ‖g₂ a✝‖)
  rw [norm_mul, mul_mul_mul_comm]
  -- 🎉 no goals
#align asymptotics.is_O_with.mul Asymptotics.IsBigOWith.mul

theorem IsBigO.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x => f₁ x * f₂ x) =O[l] fun x => g₁ x * g₂ x :=
  let ⟨_c, hc⟩ := h₁.isBigOWith
  let ⟨_c', hc'⟩ := h₂.isBigOWith
  (hc.mul hc').isBigO
#align asymptotics.is_O.mul Asymptotics.IsBigO.mul

theorem IsBigO.mul_isLittleO {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x := by
  simp only [IsLittleO_def] at *
  -- ⊢ ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x
  intro c cpos
  -- ⊢ IsBigOWith c l (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩
  -- ⊢ IsBigOWith c l (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x
  exact (hc'.mul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel' _ (ne_of_gt c'pos))
  -- 🎉 no goals
#align asymptotics.is_O.mul_is_o Asymptotics.IsBigO.mul_isLittleO

theorem IsLittleO.mul_isBigO {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x := by
  simp only [IsLittleO_def] at *
  -- ⊢ ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x
  intro c cpos
  -- ⊢ IsBigOWith c l (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩
  -- ⊢ IsBigOWith c l (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x
  exact ((h₁ (div_pos cpos c'pos)).mul hc').congr_const (div_mul_cancel _ (ne_of_gt c'pos))
  -- 🎉 no goals
#align asymptotics.is_o.mul_is_O Asymptotics.IsLittleO.mul_isBigO

theorem IsLittleO.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x :=
  h₁.mul_isBigO h₂.isBigO
#align asymptotics.is_o.mul Asymptotics.IsLittleO.mul

theorem IsBigOWith.pow' {f : α → R} {g : α → 𝕜} (h : IsBigOWith c l f g) :
    ∀ n : ℕ, IsBigOWith (Nat.casesOn n ‖(1 : R)‖ fun n => c ^ (n + 1))
      l (fun x => f x ^ n) fun x => g x ^ n
  | 0 => by simpa using isBigOWith_const_const (1 : R) (one_ne_zero' 𝕜) l
            -- 🎉 no goals
  | 1 => by simpa
            -- 🎉 no goals
  | n + 2 => by simpa [pow_succ] using h.mul (IsBigOWith.pow' h (n + 1))
                -- 🎉 no goals
#align asymptotics.is_O_with.pow' Asymptotics.IsBigOWith.pow'

theorem IsBigOWith.pow [NormOneClass R] {f : α → R} {g : α → 𝕜} (h : IsBigOWith c l f g) :
    ∀ n : ℕ, IsBigOWith (c ^ n) l (fun x => f x ^ n) fun x => g x ^ n
  | 0 => by simpa using h.pow' 0
            -- 🎉 no goals
  | n + 1 => h.pow' (n + 1)
#align asymptotics.is_O_with.pow Asymptotics.IsBigOWith.pow

theorem IsBigOWith.of_pow {n : ℕ} {f : α → 𝕜} {g : α → R} (h : IsBigOWith c l (f ^ n) (g ^ n))
    (hn : n ≠ 0) (hc : c ≤ c' ^ n) (hc' : 0 ≤ c') : IsBigOWith c' l f g :=
  IsBigOWith.of_bound <|
    (h.weaken hc).bound.mono fun x hx =>
      le_of_pow_le_pow n (mul_nonneg hc' <| norm_nonneg _) hn.bot_lt <|
        calc
          ‖f x‖ ^ n = ‖f x ^ n‖ := (norm_pow _ _).symm
          _ ≤ c' ^ n * ‖g x ^ n‖ := hx
          _ ≤ c' ^ n * ‖g x‖ ^ n := by gcongr; exact norm_pow_le' _ hn.bot_lt
                                       -- ⊢ ‖g x ^ n‖ ≤ ‖g x‖ ^ n
                                               -- 🎉 no goals
          _ = (c' * ‖g x‖) ^ n := (mul_pow _ _ _).symm
#align asymptotics.is_O_with.of_pow Asymptotics.IsBigOWith.of_pow

theorem IsBigO.pow {f : α → R} {g : α → 𝕜} (h : f =O[l] g) (n : ℕ) :
    (fun x => f x ^ n) =O[l] fun x => g x ^ n :=
  let ⟨_C, hC⟩ := h.isBigOWith
  isBigO_iff_isBigOWith.2 ⟨_, hC.pow' n⟩
#align asymptotics.is_O.pow Asymptotics.IsBigO.pow

theorem IsBigO.of_pow {f : α → 𝕜} {g : α → R} {n : ℕ} (hn : n ≠ 0) (h : (f ^ n) =O[l] (g ^ n)) :
    f =O[l] g := by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  -- ⊢ f =O[l] g
  obtain ⟨c, hc₀, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ C ≤ c ^ n
  -- ⊢ ∃ c, 0 ≤ c ∧ C ≤ c ^ n
  exact ((eventually_ge_atTop _).and <| (tendsto_pow_atTop hn).eventually_ge_atTop C).exists
  -- ⊢ f =O[l] g
  exact (hC.of_pow hn hc hc₀).isBigO
  -- 🎉 no goals
#align asymptotics.is_O.of_pow Asymptotics.IsBigO.of_pow

theorem IsLittleO.pow {f : α → R} {g : α → 𝕜} (h : f =o[l] g) {n : ℕ} (hn : 0 < n) :
    (fun x => f x ^ n) =o[l] fun x => g x ^ n := by
  cases' n with n; exact hn.false.elim; clear hn
  -- ⊢ (fun x => f x ^ Nat.zero) =o[l] fun x => g x ^ Nat.zero
                   -- ⊢ (fun x => f x ^ Nat.succ n) =o[l] fun x => g x ^ Nat.succ n
                                        -- ⊢ (fun x => f x ^ Nat.succ n) =o[l] fun x => g x ^ Nat.succ n
  induction' n with n ihn
  -- ⊢ (fun x => f x ^ Nat.succ Nat.zero) =o[l] fun x => g x ^ Nat.succ Nat.zero
  · simpa only [Nat.zero_eq, ←Nat.one_eq_succ_zero, pow_one]
    -- 🎉 no goals
  · convert h.mul ihn <;> simp [pow_succ]
    -- ⊢ f x✝ ^ Nat.succ (Nat.succ n) = f x✝ * f x✝ ^ Nat.succ n
                          -- 🎉 no goals
                          -- 🎉 no goals
#align asymptotics.is_o.pow Asymptotics.IsLittleO.pow

theorem IsLittleO.of_pow {f : α → 𝕜} {g : α → R} {n : ℕ} (h : (f ^ n) =o[l] (g ^ n)) (hn : n ≠ 0) :
    f =o[l] g :=
  IsLittleO.of_isBigOWith fun _c hc => (h.def' <| pow_pos hc _).of_pow hn le_rfl hc.le
#align asymptotics.is_o.of_pow Asymptotics.IsLittleO.of_pow

/-! ### Inverse -/


theorem IsBigOWith.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : IsBigOWith c l f g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : IsBigOWith c l (fun x => (g x)⁻¹) fun x => (f x)⁻¹ := by
  refine' IsBigOWith.of_bound (h.bound.mp (h₀.mono fun x h₀ hle => _))
  -- ⊢ ‖(g x)⁻¹‖ ≤ c * ‖(f x)⁻¹‖
  cases' eq_or_ne (f x) 0 with hx hx
  -- ⊢ ‖(g x)⁻¹‖ ≤ c * ‖(f x)⁻¹‖
  · simp only [hx, h₀ hx, inv_zero, norm_zero, mul_zero]; rfl
    -- ⊢ 0 ≤ 0
                                                          -- 🎉 no goals
  · have hc : 0 < c := pos_of_mul_pos_left ((norm_pos_iff.2 hx).trans_le hle) (norm_nonneg _)
    -- ⊢ ‖(g x)⁻¹‖ ≤ c * ‖(f x)⁻¹‖
    replace hle := inv_le_inv_of_le (norm_pos_iff.2 hx) hle
    -- ⊢ ‖(g x)⁻¹‖ ≤ c * ‖(f x)⁻¹‖
    simpa only [norm_inv, mul_inv, ← div_eq_inv_mul, div_le_iff hc] using hle
    -- 🎉 no goals
#align asymptotics.is_O_with.inv_rev Asymptotics.IsBigOWith.inv_rev

theorem IsBigO.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =O[l] g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : (fun x => (g x)⁻¹) =O[l] fun x => (f x)⁻¹ :=
  let ⟨_c, hc⟩ := h.isBigOWith
  (hc.inv_rev h₀).isBigO
#align asymptotics.is_O.inv_rev Asymptotics.IsBigO.inv_rev

theorem IsLittleO.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =o[l] g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : (fun x => (g x)⁻¹) =o[l] fun x => (f x)⁻¹ :=
  IsLittleO.of_isBigOWith fun _c hc => (h.def' hc).inv_rev h₀
#align asymptotics.is_o.inv_rev Asymptotics.IsLittleO.inv_rev

/-! ### Scalar multiplication -/


section SmulConst

variable [NormedSpace 𝕜 E']

theorem IsBigOWith.const_smul_left (h : IsBigOWith c l f' g) (c' : 𝕜) :
    IsBigOWith (‖c'‖ * c) l (fun x => c' • f' x) g :=
  IsBigOWith.of_norm_left <| by
    simpa only [norm_smul, _root_.norm_norm] using h.norm_left.const_mul_left ‖c'‖
    -- 🎉 no goals
    -- porting note: probably `Asymptotics.IsBigO.norm_norm` and `Asymptotics.IsLittleO.norm_norm`
    -- should be protected.
#align asymptotics.is_O_with.const_smul_left Asymptotics.IsBigOWith.const_smul_left

theorem IsBigO.const_smul_left (h : f' =O[l] g) (c : 𝕜) : (c • f') =O[l] g :=
  let ⟨_b, hb⟩ := h.isBigOWith
  (hb.const_smul_left _).isBigO
#align asymptotics.is_O.const_smul_left Asymptotics.IsBigO.const_smul_left

theorem IsLittleO.const_smul_left (h : f' =o[l] g) (c : 𝕜) : (c • f') =o[l] g :=
  IsLittleO.of_norm_left <| by simpa only [← norm_smul] using h.norm_left.const_mul_left ‖c‖
                               -- 🎉 no goals
#align asymptotics.is_o.const_smul_left Asymptotics.IsLittleO.const_smul_left

theorem isBigO_const_smul_left {c : 𝕜} (hc : c ≠ 0) : (fun x => c • f' x) =O[l] g ↔ f' =O[l] g := by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  -- ⊢ (fun x => c • f' x) =O[l] g ↔ f' =O[l] g
  rw [← isBigO_norm_left]
  -- ⊢ (fun x => ‖c • f' x‖) =O[l] g ↔ f' =O[l] g
  simp only [norm_smul]
  -- ⊢ (fun x => ‖c‖ * ‖f' x‖) =O[l] g ↔ f' =O[l] g
  rw [isBigO_const_mul_left_iff cne0, isBigO_norm_left]
  -- 🎉 no goals
#align asymptotics.is_O_const_smul_left Asymptotics.isBigO_const_smul_left

theorem isLittleO_const_smul_left {c : 𝕜} (hc : c ≠ 0) :
    (fun x => c • f' x) =o[l] g ↔ f' =o[l] g := by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  -- ⊢ (fun x => c • f' x) =o[l] g ↔ f' =o[l] g
  rw [← isLittleO_norm_left]
  -- ⊢ (fun x => ‖c • f' x‖) =o[l] g ↔ f' =o[l] g
  simp only [norm_smul]
  -- ⊢ (fun x => ‖c‖ * ‖f' x‖) =o[l] g ↔ f' =o[l] g
  rw [isLittleO_const_mul_left_iff cne0, isLittleO_norm_left]
  -- 🎉 no goals
#align asymptotics.is_o_const_smul_left Asymptotics.isLittleO_const_smul_left

theorem isBigO_const_smul_right {c : 𝕜} (hc : c ≠ 0) :
    (f =O[l] fun x => c • f' x) ↔ f =O[l] f' := by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  -- ⊢ (f =O[l] fun x => c • f' x) ↔ f =O[l] f'
  rw [← isBigO_norm_right]
  -- ⊢ (f =O[l] fun x => ‖c • f' x‖) ↔ f =O[l] f'
  simp only [norm_smul]
  -- ⊢ (f =O[l] fun x => ‖c‖ * ‖f' x‖) ↔ f =O[l] f'
  rw [isBigO_const_mul_right_iff cne0, isBigO_norm_right]
  -- 🎉 no goals
#align asymptotics.is_O_const_smul_right Asymptotics.isBigO_const_smul_right

theorem isLittleO_const_smul_right {c : 𝕜} (hc : c ≠ 0) :
    (f =o[l] fun x => c • f' x) ↔ f =o[l] f' := by
  have cne0 : ‖c‖ ≠ 0 := mt norm_eq_zero.mp hc
  -- ⊢ (f =o[l] fun x => c • f' x) ↔ f =o[l] f'
  rw [← isLittleO_norm_right]
  -- ⊢ (f =o[l] fun x => ‖c • f' x‖) ↔ f =o[l] f'
  simp only [norm_smul]
  -- ⊢ (f =o[l] fun x => ‖c‖ * ‖f' x‖) ↔ f =o[l] f'
  rw [isLittleO_const_mul_right_iff cne0, isLittleO_norm_right]
  -- 🎉 no goals
#align asymptotics.is_o_const_smul_right Asymptotics.isLittleO_const_smul_right

end SmulConst

section Smul

variable [NormedSpace 𝕜 E'] [NormedSpace 𝕜' F'] {k₁ : α → 𝕜} {k₂ : α → 𝕜'}

theorem IsBigOWith.smul (h₁ : IsBigOWith c l k₁ k₂) (h₂ : IsBigOWith c' l f' g') :
    IsBigOWith (c * c') l (fun x => k₁ x • f' x) fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr rfl _ _).of_norm_norm <;>
  -- ⊢ ∀ (x : α), ‖k₁ x‖ * ‖f' x‖ = ‖k₁ x • f' x‖
    · intros; simp only [norm_smul]
      -- ⊢ ‖k₁ x✝‖ * ‖f' x✝‖ = ‖k₁ x✝ • f' x✝‖
              -- 🎉 no goals
      -- ⊢ ‖k₂ x✝‖ * ‖g' x✝‖ = ‖k₂ x✝ • g' x✝‖
              -- 🎉 no goals
#align asymptotics.is_O_with.smul Asymptotics.IsBigOWith.smul

theorem IsBigO.smul (h₁ : k₁ =O[l] k₂) (h₂ : f' =O[l] g') :
    (fun x => k₁ x • f' x) =O[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr _ _).of_norm_norm <;>
  -- ⊢ ∀ (x : α), ‖k₁ x‖ * ‖f' x‖ = ‖k₁ x • f' x‖
    · intros; simp only [norm_smul]
      -- ⊢ ‖k₁ x✝‖ * ‖f' x✝‖ = ‖k₁ x✝ • f' x✝‖
              -- 🎉 no goals
      -- ⊢ ‖k₂ x✝‖ * ‖g' x✝‖ = ‖k₂ x✝ • g' x✝‖
              -- 🎉 no goals
#align asymptotics.is_O.smul Asymptotics.IsBigO.smul

theorem IsBigO.smul_isLittleO (h₁ : k₁ =O[l] k₂) (h₂ : f' =o[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul_isLittleO h₂.norm_norm).congr _ _).of_norm_norm <;>
  -- ⊢ ∀ (x : α), ‖k₁ x‖ * ‖f' x‖ = ‖k₁ x • f' x‖
    · intros; simp only [norm_smul]
      -- ⊢ ‖k₁ x✝‖ * ‖f' x✝‖ = ‖k₁ x✝ • f' x✝‖
              -- 🎉 no goals
      -- ⊢ ‖k₂ x✝‖ * ‖g' x✝‖ = ‖k₂ x✝ • g' x✝‖
              -- 🎉 no goals
#align asymptotics.is_O.smul_is_o Asymptotics.IsBigO.smul_isLittleO

theorem IsLittleO.smul_isBigO (h₁ : k₁ =o[l] k₂) (h₂ : f' =O[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul_isBigO h₂.norm_norm).congr _ _).of_norm_norm <;>
  -- ⊢ ∀ (x : α), ‖k₁ x‖ * ‖f' x‖ = ‖k₁ x • f' x‖
    · intros; simp only [norm_smul]
      -- ⊢ ‖k₁ x✝‖ * ‖f' x✝‖ = ‖k₁ x✝ • f' x✝‖
              -- 🎉 no goals
      -- ⊢ ‖k₂ x✝‖ * ‖g' x✝‖ = ‖k₂ x✝ • g' x✝‖
              -- 🎉 no goals
#align asymptotics.is_o.smul_is_O Asymptotics.IsLittleO.smul_isBigO

theorem IsLittleO.smul (h₁ : k₁ =o[l] k₂) (h₂ : f' =o[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr _ _).of_norm_norm <;>
  -- ⊢ ∀ (x : α), ‖k₁ x‖ * ‖f' x‖ = ‖k₁ x • f' x‖
    · intros; simp only [norm_smul]
      -- ⊢ ‖k₁ x✝‖ * ‖f' x✝‖ = ‖k₁ x✝ • f' x✝‖
              -- 🎉 no goals
      -- ⊢ ‖k₂ x✝‖ * ‖g' x✝‖ = ‖k₂ x✝ • g' x✝‖
              -- 🎉 no goals
#align asymptotics.is_o.smul Asymptotics.IsLittleO.smul

end Smul

/-! ### Sum -/


section Sum

variable {ι : Type*} {A : ι → α → E'} {C : ι → ℝ} {s : Finset ι}

theorem IsBigOWith.sum (h : ∀ i ∈ s, IsBigOWith (C i) l (A i) g) :
    IsBigOWith (∑ i in s, C i) l (fun x => ∑ i in s, A i x) g := by
  induction' s using Finset.induction_on with i s is IH
  -- ⊢ IsBigOWith (∑ i in ∅, C i) l (fun x => ∑ i in ∅, A i x) g
  · simp only [isBigOWith_zero', Finset.sum_empty, forall_true_iff]
    -- 🎉 no goals
  · simp only [is, Finset.sum_insert, not_false_iff]
    -- ⊢ IsBigOWith (C i + ∑ i in s, C i) l (fun x => A i x + ∑ i in s, A i x) g
    exact (h _ (Finset.mem_insert_self i s)).add (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))
    -- 🎉 no goals
#align asymptotics.is_O_with.sum Asymptotics.IsBigOWith.sum

theorem IsBigO.sum (h : ∀ i ∈ s, A i =O[l] g) : (fun x => ∑ i in s, A i x) =O[l] g := by
  simp only [IsBigO_def] at *
  -- ⊢ ∃ c, IsBigOWith c l (fun x => ∑ i in s, A i x) g
  choose! C hC using h
  -- ⊢ ∃ c, IsBigOWith c l (fun x => ∑ i in s, A i x) g
  exact ⟨_, IsBigOWith.sum hC⟩
  -- 🎉 no goals
#align asymptotics.is_O.sum Asymptotics.IsBigO.sum

theorem IsLittleO.sum (h : ∀ i ∈ s, A i =o[l] g') : (fun x => ∑ i in s, A i x) =o[l] g' := by
  induction' s using Finset.induction_on with i s is IH
  -- ⊢ (fun x => ∑ i in ∅, A i x) =o[l] g'
  · simp only [isLittleO_zero, Finset.sum_empty, forall_true_iff]
    -- 🎉 no goals
  · simp only [is, Finset.sum_insert, not_false_iff]
    -- ⊢ (fun x => A i x + ∑ i in s, A i x) =o[l] g'
    exact (h _ (Finset.mem_insert_self i s)).add (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))
    -- 🎉 no goals
#align asymptotics.is_o.sum Asymptotics.IsLittleO.sum

end Sum

/-! ### Relation between `f = o(g)` and `f / g → 0` -/


theorem IsLittleO.tendsto_div_nhds_zero {f g : α → 𝕜} (h : f =o[l] g) :
    Tendsto (fun x => f x / g x) l (𝓝 0) :=
  (isLittleO_one_iff 𝕜).mp <| by
    calc
      (fun x => f x / g x) =o[l] fun x => g x / g x := by
        simpa only [div_eq_mul_inv] using h.mul_isBigO (isBigO_refl _ _)
      _ =O[l] fun _x => (1 : 𝕜) := isBigO_of_le _ fun x => by simp [div_self_le_one]
#align asymptotics.is_o.tendsto_div_nhds_zero Asymptotics.IsLittleO.tendsto_div_nhds_zero

theorem IsLittleO.tendsto_inv_smul_nhds_zero [NormedSpace 𝕜 E'] {f : α → E'} {g : α → 𝕜}
    {l : Filter α} (h : f =o[l] g) : Tendsto (fun x => (g x)⁻¹ • f x) l (𝓝 0) := by
  simpa only [div_eq_inv_mul, ← norm_inv, ← norm_smul, ← tendsto_zero_iff_norm_tendsto_zero] using
    h.norm_norm.tendsto_div_nhds_zero
#align asymptotics.is_o.tendsto_inv_smul_nhds_zero Asymptotics.IsLittleO.tendsto_inv_smul_nhds_zero

theorem isLittleO_iff_tendsto' {f g : α → 𝕜} (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
    f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  ⟨IsLittleO.tendsto_div_nhds_zero, fun h =>
    (((isLittleO_one_iff _).mpr h).mul_isBigO (isBigO_refl g l)).congr'
      (hgf.mono fun _x => div_mul_cancel_of_imp) (eventually_of_forall fun _x => one_mul _)⟩
#align asymptotics.is_o_iff_tendsto' Asymptotics.isLittleO_iff_tendsto'

theorem isLittleO_iff_tendsto {f g : α → 𝕜} (hgf : ∀ x, g x = 0 → f x = 0) :
    f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  isLittleO_iff_tendsto' (eventually_of_forall hgf)
#align asymptotics.is_o_iff_tendsto Asymptotics.isLittleO_iff_tendsto

alias ⟨_, isLittleO_of_tendsto'⟩ := isLittleO_iff_tendsto'
#align asymptotics.is_o_of_tendsto' Asymptotics.isLittleO_of_tendsto'

alias ⟨_, isLittleO_of_tendsto⟩ := isLittleO_iff_tendsto
#align asymptotics.is_o_of_tendsto Asymptotics.isLittleO_of_tendsto

theorem isLittleO_const_left_of_ne {c : E''} (hc : c ≠ 0) :
    (fun _x => c) =o[l] g ↔ Tendsto (fun x => ‖g x‖) l atTop := by
  simp only [← isLittleO_one_left_iff ℝ]
  -- ⊢ (fun _x => c) =o[l] g ↔ (fun _x => 1) =o[l] fun x => g x
  exact ⟨(isBigO_const_const (1 : ℝ) hc l).trans_isLittleO,
    (isBigO_const_one ℝ c l).trans_isLittleO⟩
#align asymptotics.is_o_const_left_of_ne Asymptotics.isLittleO_const_left_of_ne

@[simp]
theorem isLittleO_const_left {c : E''} :
    (fun _x => c) =o[l] g'' ↔ c = 0 ∨ Tendsto (norm ∘ g'') l atTop := by
  rcases eq_or_ne c 0 with (rfl | hc)
  -- ⊢ (fun _x => 0) =o[l] g'' ↔ 0 = 0 ∨ Tendsto (norm ∘ g'') l atTop
  · simp only [isLittleO_zero, eq_self_iff_true, true_or_iff]
    -- 🎉 no goals
  · simp only [hc, false_or_iff, isLittleO_const_left_of_ne hc]; rfl
    -- ⊢ Tendsto (fun x => ‖g'' x‖) l atTop ↔ Tendsto (norm ∘ g'') l atTop
                                                                 -- 🎉 no goals
#align asymptotics.is_o_const_left Asymptotics.isLittleO_const_left

@[simp 1001] -- porting note: increase priority so that this triggers before `isLittleO_const_left`
theorem isLittleO_const_const_iff [NeBot l] {d : E''} {c : F''} :
    ((fun _x => d) =o[l] fun _x => c) ↔ d = 0 := by
  have : ¬Tendsto (Function.const α ‖c‖) l atTop :=
    not_tendsto_atTop_of_tendsto_nhds tendsto_const_nhds
  simp only [isLittleO_const_left, or_iff_left_iff_imp]
  -- ⊢ Tendsto (norm ∘ fun _x => c) l atTop → d = 0
  exact fun h => (this h).elim
  -- 🎉 no goals
#align asymptotics.is_o_const_const_iff Asymptotics.isLittleO_const_const_iff

@[simp]
theorem isLittleO_pure {x} : f'' =o[pure x] g'' ↔ f'' x = 0 :=
  calc
    f'' =o[pure x] g'' ↔ (fun _y : α => f'' x) =o[pure x] fun _ => g'' x := isLittleO_congr rfl rfl
    _ ↔ f'' x = 0 := isLittleO_const_const_iff
#align asymptotics.is_o_pure Asymptotics.isLittleO_pure

theorem isLittleO_const_id_comap_norm_atTop (c : F'') :
    (fun _x : E'' => c) =o[comap norm atTop] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_comap
#align asymptotics.is_o_const_id_comap_norm_at_top Asymptotics.isLittleO_const_id_comap_norm_atTop

theorem isLittleO_const_id_atTop (c : E'') : (fun _x : ℝ => c) =o[atTop] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_abs_atTop_atTop
#align asymptotics.is_o_const_id_at_top Asymptotics.isLittleO_const_id_atTop

theorem isLittleO_const_id_atBot (c : E'') : (fun _x : ℝ => c) =o[atBot] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_abs_atBot_atTop
#align asymptotics.is_o_const_id_at_bot Asymptotics.isLittleO_const_id_atBot

/-!
### Eventually (u / v) * v = u

If `u` and `v` are linked by an `IsBigOWith` relation, then we
eventually have `(u / v) * v = u`, even if `v` vanishes.
-/


section EventuallyMulDivCancel

variable {u v : α → 𝕜}

theorem IsBigOWith.eventually_mul_div_cancel (h : IsBigOWith c l u v) : u / v * v =ᶠ[l] u :=
  Eventually.mono h.bound fun y hy => div_mul_cancel_of_imp fun hv => by simpa [hv] using hy
                                                                         -- 🎉 no goals
#align asymptotics.is_O_with.eventually_mul_div_cancel Asymptotics.IsBigOWith.eventually_mul_div_cancel

/-- If `u = O(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem IsBigO.eventually_mul_div_cancel (h : u =O[l] v) : u / v * v =ᶠ[l] u :=
  let ⟨_c, hc⟩ := h.isBigOWith
  hc.eventually_mul_div_cancel
#align asymptotics.is_O.eventually_mul_div_cancel Asymptotics.IsBigO.eventually_mul_div_cancel

/-- If `u = o(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem IsLittleO.eventually_mul_div_cancel (h : u =o[l] v) : u / v * v =ᶠ[l] u :=
  (h.forall_isBigOWith zero_lt_one).eventually_mul_div_cancel
#align asymptotics.is_o.eventually_mul_div_cancel Asymptotics.IsLittleO.eventually_mul_div_cancel

end EventuallyMulDivCancel

/-! ### Equivalent definitions of the form `∃ φ, u =ᶠ[l] φ * v` in a `NormedField`. -/


section ExistsMulEq

variable {u v : α → 𝕜}

/-- If `‖φ‖` is eventually bounded by `c`, and `u =ᶠ[l] φ * v`, then we have `IsBigOWith c u v l`.
    This does not require any assumptions on `c`, which is why we keep this version along with
    `IsBigOWith_iff_exists_eq_mul`. -/
theorem isBigOWith_of_eq_mul (φ : α → 𝕜) (hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c) (h : u =ᶠ[l] φ * v) :
    IsBigOWith c l u v := by
  simp only [IsBigOWith_def]
  -- ⊢ ∀ᶠ (x : α) in l, ‖u x‖ ≤ c * ‖v x‖
  refine' h.symm.rw (fun x a => ‖a‖ ≤ c * ‖v x‖) (hφ.mono fun x hx => _)
  -- ⊢ (fun x a => ‖a‖ ≤ c * ‖v x‖) x ((φ * v) x)
  simp only [norm_mul, Pi.mul_apply]
  -- ⊢ ‖φ x‖ * ‖v x‖ ≤ c * ‖v x‖
  gcongr
  -- 🎉 no goals
#align asymptotics.is_O_with_of_eq_mul Asymptotics.isBigOWith_of_eq_mul

theorem isBigOWith_iff_exists_eq_mul (hc : 0 ≤ c) :
    IsBigOWith c l u v ↔ ∃ (φ : α → 𝕜) (_hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c), u =ᶠ[l] φ * v := by
  constructor
  -- ⊢ IsBigOWith c l u v → ∃ φ _hφ, u =ᶠ[l] φ * v
  · intro h
    -- ⊢ ∃ φ _hφ, u =ᶠ[l] φ * v
    use fun x => u x / v x
    -- ⊢ ∃ _hφ, u =ᶠ[l] (fun x => u x / v x) * v
    refine' ⟨Eventually.mono h.bound fun y hy => _, h.eventually_mul_div_cancel.symm⟩
    -- ⊢ ‖u y / v y‖ ≤ c
    simpa using div_le_of_nonneg_of_le_mul (norm_nonneg _) hc hy
    -- 🎉 no goals
  · rintro ⟨φ, hφ, h⟩
    -- ⊢ IsBigOWith c l u v
    exact isBigOWith_of_eq_mul φ hφ h
    -- 🎉 no goals
#align asymptotics.is_O_with_iff_exists_eq_mul Asymptotics.isBigOWith_iff_exists_eq_mul

theorem IsBigOWith.exists_eq_mul (h : IsBigOWith c l u v) (hc : 0 ≤ c) :
    ∃ (φ : α → 𝕜) (_hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c), u =ᶠ[l] φ * v :=
  (isBigOWith_iff_exists_eq_mul hc).mp h
#align asymptotics.is_O_with.exists_eq_mul Asymptotics.IsBigOWith.exists_eq_mul

theorem isBigO_iff_exists_eq_mul :
    u =O[l] v ↔ ∃ (φ : α → 𝕜) (_hφ : l.IsBoundedUnder (· ≤ ·) (norm ∘ φ)), u =ᶠ[l] φ * v := by
  constructor
  -- ⊢ u =O[l] v → ∃ φ _hφ, u =ᶠ[l] φ * v
  · rintro h
    -- ⊢ ∃ φ _hφ, u =ᶠ[l] φ * v
    rcases h.exists_nonneg with ⟨c, hnnc, hc⟩
    -- ⊢ ∃ φ _hφ, u =ᶠ[l] φ * v
    rcases hc.exists_eq_mul hnnc with ⟨φ, hφ, huvφ⟩
    -- ⊢ ∃ φ _hφ, u =ᶠ[l] φ * v
    exact ⟨φ, ⟨c, hφ⟩, huvφ⟩
    -- 🎉 no goals
  · rintro ⟨φ, ⟨c, hφ⟩, huvφ⟩
    -- ⊢ u =O[l] v
    exact isBigO_iff_isBigOWith.2 ⟨c, isBigOWith_of_eq_mul φ hφ huvφ⟩
    -- 🎉 no goals
#align asymptotics.is_O_iff_exists_eq_mul Asymptotics.isBigO_iff_exists_eq_mul

alias ⟨IsBigO.exists_eq_mul, _⟩ := isBigO_iff_exists_eq_mul
#align asymptotics.is_O.exists_eq_mul Asymptotics.IsBigO.exists_eq_mul

theorem isLittleO_iff_exists_eq_mul :
    u =o[l] v ↔ ∃ (φ : α → 𝕜) (_hφ : Tendsto φ l (𝓝 0)), u =ᶠ[l] φ * v := by
  constructor
  -- ⊢ u =o[l] v → ∃ φ _hφ, u =ᶠ[l] φ * v
  · exact fun h => ⟨fun x => u x / v x, h.tendsto_div_nhds_zero, h.eventually_mul_div_cancel.symm⟩
    -- 🎉 no goals
  · simp only [IsLittleO_def]
    -- ⊢ (∃ φ _hφ, u =ᶠ[l] φ * v) → ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c l u v
    rintro ⟨φ, hφ, huvφ⟩ c hpos
    -- ⊢ IsBigOWith c l u v
    rw [NormedAddCommGroup.tendsto_nhds_zero] at hφ
    -- ⊢ IsBigOWith c l u v
    exact isBigOWith_of_eq_mul _ ((hφ c hpos).mono fun x => le_of_lt) huvφ
    -- 🎉 no goals
#align asymptotics.is_o_iff_exists_eq_mul Asymptotics.isLittleO_iff_exists_eq_mul

alias ⟨IsLittleO.exists_eq_mul, _⟩ := isLittleO_iff_exists_eq_mul
#align asymptotics.is_o.exists_eq_mul Asymptotics.IsLittleO.exists_eq_mul

end ExistsMulEq

/-! ### Miscellaneous lemmas -/


theorem div_isBoundedUnder_of_isBigO {α : Type*} {l : Filter α} {f g : α → 𝕜} (h : f =O[l] g) :
    IsBoundedUnder (· ≤ ·) l fun x => ‖f x / g x‖ := by
  obtain ⟨c, h₀, hc⟩ := h.exists_nonneg
  -- ⊢ IsBoundedUnder (fun x x_1 => x ≤ x_1) l fun x => ‖f x / g x‖
  refine' ⟨c, eventually_map.2 (hc.bound.mono fun x hx => _)⟩
  -- ⊢ (fun x x_1 => x ≤ x_1) ‖f x / g x‖ c
  rw [norm_div]
  -- ⊢ (fun x x_1 => x ≤ x_1) (‖f x‖ / ‖g x‖) c
  exact div_le_of_nonneg_of_le_mul (norm_nonneg _) h₀ hx
  -- 🎉 no goals
#align asymptotics.div_is_bounded_under_of_is_O Asymptotics.div_isBoundedUnder_of_isBigO

theorem isBigO_iff_div_isBoundedUnder {α : Type*} {l : Filter α} {f g : α → 𝕜}
    (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
    f =O[l] g ↔ IsBoundedUnder (· ≤ ·) l fun x => ‖f x / g x‖ := by
  refine' ⟨div_isBoundedUnder_of_isBigO, fun h => _⟩
  -- ⊢ f =O[l] g
  obtain ⟨c, hc⟩ := h
  -- ⊢ f =O[l] g
  simp only [eventually_map, norm_div] at hc
  -- ⊢ f =O[l] g
  refine' IsBigO.of_bound c (hc.mp <| hgf.mono fun x hx₁ hx₂ => _)
  -- ⊢ ‖f x‖ ≤ c * ‖g x‖
  by_cases hgx : g x = 0
  -- ⊢ ‖f x‖ ≤ c * ‖g x‖
  · simp [hx₁ hgx, hgx]
    -- 🎉 no goals
  · exact (div_le_iff (norm_pos_iff.2 hgx)).mp hx₂
    -- 🎉 no goals
#align asymptotics.is_O_iff_div_is_bounded_under Asymptotics.isBigO_iff_div_isBoundedUnder

theorem isBigO_of_div_tendsto_nhds {α : Type*} {l : Filter α} {f g : α → 𝕜}
    (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) (c : 𝕜) (H : Filter.Tendsto (f / g) l (𝓝 c)) :
    f =O[l] g :=
  (isBigO_iff_div_isBoundedUnder hgf).2 <| H.norm.isBoundedUnder_le
#align asymptotics.is_O_of_div_tendsto_nhds Asymptotics.isBigO_of_div_tendsto_nhds

theorem IsLittleO.tendsto_zero_of_tendsto {α E 𝕜 : Type*} [NormedAddCommGroup E] [NormedField 𝕜]
    {u : α → E} {v : α → 𝕜} {l : Filter α} {y : 𝕜} (huv : u =o[l] v) (hv : Tendsto v l (𝓝 y)) :
    Tendsto u l (𝓝 0) := by
  suffices h : u =o[l] fun _x => (1 : 𝕜)
  -- ⊢ Tendsto u l (𝓝 0)
  · rwa [isLittleO_one_iff] at h
    -- 🎉 no goals
  exact huv.trans_isBigO (hv.isBigO_one 𝕜)
  -- 🎉 no goals
#align asymptotics.is_o.tendsto_zero_of_tendsto Asymptotics.IsLittleO.tendsto_zero_of_tendsto

theorem isLittleO_pow_pow {m n : ℕ} (h : m < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x ^ m := by
  rcases lt_iff_exists_add.1 h with ⟨p, hp0 : 0 < p, rfl⟩
  -- ⊢ (fun x => x ^ (m + p)) =o[𝓝 0] fun x => x ^ m
  suffices (fun x : 𝕜 => x ^ m * x ^ p) =o[𝓝 0] fun x => x ^ m * 1 ^ p by
    simpa only [pow_add, one_pow, mul_one]
  exact IsBigO.mul_isLittleO (isBigO_refl _ _)
    (IsLittleO.pow ((isLittleO_one_iff _).2 tendsto_id) hp0)
#align asymptotics.is_o_pow_pow Asymptotics.isLittleO_pow_pow

theorem isLittleO_norm_pow_norm_pow {m n : ℕ} (h : m < n) :
    (fun x : E' => ‖x‖ ^ n) =o[𝓝 0] fun x => ‖x‖ ^ m :=
  (isLittleO_pow_pow h).comp_tendsto tendsto_norm_zero
#align asymptotics.is_o_norm_pow_norm_pow Asymptotics.isLittleO_norm_pow_norm_pow

theorem isLittleO_pow_id {n : ℕ} (h : 1 < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x := by
  convert isLittleO_pow_pow h (𝕜 := 𝕜)
  -- ⊢ x✝ = x✝ ^ 1
  simp only [pow_one]
  -- 🎉 no goals
#align asymptotics.is_o_pow_id Asymptotics.isLittleO_pow_id

theorem isLittleO_norm_pow_id {n : ℕ} (h : 1 < n) :
    (fun x : E' => ‖x‖ ^ n) =o[𝓝 0] fun x => x := by
  have := @isLittleO_norm_pow_norm_pow E' _ _ _ h
  -- ⊢ (fun x => ‖x‖ ^ n) =o[𝓝 0] fun x => x
  simp only [pow_one] at this
  -- ⊢ (fun x => ‖x‖ ^ n) =o[𝓝 0] fun x => x
  exact isLittleO_norm_right.mp this
  -- 🎉 no goals
#align asymptotics.is_o_norm_pow_id Asymptotics.isLittleO_norm_pow_id

theorem IsBigO.eq_zero_of_norm_pow_within {f : E'' → F''} {s : Set E''} {x₀ : E''} {n : ℕ}
    (h : f =O[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ n) (hx₀ : x₀ ∈ s) (hn : 0 < n) : f x₀ = 0 :=
  mem_of_mem_nhdsWithin hx₀ h.eq_zero_imp <| by simp_rw [sub_self, norm_zero, zero_pow hn]
                                                -- 🎉 no goals
#align asymptotics.is_O.eq_zero_of_norm_pow_within Asymptotics.IsBigO.eq_zero_of_norm_pow_within

theorem IsBigO.eq_zero_of_norm_pow {f : E'' → F''} {x₀ : E''} {n : ℕ}
    (h : f =O[𝓝 x₀] fun x => ‖x - x₀‖ ^ n) (hn : 0 < n) : f x₀ = 0 := by
  rw [← nhdsWithin_univ] at h
  -- ⊢ f x₀ = 0
  exact h.eq_zero_of_norm_pow_within (mem_univ _) hn
  -- 🎉 no goals
#align asymptotics.is_O.eq_zero_of_norm_pow Asymptotics.IsBigO.eq_zero_of_norm_pow

theorem isLittleO_pow_sub_pow_sub (x₀ : E') {n m : ℕ} (h : n < m) :
    (fun x => ‖x - x₀‖ ^ m) =o[𝓝 x₀] fun x => ‖x - x₀‖ ^ n :=
  haveI : Tendsto (fun x => ‖x - x₀‖) (𝓝 x₀) (𝓝 0) := by
    apply tendsto_norm_zero.comp
    -- ⊢ Tendsto (fun x => x - x₀) (𝓝 x₀) (𝓝 0)
    rw [← sub_self x₀]
    -- ⊢ Tendsto (fun x => x - x₀) (𝓝 x₀) (𝓝 (x₀ - x₀))
    exact tendsto_id.sub tendsto_const_nhds
    -- 🎉 no goals
  (isLittleO_pow_pow h).comp_tendsto this
#align asymptotics.is_o_pow_sub_pow_sub Asymptotics.isLittleO_pow_sub_pow_sub

theorem isLittleO_pow_sub_sub (x₀ : E') {m : ℕ} (h : 1 < m) :
    (fun x => ‖x - x₀‖ ^ m) =o[𝓝 x₀] fun x => x - x₀ := by
  simpa only [isLittleO_norm_right, pow_one] using isLittleO_pow_sub_pow_sub x₀ h
  -- 🎉 no goals
#align asymptotics.is_o_pow_sub_sub Asymptotics.isLittleO_pow_sub_sub

theorem IsBigOWith.right_le_sub_of_lt_1 {f₁ f₂ : α → E'} (h : IsBigOWith c l f₁ f₂) (hc : c < 1) :
    IsBigOWith (1 / (1 - c)) l f₂ fun x => f₂ x - f₁ x :=
  IsBigOWith.of_bound <|
    mem_of_superset h.bound fun x hx => by
      simp only [mem_setOf_eq] at hx ⊢
      -- ⊢ ‖f₂ x‖ ≤ 1 / (1 - c) * ‖f₂ x - f₁ x‖
      rw [mul_comm, one_div, ← div_eq_mul_inv, _root_.le_div_iff, mul_sub, mul_one, mul_comm]
      -- ⊢ ‖f₂ x‖ - c * ‖f₂ x‖ ≤ ‖f₂ x - f₁ x‖
      · exact le_trans (sub_le_sub_left hx _) (norm_sub_norm_le _ _)
        -- 🎉 no goals
      · exact sub_pos.2 hc
        -- 🎉 no goals
#align asymptotics.is_O_with.right_le_sub_of_lt_1 Asymptotics.IsBigOWith.right_le_sub_of_lt_1

theorem IsBigOWith.right_le_add_of_lt_1 {f₁ f₂ : α → E'} (h : IsBigOWith c l f₁ f₂) (hc : c < 1) :
    IsBigOWith (1 / (1 - c)) l f₂ fun x => f₁ x + f₂ x :=
  (h.neg_right.right_le_sub_of_lt_1 hc).neg_right.of_neg_left.congr rfl (fun x => rfl) fun x => by
    rw [neg_sub, sub_neg_eq_add]
    -- 🎉 no goals
#align asymptotics.is_O_with.right_le_add_of_lt_1 Asymptotics.IsBigOWith.right_le_add_of_lt_1

theorem IsLittleO.right_isBigO_sub {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) :
    f₂ =O[l] fun x => f₂ x - f₁ x :=
  ((h.def' one_half_pos).right_le_sub_of_lt_1 one_half_lt_one).isBigO
#align asymptotics.is_o.right_is_O_sub Asymptotics.IsLittleO.right_isBigO_sub

theorem IsLittleO.right_isBigO_add {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) :
    f₂ =O[l] fun x => f₁ x + f₂ x :=
  ((h.def' one_half_pos).right_le_add_of_lt_1 one_half_lt_one).isBigO
#align asymptotics.is_o.right_is_O_add Asymptotics.IsLittleO.right_isBigO_add

/-- If `f x = O(g x)` along `cofinite`, then there exists a positive constant `C` such that
`‖f x‖ ≤ C * ‖g x‖` whenever `g x ≠ 0`. -/
theorem bound_of_isBigO_cofinite (h : f =O[cofinite] g'') :
    ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖ := by
  rcases h.exists_pos with ⟨C, C₀, hC⟩
  -- ⊢ ∃ C, C > 0 ∧ ∀ ⦃x : α⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖
  rw [IsBigOWith_def, eventually_cofinite] at hC
  -- ⊢ ∃ C, C > 0 ∧ ∀ ⦃x : α⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖
  rcases (hC.toFinset.image fun x => ‖f x‖ / ‖g'' x‖).exists_le with ⟨C', hC'⟩
  -- ⊢ ∃ C, C > 0 ∧ ∀ ⦃x : α⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖
  have : ∀ x, C * ‖g'' x‖ < ‖f x‖ → ‖f x‖ / ‖g'' x‖ ≤ C' := by simpa using hC'
  -- ⊢ ∃ C, C > 0 ∧ ∀ ⦃x : α⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖
  refine' ⟨max C C', lt_max_iff.2 (Or.inl C₀), fun x h₀ => _⟩
  -- ⊢ ‖f x‖ ≤ max C C' * ‖g'' x‖
  rw [max_mul_of_nonneg _ _ (norm_nonneg _), le_max_iff, or_iff_not_imp_left, not_le]
  -- ⊢ C * ‖g'' x‖ < ‖f x‖ → ‖f x‖ ≤ C' * ‖g'' x‖
  exact fun hx => (div_le_iff (norm_pos_iff.2 h₀)).1 (this _ hx)
  -- 🎉 no goals
#align asymptotics.bound_of_is_O_cofinite Asymptotics.bound_of_isBigO_cofinite

theorem isBigO_cofinite_iff (h : ∀ x, g'' x = 0 → f'' x = 0) :
    f'' =O[cofinite] g'' ↔ ∃ C, ∀ x, ‖f'' x‖ ≤ C * ‖g'' x‖ :=
  ⟨fun h' =>
    let ⟨C, _C₀, hC⟩ := bound_of_isBigO_cofinite h'
    ⟨C, fun x => if hx : g'' x = 0 then by simp [h _ hx, hx] else hC hx⟩,
                                           -- 🎉 no goals
    fun h => (isBigO_top.2 h).mono le_top⟩
#align asymptotics.is_O_cofinite_iff Asymptotics.isBigO_cofinite_iff

theorem bound_of_isBigO_nat_atTop {f : ℕ → E} {g'' : ℕ → E''} (h : f =O[atTop] g'') :
    ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖ :=
  bound_of_isBigO_cofinite <| by rwa [Nat.cofinite_eq_atTop]
                                 -- 🎉 no goals
#align asymptotics.bound_of_is_O_nat_at_top Asymptotics.bound_of_isBigO_nat_atTop

theorem isBigO_nat_atTop_iff {f : ℕ → E''} {g : ℕ → F''} (h : ∀ x, g x = 0 → f x = 0) :
    f =O[atTop] g ↔ ∃ C, ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by
  rw [← Nat.cofinite_eq_atTop, isBigO_cofinite_iff h]
  -- 🎉 no goals
#align asymptotics.is_O_nat_at_top_iff Asymptotics.isBigO_nat_atTop_iff

theorem isBigO_one_nat_atTop_iff {f : ℕ → E''} :
    f =O[atTop] (fun _n => 1 : ℕ → ℝ) ↔ ∃ C, ∀ n, ‖f n‖ ≤ C :=
  Iff.trans (isBigO_nat_atTop_iff fun n h => (one_ne_zero h).elim) <| by
    simp only [norm_one, mul_one]
    -- 🎉 no goals
#align asymptotics.is_O_one_nat_at_top_iff Asymptotics.isBigO_one_nat_atTop_iff

theorem isBigOWith_pi {ι : Type*} [Fintype ι] {E' : ι → Type*} [∀ i, NormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} {C : ℝ} (hC : 0 ≤ C) :
    IsBigOWith C l f g' ↔ ∀ i, IsBigOWith C l (fun x => f x i) g' := by
  have : ∀ x, 0 ≤ C * ‖g' x‖ := fun x => mul_nonneg hC (norm_nonneg _)
  -- ⊢ IsBigOWith C l f g' ↔ ∀ (i : ι), IsBigOWith C l (fun x => f x i) g'
  simp only [isBigOWith_iff, pi_norm_le_iff_of_nonneg (this _), eventually_all]
  -- 🎉 no goals
#align asymptotics.is_O_with_pi Asymptotics.isBigOWith_pi

@[simp]
theorem isBigO_pi {ι : Type*} [Fintype ι] {E' : ι → Type*} [∀ i, NormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} : f =O[l] g' ↔ ∀ i, (fun x => f x i) =O[l] g' := by
  simp only [isBigO_iff_eventually_isBigOWith, ← eventually_all]
  -- ⊢ (∀ᶠ (c : ℝ) in atTop, IsBigOWith c l f g') ↔ ∀ᶠ (x : ℝ) in atTop, ∀ (i : ι), …
  exact eventually_congr (eventually_atTop.2 ⟨0, fun c => isBigOWith_pi⟩)
  -- 🎉 no goals
#align asymptotics.is_O_pi Asymptotics.isBigO_pi

@[simp]
theorem isLittleO_pi {ι : Type*} [Fintype ι] {E' : ι → Type*} [∀ i, NormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} : f =o[l] g' ↔ ∀ i, (fun x => f x i) =o[l] g' := by
  simp (config := { contextual := true }) only [IsLittleO_def, isBigOWith_pi, le_of_lt]
  -- ⊢ (∀ ⦃c : ℝ⦄, 0 < c → ∀ (i : ι), IsBigOWith c l (fun x => f x i) g') ↔ ∀ (i :  …
  exact ⟨fun h i c hc => h hc i, fun h c hc i => h i hc⟩
  -- 🎉 no goals
#align asymptotics.is_o_pi Asymptotics.isLittleO_pi

theorem IsBigO.nat_cast_atTop {R : Type*} [StrictOrderedSemiring R] [Archimedean R]
    {f : R → E} {g : R → F} (h : f =O[atTop] g) :
    (fun (n:ℕ) => f n) =O[atTop] (fun n => g n) :=
  IsBigO.comp_tendsto h tendsto_nat_cast_atTop_atTop

theorem IsLittleO.nat_cast_atTop {R : Type*} [StrictOrderedSemiring R] [Archimedean R]
    {f : R → E} {g : R → F} (h : f =o[atTop] g) :
    (fun (n:ℕ) => f n) =o[atTop] (fun n => g n) :=
  IsLittleO.comp_tendsto h tendsto_nat_cast_atTop_atTop

theorem isBigO_atTop_iff_eventually_exists {α : Type*} [SemilatticeSup α] [Nonempty α]
    {f : α → E} {g : α → F} : f =O[atTop] g ↔ ∀ᶠ n₀ in atTop, ∃ c, ∀ n ≥ n₀, ‖f n‖ ≤ c * ‖g n‖ := by
  rw [isBigO_iff, exists_eventually_atTop]
  -- 🎉 no goals

theorem isBigO_atTop_iff_eventually_exists_pos {α : Type*}
    [SemilatticeSup α] [Nonempty α] {f : α → G} {g : α → G'} :
    f =O[atTop] g ↔ ∀ᶠ n₀ in atTop, ∃ c > 0, ∀ n ≥ n₀, c * ‖f n‖ ≤ ‖g n‖ := by
  simp_rw [isBigO_iff'', ← exists_prop, Subtype.exists', exists_eventually_atTop]
  -- 🎉 no goals

end Asymptotics

open Asymptotics

theorem summable_of_isBigO {ι E} [NormedAddCommGroup E] [CompleteSpace E] {f : ι → E} {g : ι → ℝ}
    (hg : Summable g) (h : f =O[cofinite] g) : Summable f :=
  let ⟨C, hC⟩ := h.isBigOWith
  summable_of_norm_bounded_eventually (fun x => C * ‖g x‖) (hg.abs.mul_left _) hC.bound
set_option linter.uppercaseLean3 false in
#align summable_of_is_O summable_of_isBigO

theorem summable_of_isBigO_nat {E} [NormedAddCommGroup E] [CompleteSpace E] {f : ℕ → E} {g : ℕ → ℝ}
    (hg : Summable g) (h : f =O[atTop] g) : Summable f :=
  summable_of_isBigO hg <| Nat.cofinite_eq_atTop.symm ▸ h
set_option linter.uppercaseLean3 false in
#align summable_of_is_O_nat summable_of_isBigO_nat

namespace LocalHomeomorph

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]

variable {E : Type*} [Norm E] {F : Type*} [Norm F]

/-- Transfer `IsBigOWith` over a `LocalHomeomorph`. -/
theorem isBigOWith_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E}
    {g : β → F} {C : ℝ} : IsBigOWith C (𝓝 b) f g ↔ IsBigOWith C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
  ⟨fun h =>
    h.comp_tendsto <| by
      have := e.continuousAt (e.map_target hb)
      -- ⊢ Tendsto (↑e) (𝓝 (↑(LocalHomeomorph.symm e) b)) (𝓝 b)
      rwa [ContinuousAt, e.rightInvOn hb] at this,
      -- 🎉 no goals
    fun h =>
    (h.comp_tendsto (e.continuousAt_symm hb)).congr' rfl
      ((e.eventually_right_inverse hb).mono fun x hx => congr_arg f hx)
      ((e.eventually_right_inverse hb).mono fun x hx => congr_arg g hx)⟩
set_option linter.uppercaseLean3 false in
#align local_homeomorph.is_O_with_congr LocalHomeomorph.isBigOWith_congr

/-- Transfer `IsBigO` over a `LocalHomeomorph`. -/
theorem isBigO_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E} {g : β → F} :
    f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [IsBigO_def]
  -- ⊢ (∃ c, IsBigOWith c (𝓝 b) f g) ↔ ∃ c, IsBigOWith c (𝓝 (↑(LocalHomeomorph.symm …
  exact exists_congr fun C => e.isBigOWith_congr hb
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align local_homeomorph.is_O_congr LocalHomeomorph.isBigO_congr

/-- Transfer `IsLittleO` over a `LocalHomeomorph`. -/
theorem isLittleO_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E}
    {g : β → F} : f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [IsLittleO_def]
  -- ⊢ (∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c (𝓝 b) f g) ↔ ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith  …
  exact forall₂_congr fun c _hc => e.isBigOWith_congr hb
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align local_homeomorph.is_o_congr LocalHomeomorph.isLittleO_congr

end LocalHomeomorph

namespace Homeomorph

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]

variable {E : Type*} [Norm E] {F : Type*} [Norm F]

open Asymptotics

/-- Transfer `IsBigOWith` over a `Homeomorph`. -/
theorem isBigOWith_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} {C : ℝ} :
    IsBigOWith C (𝓝 b) f g ↔ IsBigOWith C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
  e.toLocalHomeomorph.isBigOWith_congr trivial
set_option linter.uppercaseLean3 false in
#align homeomorph.is_O_with_congr Homeomorph.isBigOWith_congr

/-- Transfer `IsBigO` over a `Homeomorph`. -/
theorem isBigO_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} :
    f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [IsBigO_def]
  -- ⊢ (∃ c, IsBigOWith c (𝓝 b) f g) ↔ ∃ c, IsBigOWith c (𝓝 (↑(Homeomorph.symm e) b …
  exact exists_congr fun C => e.isBigOWith_congr
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align homeomorph.is_O_congr Homeomorph.isBigO_congr

/-- Transfer `IsLittleO` over a `Homeomorph`. -/
theorem isLittleO_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} :
    f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [IsLittleO_def]
  -- ⊢ (∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith c (𝓝 b) f g) ↔ ∀ ⦃c : ℝ⦄, 0 < c → IsBigOWith  …
  exact forall₂_congr fun c _hc => e.isBigOWith_congr
  -- 🎉 no goals
#align homeomorph.is_o_congr Homeomorph.isLittleO_congr

end Homeomorph
