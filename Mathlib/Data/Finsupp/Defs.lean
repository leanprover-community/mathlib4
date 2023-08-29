/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Scott Morrison
-/
import Mathlib.Algebra.IndicatorFunction
import Mathlib.GroupTheory.Submonoid.Basic

#align_import data.finsupp.defs from "leanprover-community/mathlib"@"842328d9df7e96fd90fc424e115679c15fb23a71"

/-!
# Type of functions with finite support

For any type `α` and any type `M` with zero, we define the type `Finsupp α M` (notation: `α →₀ M`)
of finitely supported functions from `α` to `M`, i.e. the functions which are zero everywhere
on `α` except on a finite set.

Functions with finite support are used (at least) in the following parts of the library:

* `MonoidAlgebra R M` and `AddMonoidAlgebra R M` are defined as `M →₀ R`;

* polynomials and multivariate polynomials are defined as `AddMonoidAlgebra`s, hence they use
  `Finsupp` under the hood;

* the linear combination of a family of vectors `v i` with coefficients `f i` (as used, e.g., to
  define linearly independent family `LinearIndependent`) is defined as a map
  `Finsupp.total : (ι → M) → (ι →₀ R) →ₗ[R] M`.

Some other constructions are naturally equivalent to `α →₀ M` with some `α` and `M` but are defined
in a different way in the library:

* `Multiset α ≃+ α →₀ ℕ`;
* `FreeAbelianGroup α ≃+ α →₀ ℤ`.

Most of the theory assumes that the range is a commutative additive monoid. This gives us the big
sum operator as a powerful way to construct `Finsupp` elements, which is defined in
`Algebra/BigOperators/Finsupp`.

-- Porting note: the semireducibility remark no longer applies in Lean 4, afaict.
Many constructions based on `α →₀ M` use `semireducible` type tags to avoid reusing unwanted type
instances. E.g., `MonoidAlgebra`, `AddMonoidAlgebra`, and types based on these two have
non-pointwise multiplication.

## Main declarations

* `Finsupp`: The type of finitely supported functions from `α` to `β`.
* `Finsupp.single`: The `Finsupp` which is nonzero in exactly one point.
* `Finsupp.update`: Changes one value of a `Finsupp`.
* `Finsupp.erase`: Replaces one value of a `Finsupp` by `0`.
* `Finsupp.onFinset`: The restriction of a function to a `Finset` as a `Finsupp`.
* `Finsupp.mapRange`: Composition of a `ZeroHom` with a `Finsupp`.
* `Finsupp.embDomain`: Maps the domain of a `Finsupp` by an embedding.
* `Finsupp.zipWith`: Postcomposition of two `Finsupp`s with a function `f` such that `f 0 0 = 0`.

## Notations

This file adds `α →₀ M` as a global notation for `Finsupp α M`.

We also use the following convention for `Type*` variables in this file

* `α`, `β`, `γ`: types with no additional structure that appear as the first argument to `Finsupp`
  somewhere in the statement;

* `ι` : an auxiliary index type;

* `M`, `M'`, `N`, `P`: types with `Zero` or `(Add)(Comm)Monoid` structure; `M` is also used
  for a (semi)module over a (semi)ring.

* `G`, `H`: groups (commutative or not, multiplicative or additive);

* `R`, `S`: (semi)rings.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

## TODO

* Expand the list of definitions and important lemmas to the module docstring.

-/


noncomputable section

open Finset Function

open BigOperators

variable {α β γ ι M M' N P G H R S : Type*}

/-- `Finsupp α M`, denoted `α →₀ M`, is the type of functions `f : α → M` such that
  `f x = 0` for all but finitely many `x`. -/
structure Finsupp (α : Type*) (M : Type*) [Zero M] where
  /-- The support of a finitely supported function (aka `Finsupp`). -/
  support : Finset α
  /-- The underlying function of a bundled finitely supported function (aka `Finsupp`). -/
  toFun : α → M
  /-- The witness that the support of a `Finsupp` is indeed the exact locus where its
  underlying function is nonzero. -/
  mem_support_toFun : ∀ a, a ∈ support ↔ toFun a ≠ 0
#align finsupp Finsupp
#align finsupp.support Finsupp.support
#align finsupp.to_fun Finsupp.toFun
#align finsupp.mem_support_to_fun Finsupp.mem_support_toFun

@[inherit_doc]
infixr:25 " →₀ " => Finsupp

namespace Finsupp

/-! ### Basic declarations about `Finsupp` -/


section Basic

variable [Zero M]

instance funLike : FunLike (α →₀ M) α fun _ => M :=
  ⟨toFun, by
    rintro ⟨s, f, hf⟩ ⟨t, g, hg⟩ (rfl : f = g)
    -- ⊢ { support := s, toFun := f, mem_support_toFun := hf } = { support := t, toFu …
    congr
    -- ⊢ s = t
    ext a
    -- ⊢ a ∈ s ↔ a ∈ t
    exact (hf _).trans (hg _).symm⟩
    -- 🎉 no goals
#align finsupp.fun_like Finsupp.funLike

/-- Helper instance for when there are too many metavariables to apply the `FunLike` instance
directly. -/
instance coeFun : CoeFun (α →₀ M) fun _ => α → M :=
  inferInstance
#align finsupp.has_coe_to_fun Finsupp.coeFun

@[ext]
theorem ext {f g : α →₀ M} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext _ _ h
#align finsupp.ext Finsupp.ext

@[deprecated FunLike.ext_iff]
theorem ext_iff {f g : α →₀ M} : f = g ↔ ∀ a, f a = g a :=
  FunLike.ext_iff
#align finsupp.ext_iff Finsupp.ext_iff

@[deprecated FunLike.coe_fn_eq]
theorem coeFn_inj {f g : α →₀ M} : (f : α → M) = g ↔ f = g :=
  FunLike.coe_fn_eq
#align finsupp.coe_fn_inj Finsupp.coeFn_inj

@[deprecated FunLike.coe_injective]
theorem coeFn_injective : @Function.Injective (α →₀ M) (α → M) (⇑) :=
  FunLike.coe_injective
#align finsupp.coe_fn_injective Finsupp.coeFn_injective

@[deprecated FunLike.congr_fun]
theorem congr_fun {f g : α →₀ M} (h : f = g) (a : α) : f a = g a :=
  FunLike.congr_fun h _
#align finsupp.congr_fun Finsupp.congr_fun

@[simp]
theorem coe_mk (f : α → M) (s : Finset α) (h : ∀ a, a ∈ s ↔ f a ≠ 0) : ⇑(⟨s, f, h⟩ : α →₀ M) = f :=
  rfl
#align finsupp.coe_mk Finsupp.coe_mk

instance zero : Zero (α →₀ M) :=
  ⟨⟨∅, 0, fun _ => ⟨fun h ↦ (not_mem_empty _ h).elim, fun H => (H rfl).elim⟩⟩⟩
#align finsupp.has_zero Finsupp.zero

@[simp]
theorem coe_zero : ⇑(0 : α →₀ M) = 0 :=
  rfl
#align finsupp.coe_zero Finsupp.coe_zero

theorem zero_apply {a : α} : (0 : α →₀ M) a = 0 :=
  rfl
#align finsupp.zero_apply Finsupp.zero_apply

@[simp]
theorem support_zero : (0 : α →₀ M).support = ∅ :=
  rfl
#align finsupp.support_zero Finsupp.support_zero

instance inhabited : Inhabited (α →₀ M) :=
  ⟨0⟩
#align finsupp.inhabited Finsupp.inhabited

@[simp]
theorem mem_support_iff {f : α →₀ M} : ∀ {a : α}, a ∈ f.support ↔ f a ≠ 0 :=
  @(f.mem_support_toFun)
#align finsupp.mem_support_iff Finsupp.mem_support_iff

@[simp, norm_cast]
theorem fun_support_eq (f : α →₀ M) : Function.support f = f.support :=
  Set.ext fun _x => mem_support_iff.symm
#align finsupp.fun_support_eq Finsupp.fun_support_eq

theorem not_mem_support_iff {f : α →₀ M} {a} : a ∉ f.support ↔ f a = 0 :=
  not_iff_comm.1 mem_support_iff.symm
#align finsupp.not_mem_support_iff Finsupp.not_mem_support_iff

@[simp, norm_cast]
theorem coe_eq_zero {f : α →₀ M} : (f : α → M) = 0 ↔ f = 0 := by rw [← coe_zero, FunLike.coe_fn_eq]
                                                                 -- 🎉 no goals
#align finsupp.coe_eq_zero Finsupp.coe_eq_zero

theorem ext_iff' {f g : α →₀ M} : f = g ↔ f.support = g.support ∧ ∀ x ∈ f.support, f x = g x :=
  ⟨fun h => h ▸ ⟨rfl, fun _ _ => rfl⟩, fun ⟨h₁, h₂⟩ =>
    ext fun a => by
      classical
      exact if h : a ∈ f.support then h₂ a h else by
        have hf : f a = 0 := not_mem_support_iff.1 h
        have hg : g a = 0 := by rwa [h₁, not_mem_support_iff] at h
        rw [hf, hg]⟩
#align finsupp.ext_iff' Finsupp.ext_iff'

@[simp]
theorem support_eq_empty {f : α →₀ M} : f.support = ∅ ↔ f = 0 := by
  exact_mod_cast @Function.support_eq_empty_iff _ _ _ f
  -- 🎉 no goals
#align finsupp.support_eq_empty Finsupp.support_eq_empty

theorem support_nonempty_iff {f : α →₀ M} : f.support.Nonempty ↔ f ≠ 0 := by
  simp only [Finsupp.support_eq_empty, Finset.nonempty_iff_ne_empty, Ne.def]
  -- 🎉 no goals
#align finsupp.support_nonempty_iff Finsupp.support_nonempty_iff

theorem nonzero_iff_exists {f : α →₀ M} : f ≠ 0 ↔ ∃ a : α, f a ≠ 0 := by
  simp [← Finsupp.support_eq_empty, Finset.eq_empty_iff_forall_not_mem]
  -- 🎉 no goals
#align finsupp.nonzero_iff_exists Finsupp.nonzero_iff_exists

theorem card_support_eq_zero {f : α →₀ M} : card f.support = 0 ↔ f = 0 := by simp
                                                                             -- 🎉 no goals
#align finsupp.card_support_eq_zero Finsupp.card_support_eq_zero

instance decidableEq [DecidableEq α] [DecidableEq M] : DecidableEq (α →₀ M) := fun f g =>
  decidable_of_iff (f.support = g.support ∧ ∀ a ∈ f.support, f a = g a) ext_iff'.symm
#align finsupp.decidable_eq Finsupp.decidableEq

theorem finite_support (f : α →₀ M) : Set.Finite (Function.support f) :=
  f.fun_support_eq.symm ▸ f.support.finite_toSet
#align finsupp.finite_support Finsupp.finite_support

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2:
  warning: expanding binder collection (a «expr ∉ » s) -/
theorem support_subset_iff {s : Set α} {f : α →₀ M} :
    ↑f.support ⊆ s ↔ ∀ (a) (_ : a ∉ s), f a = 0 := by
  simp only [Set.subset_def, mem_coe, mem_support_iff]; exact forall_congr' fun a => not_imp_comm
  -- ⊢ (∀ (x : α), ↑f x ≠ 0 → x ∈ s) ↔ ∀ (a : α), ¬a ∈ s → ↑f a = 0
                                                        -- 🎉 no goals
#align finsupp.support_subset_iff Finsupp.support_subset_iff

/-- Given `Finite α`, `equivFunOnFinite` is the `Equiv` between `α →₀ β` and `α → β`.
  (All functions on a finite type are finitely supported.) -/
@[simps]
def equivFunOnFinite [Finite α] : (α →₀ M) ≃ (α → M) where
  toFun := (⇑)
  invFun f := mk (Function.support f).toFinite.toFinset f fun _a => Set.Finite.mem_toFinset _
  left_inv _f := ext fun _x => rfl
  right_inv _f := rfl
#align finsupp.equiv_fun_on_finite Finsupp.equivFunOnFinite

@[simp]
theorem equivFunOnFinite_symm_coe {α} [Finite α] (f : α →₀ M) : equivFunOnFinite.symm f = f :=
  equivFunOnFinite.symm_apply_apply f
#align finsupp.equiv_fun_on_finite_symm_coe Finsupp.equivFunOnFinite_symm_coe

/--
If `α` has a unique term, the type of finitely supported functions `α →₀ β` is equivalent to `β`.
-/
@[simps!]
noncomputable def _root_.Equiv.finsuppUnique {ι : Type*} [Unique ι] : (ι →₀ M) ≃ M :=
  Finsupp.equivFunOnFinite.trans (Equiv.funUnique ι M)
#align equiv.finsupp_unique Equiv.finsuppUnique
#align equiv.finsupp_unique_symm_apply_support_val Equiv.finsuppUnique_symm_apply_support_val
#align equiv.finsupp_unique_symm_apply_to_fun Equiv.finsuppUnique_symm_apply_toFun
#align equiv.finsupp_unique_apply Equiv.finsuppUnique_apply

@[ext]
theorem unique_ext [Unique α] {f g : α →₀ M} (h : f default = g default) : f = g :=
  ext fun a => by rwa [Unique.eq_default a]
                  -- 🎉 no goals
#align finsupp.unique_ext Finsupp.unique_ext

theorem unique_ext_iff [Unique α] {f g : α →₀ M} : f = g ↔ f default = g default :=
  ⟨fun h => h ▸ rfl, unique_ext⟩
#align finsupp.unique_ext_iff Finsupp.unique_ext_iff

end Basic

/-! ### Declarations about `single` -/


section Single

variable [Zero M] {a a' : α} {b : M}

/-- `single a b` is the finitely supported function with value `b` at `a` and zero otherwise. -/
def single (a : α) (b : M) : α →₀ M
    where
  support :=
    haveI := Classical.decEq M
    if b = 0 then ∅ else {a}
  toFun :=
    haveI := Classical.decEq α
    Pi.single a b
  mem_support_toFun a' := by
    classical
      obtain rfl | hb := eq_or_ne b 0
      · simp [Pi.single, update]
      rw [if_neg hb, mem_singleton]
      obtain rfl | ha := eq_or_ne a' a
      · simp [hb, Pi.single, update]
      simp [Pi.single_eq_of_ne' ha.symm, ha]
#align finsupp.single Finsupp.single

theorem single_apply [Decidable (a = a')] : single a b a' = if a = a' then b else 0 := by
  classical
  simp_rw [@eq_comm _ a a']
  convert Pi.single_apply a b a'
#align finsupp.single_apply Finsupp.single_apply

theorem single_apply_left {f : α → β} (hf : Function.Injective f) (x z : α) (y : M) :
    single (f x) y (f z) = single x y z := by classical simp only [single_apply, hf.eq_iff]
                                              -- 🎉 no goals
#align finsupp.single_apply_left Finsupp.single_apply_left

theorem single_eq_set_indicator : ⇑(single a b) = Set.indicator {a} fun _ => b := by
  classical
  ext
  simp [single_apply, Set.indicator, @eq_comm _ a]
#align finsupp.single_eq_set_indicator Finsupp.single_eq_set_indicator

@[simp]
theorem single_eq_same : (single a b : α →₀ M) a = b := by
  classical exact Pi.single_eq_same (f := λ _ => M) a b
  -- 🎉 no goals
#align finsupp.single_eq_same Finsupp.single_eq_same

@[simp]
theorem single_eq_of_ne (h : a ≠ a') : (single a b : α →₀ M) a' = 0 := by
  classical exact Pi.single_eq_of_ne' h _
  -- 🎉 no goals
#align finsupp.single_eq_of_ne Finsupp.single_eq_of_ne

theorem single_eq_update [DecidableEq α] (a : α) (b : M) :
    ⇑(single a b) = Function.update (0 : _) a b :=
  by classical rw [single_eq_set_indicator, ← Set.piecewise_eq_indicator, Set.piecewise_singleton]
     -- 🎉 no goals
#align finsupp.single_eq_update Finsupp.single_eq_update

theorem single_eq_pi_single [DecidableEq α] (a : α) (b : M) : ⇑(single a b) = Pi.single a b :=
  single_eq_update a b
#align finsupp.single_eq_pi_single Finsupp.single_eq_pi_single

@[simp]
theorem single_zero (a : α) : (single a 0 : α →₀ M) = 0 :=
  FunLike.coe_injective <| by
    classical simpa only [single_eq_update, coe_zero] using Function.update_eq_self a (0 : α → M)
    -- 🎉 no goals
#align finsupp.single_zero Finsupp.single_zero

theorem single_of_single_apply (a a' : α) (b : M) :
    single a ((single a' b) a) = single a' (single a' b) a := by
  classical
  rw [single_apply, single_apply]
  ext
  split_ifs with h
  · rw [h]
  · rw [zero_apply, single_apply, ite_self]
#align finsupp.single_of_single_apply Finsupp.single_of_single_apply

theorem support_single_ne_zero (a : α) (hb : b ≠ 0) : (single a b).support = {a} :=
  if_neg hb
#align finsupp.support_single_ne_zero Finsupp.support_single_ne_zero

theorem support_single_subset : (single a b).support ⊆ {a} := by
  classical show ite _ _ _ ⊆ _; split_ifs <;> [exact empty_subset _; exact Subset.refl _]
  -- 🎉 no goals
#align finsupp.support_single_subset Finsupp.support_single_subset

theorem single_apply_mem (x) : single a b x ∈ ({0, b} : Set M) := by
  rcases em (a = x) with (rfl | hx) <;> [simp; simp [single_eq_of_ne hx]]
  -- 🎉 no goals
#align finsupp.single_apply_mem Finsupp.single_apply_mem

theorem range_single_subset : Set.range (single a b) ⊆ {0, b} :=
  Set.range_subset_iff.2 single_apply_mem
#align finsupp.range_single_subset Finsupp.range_single_subset

/-- `Finsupp.single a b` is injective in `b`. For the statement that it is injective in `a`, see
`Finsupp.single_left_injective` -/
theorem single_injective (a : α) : Function.Injective (single a : M → α →₀ M) := fun b₁ b₂ eq => by
  have : (single a b₁ : α →₀ M) a = (single a b₂ : α →₀ M) a := by rw [eq]
  -- ⊢ b₁ = b₂
  rwa [single_eq_same, single_eq_same] at this
  -- 🎉 no goals
#align finsupp.single_injective Finsupp.single_injective

theorem single_apply_eq_zero {a x : α} {b : M} : single a b x = 0 ↔ x = a → b = 0 := by
  simp [single_eq_set_indicator]
  -- 🎉 no goals
#align finsupp.single_apply_eq_zero Finsupp.single_apply_eq_zero

theorem single_apply_ne_zero {a x : α} {b : M} : single a b x ≠ 0 ↔ x = a ∧ b ≠ 0 := by
  simp [single_apply_eq_zero]
  -- 🎉 no goals
#align finsupp.single_apply_ne_zero Finsupp.single_apply_ne_zero

theorem mem_support_single (a a' : α) (b : M) : a ∈ (single a' b).support ↔ a = a' ∧ b ≠ 0 := by
  simp [single_apply_eq_zero, not_or]
  -- 🎉 no goals
#align finsupp.mem_support_single Finsupp.mem_support_single

theorem eq_single_iff {f : α →₀ M} {a b} : f = single a b ↔ f.support ⊆ {a} ∧ f a = b := by
  refine' ⟨fun h => h.symm ▸ ⟨support_single_subset, single_eq_same⟩, _⟩
  -- ⊢ f.support ⊆ {a} ∧ ↑f a = b → f = single a b
  rintro ⟨h, rfl⟩
  -- ⊢ f = single a (↑f a)
  ext x
  -- ⊢ ↑f x = ↑(single a (↑f a)) x
  by_cases hx : a = x <;> simp only [hx, single_eq_same, single_eq_of_ne, Ne.def, not_false_iff]
  -- ⊢ ↑f x = ↑(single a (↑f a)) x
                          -- 🎉 no goals
                          -- ⊢ ↑f x = 0
  exact not_mem_support_iff.1 (mt (fun hx => (mem_singleton.1 (h hx)).symm) hx)
  -- 🎉 no goals
#align finsupp.eq_single_iff Finsupp.eq_single_iff

theorem single_eq_single_iff (a₁ a₂ : α) (b₁ b₂ : M) :
    single a₁ b₁ = single a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0 := by
  constructor
  -- ⊢ single a₁ b₁ = single a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0
  · intro eq
    -- ⊢ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0
    by_cases h : a₁ = a₂
    -- ⊢ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0
    · refine' Or.inl ⟨h, _⟩
      -- ⊢ b₁ = b₂
      rwa [h, (single_injective a₂).eq_iff] at eq
      -- 🎉 no goals
    · rw [FunLike.ext_iff] at eq
      -- ⊢ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0
      have h₁ := eq a₁
      -- ⊢ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0
      have h₂ := eq a₂
      -- ⊢ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0
      simp only [single_eq_same, single_eq_of_ne h, single_eq_of_ne (Ne.symm h)] at h₁ h₂
      -- ⊢ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0
      exact Or.inr ⟨h₁, h₂.symm⟩
      -- 🎉 no goals
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    -- ⊢ single a₁ b₁ = single a₁ b₁
    · rfl
      -- 🎉 no goals
    · rw [single_zero, single_zero]
      -- 🎉 no goals
#align finsupp.single_eq_single_iff Finsupp.single_eq_single_iff

/-- `Finsupp.single a b` is injective in `a`. For the statement that it is injective in `b`, see
`Finsupp.single_injective` -/
theorem single_left_injective (h : b ≠ 0) : Function.Injective fun a : α => single a b :=
  fun _a _a' H => (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h hb.1).left
#align finsupp.single_left_injective Finsupp.single_left_injective

theorem single_left_inj (h : b ≠ 0) : single a b = single a' b ↔ a = a' :=
  (single_left_injective h).eq_iff
#align finsupp.single_left_inj Finsupp.single_left_inj

theorem support_single_ne_bot (i : α) (h : b ≠ 0) : (single i b).support ≠ ⊥ := by
  simpa only [support_single_ne_zero _ h] using singleton_ne_empty _
  -- 🎉 no goals
#align finsupp.support_single_ne_bot Finsupp.support_single_ne_bot

theorem support_single_disjoint {b' : M} (hb : b ≠ 0) (hb' : b' ≠ 0) {i j : α} :
    Disjoint (single i b).support (single j b').support ↔ i ≠ j := by
  rw [support_single_ne_zero _ hb, support_single_ne_zero _ hb', disjoint_singleton]
  -- 🎉 no goals
#align finsupp.support_single_disjoint Finsupp.support_single_disjoint

@[simp]
theorem single_eq_zero : single a b = 0 ↔ b = 0 := by
  simp [FunLike.ext_iff, single_eq_set_indicator]
  -- 🎉 no goals
#align finsupp.single_eq_zero Finsupp.single_eq_zero

theorem single_swap (a₁ a₂ : α) (b : M) : single a₁ b a₂ = single a₂ b a₁ := by
  classical simp only [single_apply, eq_comm]
  -- 🎉 no goals
#align finsupp.single_swap Finsupp.single_swap

instance nontrivial [Nonempty α] [Nontrivial M] : Nontrivial (α →₀ M) := by
  inhabit α
  -- ⊢ Nontrivial (α →₀ M)
  rcases exists_ne (0 : M) with ⟨x, hx⟩
  -- ⊢ Nontrivial (α →₀ M)
  exact nontrivial_of_ne (single default x) 0 (mt single_eq_zero.1 hx)
  -- 🎉 no goals
#align finsupp.nontrivial Finsupp.nontrivial

theorem unique_single [Unique α] (x : α →₀ M) : x = single default (x default) :=
  ext <| Unique.forall_iff.2 single_eq_same.symm
#align finsupp.unique_single Finsupp.unique_single

@[simp]
theorem unique_single_eq_iff [Unique α] {b' : M} : single a b = single a' b' ↔ b = b' := by
  rw [unique_ext_iff, Unique.eq_default a, Unique.eq_default a', single_eq_same, single_eq_same]
  -- 🎉 no goals
#align finsupp.unique_single_eq_iff Finsupp.unique_single_eq_iff

theorem support_eq_singleton {f : α →₀ M} {a : α} :
    f.support = {a} ↔ f a ≠ 0 ∧ f = single a (f a) :=
  ⟨fun h =>
    ⟨mem_support_iff.1 <| h.symm ▸ Finset.mem_singleton_self a,
      eq_single_iff.2 ⟨subset_of_eq h, rfl⟩⟩,
    fun h => h.2.symm ▸ support_single_ne_zero _ h.1⟩
#align finsupp.support_eq_singleton Finsupp.support_eq_singleton

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2:
  warning: expanding binder collection (b «expr ≠ » 0) -/
theorem support_eq_singleton' {f : α →₀ M} {a : α} :
    f.support = {a} ↔ ∃ (b : _) (_ : b ≠ 0), f = single a b :=
  ⟨fun h =>
    let h := support_eq_singleton.1 h
    ⟨_, h.1, h.2⟩,
    fun ⟨_b, hb, hf⟩ => hf.symm ▸ support_single_ne_zero _ hb⟩
#align finsupp.support_eq_singleton' Finsupp.support_eq_singleton'

theorem card_support_eq_one {f : α →₀ M} : card f.support = 1 ↔ ∃ a, f a ≠ 0 ∧ f = single a (f a) :=
  by simp only [card_eq_one, support_eq_singleton]
     -- 🎉 no goals
#align finsupp.card_support_eq_one Finsupp.card_support_eq_one

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2:
  warning: expanding binder collection (b «expr ≠ » 0) -/
theorem card_support_eq_one' {f : α →₀ M} :
    card f.support = 1 ↔ ∃ (a : _) (b : _) (_ : b ≠ 0), f = single a b := by
  simp only [card_eq_one, support_eq_singleton']
  -- 🎉 no goals
#align finsupp.card_support_eq_one' Finsupp.card_support_eq_one'

theorem support_subset_singleton {f : α →₀ M} {a : α} : f.support ⊆ {a} ↔ f = single a (f a) :=
  ⟨fun h => eq_single_iff.mpr ⟨h, rfl⟩, fun h => (eq_single_iff.mp h).left⟩
#align finsupp.support_subset_singleton Finsupp.support_subset_singleton

theorem support_subset_singleton' {f : α →₀ M} {a : α} : f.support ⊆ {a} ↔ ∃ b, f = single a b :=
  ⟨fun h => ⟨f a, support_subset_singleton.mp h⟩, fun ⟨b, hb⟩ => by
    rw [hb, support_subset_singleton, single_eq_same]⟩
    -- 🎉 no goals
#align finsupp.support_subset_singleton' Finsupp.support_subset_singleton'

theorem card_support_le_one [Nonempty α] {f : α →₀ M} :
    card f.support ≤ 1 ↔ ∃ a, f = single a (f a) := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton]
  -- 🎉 no goals
#align finsupp.card_support_le_one Finsupp.card_support_le_one

theorem card_support_le_one' [Nonempty α] {f : α →₀ M} :
    card f.support ≤ 1 ↔ ∃ a b, f = single a b := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton']
  -- 🎉 no goals
#align finsupp.card_support_le_one' Finsupp.card_support_le_one'

@[simp]
theorem equivFunOnFinite_single [DecidableEq α] [Finite α] (x : α) (m : M) :
    Finsupp.equivFunOnFinite (Finsupp.single x m) = Pi.single x m := by
  ext
  -- ⊢ ↑equivFunOnFinite (single x m) x✝ = Pi.single x m x✝
  simp [Finsupp.single_eq_pi_single, equivFunOnFinite]
  -- 🎉 no goals
#align finsupp.equiv_fun_on_finite_single Finsupp.equivFunOnFinite_single

@[simp]
theorem equivFunOnFinite_symm_single [DecidableEq α] [Finite α] (x : α) (m : M) :
    Finsupp.equivFunOnFinite.symm (Pi.single x m) = Finsupp.single x m := by
  rw [← equivFunOnFinite_single, Equiv.symm_apply_apply]
  -- 🎉 no goals
#align finsupp.equiv_fun_on_finite_symm_single Finsupp.equivFunOnFinite_symm_single

end Single

/-! ### Declarations about `update` -/


section Update

variable [Zero M] (f : α →₀ M) (a : α) (b : M) (i : α)

/-- Replace the value of a `α →₀ M` at a given point `a : α` by a given value `b : M`.
If `b = 0`, this amounts to removing `a` from the `Finsupp.support`.
Otherwise, if `a` was not in the `Finsupp.support`, it is added to it.

This is the finitely-supported version of `Function.update`. -/
def update (f : α →₀ M) (a : α) (b : M) : α →₀ M where
  support := by
    haveI := Classical.decEq α; haveI := Classical.decEq M
    -- ⊢ Finset α
                                -- ⊢ Finset α
    exact if b = 0 then f.support.erase a else insert a f.support
    -- 🎉 no goals
  toFun :=
    haveI := Classical.decEq α
    Function.update f a b
  mem_support_toFun i := by
    classical
    simp [Function.update, Ne.def]
    split_ifs with hb ha ha <;>
      try simp only [*, not_false_iff, iff_true, not_true, iff_false]
    · rw [Finset.mem_erase]
      simp
    · rw [Finset.mem_erase]
      simp [ha]
    · rw [Finset.mem_insert]
      simp [ha]
    · rw [Finset.mem_insert]
      simp [ha]
#align finsupp.update Finsupp.update

@[simp]
theorem coe_update [DecidableEq α] : (f.update a b : α → M) = Function.update f a b := by
  delta update Function.update
  -- ⊢ ↑{ support := if b = 0 then erase f.support a else insert a f.support, toFun …
  ext
  -- ⊢ ↑{ support := if b = 0 then erase f.support a else insert a f.support, toFun …
  dsimp
  -- ⊢ (if h : x✝ = a then (_ : a = x✝) ▸ b else ↑f x✝) = if h : x✝ = a then (_ : a …
  split_ifs <;> simp
  -- ⊢ (_ : a = x✝) ▸ b = (_ : a = x✝) ▸ b
                -- 🎉 no goals
                -- 🎉 no goals
#align finsupp.coe_update Finsupp.coe_update

@[simp]
theorem update_self : f.update a (f a) = f := by
  classical
    ext
    simp
#align finsupp.update_self Finsupp.update_self

@[simp]
theorem zero_update : update 0 a b = single a b := by
  classical
    ext
    rw [single_eq_update]
    rfl
#align finsupp.zero_update Finsupp.zero_update

theorem support_update [DecidableEq α] [DecidableEq M] :
    support (f.update a b) = if b = 0 then f.support.erase a else insert a f.support := by
  classical
  dsimp [update]; congr <;> apply Subsingleton.elim
#align finsupp.support_update Finsupp.support_update

@[simp]
theorem support_update_zero [DecidableEq α] : support (f.update a 0) = f.support.erase a := by
  classical
  simp only [update, ite_true, mem_support_iff, ne_eq, not_not]
  congr; apply Subsingleton.elim
#align finsupp.support_update_zero Finsupp.support_update_zero

variable {b}

theorem support_update_ne_zero [DecidableEq α] (h : b ≠ 0) :
    support (f.update a b) = insert a f.support := by
  classical
  simp only [update, h, ite_false, mem_support_iff, ne_eq]
  congr; apply Subsingleton.elim
#align finsupp.support_update_ne_zero Finsupp.support_update_ne_zero

end Update

/-! ### Declarations about `erase` -/


section Erase

variable [Zero M]

/--
`erase a f` is the finitely supported function equal to `f` except at `a` where it is equal to `0`.
If `a` is not in the support of `f` then `erase a f = f`.
-/
def erase (a : α) (f : α →₀ M) : α →₀ M where
  support :=
    haveI := Classical.decEq α
    f.support.erase a
  toFun a' :=
    haveI := Classical.decEq α
    if a' = a then 0 else f a'
  mem_support_toFun a' := by
    classical
    rw [mem_erase, mem_support_iff]; dsimp
    split_ifs with h
    exact ⟨fun H _ => H.1 h, fun H => (H rfl).elim⟩
    exact and_iff_right h
#align finsupp.erase Finsupp.erase

@[simp]
theorem support_erase [DecidableEq α] {a : α} {f : α →₀ M} :
    (f.erase a).support = f.support.erase a := by
  classical
  dsimp [erase]
  congr; apply Subsingleton.elim
#align finsupp.support_erase Finsupp.support_erase

@[simp]
theorem erase_same {a : α} {f : α →₀ M} : (f.erase a) a = 0 := by
  classical simp only [erase, coe_mk, ite_true]
  -- 🎉 no goals
#align finsupp.erase_same Finsupp.erase_same

@[simp]
theorem erase_ne {a a' : α} {f : α →₀ M} (h : a' ≠ a) : (f.erase a) a' = f a' := by
  classical simp only [erase, coe_mk, h, ite_false]
  -- 🎉 no goals
#align finsupp.erase_ne Finsupp.erase_ne

@[simp]
theorem erase_single {a : α} {b : M} : erase a (single a b) = 0 := by
  ext s; by_cases hs : s = a
  -- ⊢ ↑(erase a (single a b)) s = ↑0 s
         -- ⊢ ↑(erase a (single a b)) s = ↑0 s
  · rw [hs, erase_same]
    -- ⊢ 0 = ↑0 a
    rfl
    -- 🎉 no goals
  · rw [erase_ne hs]
    -- ⊢ ↑(single a b) s = ↑0 s
    exact single_eq_of_ne (Ne.symm hs)
    -- 🎉 no goals
#align finsupp.erase_single Finsupp.erase_single

theorem erase_single_ne {a a' : α} {b : M} (h : a ≠ a') : erase a (single a' b) = single a' b := by
  ext s; by_cases hs : s = a
  -- ⊢ ↑(erase a (single a' b)) s = ↑(single a' b) s
         -- ⊢ ↑(erase a (single a' b)) s = ↑(single a' b) s
  · rw [hs, erase_same, single_eq_of_ne h.symm]
    -- 🎉 no goals
  · rw [erase_ne hs]
    -- 🎉 no goals
#align finsupp.erase_single_ne Finsupp.erase_single_ne

@[simp]
theorem erase_of_not_mem_support {f : α →₀ M} {a} (haf : a ∉ f.support) : erase a f = f := by
  ext b; by_cases hab : b = a
  -- ⊢ ↑(erase a f) b = ↑f b
         -- ⊢ ↑(erase a f) b = ↑f b
  · rwa [hab, erase_same, eq_comm, ← not_mem_support_iff]
    -- 🎉 no goals
  · rw [erase_ne hab]
    -- 🎉 no goals
#align finsupp.erase_of_not_mem_support Finsupp.erase_of_not_mem_support

@[simp, nolint simpNF] -- Porting note: simpNF linter claims simp can prove this, it can not
theorem erase_zero (a : α) : erase a (0 : α →₀ M) = 0 := by
  classical rw [← support_eq_empty, support_erase, support_zero, erase_empty]
  -- 🎉 no goals
#align finsupp.erase_zero Finsupp.erase_zero

end Erase

/-! ### Declarations about `onFinset` -/


section OnFinset

variable [Zero M]

/-- `Finsupp.onFinset s f hf` is the finsupp function representing `f` restricted to the finset `s`.
The function must be `0` outside of `s`. Use this when the set needs to be filtered anyways,
otherwise a better set representation is often available. -/
def onFinset (s : Finset α) (f : α → M) (hf : ∀ a, f a ≠ 0 → a ∈ s) : α →₀ M where
  support :=
    haveI := Classical.decEq M
    s.filter (f · ≠ 0)
  toFun := f
  mem_support_toFun := by classical simpa
                          -- 🎉 no goals
#align finsupp.on_finset Finsupp.onFinset

@[simp]
theorem onFinset_apply {s : Finset α} {f : α → M} {hf a} : (onFinset s f hf : α →₀ M) a = f a :=
  rfl
#align finsupp.on_finset_apply Finsupp.onFinset_apply

@[simp]
theorem support_onFinset_subset {s : Finset α} {f : α → M} {hf} :
    (onFinset s f hf).support ⊆ s := by
  classical convert filter_subset (f · ≠ 0) s
  -- 🎉 no goals
#align finsupp.support_on_finset_subset Finsupp.support_onFinset_subset

-- @[simp] -- Porting note: simp can prove this
theorem mem_support_onFinset {s : Finset α} {f : α → M} (hf : ∀ a : α, f a ≠ 0 → a ∈ s) {a : α} :
    a ∈ (Finsupp.onFinset s f hf).support ↔ f a ≠ 0 := by
  rw [Finsupp.mem_support_iff, Finsupp.onFinset_apply]
  -- 🎉 no goals
#align finsupp.mem_support_on_finset Finsupp.mem_support_onFinset

theorem support_onFinset [DecidableEq M] {s : Finset α} {f : α → M}
    (hf : ∀ a : α, f a ≠ 0 → a ∈ s) :
    (Finsupp.onFinset s f hf).support = s.filter fun a => f a ≠ 0 := by
  dsimp [onFinset]; congr
  -- ⊢ filter (fun x => ¬f x = 0) s = filter (fun a => ¬f a = 0) s
                    -- 🎉 no goals
#align finsupp.support_on_finset Finsupp.support_onFinset

end OnFinset

section OfSupportFinite

variable [Zero M]

/-- The natural `Finsupp` induced by the function `f` given that it has finite support. -/
noncomputable def ofSupportFinite (f : α → M) (hf : (Function.support f).Finite) : α →₀ M where
  support := hf.toFinset
  toFun := f
  mem_support_toFun _ := hf.mem_toFinset
#align finsupp.of_support_finite Finsupp.ofSupportFinite

theorem ofSupportFinite_coe {f : α → M} {hf : (Function.support f).Finite} :
    (ofSupportFinite f hf : α → M) = f :=
  rfl
#align finsupp.of_support_finite_coe Finsupp.ofSupportFinite_coe

instance canLift : CanLift (α → M) (α →₀ M) (⇑) fun f => (Function.support f).Finite
    where prf f hf := ⟨ofSupportFinite f hf, rfl⟩
#align finsupp.can_lift Finsupp.canLift

end OfSupportFinite

/-! ### Declarations about `mapRange` -/


section MapRange

variable [Zero M] [Zero N] [Zero P]

/-- The composition of `f : M → N` and `g : α →₀ M` is `mapRange f hf g : α →₀ N`,
which is well-defined when `f 0 = 0`.

This preserves the structure on `f`, and exists in various bundled forms for when `f` is itself
bundled (defined in `Data/Finsupp/Basic`):

* `Finsupp.mapRange.equiv`
* `Finsupp.mapRange.zeroHom`
* `Finsupp.mapRange.addMonoidHom`
* `Finsupp.mapRange.addEquiv`
* `Finsupp.mapRange.linearMap`
* `Finsupp.mapRange.linearEquiv`
-/
def mapRange (f : M → N) (hf : f 0 = 0) (g : α →₀ M) : α →₀ N :=
  onFinset g.support (f ∘ g) fun a => by
    rw [mem_support_iff, not_imp_not]; exact fun H => (congr_arg f H).trans hf
    -- ⊢ ↑g a = 0 → (f ∘ ↑g) a = 0
                                       -- 🎉 no goals
#align finsupp.map_range Finsupp.mapRange

@[simp]
theorem mapRange_apply {f : M → N} {hf : f 0 = 0} {g : α →₀ M} {a : α} :
    mapRange f hf g a = f (g a) :=
  rfl
#align finsupp.map_range_apply Finsupp.mapRange_apply

@[simp]
theorem mapRange_zero {f : M → N} {hf : f 0 = 0} : mapRange f hf (0 : α →₀ M) = 0 :=
  ext fun a => by simp only [hf, zero_apply, mapRange_apply]
                  -- 🎉 no goals
#align finsupp.map_range_zero Finsupp.mapRange_zero

@[simp]
theorem mapRange_id (g : α →₀ M) : mapRange id rfl g = g :=
  ext fun _ => rfl
#align finsupp.map_range_id Finsupp.mapRange_id

theorem mapRange_comp (f : N → P) (hf : f 0 = 0) (f₂ : M → N) (hf₂ : f₂ 0 = 0) (h : (f ∘ f₂) 0 = 0)
    (g : α →₀ M) : mapRange (f ∘ f₂) h g = mapRange f hf (mapRange f₂ hf₂ g) :=
  ext fun _ => rfl
#align finsupp.map_range_comp Finsupp.mapRange_comp

theorem support_mapRange {f : M → N} {hf : f 0 = 0} {g : α →₀ M} :
    (mapRange f hf g).support ⊆ g.support :=
  support_onFinset_subset
#align finsupp.support_map_range Finsupp.support_mapRange

@[simp]
theorem mapRange_single {f : M → N} {hf : f 0 = 0} {a : α} {b : M} :
    mapRange f hf (single a b) = single a (f b) :=
  ext fun a' => by
    classical simpa only [single_eq_pi_single] using Pi.apply_single _ (fun _ => hf) a _ a'
    -- 🎉 no goals
#align finsupp.map_range_single Finsupp.mapRange_single

theorem support_mapRange_of_injective {e : M → N} (he0 : e 0 = 0) (f : ι →₀ M)
    (he : Function.Injective e) : (Finsupp.mapRange e he0 f).support = f.support := by
  ext
  -- ⊢ a✝ ∈ (mapRange e he0 f).support ↔ a✝ ∈ f.support
  simp only [Finsupp.mem_support_iff, Ne.def, Finsupp.mapRange_apply]
  -- ⊢ ¬e (↑f a✝) = 0 ↔ ¬↑f a✝ = 0
  exact he.ne_iff' he0
  -- 🎉 no goals
#align finsupp.support_map_range_of_injective Finsupp.support_mapRange_of_injective

end MapRange

/-! ### Declarations about `embDomain` -/


section EmbDomain

variable [Zero M] [Zero N]

/-- Given `f : α ↪ β` and `v : α →₀ M`, `Finsupp.embDomain f v : β →₀ M`
is the finitely supported function whose value at `f a : β` is `v a`.
For a `b : β` outside the range of `f`, it is zero. -/
def embDomain (f : α ↪ β) (v : α →₀ M) : β →₀ M where
  support := v.support.map f
  toFun a₂ :=
    haveI := Classical.decEq β
    if h : a₂ ∈ v.support.map f then
      v
        (v.support.choose (fun a₁ => f a₁ = a₂)
          (by
            rcases Finset.mem_map.1 h with ⟨a, ha, rfl⟩
            -- ⊢ ∃! a_1, a_1 ∈ v.support ∧ (fun a₁ => ↑f a₁ = ↑f a) a_1
            exact ExistsUnique.intro a ⟨ha, rfl⟩ fun b ⟨_, hb⟩ => f.injective hb))
            -- 🎉 no goals
    else 0
  mem_support_toFun a₂ := by
    dsimp
    -- ⊢ a₂ ∈ map f v.support ↔ ¬(if h : a₂ ∈ map f v.support then ↑v (choose (fun a₁ …
    split_ifs with h
    -- ⊢ a₂ ∈ map f v.support ↔ ¬↑v (choose (fun a₁ => ↑f a₁ = a₂) v.support (_ : ∃!  …
    · simp only [h, true_iff_iff, Ne.def]
      -- ⊢ ¬↑v (choose (fun a₁ => ↑f a₁ = a₂) v.support (_ : ∃! a, a ∈ v.support ∧ ↑f a …
      rw [← not_mem_support_iff, not_not]
      -- ⊢ choose (fun a₁ => ↑f a₁ = a₂) v.support (_ : ∃! a, a ∈ v.support ∧ ↑f a = a₂ …
      classical apply Finset.choose_mem
      -- 🎉 no goals
    · simp only [h, Ne.def, ne_self_iff_false]
      -- 🎉 no goals
#align finsupp.emb_domain Finsupp.embDomain

@[simp]
theorem support_embDomain (f : α ↪ β) (v : α →₀ M) : (embDomain f v).support = v.support.map f :=
  rfl
#align finsupp.support_emb_domain Finsupp.support_embDomain

@[simp]
theorem embDomain_zero (f : α ↪ β) : (embDomain f 0 : β →₀ M) = 0 :=
  rfl
#align finsupp.emb_domain_zero Finsupp.embDomain_zero

@[simp]
theorem embDomain_apply (f : α ↪ β) (v : α →₀ M) (a : α) : embDomain f v (f a) = v a := by
  classical
    change dite _ _ _ = _
    split_ifs with h <;> rw [Finset.mem_map' f] at h
    · refine' congr_arg (v : α → M) (f.inj' _)
      exact Finset.choose_property (fun a₁ => f a₁ = f a) _ _
    · exact (not_mem_support_iff.1 h).symm
#align finsupp.emb_domain_apply Finsupp.embDomain_apply

theorem embDomain_notin_range (f : α ↪ β) (v : α →₀ M) (a : β) (h : a ∉ Set.range f) :
    embDomain f v a = 0 := by
  classical
    refine' dif_neg (mt (fun h => _) h)
    rcases Finset.mem_map.1 h with ⟨a, _h, rfl⟩
    exact Set.mem_range_self a
#align finsupp.emb_domain_notin_range Finsupp.embDomain_notin_range

theorem embDomain_injective (f : α ↪ β) : Function.Injective (embDomain f : (α →₀ M) → β →₀ M) :=
  fun l₁ l₂ h => ext fun a => by simpa only [embDomain_apply] using FunLike.ext_iff.1 h (f a)
                                 -- 🎉 no goals
#align finsupp.emb_domain_injective Finsupp.embDomain_injective

@[simp]
theorem embDomain_inj {f : α ↪ β} {l₁ l₂ : α →₀ M} : embDomain f l₁ = embDomain f l₂ ↔ l₁ = l₂ :=
  (embDomain_injective f).eq_iff
#align finsupp.emb_domain_inj Finsupp.embDomain_inj

@[simp]
theorem embDomain_eq_zero {f : α ↪ β} {l : α →₀ M} : embDomain f l = 0 ↔ l = 0 :=
  (embDomain_injective f).eq_iff' <| embDomain_zero f
#align finsupp.emb_domain_eq_zero Finsupp.embDomain_eq_zero

theorem embDomain_mapRange (f : α ↪ β) (g : M → N) (p : α →₀ M) (hg : g 0 = 0) :
    embDomain f (mapRange g hg p) = mapRange g hg (embDomain f p) := by
  ext a
  -- ⊢ ↑(embDomain f (mapRange g hg p)) a = ↑(mapRange g hg (embDomain f p)) a
  by_cases h : a ∈ Set.range f
  -- ⊢ ↑(embDomain f (mapRange g hg p)) a = ↑(mapRange g hg (embDomain f p)) a
  · rcases h with ⟨a', rfl⟩
    -- ⊢ ↑(embDomain f (mapRange g hg p)) (↑f a') = ↑(mapRange g hg (embDomain f p))  …
    rw [mapRange_apply, embDomain_apply, embDomain_apply, mapRange_apply]
    -- 🎉 no goals
  · rw [mapRange_apply, embDomain_notin_range, embDomain_notin_range, ← hg] <;> assumption
    -- ⊢ ¬a ∈ Set.range ↑f
                                                                                -- 🎉 no goals
                                                                                -- 🎉 no goals
#align finsupp.emb_domain_map_range Finsupp.embDomain_mapRange

theorem single_of_embDomain_single (l : α →₀ M) (f : α ↪ β) (a : β) (b : M) (hb : b ≠ 0)
    (h : l.embDomain f = single a b) : ∃ x, l = single x b ∧ f x = a := by
  classical
    have h_map_support : Finset.map f l.support = {a} := by
      rw [← support_embDomain, h, support_single_ne_zero _ hb]
    have ha : a ∈ Finset.map f l.support := by simp only [h_map_support, Finset.mem_singleton]
    rcases Finset.mem_map.1 ha with ⟨c, _hc₁, hc₂⟩
    use c
    constructor
    · ext d
      rw [← embDomain_apply f l, h]
      by_cases h_cases : c = d
      · simp only [Eq.symm h_cases, hc₂, single_eq_same]
      · rw [single_apply, single_apply, if_neg, if_neg h_cases]
        by_contra hfd
        exact h_cases (f.injective (hc₂.trans hfd))
    · exact hc₂
#align finsupp.single_of_emb_domain_single Finsupp.single_of_embDomain_single

@[simp]
theorem embDomain_single (f : α ↪ β) (a : α) (m : M) :
    embDomain f (single a m) = single (f a) m := by
  classical
    ext b
    by_cases h : b ∈ Set.range f
    · rcases h with ⟨a', rfl⟩
      simp [single_apply]
    · simp only [embDomain_notin_range, h, single_apply, not_false_iff]
      rw [if_neg]
      rintro rfl
      simp at h
#align finsupp.emb_domain_single Finsupp.embDomain_single

end EmbDomain

/-! ### Declarations about `zipWith` -/


section ZipWith

variable [Zero M] [Zero N] [Zero P]

/-- Given finitely supported functions `g₁ : α →₀ M` and `g₂ : α →₀ N` and function `f : M → N → P`,
`Finsupp.zipWith f hf g₁ g₂` is the finitely supported function `α →₀ P` satisfying
`zipWith f hf g₁ g₂ a = f (g₁ a) (g₂ a)`, which is well-defined when `f 0 0 = 0`. -/
def zipWith (f : M → N → P) (hf : f 0 0 = 0) (g₁ : α →₀ M) (g₂ : α →₀ N) : α →₀ P :=
  onFinset
    (haveI := Classical.decEq α; g₁.support ∪ g₂.support)
    (fun a => f (g₁ a) (g₂ a))
    fun a (H : f _ _ ≠ 0) => by
      classical
      rw [mem_union, mem_support_iff, mem_support_iff, ← not_and_or]
      rintro ⟨h₁, h₂⟩; rw [h₁, h₂] at H; exact H hf
#align finsupp.zip_with Finsupp.zipWith

@[simp]
theorem zipWith_apply {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M} {g₂ : α →₀ N} {a : α} :
    zipWith f hf g₁ g₂ a = f (g₁ a) (g₂ a) :=
  rfl
#align finsupp.zip_with_apply Finsupp.zipWith_apply

theorem support_zipWith [D : DecidableEq α] {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M}
    {g₂ : α →₀ N} : (zipWith f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support := by
  rw [Subsingleton.elim D] <;> exact support_onFinset_subset
  -- ⊢ (zipWith f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support
                               -- 🎉 no goals
#align finsupp.support_zip_with Finsupp.support_zipWith

end ZipWith

/-! ### Additive monoid structure on `α →₀ M` -/


section AddZeroClass

variable [AddZeroClass M]

instance add : Add (α →₀ M) :=
  ⟨zipWith (· + ·) (add_zero 0)⟩
#align finsupp.has_add Finsupp.add

@[simp]
theorem coe_add (f g : α →₀ M) : ⇑(f + g) = f + g :=
  rfl
#align finsupp.coe_add Finsupp.coe_add

theorem add_apply (g₁ g₂ : α →₀ M) (a : α) : (g₁ + g₂) a = g₁ a + g₂ a :=
  rfl
#align finsupp.add_apply Finsupp.add_apply

theorem support_add [DecidableEq α] {g₁ g₂ : α →₀ M} :
    (g₁ + g₂).support ⊆ g₁.support ∪ g₂.support :=
  support_zipWith
#align finsupp.support_add Finsupp.support_add

theorem support_add_eq [DecidableEq α] {g₁ g₂ : α →₀ M} (h : Disjoint g₁.support g₂.support) :
    (g₁ + g₂).support = g₁.support ∪ g₂.support :=
  le_antisymm support_zipWith fun a ha =>
    (Finset.mem_union.1 ha).elim
      (fun ha => by
        have : a ∉ g₂.support := disjoint_left.1 h ha
        -- ⊢ a ∈ (g₁ + g₂).support
        simp only [mem_support_iff, not_not] at *; simpa only [add_apply, this, add_zero] )
        -- ⊢ ↑(g₁ + g₂) a ≠ 0
                                                   -- 🎉 no goals
      fun ha => by
      have : a ∉ g₁.support := disjoint_right.1 h ha
      -- ⊢ a ∈ (g₁ + g₂).support
      simp only [mem_support_iff, not_not] at *; simpa only [add_apply, this, zero_add]
      -- ⊢ ↑(g₁ + g₂) a ≠ 0
                                                 -- 🎉 no goals
#align finsupp.support_add_eq Finsupp.support_add_eq

@[simp]
theorem single_add (a : α) (b₁ b₂ : M) : single a (b₁ + b₂) = single a b₁ + single a b₂ :=
  ext fun a' => by
    by_cases h : a = a'
    -- ⊢ ↑(single a (b₁ + b₂)) a' = ↑(single a b₁ + single a b₂) a'
    · rw [h, add_apply, single_eq_same, single_eq_same, single_eq_same]
      -- 🎉 no goals
    · rw [add_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, zero_add]
      -- 🎉 no goals
#align finsupp.single_add Finsupp.single_add

instance addZeroClass : AddZeroClass (α →₀ M) :=
  FunLike.coe_injective.addZeroClass _ coe_zero coe_add
#align finsupp.add_zero_class Finsupp.addZeroClass

/-- `Finsupp.single` as an `AddMonoidHom`.

See `Finsupp.lsingle` in `LinearAlgebra/Finsupp` for the stronger version as a linear map. -/
@[simps]
def singleAddHom (a : α) : M →+ α →₀ M where
  toFun := single a
  map_zero' := single_zero a
  map_add' := single_add a
#align finsupp.single_add_hom Finsupp.singleAddHom

/-- Evaluation of a function `f : α →₀ M` at a point as an additive monoid homomorphism.

See `Finsupp.lapply` in `LinearAlgebra/Finsupp` for the stronger version as a linear map. -/
@[simps apply]
def applyAddHom (a : α) : (α →₀ M) →+ M where
  toFun g := g a
  map_zero' := zero_apply
  map_add' _ _ := add_apply _ _ _
#align finsupp.apply_add_hom Finsupp.applyAddHom
#align finsupp.apply_add_hom_apply Finsupp.applyAddHom_apply

/-- Coercion from a `Finsupp` to a function type is an `AddMonoidHom`. -/
@[simps]
noncomputable def coeFnAddHom : (α →₀ M) →+ α → M where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add
#align finsupp.coe_fn_add_hom Finsupp.coeFnAddHom
#align finsupp.coe_fn_add_hom_apply Finsupp.coeFnAddHom_apply

theorem update_eq_single_add_erase (f : α →₀ M) (a : α) (b : M) :
    f.update a b = single a b + f.erase a := by
  classical
    ext j
    rcases eq_or_ne a j with (rfl | h)
    · simp
    · simp [Function.update_noteq h.symm, single_apply, h, erase_ne, h.symm]
#align finsupp.update_eq_single_add_erase Finsupp.update_eq_single_add_erase

theorem update_eq_erase_add_single (f : α →₀ M) (a : α) (b : M) :
    f.update a b = f.erase a + single a b := by
  classical
    ext j
    rcases eq_or_ne a j with (rfl | h)
    · simp
    · simp [Function.update_noteq h.symm, single_apply, h, erase_ne, h.symm]
#align finsupp.update_eq_erase_add_single Finsupp.update_eq_erase_add_single

theorem single_add_erase (a : α) (f : α →₀ M) : single a (f a) + f.erase a = f := by
  rw [← update_eq_single_add_erase, update_self]
  -- 🎉 no goals
#align finsupp.single_add_erase Finsupp.single_add_erase

theorem erase_add_single (a : α) (f : α →₀ M) : f.erase a + single a (f a) = f := by
  rw [← update_eq_erase_add_single, update_self]
  -- 🎉 no goals
#align finsupp.erase_add_single Finsupp.erase_add_single

@[simp]
theorem erase_add (a : α) (f f' : α →₀ M) : erase a (f + f') = erase a f + erase a f' := by
  ext s; by_cases hs : s = a
  -- ⊢ ↑(erase a (f + f')) s = ↑(erase a f + erase a f') s
         -- ⊢ ↑(erase a (f + f')) s = ↑(erase a f + erase a f') s
  · rw [hs, add_apply, erase_same, erase_same, erase_same, add_zero]
    -- 🎉 no goals
  rw [add_apply, erase_ne hs, erase_ne hs, erase_ne hs, add_apply]
  -- 🎉 no goals
#align finsupp.erase_add Finsupp.erase_add

/-- `Finsupp.erase` as an `AddMonoidHom`. -/
@[simps]
def eraseAddHom (a : α) : (α →₀ M) →+ α →₀ M where
  toFun := erase a
  map_zero' := erase_zero a
  map_add' := erase_add a
#align finsupp.erase_add_hom Finsupp.eraseAddHom

@[elab_as_elim]
protected theorem induction {p : (α →₀ M) → Prop} (f : α →₀ M) (h0 : p 0)
    (ha : ∀ (a b) (f : α →₀ M), a ∉ f.support → b ≠ 0 → p f → p (single a b + f)) : p f :=
  suffices ∀ (s) (f : α →₀ M), f.support = s → p f from this _ _ rfl
  fun s =>
  Finset.cons_induction_on s (fun f hf => by rwa [support_eq_empty.1 hf]) fun a s has ih f hf => by
                                             -- 🎉 no goals
    suffices p (single a (f a) + f.erase a) by rwa [single_add_erase] at this
    -- ⊢ p (single a (↑f a) + erase a f)
    classical
      apply ha
      · rw [support_erase, mem_erase]
        exact fun H => H.1 rfl
      · rw [← mem_support_iff, hf]
        exact mem_cons_self _ _
      · apply ih _ _
        rw [support_erase, hf, Finset.erase_cons]
#align finsupp.induction Finsupp.induction

theorem induction₂ {p : (α →₀ M) → Prop} (f : α →₀ M) (h0 : p 0)
    (ha : ∀ (a b) (f : α →₀ M), a ∉ f.support → b ≠ 0 → p f → p (f + single a b)) : p f :=
  suffices ∀ (s) (f : α →₀ M), f.support = s → p f from this _ _ rfl
  fun s =>
  Finset.cons_induction_on s (fun f hf => by rwa [support_eq_empty.1 hf]) fun a s has ih f hf => by
                                             -- 🎉 no goals
    suffices p (f.erase a + single a (f a)) by rwa [erase_add_single] at this
    -- ⊢ p (erase a f + single a (↑f a))
    classical
      apply ha
      · rw [support_erase, mem_erase]
        exact fun H => H.1 rfl
      · rw [← mem_support_iff, hf]
        exact mem_cons_self _ _
      · apply ih _ _
        rw [support_erase, hf, Finset.erase_cons]
#align finsupp.induction₂ Finsupp.induction₂

theorem induction_linear {p : (α →₀ M) → Prop} (f : α →₀ M) (h0 : p 0)
    (hadd : ∀ f g : α →₀ M, p f → p g → p (f + g)) (hsingle : ∀ a b, p (single a b)) : p f :=
  induction₂ f h0 fun _a _b _f _ _ w => hadd _ _ w (hsingle _ _)
#align finsupp.induction_linear Finsupp.induction_linear

@[simp]
theorem add_closure_setOf_eq_single :
    AddSubmonoid.closure { f : α →₀ M | ∃ a b, f = single a b } = ⊤ :=
  top_unique fun x _hx =>
    Finsupp.induction x (AddSubmonoid.zero_mem _) fun a b _f _ha _hb hf =>
      AddSubmonoid.add_mem _ (AddSubmonoid.subset_closure <| ⟨a, b, rfl⟩) hf
#align finsupp.add_closure_set_of_eq_single Finsupp.add_closure_setOf_eq_single

/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`,
then they are equal. -/
theorem addHom_ext [AddZeroClass N] ⦃f g : (α →₀ M) →+ N⦄
    (H : ∀ x y, f (single x y) = g (single x y)) : f = g := by
  refine' AddMonoidHom.eq_of_eqOn_denseM add_closure_setOf_eq_single _
  -- ⊢ Set.EqOn ↑f ↑g {f | ∃ a b, f = single a b}
  rintro _ ⟨x, y, rfl⟩
  -- ⊢ ↑f (single x y) = ↑g (single x y)
  apply H
  -- 🎉 no goals
#align finsupp.add_hom_ext Finsupp.addHom_ext

/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`,
then they are equal.

We formulate this using equality of `AddMonoidHom`s so that `ext` tactic can apply a type-specific
extensionality lemma after this one.  E.g., if the fiber `M` is `ℕ` or `ℤ`, then it suffices to
verify `f (single a 1) = g (single a 1)`. -/
@[ext high]
theorem addHom_ext' [AddZeroClass N] ⦃f g : (α →₀ M) →+ N⦄
    (H : ∀ x, f.comp (singleAddHom x) = g.comp (singleAddHom x)) : f = g :=
  addHom_ext fun x => FunLike.congr_fun (H x)
#align finsupp.add_hom_ext' Finsupp.addHom_ext'

theorem mulHom_ext [MulOneClass N] ⦃f g : Multiplicative (α →₀ M) →* N⦄
    (H : ∀ x y, f (Multiplicative.ofAdd <| single x y) = g (Multiplicative.ofAdd <| single x y)) :
    f = g :=
  MonoidHom.ext <|
    FunLike.congr_fun <| by
      have := @addHom_ext α M (Additive N) _ _
        (MonoidHom.toAdditive'' f) (MonoidHom.toAdditive'' g) H
      ext
      -- ⊢ ↑f x✝ = ↑g x✝
      rw [FunLike.ext_iff] at this
      -- ⊢ ↑f x✝ = ↑g x✝
      apply this
      -- 🎉 no goals
#align finsupp.mul_hom_ext Finsupp.mulHom_ext

@[ext]
theorem mulHom_ext' [MulOneClass N] {f g : Multiplicative (α →₀ M) →* N}
    (H : ∀ x, f.comp (AddMonoidHom.toMultiplicative (singleAddHom x)) =
              g.comp (AddMonoidHom.toMultiplicative (singleAddHom x))) :
    f = g :=
  mulHom_ext fun x => FunLike.congr_fun (H x)
#align finsupp.mul_hom_ext' Finsupp.mulHom_ext'

theorem mapRange_add [AddZeroClass N] {f : M → N} {hf : f 0 = 0}
    (hf' : ∀ x y, f (x + y) = f x + f y) (v₁ v₂ : α →₀ M) :
    mapRange f hf (v₁ + v₂) = mapRange f hf v₁ + mapRange f hf v₂ :=
  ext fun _ => by simp only [hf', add_apply, mapRange_apply]
                  -- 🎉 no goals
#align finsupp.map_range_add Finsupp.mapRange_add

theorem mapRange_add' [AddZeroClass N] [AddMonoidHomClass β M N] {f : β} (v₁ v₂ : α →₀ M) :
    mapRange f (map_zero f) (v₁ + v₂) = mapRange f (map_zero f) v₁ + mapRange f (map_zero f) v₂ :=
  mapRange_add (map_add f) v₁ v₂
#align finsupp.map_range_add' Finsupp.mapRange_add'

/-- Bundle `Finsupp.embDomain f` as an additive map from `α →₀ M` to `β →₀ M`. -/
@[simps]
def embDomain.addMonoidHom (f : α ↪ β) : (α →₀ M) →+ β →₀ M where
  toFun v := embDomain f v
  map_zero' := by simp
                  -- 🎉 no goals
  map_add' v w := by
    ext b
    -- ⊢ ↑(ZeroHom.toFun { toFun := fun v => embDomain f v, map_zero' := (_ : 0 = 0)  …
    by_cases h : b ∈ Set.range f
    -- ⊢ ↑(ZeroHom.toFun { toFun := fun v => embDomain f v, map_zero' := (_ : 0 = 0)  …
    · rcases h with ⟨a, rfl⟩
      -- ⊢ ↑(ZeroHom.toFun { toFun := fun v => embDomain f v, map_zero' := (_ : 0 = 0)  …
      simp
      -- 🎉 no goals
    · simp only [Set.mem_range, not_exists, coe_add, Pi.add_apply,
        embDomain_notin_range _ _ _ h, add_zero]
#align finsupp.emb_domain.add_monoid_hom Finsupp.embDomain.addMonoidHom

@[simp]
theorem embDomain_add (f : α ↪ β) (v w : α →₀ M) :
    embDomain f (v + w) = embDomain f v + embDomain f w :=
  (embDomain.addMonoidHom f).map_add v w
#align finsupp.emb_domain_add Finsupp.embDomain_add

end AddZeroClass

section AddMonoid

variable [AddMonoid M]

/-- Note the general `SMul` instance for `Finsupp` doesn't apply as `ℕ` is not distributive
unless `β i`'s addition is commutative. -/
instance hasNatScalar : SMul ℕ (α →₀ M) :=
  ⟨fun n v => v.mapRange ((· • ·) n) (nsmul_zero _)⟩
#align finsupp.has_nat_scalar Finsupp.hasNatScalar

instance addMonoid : AddMonoid (α →₀ M) :=
  FunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl
#align finsupp.add_monoid Finsupp.addMonoid

end AddMonoid

instance addCommMonoid [AddCommMonoid M] : AddCommMonoid (α →₀ M) :=
  FunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl
#align finsupp.add_comm_monoid Finsupp.addCommMonoid

instance neg [NegZeroClass G] : Neg (α →₀ G) :=
  ⟨mapRange Neg.neg neg_zero⟩
#align finsupp.has_neg Finsupp.neg

@[simp]
theorem coe_neg [NegZeroClass G] (g : α →₀ G) : ⇑(-g) = -g :=
  rfl
#align finsupp.coe_neg Finsupp.coe_neg

theorem neg_apply [NegZeroClass G] (g : α →₀ G) (a : α) : (-g) a = -g a :=
  rfl
#align finsupp.neg_apply Finsupp.neg_apply

theorem mapRange_neg [NegZeroClass G] [NegZeroClass H] {f : G → H} {hf : f 0 = 0}
    (hf' : ∀ x, f (-x) = -f x) (v : α →₀ G) : mapRange f hf (-v) = -mapRange f hf v :=
  ext fun _ => by simp only [hf', neg_apply, mapRange_apply]
                  -- 🎉 no goals
#align finsupp.map_range_neg Finsupp.mapRange_neg

theorem mapRange_neg' [AddGroup G] [SubtractionMonoid H] [AddMonoidHomClass β G H] {f : β}
    (v : α →₀ G) : mapRange f (map_zero f) (-v) = -mapRange f (map_zero f) v :=
  mapRange_neg (map_neg f) v
#align finsupp.map_range_neg' Finsupp.mapRange_neg'

instance sub [SubNegZeroMonoid G] : Sub (α →₀ G) :=
  ⟨zipWith Sub.sub (sub_zero _)⟩
#align finsupp.has_sub Finsupp.sub

@[simp]
theorem coe_sub [SubNegZeroMonoid G] (g₁ g₂ : α →₀ G) : ⇑(g₁ - g₂) = g₁ - g₂ :=
  rfl
#align finsupp.coe_sub Finsupp.coe_sub

theorem sub_apply [SubNegZeroMonoid G] (g₁ g₂ : α →₀ G) (a : α) : (g₁ - g₂) a = g₁ a - g₂ a :=
  rfl
#align finsupp.sub_apply Finsupp.sub_apply

theorem mapRange_sub [SubNegZeroMonoid G] [SubNegZeroMonoid H] {f : G → H} {hf : f 0 = 0}
    (hf' : ∀ x y, f (x - y) = f x - f y) (v₁ v₂ : α →₀ G) :
    mapRange f hf (v₁ - v₂) = mapRange f hf v₁ - mapRange f hf v₂ :=
  ext fun _ => by simp only [hf', sub_apply, mapRange_apply]
                  -- 🎉 no goals
#align finsupp.map_range_sub Finsupp.mapRange_sub

theorem mapRange_sub' [AddGroup G] [SubtractionMonoid H] [AddMonoidHomClass β G H] {f : β}
    (v₁ v₂ : α →₀ G) :
    mapRange f (map_zero f) (v₁ - v₂) = mapRange f (map_zero f) v₁ - mapRange f (map_zero f) v₂ :=
  mapRange_sub (map_sub f) v₁ v₂
#align finsupp.map_range_sub' Finsupp.mapRange_sub'

/-- Note the general `SMul` instance for `Finsupp` doesn't apply as `ℤ` is not distributive
unless `β i`'s addition is commutative. -/
instance hasIntScalar [AddGroup G] : SMul ℤ (α →₀ G) :=
  ⟨fun n v => v.mapRange ((· • ·) n) (zsmul_zero _)⟩
#align finsupp.has_int_scalar Finsupp.hasIntScalar

instance addGroup [AddGroup G] : AddGroup (α →₀ G) :=
  FunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl
#align finsupp.add_group Finsupp.addGroup

instance addCommGroup [AddCommGroup G] : AddCommGroup (α →₀ G) :=
  FunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ =>
    rfl
#align finsupp.add_comm_group Finsupp.addCommGroup

theorem single_add_single_eq_single_add_single [AddCommMonoid M] {k l m n : α} {u v : M}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    single k u + single l v = single m u + single n v ↔
      (k = m ∧ l = n) ∨ (u = v ∧ k = n ∧ l = m) ∨ (u + v = 0 ∧ k = l ∧ m = n) := by
  classical
    simp_rw [FunLike.ext_iff, coe_add, single_eq_pi_single, ← funext_iff]
    exact Pi.single_add_single_eq_single_add_single hu hv
#align finsupp.single_add_single_eq_single_add_single Finsupp.single_add_single_eq_single_add_single

@[simp]
theorem support_neg [AddGroup G] (f : α →₀ G) : support (-f) = support f :=
  Finset.Subset.antisymm support_mapRange
    (calc
      support f = support (- -f) := congr_arg support (neg_neg _).symm
      _ ⊆ support (-f) := support_mapRange
      )
#align finsupp.support_neg Finsupp.support_neg

theorem support_sub [DecidableEq α] [AddGroup G] {f g : α →₀ G} :
    support (f - g) ⊆ support f ∪ support g := by
  rw [sub_eq_add_neg, ← support_neg g]
  -- ⊢ (f + -g).support ⊆ f.support ∪ (-g).support
  exact support_add
  -- 🎉 no goals
#align finsupp.support_sub Finsupp.support_sub

theorem erase_eq_sub_single [AddGroup G] (f : α →₀ G) (a : α) : f.erase a = f - single a (f a) := by
  ext a'
  -- ⊢ ↑(erase a f) a' = ↑(f - single a (↑f a)) a'
  rcases eq_or_ne a a' with (rfl | h)
  -- ⊢ ↑(erase a f) a = ↑(f - single a (↑f a)) a
  · simp
    -- 🎉 no goals
  · simp [erase_ne h.symm, single_eq_of_ne h]
    -- 🎉 no goals
#align finsupp.erase_eq_sub_single Finsupp.erase_eq_sub_single

theorem update_eq_sub_add_single [AddGroup G] (f : α →₀ G) (a : α) (b : G) :
    f.update a b = f - single a (f a) + single a b := by
  rw [update_eq_erase_add_single, erase_eq_sub_single]
  -- 🎉 no goals
#align finsupp.update_eq_sub_add_single Finsupp.update_eq_sub_add_single

end Finsupp
