/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.Order.EuclideanAbsoluteValue

#align_import number_theory.class_number.admissible_absolute_value from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Admissible absolute values
This file defines a structure `AbsoluteValue.IsAdmissible` which we use to show the class number
of the ring of integers of a global field is finite.

## Main definitions

 * `AbsoluteValue.IsAdmissible abv` states the absolute value `abv : R → ℤ`
   respects the Euclidean domain structure on `R`, and that a large enough set
   of elements of `R^n` contains a pair of elements whose remainders are
   pointwise close together.

## Main results

 * `AbsoluteValue.absIsAdmissible` shows the "standard" absolute value on `ℤ`,
   mapping negative `x` to `-x`, is admissible.
 * `Polynomial.cardPowDegreeIsAdmissible` shows `cardPowDegree`,
   mapping `p : Polynomial 𝔽_q` to `q ^ degree p`, is admissible
-/

local infixl:50 " ≺ " => EuclideanDomain.r

namespace AbsoluteValue

variable {R : Type*} [EuclideanDomain R]

variable (abv : AbsoluteValue R ℤ)

/-- An absolute value `R → ℤ` is admissible if it respects the Euclidean domain
structure and a large enough set of elements in `R^n` will contain a pair of
elements whose remainders are pointwise close together. -/
structure IsAdmissible extends IsEuclidean abv where
  protected card : ℝ → ℕ
  /-- For all `ε > 0` and finite families `A`, we can partition the remainders of `A` mod `b`
  into `abv.card ε` sets, such that all elements in each part of remainders are close together. -/
  exists_partition' :
    ∀ (n : ℕ) {ε : ℝ} (_ : 0 < ε) {b : R} (_ : b ≠ 0) (A : Fin n → R),
      ∃ t : Fin n → Fin (card ε), ∀ i₀ i₁, t i₀ = t i₁ → (abv (A i₁ % b - A i₀ % b) : ℝ) < abv b • ε
#align absolute_value.is_admissible AbsoluteValue.IsAdmissible

-- Porting note: no docstrings for IsAdmissible
attribute [nolint docBlame] IsAdmissible.card


namespace IsAdmissible

variable {abv}

/-- For all `ε > 0` and finite families `A`, we can partition the remainders of `A` mod `b`
into `abv.card ε` sets, such that all elements in each part of remainders are close together. -/
theorem exists_partition {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) {b : R} (hb : b ≠ 0)
    (A : ι → R) (h : abv.IsAdmissible) : ∃ t : ι → Fin (h.card ε),
      ∀ i₀ i₁, t i₀ = t i₁ → (abv (A i₁ % b - A i₀ % b) : ℝ) < abv b • ε := by
  let e := Fintype.equivFin ι
  -- ⊢ ∃ t, ∀ (i₀ i₁ : ι), t i₀ = t i₁ → ↑(↑abv (A i₁ % b - A i₀ % b)) < ↑abv b • ε
  obtain ⟨t, ht⟩ := h.exists_partition' (Fintype.card ι) hε hb (A ∘ e.symm)
  -- ⊢ ∃ t, ∀ (i₀ i₁ : ι), t i₀ = t i₁ → ↑(↑abv (A i₁ % b - A i₀ % b)) < ↑abv b • ε
  refine' ⟨t ∘ e, fun i₀ i₁ h ↦ _⟩
  -- ⊢ ↑(↑abv (A i₁ % b - A i₀ % b)) < ↑abv b • ε
  convert (config := {transparency := .default})
    ht (e i₀) (e i₁) h <;> simp only [e.symm_apply_apply]
                           -- 🎉 no goals
                           -- 🎉 no goals
#align absolute_value.is_admissible.exists_partition AbsoluteValue.IsAdmissible.exists_partition

/-- Any large enough family of vectors in `R^n` has a pair of elements
whose remainders are close together, pointwise. -/
theorem exists_approx_aux (n : ℕ) (h : abv.IsAdmissible) :
    ∀ {ε : ℝ} (_hε : 0 < ε) {b : R} (_hb : b ≠ 0) (A : Fin (h.card ε ^ n).succ → Fin n → R),
      ∃ i₀ i₁, i₀ ≠ i₁ ∧ ∀ k, (abv (A i₁ k % b - A i₀ k % b) : ℝ) < abv b • ε := by
  haveI := Classical.decEq R
  -- ⊢ ∀ {ε : ℝ}, 0 < ε → ∀ {b : R}, b ≠ 0 → ∀ (A : Fin (Nat.succ (IsAdmissible.car …
  induction' n with n ih
  -- ⊢ ∀ {ε : ℝ}, 0 < ε → ∀ {b : R}, b ≠ 0 → ∀ (A : Fin (Nat.succ (IsAdmissible.car …
  · intro ε _hε b _hb A
    -- ⊢ ∃ i₀ i₁, i₀ ≠ i₁ ∧ ∀ (k : Fin Nat.zero), ↑(↑abv (A i₁ k % b - A i₀ k % b)) < …
    refine' ⟨0, 1, _, _⟩
    -- ⊢ 0 ≠ 1
    · simp
      -- 🎉 no goals
    rintro ⟨i, ⟨⟩⟩
    -- 🎉 no goals
  intro ε hε b hb A
  -- ⊢ ∃ i₀ i₁, i₀ ≠ i₁ ∧ ∀ (k : Fin (Nat.succ n)), ↑(↑abv (A i₁ k % b - A i₀ k % b …
  let M := h.card ε
  -- ⊢ ∃ i₀ i₁, i₀ ≠ i₁ ∧ ∀ (k : Fin (Nat.succ n)), ↑(↑abv (A i₁ k % b - A i₀ k % b …
  -- By the "nicer" pigeonhole principle, we can find a collection `s`
  -- of more than `M^n` remainders where the first components lie close together:
  obtain ⟨s, s_inj, hs⟩ :
    ∃ s : Fin (M ^ n).succ → Fin (M ^ n.succ).succ,
      Function.Injective s ∧ ∀ i₀ i₁, (abv (A (s i₁) 0 % b - A (s i₀) 0 % b) : ℝ) < abv b • ε := by
    -- We can partition the `A`s into `M` subsets where
    -- the first components lie close together:
    obtain ⟨t, ht⟩ :
      ∃ t : Fin (M ^ n.succ).succ → Fin M,
        ∀ i₀ i₁, t i₀ = t i₁ → (abv (A i₁ 0 % b - A i₀ 0 % b) : ℝ) < abv b • ε :=
      h.exists_partition hε hb fun x ↦ A x 0
    -- Since the `M` subsets contain more than `M * M^n` elements total,
    -- there must be a subset that contains more than `M^n` elements.
    obtain ⟨s, hs⟩ :=
      @Fintype.exists_lt_card_fiber_of_mul_lt_card _ _ _ _ _ t (M ^ n)
        (by simpa only [Fintype.card_fin, pow_succ] using Nat.lt_succ_self (M ^ n.succ))
    refine'
      ⟨fun i ↦ (Finset.univ.filter fun x ↦ t x = s).toList.nthLe i _, _, fun i₀ i₁ ↦ ht _ _ _⟩
    · refine' i.2.trans_le _
      rwa [Finset.length_toList]
    · intro i j h
      ext
      exact Fin.mk.inj_iff.mp (List.nodup_iff_injective_get.mp (Finset.nodup_toList _) h)
    have : ∀ i h, (Finset.univ.filter fun x ↦ t x = s).toList.nthLe i h ∈
        Finset.univ.filter fun x ↦ t x = s := by
      intro i h
      exact Finset.mem_toList.mp (List.get_mem _ i h)
    obtain ⟨_, h₀⟩ := Finset.mem_filter.mp (this i₀ _)
    obtain ⟨_, h₁⟩ := Finset.mem_filter.mp (this i₁ _)
    exact h₀.trans h₁.symm
  -- Since `s` is large enough, there are two elements of `A ∘ s`
  -- where the second components lie close together.
  obtain ⟨k₀, k₁, hk, h⟩ := ih hε hb fun x ↦ Fin.tail (A (s x))
  -- ⊢ ∃ i₀ i₁, i₀ ≠ i₁ ∧ ∀ (k : Fin (Nat.succ n)), ↑(↑abv (A i₁ k % b - A i₀ k % b …
  refine' ⟨s k₀, s k₁, fun h ↦ hk (s_inj h), fun i ↦ Fin.cases _ (fun i ↦ _) i⟩
  -- ⊢ ↑(↑abv (A (s k₁) 0 % b - A (s k₀) 0 % b)) < ↑abv b • ε
  · exact hs k₀ k₁
    -- 🎉 no goals
  · exact h i
    -- 🎉 no goals
#align absolute_value.is_admissible.exists_approx_aux AbsoluteValue.IsAdmissible.exists_approx_aux

/-- Any large enough family of vectors in `R^ι` has a pair of elements
whose remainders are close together, pointwise. -/
theorem exists_approx {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) {b : R} (hb : b ≠ 0)
    (h : abv.IsAdmissible) (A : Fin (h.card ε ^ Fintype.card ι).succ → ι → R) :
    ∃ i₀ i₁, i₀ ≠ i₁ ∧ ∀ k, (abv (A i₁ k % b - A i₀ k % b) : ℝ) < abv b • ε := by
  let e := Fintype.equivFin ι
  -- ⊢ ∃ i₀ i₁, i₀ ≠ i₁ ∧ ∀ (k : ι), ↑(↑abv (A i₁ k % b - A i₀ k % b)) < ↑abv b • ε
  obtain ⟨i₀, i₁, ne, h⟩ := h.exists_approx_aux (Fintype.card ι) hε hb fun x y ↦ A x (e.symm y)
  -- ⊢ ∃ i₀ i₁, i₀ ≠ i₁ ∧ ∀ (k : ι), ↑(↑abv (A i₁ k % b - A i₀ k % b)) < ↑abv b • ε
  refine' ⟨i₀, i₁, ne, fun k ↦ _⟩
  -- ⊢ ↑(↑abv (A i₁ k % b - A i₀ k % b)) < ↑abv b • ε
  convert h (e k) <;> simp only [e.symm_apply_apply]
  -- ⊢ k = ↑e.symm (↑e k)
                      -- 🎉 no goals
                      -- 🎉 no goals
#align absolute_value.is_admissible.exists_approx AbsoluteValue.IsAdmissible.exists_approx

end IsAdmissible

end AbsoluteValue
