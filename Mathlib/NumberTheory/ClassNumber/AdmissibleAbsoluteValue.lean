/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Algebra.Order.AbsoluteValue.Euclidean

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
set_option backward.defeqAttrib.useBackward true

@[expose] public section

local infixl:50 " ≺ " => EuclideanDomain.r

namespace AbsoluteValue

variable {R : Type*} [EuclideanDomain R]
variable (abv : AbsoluteValue R ℤ)

/-- An absolute value `R → ℤ` is admissible if it respects the Euclidean domain
structure and a large enough set of elements in `R^n` will contain a pair of
elements whose remainders are pointwise close together. -/
structure IsAdmissible extends IsEuclidean abv where
  /-- The cardinality required for a given `ε`. -/
  protected card : ℝ → ℕ
  /-- For all `ε > 0` and finite families `A`, we can partition the remainders of `A` mod `b`
  into `abv.card ε` sets, such that all elements in each part of remainders are close together. -/
  exists_partition' :
    ∀ (n : ℕ) {ε : ℝ} (_ : 0 < ε) {b : R} (_ : b ≠ 0) (A : Fin n → R),
      ∃ t : Fin n → Fin (card ε), ∀ i₀ i₁, t i₀ = t i₁ → (abv (A i₁ % b - A i₀ % b) : ℝ) < abv b • ε

namespace IsAdmissible

variable {abv}

/-- For all `ε > 0` and finite families `A`, we can partition the remainders of `A` mod `b`
into `abv.card ε` sets, such that all elements in each part of remainders are close together. -/
theorem exists_partition {ι : Type*} [Finite ι] {ε : ℝ} (hε : 0 < ε) {b : R} (hb : b ≠ 0)
    (A : ι → R) (h : abv.IsAdmissible) : ∃ t : ι → Fin (h.card ε),
      ∀ i₀ i₁, t i₀ = t i₁ → (abv (A i₁ % b - A i₀ % b) : ℝ) < abv b • ε := by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  obtain ⟨t, ht⟩ := h.exists_partition' n hε hb (A ∘ e.symm)
  refine ⟨t ∘ e, fun i₀ i₁ h ↦ ?_⟩
  convert (config := { transparency := .default })
    ht (e i₀) (e i₁) h <;> simp only [e.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Any large enough family of vectors in `R^n` has a pair of elements
whose remainders are close together, pointwise. -/
theorem exists_approx_aux (n : ℕ) (h : abv.IsAdmissible) :
    ∀ {ε : ℝ} (_hε : 0 < ε) {b : R} (_hb : b ≠ 0) (A : Fin (h.card ε ^ n).succ → Fin n → R),
      ∃ i₀ i₁, i₀ ≠ i₁ ∧ ∀ k, (abv (A i₁ k % b - A i₀ k % b) : ℝ) < abv b • ε := by
  haveI := Classical.decEq R
  induction n with
  | zero =>
    intro ε _hε b _hb A
    refine ⟨0, 1, ?_, ?_⟩
    · simp
    rintro ⟨i, ⟨⟩⟩
  | succ n ih =>
  intro ε hε b hb A
  let M := h.card ε
  -- By the "nicer" pigeonhole principle, we can find a collection `s`
  -- of more than `M ^ n` remainders where the first components lie close together:
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
      Fintype.exists_lt_card_fiber_of_mul_lt_card (f := t)
        (by simpa only [Fintype.card_fin, pow_succ'] using Nat.lt_succ_self (M ^ n.succ))
    have : (M ^ n).succ ≤ (Finset.toList {x | t x = s}).length := by
      rwa [Finset.length_toList]
    refine ⟨fun i ↦ (Finset.toList {x | t x = s})[i.castLE this], fun i j h ↦ ?_,
      fun i₀ i₁ ↦ ht _ _ ?_⟩
    · simpa [(Finset.nodup_toList _).getElem_inj_iff, Fin.val_inj] using h
    · have (i : Fin (M ^ n).succ) : t (Finset.toList {x | t x = s})[i.castLE this] = s :=
        (Finset.mem_filter.mp ((Finset.mem_toList (s := {x | t x = s})).mp (List.getElem_mem _))).2
      simp_rw [this]
  -- Since `s` is large enough, there are two elements of `A ∘ s`
  -- where the second components lie close together.
  obtain ⟨k₀, k₁, hk, h⟩ := ih hε hb fun x ↦ Fin.tail (A (s x))
  refine ⟨s k₀, s k₁, fun h ↦ hk (s_inj h), fun i ↦ Fin.cases ?_ (fun i ↦ ?_) i⟩
  · exact hs k₀ k₁
  · exact h i

/-- Any large enough family of vectors in `R^ι` has a pair of elements
whose remainders are close together, pointwise. -/
theorem exists_approx {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) {b : R} (hb : b ≠ 0)
    (h : abv.IsAdmissible) (A : Fin (h.card ε ^ Fintype.card ι).succ → ι → R) :
    ∃ i₀ i₁, i₀ ≠ i₁ ∧ ∀ k, (abv (A i₁ k % b - A i₀ k % b) : ℝ) < abv b • ε := by
  let e := Fintype.equivFin ι
  obtain ⟨i₀, i₁, ne, h⟩ := h.exists_approx_aux (Fintype.card ι) hε hb fun x y ↦ A x (e.symm y)
  refine ⟨i₀, i₁, ne, fun k ↦ ?_⟩
  convert h (e k) <;> simp only [e.symm_apply_apply]

end IsAdmissible

end AbsoluteValue
