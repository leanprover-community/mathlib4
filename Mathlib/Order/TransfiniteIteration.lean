/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Violeta Hernández Palacios
-/
module

public import Mathlib.Order.SuccPred.Limit

/-!
# Transfinite iteration of a function `I → I`

This file aims to define the transfinite iteration of a function `φ : I → I`, starting at a point
`i₀ : I`. Any reasonable definition must satisfy that `iterate φ ⊥ i₀ = i₀` and
`iterate φ (succ j) i₀ = φ (iterate φ j i₀)`. There are multiple ways to handle limit points; two
reasonable approaches are to take the suprema or infima of all previous values. We define these as
`supTransfiniteIterate` and `infTransfiniteIterate`.

If `I` is a complete lattice, we show that `j ↦ supTransfiniteIterate φ j i₀` is a monotone function
if `i ≤ φ i` for all `i`. Moreover, if `i < φ i` when `i ≠ ⊤`, we show in the theorem
`top_mem_range_supTransfiniteIterate` that there exists `j : J` such that `transfiniteIteration φ i₀
j = ⊤` if we assume that `j ↦ transfiniteIterate φ i₀ j : J → I` is not injective (which shall hold
when we know `Cardinal.mk I < Cardinal.mk J`).

## TODO (@joelriou)
* deduce that in a Grothendieck abelian category, there is a *set* `I` of monomorphisms such that
  any monomorphism is a transfinite composition of pushouts of morphisms in `I`, and then an object
  `X` is injective iff `X ⟶ 0` has the right lifting property with respect to `I`.

-/

public section

open Order

variable {I J : Type*} [LinearOrder J] [WellFoundedLT J] (φ : I → I) (i₀ : I)

section SupSet
variable [SupSet I]

/-- The `j`th-iteration of a function `φ : I → I` when `j : J` belongs to a well-ordered type,
defined by taking *suprema* at limit points. -/
@[to_dual (dont_translate := J)
/-- The `j`th-iteration of a function `φ : I → I` when `j : J` belongs to a well-ordered type,
defined by taking *infima* at limit points. -/]
noncomputable def supTransfiniteIterate (j : J) : I → I :=
  let := SuccOrder.ofLinearWellFoundedLT J
  SuccOrder.limitRecOn j
    (fun _ _ ↦ id) (fun _ _ g ↦ φ ∘ g) (fun y _ h ↦ ⨆ x : Set.Iio y, h x.1 (Set.mem_Iio.1 x.2))

@[deprecated (since := "2026-09-15")]
alias transfiniteIterate := supTransfiniteIterate

@[to_dual (dont_translate := J) (attr := simp) infTransfiniteIterate_of_isMin]
theorem supTransfiniteIterate_of_isMin {j : J} (hj : IsMin j) :
    supTransfiniteIterate φ j i₀ = i₀ := by
  let := SuccOrder.ofLinearWellFoundedLT J
  rw [supTransfiniteIterate, SuccOrder.limitRecOn_isMin _ _ _ hj]
  rfl

@[to_dual (dont_translate := J) (attr := simp) infTransfiniteIterate_bot]
theorem supTransfiniteIterate_bot [OrderBot J] : supTransfiniteIterate φ (⊥ : J) i₀ = i₀ :=
  supTransfiniteIterate_of_isMin _ _ isMin_bot

@[deprecated (since := "2026-09-15")]
alias transfiniteIterate_bot := supTransfiniteIterate_bot

@[to_dual (dont_translate := J) infTransfiniteIterate_succ_of_not_isMax]
theorem supTransfiniteIterate_succ_of_not_isMax [SuccOrder J] {j : J} (hj : ¬ IsMax j) :
    supTransfiniteIterate φ (Order.succ j) i₀ = φ (supTransfiniteIterate φ j i₀) := by
  obtain rfl : ‹_› = SuccOrder.ofLinearWellFoundedLT J := by subsingleton
  let := SuccOrder.ofLinearWellFoundedLT J
  rw [supTransfiniteIterate, SuccOrder.limitRecOn_succ_of_not_isMax _ _ _ hj]
  rfl

@[deprecated (since := "2026-09-15")]
alias transfiniteIterate_succ := supTransfiniteIterate_succ_of_not_isMax

@[to_dual (dont_translate := J) (attr := simp) infTransfiniteIterate_succ]
theorem supTransfiniteIterate_succ [SuccOrder J] [NoMaxOrder J] (j : J) :
    supTransfiniteIterate φ (Order.succ j) i₀ = φ (supTransfiniteIterate φ j i₀) :=
  supTransfiniteIterate_succ_of_not_isMax _ _ (not_isMax j)

@[to_dual (dont_translate := J) infTransfiniteIterate_limit]
theorem supTransfiniteIterate_limit {j : J} (hj : Order.IsSuccLimit j) :
    supTransfiniteIterate φ j i₀ = ⨆ x : Set.Iio j, supTransfiniteIterate φ x.1 i₀ := by
  let := SuccOrder.ofLinearWellFoundedLT J
  unfold supTransfiniteIterate
  simp [SuccOrder.limitRecOn_of_isSuccLimit _ _ _ hj]

@[deprecated (since := "2026-09-15")]
alias transfiniteIterate_limit := supTransfiniteIterate_limit

open OrderDual in
@[to_dual (dont_translate := J)]
theorem supTransfiniteIterate_dual (j : J) :
    supTransfiniteIterate φ j i₀ = infTransfiniteIterate (toDual ∘ φ ∘ ofDual) j (toDual i₀) :=
  (rfl)

end SupSet

section CompleteLattice
variable [CompleteLattice I] {φ : I → I}

@[to_dual (dont_translate := J) infTransfiniteIterate_anti]
theorem supTransfiniteIterate_mono (hφ : ∀ i, i ≤ φ i) {j k : J} (h : j ≤ k) :
    supTransfiniteIterate φ j i₀ ≤ supTransfiniteIterate φ k i₀ := by
  have := SuccOrder.ofLinearWellFoundedLT J
  induction k using SuccOrder.limitRecOn with
  | isMin k' hk' =>
    rw [supTransfiniteIterate_of_isMin _ _ hk', supTransfiniteIterate_of_isMin _ _ (hk'.mono h)]
  | succ k' hk' IH =>
    obtain h | rfl := h.lt_or_eq
    · rw [Order.lt_succ_iff_of_not_isMax hk'] at h
      grw [IH h, supTransfiniteIterate_succ_of_not_isMax _ _ hk']
      exact hφ _
    · rfl
  | isSuccLimit k' hk' _ =>
    obtain h | rfl := h.lt_or_eq
    · rw [supTransfiniteIterate_limit _ _ hk']
      exact le_iSup (fun l : Set.Iio k' ↦ supTransfiniteIterate φ l.1 i₀) ⟨j, Set.mem_Iio.1 h⟩
    · rfl

theorem supTransfiniteIterate_monotone (hφ : ∀ i, i ≤ φ i) :
    Monotone (fun j : J ↦ supTransfiniteIterate φ j i₀) :=
  fun _ _ h ↦ supTransfiniteIterate_mono _ hφ h

@[deprecated (since := "2026-09-15")]
alias monotone_transfiniteIterate := supTransfiniteIterate_monotone

theorem infTransfiniteIterate_antitone (hφ : ∀ i, φ i ≤ i) :
    Antitone (fun j : J ↦ infTransfiniteIterate φ j i₀) :=
  fun _ _ h ↦ infTransfiniteIterate_anti _ hφ h

-- TODO: prove that if `∀ i, i ≤ φ i` and `supTransfiniteIterate` isn't injective, then it is
-- eventually constant.

@[to_dual (dont_translate := J) top_mem_range_infTransfiniteIterate]
theorem top_mem_range_supTransfiniteIterate {i₀ : I}
    (hφ' : ∀ i ≠ (⊤ : I), i < φ i) (φtop : φ ⊤ = ⊤)
    (H : ¬ Function.Injective (fun j : J ↦ supTransfiniteIterate φ j i₀)) :
    ∃ (j : J), supTransfiniteIterate φ j i₀ = ⊤ := by
  have := SuccOrder.ofLinearWellFoundedLT J
  have hφ (i : I) : i ≤ φ i := by
    by_cases hi : i = ⊤
    · subst hi
      rw [φtop]
    · exact (hφ' i hi).le
  obtain ⟨j₁, j₂, hj, eq⟩ : ∃ (j₁ j₂ : J) (hj : j₁ < j₂),
      supTransfiniteIterate φ j₁ i₀ = supTransfiniteIterate φ j₂ i₀ := by
    grind [Function.Injective]
  by_contra!
  suffices supTransfiniteIterate φ j₁ i₀ < supTransfiniteIterate φ j₂ i₀ by
    simp only [eq, lt_self_iff_false] at this
  have hj₁ : ¬ IsMax j₁ := by
    simp only [not_isMax_iff]
    exact ⟨_, hj⟩
  refine lt_of_lt_of_le (hφ' _ (this j₁)) ?_
  rw [← supTransfiniteIterate_succ_of_not_isMax φ i₀ hj₁]
  exact supTransfiniteIterate_mono _ hφ (Order.succ_le_of_lt hj)

end CompleteLattice
