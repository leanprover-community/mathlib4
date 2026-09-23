/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Well-formed bases

## Main definitions

* `WellFormedBasis basis`: a predicate meaning that all functions from `basis` tend to `atTop`,
  and `basis` is sorted such that if
  `g` goes after `f` in `basis`, then `log f =o[atTop] log g`.

-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

open Asymptotics Filter

/-- List of functions used to construct monomials in multiseries. -/
abbrev Basis := List (ℝ → ℝ)

/-- `WellFormedBasis basis` means that all functions from `basis` tend to `atTop`, and
`basis` is sorted such that if
`g` goes after `f` in `basis`, then `log f =o[atTop] log g`.

We use two types `Basis` and `WellFormedBasis` instead of a single bundled one because it
it lets us to use the `List` API for `Basis`. -/
def WellFormedBasis (basis : Basis) : Prop :=
  basis.Pairwise (fun x y => (Real.log ∘ y) =o[atTop] (Real.log ∘ x)) ∧
  ∀ f ∈ basis, Tendsto f atTop atTop

namespace WellFormedBasis

theorem nil : WellFormedBasis [] := by simp [WellFormedBasis]

theorem single (f : ℝ → ℝ) (hf : Tendsto f atTop atTop) : WellFormedBasis [f] := by
  simpa [WellFormedBasis]

theorem of_sublist {basis basis' : Basis} (h : List.Sublist basis basis')
    (h_basis : WellFormedBasis basis') : WellFormedBasis basis :=
  ⟨h_basis.left.sublist h, fun _ hf ↦ h_basis.right _ (h.subset hf)⟩

/-- The tail of a well-formed basis is well-formed. -/
theorem tail {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h : WellFormedBasis (basis_hd :: basis_tl)) : WellFormedBasis basis_tl :=
  h.of_sublist (by simp)

theorem of_append_right {left right : Basis} (h : WellFormedBasis (left ++ right)) :
    WellFormedBasis right :=
  h.of_sublist (by simp)

theorem compare_left_aux {basis : Basis} {f : ℝ → ℝ} (h : WellFormedBasis basis)
    (h_comp : ∀ g, basis.getLast? = .some g → (Real.log ∘ f) =o[atTop] (Real.log ∘ g)) :
    ∀ g ∈ basis, (Real.log ∘ f) =o[atTop] (Real.log ∘ g) := by
  intro g hg
  rcases basis.eq_nil_or_concat with rfl | ⟨basis_begin, basis_end, rfl⟩
  · simp at hg
  simp only [List.concat_eq_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq,
    forall_eq'] at hg h_comp
  rcases hg with hg | hg
  · simp only [WellFormedBasis, List.concat_eq_append, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at h
    exact h_comp.trans (by grind)
  · grind

theorem compare_right_aux {basis : Basis} {f : ℝ → ℝ} (h : WellFormedBasis basis)
    (h_comp : ∀ g, basis.head? = .some g → (Real.log ∘ g) =o[atTop] (Real.log ∘ f)) :
    ∀ g ∈ basis, (Real.log ∘ g) =o[atTop] (Real.log ∘ f) := by
  intro g hg
  cases basis with
  | nil => simp at hg
  | cons basis_hd basis_tl =>
    specialize h_comp basis_hd (by simp)
    simp only [List.mem_cons] at hg
    rcases hg with hg | hg
    · simpa [hg]
    · simp only [WellFormedBasis, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h
      exact .trans (by grind) h_comp

theorem append {left right : Basis}
    (h_left : WellFormedBasis left) (h_right : WellFormedBasis right)
    (h : ∀ f ∈ left, ∀ g ∈ right, (Real.log ∘ g) =o[atTop] (Real.log ∘ f)) :
    WellFormedBasis (left ++ right) := by
  simp only [WellFormedBasis] at *
  constructor
  · simpa [List.pairwise_append, h_left, h_right] using h
  · grind

theorem cons {basis : Basis} {f : ℝ → ℝ} (h_basis : WellFormedBasis basis)
    (hf_tendsto : Tendsto f atTop atTop)
    (hf : ∀ g ∈ basis, (Real.log ∘ g) =o[atTop] (Real.log ∘ f)) :
    WellFormedBasis (f :: basis) := by
  change WellFormedBasis ([f] ++ basis)
  exact append (by simpa [WellFormedBasis]) h_basis (by simpa)

theorem insert {left right : Basis} {f : ℝ → ℝ}
    (h : WellFormedBasis (left ++ right)) (hf_tendsto : Tendsto f atTop atTop)
    (hf_comp_left : ∀ g, left.getLast? = .some g → (Real.log ∘ f) =o[atTop] (Real.log ∘ g))
    (hf_comp_right : ∀ g, right.head? = .some g → (Real.log ∘ g) =o[atTop] (Real.log ∘ f)) :
    WellFormedBasis (left ++ f :: right) := by
  have : WellFormedBasis (f :: right) := cons (h.of_sublist (by simp)) hf_tendsto
    (compare_right_aux (h.of_sublist (by simp)) hf_comp_right)
  apply compare_left_aux (h.of_sublist (by simp)) at hf_comp_left
  apply append (h.of_sublist (by simp)) this
  exact fun g hg ↦ compare_right_aux this (by grind)

theorem push {basis : Basis} {f : ℝ → ℝ} (h : WellFormedBasis basis)
    (hf_tendsto : Tendsto f atTop atTop)
    (hf_comp : ∀ g, basis.getLast? = .some g → (Real.log ∘ f) =o[atTop] (Real.log ∘ g)) :
    WellFormedBasis (basis ++ [f]) :=
  insert (by simp [h]) hf_tendsto hf_comp (by simp)

/-- All functions from a well-formed basis tend to `atTop`. -/
theorem tendsto_atTop {basis : Basis} (h : WellFormedBasis basis) {f : ℝ → ℝ}
    (hf : f ∈ basis) :
    Tendsto f atTop atTop := h.right f hf

/-- Eventually all functions from a well-formed basis are positive. -/
theorem eventually_pos {basis : Basis} (h : WellFormedBasis basis) :
    ∀ᶠ x in atTop, ∀ f ∈ basis, 0 < f x := by
  induction basis with
  | nil => simp
  | cons hd tl ih =>
    simp only [WellFormedBasis, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h
    simp only [List.mem_cons, forall_eq_or_imp]
    exact (h.right.left.eventually <| eventually_gt_atTop 0).and (ih (by tauto))

/-- The first function in a well-formed basis is eventually positive. -/
theorem head_eventually_pos {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h : WellFormedBasis (basis_hd :: basis_tl)) : ∀ᶠ x in atTop, 0 < basis_hd x :=
  (forall_eventually_of_eventually_forall h.eventually_pos basis_hd).mono (by grind)

/-- All functions in the tail of a well-formed basis are little-o of the basis' head. -/
theorem tail_isLittleO_head {hd : ℝ → ℝ} {tl : Basis}
    (h : WellFormedBasis (hd :: tl)) {f : ℝ → ℝ} (hf : f ∈ tl) :
    (Real.log ∘ f) =o[atTop] (Real.log ∘ hd) := by
  rw [WellFormedBasis, List.pairwise_cons] at h
  exact h.left.left _ hf

theorem push_log_last {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl)) :
    WellFormedBasis ((basis_hd :: basis_tl) ++
      [Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)]) := by
  apply h_basis.push
  · simp [Real.tendsto_log_atTop.comp, h_basis.right]
  · intro g hg
    simpa [List.getLast_of_getLast?_eq_some hg] using Real.isLittleO_log_id_atTop.comp_tendsto <|
      Real.tendsto_log_atTop.comp <| h_basis.tendsto_atTop <| List.mem_of_getLast? hg

end WellFormedBasis

/-! ### Basis extensions -/

/-- The type of extensions of a given basis, defined as an inductive type.
Given a `basis : Basis` and `ex : BasisExtension basis` of it, one can use `getBasis` to produce a
basis `basis'` for which `basis <+ basis'`. Moreover, all such bases for which `basis` is a sublist
can be obtained in this manner. In this sense `BasisExtension` is a `Type`-valued analogue
of `List.Sublist`. -/
inductive BasisExtension : Basis → Type
| nil : BasisExtension []
| keep (basis_hd : ℝ → ℝ) {basis_tl : Basis} (ex : BasisExtension basis_tl) :
  BasisExtension (basis_hd :: basis_tl)
| insert {basis : Basis} (f : ℝ → ℝ) (ex : BasisExtension basis) : BasisExtension basis

namespace BasisExtension

/-- The basis after applying a basis extension. -/
def getBasis {basis : Basis} (ex : BasisExtension basis) : Basis :=
  match ex with
  | nil => []
  | keep basis_hd ex => basis_hd :: ex.getBasis
  | insert f ex => f :: ex.getBasis

theorem sublist_getBasis {basis : Basis} {ex : BasisExtension basis} :
    List.Sublist basis ex.getBasis := by
  induction ex with
  | nil => simp
  | keep _ ex ih => simpa [getBasis] using ih
  | insert _ ex ih => exact List.Sublist.cons _ ih

theorem insert_tail_wellFormedBasis {basis : Basis} {f : ℝ → ℝ}
    {ex_tl : BasisExtension basis}
    (h_basis : WellFormedBasis <| BasisExtension.getBasis (.insert f ex_tl)) :
    WellFormedBasis ex_tl.getBasis :=
  h_basis.of_sublist (by simp [getBasis])

end BasisExtension

end Tactic.ComputeAsymptotics
