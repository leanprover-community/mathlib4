/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.Exponential

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
`g` goes after `f` in `basis`, then `log f =o[atTop] log g`. -/
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

theorem insert {left right : Basis} {f : ℝ → ℝ}
    (h : WellFormedBasis (left ++ right)) (hf_tendsto : Tendsto f atTop atTop)
    (hf_comp_left : ∀ g, left.getLast? = .some g → (Real.log ∘ f) =o[atTop] (Real.log ∘ g))
    (hf_comp_right : ∀ g, right.head? = .some g → (Real.log ∘ g) =o[atTop] (Real.log ∘ f)) :
    WellFormedBasis (left ++ f :: right) := by
  simp only [WellFormedBasis, List.mem_append, List.mem_cons] at h ⊢
  constructor
  · rw [List.pairwise_append]
    constructorm* _ ∧ _
    · exact h.left.sublist (List.sublist_append_left _ _)
    · rw [List.pairwise_cons]
      refine ⟨?_, h.left.sublist (List.sublist_append_right _ _)⟩
      intro g hg
      cases right with
      | nil => simp at hg
      | cons right_hd right_tl =>
        specialize hf_comp_right right_hd (by simp)
        rcases hg with hg | hg
        · gcongr
        · rw [List.pairwise_append, List.pairwise_cons] at h
          exact .trans (by tauto) hf_comp_right
    · intro g hg k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · rcases left.eq_nil_or_concat with h_left | ⟨left_begin, left_end, rfl⟩
        · simp [h_left] at hg
        · rw [List.concat_eq_append, List.getLast?_append] at hf_comp_left
          rw [List.concat_eq_append, List.mem_append, List.mem_singleton] at hg
          rcases hg with hg | rfl
          · grind [(hf_comp_left _ rfl).trans]
          · exact hf_comp_left g rfl
      · rw [List.pairwise_append] at h
        grind
  · rintro g (hg | hg | hg)
    · exact h.right _ (.inl hg)
    · convert hf_tendsto
    · exact h.right _ (.inr hg)

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
theorem tail_IsLittleO_head {hd : ℝ → ℝ} {tl : Basis}
    (h : WellFormedBasis (hd :: tl)) {f : ℝ → ℝ} (hf : f ∈ tl) :
    (Real.log ∘ f) =o[atTop] (Real.log ∘ hd) := by
  rw [WellFormedBasis, List.pairwise_cons] at h
  exact h.left.left _ hf

theorem pushLogLast {basis_hd : ℝ → ℝ} {basis_tl : Basis}
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

/-- Basis extension. It is a `Type`-version of `List.Sublist`.
Using `getBasis` one can construct any `basis'` from `basis` if `basis <+ basis'`. -/
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

theorem getBasis_Sublist {basis : Basis} {ex : BasisExtension basis} :
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
