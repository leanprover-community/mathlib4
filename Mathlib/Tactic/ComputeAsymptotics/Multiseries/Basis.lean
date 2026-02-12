/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Defs
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

/-- Auxillary lemma. If function `f` is eventually positive, `g` tends to `atTop`, and
`log f =o[atTop] log g` then for any `a` and `b > 0`, then `f^a =o[atTop] g^b`. -/
theorem basis_compare {f g : ℝ → ℝ} (a b : ℝ) (hf : ∀ᶠ x in atTop, 0 < f x)
    (hg : Tendsto g atTop atTop) (h : (Real.log ∘ f) =o[atTop] (Real.log ∘ g)) (hb : 0 < b) :
    (fun x ↦ (f x)^a) =o[atTop] fun x ↦ (g x)^b := by
  obtain ⟨φ, h1, h2⟩ := IsLittleO.exists_eq_mul <| IsLittleO.const_mul_right' (c := b)
    (isUnit_iff_ne_zero.mpr hb.ne.symm) (IsLittleO.const_mul_left h a)
  have hf_exp_log : (fun x ↦ (f x)^a) =ᶠ[atTop] fun x ↦ Real.exp (a * (Real.log (f x))) := by
    simp only [EventuallyEq]
    apply hf.mono
    intro x hx
    rw [mul_comm, Real.exp_mul, Real.exp_log hx]
  have hg_exp_log : (fun x ↦ (g x)^b) =ᶠ[atTop] fun x ↦ Real.exp (b * (Real.log (g x))) := by
    simp only [EventuallyEq]
    apply (Tendsto.eventually_gt_atTop hg 0).mono
    intro x hx
    rw [mul_comm, Real.exp_mul, Real.exp_log hx]
  apply IsLittleO.trans_eventuallyEq _ hg_exp_log.symm
  apply EventuallyEq.trans_isLittleO hf_exp_log
  simp only [Function.comp_apply] at h2
  have h2 := EventuallyEq.fun_comp h2 Real.exp
  eta_expand at h2
  simp only [Function.comp_apply, Pi.mul_apply] at h2
  apply EventuallyEq.trans_isLittleO h2
  apply isLittleO_of_tendsto'
  · apply Eventually.of_forall
    intro x h
    absurd h
    apply (Real.exp_pos _).ne.symm
  · simp only [← Real.exp_sub, Real.tendsto_exp_comp_nhds_zero]
    conv =>
      arg 1
      ext x
      rw [show φ x * (b * Real.log (g x)) - b * Real.log (g x) =
        b * ((φ x - 1) * Real.log (g x)) by ring]
    apply Tendsto.const_mul_atBot hb
    apply Tendsto.neg_mul_atTop (C := -1) (by simp)
    · simp_rw [show (-1 : ℝ) = 0 - 1 by simp]
      apply Tendsto.sub_const h1
    · exact Tendsto.comp Real.tendsto_log_atTop hg

/-- Any power of function from well-formed basis' tail is Majorized by
basis' head with zero exponent. -/
theorem basis_tail_pow_Majorized_head {hd f : ℝ → ℝ} {tl : Basis}
    (h_basis : WellFormedBasis (hd :: tl)) (hf : f ∈ tl) (r : ℝ) :
    Majorized (fun x ↦ (f x)^r) hd 0 := by
  simp only [Majorized]
  intro exp h_exp
  apply basis_compare
  · apply h_basis.tail.eventually_pos.mono
    intro x h
    apply h
    exact hf
  · apply h_basis.tendsto_atTop
    simp
  · simp only [WellFormedBasis, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h_basis
    tauto
  · exact h_exp

/-- If `basis_hd :: basis_tl` is well-formed and function `fC` can be approximated by
`ms : MultiseriesExpansion basis_tl`, then `fC` can be Majorized by `basis_hd` with zero
exponent. -/
theorem MultiseriesExpansion.Approximates_coef_Majorized_head {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : MultiseriesExpansion basis_tl} (h_approx : ms.Approximates)
    (h_basis : WellFormedBasis (basis_hd :: basis_tl)) :
    Majorized ms.toFun basis_hd 0 := by
  cases basis_tl with
  | nil =>
    simp only [const_toFun]
    apply Majorized.const
    apply h_basis.tendsto_atTop
    simp
  | cons basis_tl_hd basis_tl_tl =>
    cases ms with
    | nil f =>
      simp only [Approximates_nil_iff, mk_toFun] at h_approx ⊢
      apply Majorized.of_eventuallyEq h_approx
      apply Majorized.zero
    | cons exp coef tl f =>
      obtain ⟨_, h_maj, _⟩ := Approximates_cons h_approx
      simp only [mk_toFun]
      intro exp' h_exp
      apply Asymptotics.IsLittleO.trans <| h_maj (exp + 1) (by linarith)
      apply basis_compare
      · apply h_basis.tail.head_eventually_pos
      · apply h_basis.tendsto_atTop
        simp only [List.mem_cons, true_or]
      · simp only [WellFormedBasis, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h_basis
        exact h_basis.left.left.left
      · exact h_exp

/-- Basis extension. Using `getBasis` one can construct any `basis'` from `basis`
if `basis <+ basis'`. -/
inductive BasisExtension : Basis → Type
| nil : BasisExtension []
| keep (basis_hd : ℝ → ℝ) {basis_tl : Basis} (ex : BasisExtension basis_tl) :
  BasisExtension (basis_hd :: basis_tl)
| insert {basis : Basis} (f : ℝ → ℝ) (ex : BasisExtension basis) : BasisExtension basis

namespace BasisExtension

/-- Basis after applying a basis extension. -/
def getBasis {basis : Basis} (ex : BasisExtension basis) : Basis :=
  match ex with
  | nil => []
  | keep basis_hd ex => basis_hd :: ex.getBasis
  | insert f ex => f :: ex.getBasis

theorem getBasis_Sublist {basis : Basis} {ex : BasisExtension basis} :
    List.Sublist basis ex.getBasis := by
  induction ex with
  | nil => simp
  | keep _ ex ih =>
    simp only [getBasis, List.cons_sublist_cons]
    apply ih
  | insert _ ex ih =>
    simp only [getBasis]
    apply List.Sublist.cons
    apply ih

theorem insert_WellFormedBasis_tail {basis : Basis} {f : ℝ → ℝ}
    {ex_tl : BasisExtension basis}
    (h_basis : WellFormedBasis <| BasisExtension.getBasis (.insert f ex_tl)) :
    WellFormedBasis ex_tl.getBasis := by
  apply WellFormedBasis.of_sublist _ h_basis
  simp [getBasis]

end BasisExtension

-- TODO: refactor this using `WellFormedBasis.push`, and use the current proof to prove it
theorem insertLastLog_WellFormedBasis {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl)) :
    WellFormedBasis ((basis_hd :: basis_tl) ++
      [Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)]) := by
  simp only [WellFormedBasis]
  constructor
  · rw [List.pairwise_append]
    constructor
    · exact h_basis.left
    constructor
    · simp
    intro f hf g hg
    simp only [List.mem_singleton] at hg
    subst hg
    suffices (Real.log ∘ (basis_hd :: basis_tl).getLast (List.cons_ne_nil _ _))
        =O[atTop] (Real.log ∘ f) by
      apply Asymptotics.IsLittleO.trans_isBigO _ this
      apply And.right at h_basis
      specialize h_basis ((basis_hd :: basis_tl).getLast (List.cons_ne_nil _ _)) (by simp)
      set g := (basis_hd :: basis_tl).getLast (List.cons_ne_nil _ _)
      change (Real.log ∘ Real.log ∘ g) =o[atTop] (id ∘ Real.log ∘ g)
      apply Asymptotics.IsLittleO.comp_tendsto Real.isLittleO_log_id_atTop
      exact Filter.Tendsto.comp Real.tendsto_log_atTop h_basis
    induction basis_tl generalizing basis_hd f with
    | nil =>
      simp only [List.mem_singleton] at hf
      simp only [List.getLast_singleton, hf]
      apply isBigO_refl
    | cons basis_tl_hd basis_tl_tl ih =>
      specialize ih h_basis.tail
      rw [List.mem_cons] at hf
      rcases hf with hf | hf
      · subst hf
        specialize ih basis_tl_hd (by simp)
        calc
          _ =O[atTop] (Real.log ∘ basis_tl_hd) := ih
          _ =O[atTop] (Real.log ∘ f) := by
            apply IsLittleO.isBigO
            simp only [WellFormedBasis, List.pairwise_cons, List.mem_cons,
              forall_eq_or_imp] at h_basis
            tauto
      · exact ih f hf
  · intro f hf
    rw [List.mem_append] at hf
    rcases hf with hf | hf
    · exact h_basis.right _ hf
    simp only [List.mem_singleton] at hf
    subst hf
    apply Filter.Tendsto.comp Real.tendsto_log_atTop
    apply h_basis.right
    simp

end Tactic.ComputeAsymptotics
