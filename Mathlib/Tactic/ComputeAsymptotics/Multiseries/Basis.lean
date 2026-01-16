/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Defs
public import Mathlib.Analysis.Complex.Exponential

/-!
# Lemmas about well ordered basises

## Main definitions

* `WellFormedBasis basis` is a predicate meaning that all function from `basis` tend to `atTop`,
and `basis` is sorted such that if
function `g` goes after `f` in `basis`, then `log f =o[atTop] log g`.

-/

@[expose] public section

open Asymptotics Filter

namespace ComputeAsymptotics

/-- `WellFormedBasis basis` means that all function from `basis` tend to `atTop`, and
`basis` is sorted such that if
function `g` goes after `f` in `basis`, then `log f =o[atTop] log g`. -/
def WellFormedBasis (basis : Basis) : Prop :=
  basis.Pairwise (fun x y => (Real.log ∘ y) =o[atTop] (Real.log ∘ x)) ∧
  ∀ f ∈ basis, Tendsto f atTop atTop

theorem WellFormedBasis.nil : WellFormedBasis [] := by simp [WellFormedBasis]

theorem WellFormedBasis.single (f : ℝ → ℝ) (hf : Tendsto f atTop atTop) : WellFormedBasis [f] := by
  simpa [WellFormedBasis]

theorem WellFormedBasis.of_sublist {basis basis' : Basis} (h : List.Sublist basis basis')
    (h_basis : WellFormedBasis basis') : WellFormedBasis basis := by
  simp only [WellFormedBasis] at h_basis ⊢
  constructor
  · exact h_basis.left.sublist h
  · intro f hf
    exact h_basis.right _ (h.subset hf)

/-- Tail of well-formed basis is well-ordered. -/
theorem WellFormedBasis.tail {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h : WellFormedBasis (basis_hd :: basis_tl)) : WellFormedBasis basis_tl :=
  WellFormedBasis.of_sublist (by simp) h

theorem WellFormedBasis.of_append_right {left right : Basis} (h : WellFormedBasis (left ++ right)) :
    WellFormedBasis right :=
  WellFormedBasis.of_sublist (by simp) h

theorem WellFormedBasis.insert {left right : Basis} {f : ℝ → ℝ}
    (h : WellFormedBasis (left ++ right))
    (hf_tendsto : Tendsto f atTop atTop)
    (hf_comp_left : ∀ g, left.getLast? = .some g → (Real.log ∘ f) =o[atTop] (Real.log ∘ g))
    (hf_comp_right : ∀ g, right.head? = .some g → (Real.log ∘ g) =o[atTop] (Real.log ∘ f)) :
    WellFormedBasis (left ++ f :: right) := by
  simp only [WellFormedBasis, List.mem_append, List.mem_cons] at h ⊢
  constructor
  · rw [List.pairwise_append]
    constructorm* _ ∧ _
    · exact h.left.sublist (List.sublist_append_left _ _)
    · rw [List.pairwise_cons]
      constructor
      · intro g hg
        cases right with
        | nil => simp at hg
        | cons right_hd right_tl =>
          specialize hf_comp_right right_hd (by simp)
          simp only [List.mem_cons] at hg
          rcases hg with hg | hg
          · rwa [hg]
          apply IsLittleO.trans _ hf_comp_right
          apply And.left at h
          rw [List.pairwise_append] at h
          replace h := h.right.left
          simp only [List.pairwise_cons] at h
          apply h.left _ hg
      · apply h.left.sublist (List.sublist_append_right _ _)
    · intro g hg k hk
      simp only [List.mem_cons] at hk
      rcases hk with hk | hk
      · subst hk
        rcases left.eq_nil_or_concat with h_left | ⟨left_begin, left_end, rfl⟩
        · simp [h_left] at hg
        simp only [List.concat_eq_append, List.getLast?_append,
          List.getLast?_singleton] at hf_comp_left
        simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · apply (hf_comp_left _ rfl).trans
          apply And.left at h
          rw [List.pairwise_append] at h
          apply And.left at h
          simp only [List.concat_eq_append, List.pairwise_append, List.pairwise_cons,
            List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self,
            List.mem_singleton, forall_eq, true_and] at h
          tauto
        · exact hf_comp_left g rfl
      · apply And.left at h
        simp only [List.pairwise_append] at h
        tauto
  · rintro g (hg | hg | hg)
    · exact h.right _ (.inl hg)
    · convert hf_tendsto
    · exact h.right _ (.inr hg)

theorem WellFormedBasis.push {basis : Basis} {f : ℝ → ℝ}
    (h : WellFormedBasis basis)
    (hf_tendsto : Tendsto f atTop atTop)
    (hf_comp : ∀ g, basis.getLast? = .some g → (Real.log ∘ f) =o[atTop] (Real.log ∘ g)) :
    WellFormedBasis (basis ++ [f]) :=
  WellFormedBasis.insert (right := []) (by simp [h]) hf_tendsto hf_comp (by simp)

/-- All functions from well-formed basis tends to `atTop`. -/
theorem basis_tendsto_top {basis : Basis} (h : WellFormedBasis basis) :
    ∀ f ∈ basis, Tendsto f atTop atTop := by
  simp only [WellFormedBasis] at h
  exact h.right

/-- Eventually all functions from well-formed basis are positive. -/
theorem basis_eventually_pos {basis : Basis} (h : WellFormedBasis basis) :
    ∀ᶠ x in atTop, ∀ f ∈ basis, 0 < f x := by
  induction basis with
  | nil => simp
  | cons hd tl ih =>
    simp only [WellFormedBasis, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h
    simp only [List.mem_cons, forall_eq_or_imp]
    apply Filter.Eventually.and
    · exact Tendsto.eventually h.right.left <| eventually_gt_atTop 0
    · apply ih
      simp only [WellFormedBasis]
      tauto

/-- First function from well-formed basis is eventually positive. -/
theorem basis_head_eventually_pos {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h : WellFormedBasis (basis_hd :: basis_tl)) : ∀ᶠ x in atTop, 0 < basis_hd x := by
  apply ((forall_eventually_of_eventually_forall (basis_eventually_pos h)) basis_hd).mono
  intro x h
  apply h
  simp

/-- All functions of well-formed basis' tail are o-little of basis' head. -/
theorem basis_IsLittleO_of_head {hd : ℝ → ℝ} {tl : Basis} (h : WellFormedBasis (hd :: tl)) :
    ∀ f ∈ tl, (Real.log ∘ f) =o[atTop] (Real.log ∘ hd) := by
  simp only [WellFormedBasis, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h
  exact h.left.left

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

/-- Any power of function from well-formed basis' tail is majorated by
basis' head with zero exponent. -/
theorem basis_tail_pow_majorated_head {hd f : ℝ → ℝ} {tl : Basis}
    (h_basis : WellFormedBasis (hd :: tl)) (hf : f ∈ tl) (r : ℝ) :
    PreMS.majorated (fun x ↦ (f x)^r) hd 0 := by
  simp only [PreMS.majorated]
  intro exp h_exp
  apply basis_compare
  · apply (basis_eventually_pos h_basis.tail).mono
    intro x h
    apply h
    exact hf
  · apply basis_tendsto_top h_basis
    simp
  · simp only [WellFormedBasis, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h_basis
    tauto
  · exact h_exp

/-- Any function from well-formed basis' tail is majorated by basis' head with zero exponent. -/
theorem basis_tail_majorated_head {hd f : ℝ → ℝ} {tl : Basis}
    (h_basis : WellFormedBasis (hd :: tl)) (hf : f ∈ tl) :
    PreMS.majorated f hd 0 := by
  convert basis_tail_pow_majorated_head h_basis hf 1 using 1
  ext t
  simp

/-- If `basis_hd :: basis_tl` is well-formed and function `fC` can be approximated by
`ms : PreMS basis_tl`, then `fC` can be majorated by `basis_hd` with zero exponent. -/
theorem PreMS.Approximates_coef_majorated_head {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS basis_tl} (h_approx : ms.Approximates)
    (h_basis : WellFormedBasis (basis_hd :: basis_tl)) :
    majorated ms.toFun basis_hd 0 := by
  cases basis_tl with
  | nil =>
    simp
    apply const_majorated
    apply basis_tendsto_top h_basis
    simp
  | cons basis_tl_hd basis_tl_tl =>
    cases ms with
    | nil f =>
      simp at h_approx ⊢
      apply majorated_of_EventuallyEq h_approx
      apply zero_majorated
    | cons exp coef tl f =>
      obtain ⟨_, h_maj, _⟩ := Approximates_cons h_approx
      simp
      intro exp' h_exp
      apply Asymptotics.IsLittleO.trans <| h_maj (exp + 1) (by linarith)
      apply basis_compare
      · apply basis_head_eventually_pos (h_basis.tail)
      · apply basis_tendsto_top h_basis
        simp only [List.mem_cons, true_or]
      · simp only [WellFormedBasis, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h_basis
        exact h_basis.left.left.left
      · exact h_exp

/-- Basis extension. It is a data-version of `List.Sublist`.
Using `getBasis` one can construct any `basis'` from `basis` if `basis <+ basis'`. -/
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

-- TODO: remove examples
example :
  let basis := [fun x ↦ x];
  let ex : BasisExtension basis := .keep _ .nil;
  ex.getBasis = [fun x ↦ x] := rfl

example :
  let basis := [fun x ↦ x];
  let ex : BasisExtension basis := .keep _ (.insert Real.log .nil);
  ex.getBasis = [fun x ↦ x, Real.log] := rfl

example :
  let basis := [fun x ↦ x, fun x ↦ 3 * x];
  let ex : BasisExtension basis := .keep _ (.insert Real.log (.keep _ .nil));
  ex.getBasis = [fun x ↦ x, Real.log, fun x ↦ 3 * x] := by
    rfl

theorem getBasis_Sublist {basis : Basis} {ex : BasisExtension basis} :
    List.Sublist basis ex.getBasis := by
  induction ex with
  | nil => simp
  | keep _ ex ih =>
    simp [getBasis]
    apply ih
  | insert _ ex ih =>
    simp [getBasis]
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

end ComputeAsymptotics
