import Mathlib.Tactic.Tendsto.Multiseries.Basic

open Asymptotics Filter

namespace TendstoTactic

/-- Approximations of logarithm of all but last basis functions. -/
inductive LogBasis : Basis → Type
| nil : LogBasis []
| single (f : ℝ → ℝ) : LogBasis [f]
| cons (basis_hd basis_tl_hd : ℝ → ℝ) (basis_tl_tl : Basis)
    (logBasis_tl : LogBasis (basis_tl_hd :: basis_tl_tl)) (ms : PreMS (basis_tl_hd :: basis_tl_tl)) :
    LogBasis (basis_hd :: basis_tl_hd :: basis_tl_tl)

namespace LogBasis

def WellFormed {basis : Basis} (logBasis : LogBasis basis) : Prop :=
  match logBasis with
  | .nil => True
  | .single f => True
  | .cons basis_hd _ _ logBasis_tl ms =>
    ms.WellOrdered ∧
    ms.Approximates (Real.log ∘ basis_hd) ∧
    WellFormed logBasis_tl

theorem nil_WellFormed : WellFormed (.nil) := by simp [WellFormed]

theorem single_WellFormed (f : ℝ → ℝ) : WellFormed (.single f) := by simp [WellFormed]

def tail {basis_hd : ℝ → ℝ} {basis_tl : Basis} (logBasis : LogBasis (basis_hd :: basis_tl)) :
    LogBasis basis_tl :=
  match logBasis with
  | .single f => .nil
  | .cons _ _ _ logBasis_tl _ => logBasis_tl

theorem tail_WellFormed {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {logBasis : LogBasis (basis_hd :: basis_tl)} (h_wf : logBasis.WellFormed) :
    (logBasis.tail).WellFormed := by
  cases logBasis with
  | single => simp [WellFormed]
  | cons _ _ _ logBasis_tl ms =>
    simp [WellFormed] at h_wf
    simp [tail]
    exact h_wf.right.right

noncomputable def extendBasisMiddle {right_hd : ℝ → ℝ} {left right_tl : Basis} (f : ℝ → ℝ)
    (logBasis : LogBasis (left ++ right_hd :: right_tl)) (ms : PreMS (right_hd :: right_tl)) :
    LogBasis (left ++ f :: right_hd :: right_tl) :=
  match left with
  | [] => .cons _ _ _ logBasis ms
  | List.cons left_hd left_tl =>
    match left_tl with
    | [] =>
      match logBasis with
      | .cons _ _ _ logBasis_tl ms'  =>
        .cons _ _ _ (extendBasisMiddle (left := []) f logBasis_tl ms)
          (ms'.extendBasisMiddle (left := []) f)
    | List.cons left_tl_hd left_tl_tl =>
      match logBasis with
      | .cons _ _ _ logBasis_tl ms' =>
        .cons _ _ _
          (extendBasisMiddle (left := left_tl_hd :: left_tl_tl) f logBasis_tl ms)
          (ms'.extendBasisMiddle (left := left_tl_hd :: left_tl_tl) f)

noncomputable def extendBasisEnd {basis_hd : ℝ → ℝ} {basis_tl : Basis} (f : ℝ → ℝ)
    (logBasis : LogBasis (basis_hd :: basis_tl)) (ms : PreMS [f]) :
    LogBasis (basis_hd :: basis_tl ++ [f]) :=
  match logBasis with
  | .single _ => .cons _ _ _ (.single _) ms
  | .cons _ basis_tl_hd basis_tl_tl logBasis_tl ms' =>
    .cons _ _ _ (extendBasisEnd f logBasis_tl ms)
      (ms'.extendBasisEnd _)

noncomputable def insertLastLog {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (logBasis : LogBasis (basis_hd :: basis_tl)) :
    LogBasis ((basis_hd :: basis_tl) ++ [Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)]) :=
  logBasis.extendBasisEnd (Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)) (PreMS.monomial _ 0)

theorem extendBasisMiddle_WellFormed {right_hd : ℝ → ℝ} {left right_tl : Basis} {f : ℝ → ℝ}
    {logBasis : LogBasis (left ++ right_hd :: right_tl)} {ms : PreMS (right_hd :: right_tl)}
    (h_basis : WellFormedBasis (left ++ f ::right_hd :: right_tl))
    (h_wf : logBasis.WellFormed)
    (h_wo : ms.WellOrdered) (h_approx : ms.Approximates (Real.log ∘ f)) :
    (logBasis.extendBasisMiddle f ms).WellFormed := by
  cases' left with left_hd left_tl
  · cases logBasis with
    | single => simp [WellFormed, h_wo, h_approx]
    | cons _ right_tl_hd right_tl_tl logBasis_tl ms' =>
      simp [WellFormed] at h_wf
      simp [extendBasisMiddle, WellFormed, h_wo, h_approx, h_wf]
  cases' left_tl with left_tl_hd left_tl_tl
  · cases logBasis with | cons _ _ _ logBasis_tl ms' =>
    simp [WellFormed] at h_wf
    simp [extendBasisMiddle, WellFormed, h_wo, h_approx, h_wf.right]
    constructor
    · exact PreMS.extendBasisMiddle_WellOrdered h_wf.left
    · apply PreMS.extendBasisMiddle_Approximates h_basis.tail h_wf.right.left
  cases logBasis with | cons _ _ _ logBasis_tl ms' =>
  simp [WellFormed] at h_wf
  simp [extendBasisMiddle, WellFormed]
  constructor
  · exact PreMS.extendBasisMiddle_WellOrdered h_wf.left
  constructor
  · exact PreMS.extendBasisMiddle_Approximates h_basis.tail h_wf.right.left
  · exact extendBasisMiddle_WellFormed h_basis.tail h_wf.right.right h_wo h_approx

theorem extendBasisEnd_WellFormed {basis_hd : ℝ → ℝ} {basis_tl : Basis} {f : ℝ → ℝ}
    {logBasis : LogBasis (basis_hd :: basis_tl)} {ms : PreMS [f]}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl ++ [f]))
    (h_wf : logBasis.WellFormed)
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates (Real.log ∘ (basis_hd :: basis_tl).getLast
      (basis_tl.cons_ne_nil basis_hd))) :
    (logBasis.extendBasisEnd f ms).WellFormed := by
  cases logBasis with
  | single => simpa [WellFormed, h_wo] using h_approx
  | cons _ basis_tl_hd basis_tl_tl logBasis_tl ms' =>
    simp [WellFormed] at h_wf
    simp [extendBasisEnd, WellFormed, h_wo, h_approx, h_wf]
    constructor
    · exact PreMS.extendBasisEnd_WellOrdered h_wf.left
    constructor
    · exact PreMS.extendBasisEnd_Approximates h_basis.tail h_wf.right.left
    · exact extendBasisEnd_WellFormed h_basis.tail h_wf.right.right h_wo h_approx

end LogBasis

theorem insertLastLog_WellOrdered {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl)) :
    WellFormedBasis ((basis_hd :: basis_tl) ++ [Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)]) := by
  simp only [WellFormedBasis]
  constructor
  · rw [List.pairwise_append]
    constructor
    · exact h_basis.left
    constructor
    · simp
    intro f hf g hg
    simp at hg
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
      simp at hf
      simp [hf]
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
            simp [WellFormedBasis] at h_basis
            tauto
      · exact ih f hf
  · intro f hf
    rw [List.mem_append] at hf
    rcases hf with hf | hf
    · exact h_basis.right _ hf
    simp at hf
    subst hf
    apply Filter.Tendsto.comp Real.tendsto_log_atTop
    apply h_basis.right
    simp

theorem LogBasis.insertLastLog_WellFormed {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {logBasis : LogBasis (basis_hd :: basis_tl)}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl))
    (h_wf : logBasis.WellFormed) :
    (logBasis.insertLastLog).WellFormed := by
  simp [insertLastLog]
  apply extendBasisEnd_WellFormed
  · exact insertLastLog_WellOrdered h_basis
  · exact h_wf
  · exact PreMS.monomial_WellOrdered
  · have : WellFormedBasis [Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)] := by
      apply WellFormedBasis.single
      apply Filter.Tendsto.comp Real.tendsto_log_atTop
      apply h_basis.right
      simp
    exact PreMS.monomial_Approximates this (n := ⟨0, by simp⟩)

end TendstoTactic
