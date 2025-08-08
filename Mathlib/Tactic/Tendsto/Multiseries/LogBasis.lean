import Mathlib.Tactic.Tendsto.Multiseries.Basic

open Asymptotics Filter

namespace TendstoTactic

/-- Approximations of logarithm of all but last basis functions. -/
inductive LogBasis : Basis → Type
| nil : LogBasis []
| single (f : ℝ → ℝ) : LogBasis [f]
| cons (basis_hd basis_tl_hd : ℝ → ℝ) (basis_tl_tl : Basis)
    (logBasis_tl : LogBasis (basis_tl_hd :: basis_tl_tl)) (ms : PreMS (basis_tl_hd :: basis_tl_tl))
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates (Real.log ∘ basis_hd)) :
    LogBasis (basis_hd :: basis_tl_hd :: basis_tl_tl)

namespace LogBasis

def tail {basis_hd : ℝ → ℝ} {basis_tl : Basis} (logBasis : LogBasis (basis_hd :: basis_tl)) :
    LogBasis basis_tl :=
  match logBasis with
  | .single f => .nil
  | .cons _ _ _ logBasis_tl _ _ _ => logBasis_tl

-- TODO: do we need it?
def tail' {basis : Basis} (logBasis : LogBasis basis) : LogBasis basis.tail :=
  match logBasis with
  | .nil => .nil
  | .single f => .nil
  | .cons _ _ _ logBasis_tl _ _ _ => logBasis_tl

noncomputable def extendBasisMiddle {right_hd : ℝ → ℝ} {left right_tl : Basis} (f : ℝ → ℝ)
    (logBasis : LogBasis (left ++ right_hd :: right_tl)) (ms : PreMS (right_hd :: right_tl))
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates (Real.log ∘ f)) :
    LogBasis (left ++ f :: right_hd :: right_tl) :=
  match left with
  | [] => .cons _ _ _ logBasis ms h_wo h_approx
  | List.cons left_hd left_tl =>
    match left_tl with
    | [] =>
      match logBasis with
      | .cons _ _ _ logBasis_tl ms' h_wo' h_approx' =>
        .cons _ _ _ (extendBasisMiddle (left := []) f logBasis_tl ms h_wo h_approx)
          (ms'.extendBasisMiddle (left := []) f)
          (PreMS.extendBasisMiddle_WellOrdered h_wo')
          (PreMS.extendBasisMiddle_Approximates h_approx')
    | List.cons left_tl_hd left_tl_tl =>
      match logBasis with
      | .cons _ _ _ logBasis_tl ms' h_wo' h_approx' =>
        .cons _ _ _
          (extendBasisMiddle (left := left_tl_hd :: left_tl_tl) f logBasis_tl ms h_wo h_approx)
          (ms'.extendBasisMiddle (left := left_tl_hd :: left_tl_tl) f)
          (PreMS.extendBasisMiddle_WellOrdered h_wo')
          (PreMS.extendBasisMiddle_Approximates h_approx')

noncomputable def extendBasisEnd {basis_hd : ℝ → ℝ} {basis_tl : Basis} (f : ℝ → ℝ)
    (logBasis : LogBasis (basis_hd :: basis_tl)) (ms : PreMS [f])
    (h_wo : ms.WellOrdered)
    (h_approx : ms.Approximates (Real.log ∘ (basis_hd :: basis_tl).getLast
      (basis_tl.cons_ne_nil basis_hd))) :
    LogBasis (basis_hd :: basis_tl ++ [f]) :=
  match logBasis with
  | .single _ => .cons _ _ _ (.single _) _ h_wo h_approx
  | .cons _ basis_tl_hd basis_tl_tl logBasis_tl ms' h_wo' h_approx' =>
    .cons _ _ _ (extendBasisEnd f logBasis_tl ms h_wo h_approx)
      (ms'.extendBasisEnd _)
      (PreMS.extendBasisEnd_WellOrdered h_wo')
      (PreMS.extendBasisEnd_Approximates h_approx')

noncomputable def insertLastLog {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl))
    (logBasis : LogBasis (basis_hd :: basis_tl)) :
    LogBasis ((basis_hd :: basis_tl) ++ [Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)]) :=
  match logBasis with
  | .single f => .cons f (Real.log ∘ f) [] (.single _) (PreMS.monomial _ 0)
      (by sorry)
      (by
        rw [show 0 = @Fin.val [Real.log ∘ f].length ⟨0, by simp⟩ by rfl]
        apply PreMS.monomial_Approximates
        simp [WellFormedBasis] at h_basis ⊢
        sorry -- library
      )
  | .cons basis_hd basis_tl_hd basis_tl_tl logBasis_tl ms h_wo h_approx =>
    .cons _ _ _ (insertLastLog h_basis.tail logBasis_tl) (ms.extendBasisEnd _)
      (PreMS.extendBasisEnd_WellOrdered h_wo)
      (PreMS.extendBasisEnd_Approximates h_approx)

end LogBasis

theorem insertLastLog_WellOrdered {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl)) :
    WellFormedBasis ((basis_hd :: basis_tl) ++ [Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)]) := by
  sorry

end TendstoTactic
