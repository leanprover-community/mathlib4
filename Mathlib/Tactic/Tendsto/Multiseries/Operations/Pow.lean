/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.Tendsto.Multiseries.Operations.Inv
import Mathlib.Tactic.Tendsto.Multiseries.Trimming
import Mathlib.Tactic.Tendsto.Multiseries.LeadingTerm

/-!
# Powers for multiseries

-/

open Filter Asymptotics

namespace TendstoTactic

namespace PreMS

open LazySeries Stream' Seq

def powSeries (x : ℝ) : LazySeries := sorry

noncomputable def pow {basis : Basis} (ms : PreMS basis) (x : ℝ) : PreMS basis :=
  match basis with
  | [] => ms^x
  | List.cons _ _ =>
    match destruct ms with
    | none => .nil
    | some ((exp, coef), tl) => mulMonomial
      ((powSeries x).apply (mulMonomial tl coef.inv' (-exp))) (coef.pow x) (exp * x)
