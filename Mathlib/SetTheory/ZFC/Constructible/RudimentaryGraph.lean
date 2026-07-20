/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Rudimentary
public import Mathlib.SetTheory.ZFC.Constructible.Delta0GodelGraph

/-!
# First-order graph formulas for rudimentary terms

Every rudimentary term with finitely many variables has an exact graph formula
in the ambient `ZFSet` universe.  Terms over an arbitrary variable type are
first reified using one finite parameter slot for each variable occurrence.

The application case below deliberately uses two unrestricted existential
quantifiers.  Thus the resulting formula is an ambient first-order graph; it
does not assert that all intermediate term values belong to a prescribed
transitive set.
-/

@[expose] public section

universe u v

namespace Constructible.Godel

open Constructible.Delta0Formula

namespace RudimentaryTerm

/-- Embed the graph of the left subterm into the two-witness application context. -/
def leftGraphRename (n : Nat) : Fin (n + 1) → Fin (n + 3) :=
  Fin.lastCases (Fin.last (n + 1)).castSucc
    (fun i => i.castSucc.castSucc.castSucc)

/-- Embed the graph of the right subterm into the two-witness application context. -/
def rightGraphRename (n : Nat) : Fin (n + 1) → Fin (n + 3) :=
  Fin.lastCases (Fin.last (n + 2))
    (fun i => i.castSucc.castSucc.castSucc)

/-- Select `[outer output, left value, right value]` in an application context. -/
def opGraphRename (n : Nat) : Fin 3 → Fin (n + 3) :=
  ![(Fin.last n).castSucc.castSucc,
    (Fin.last (n + 1)).castSucc,
    Fin.last (n + 2)]

theorem appTuple_comp_leftGraphRename {A : Type u} {n : Nat}
    (params : Tuple A n) (out left right : A) :
    (fun i => snoc (snoc (snoc params out) left) right
      (leftGraphRename n i)) = snoc params left := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [leftGraphRename]
  · simp [leftGraphRename]

theorem appTuple_comp_rightGraphRename {A : Type u} {n : Nat}
    (params : Tuple A n) (out left right : A) :
    (fun i => snoc (snoc (snoc params out) left) right
      (rightGraphRename n i)) = snoc params right := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [rightGraphRename]
  · simp [rightGraphRename]

theorem appTuple_comp_opGraphRename {A : Type u} {n : Nat}
    (params : Tuple A n) (out left right : A) :
    (fun i => snoc (snoc (snoc params out) left) right
      (opGraphRename n i)) = ![out, left, right] := by
  funext i
  fin_cases i <;> simp [opGraphRename]

/--
Compile a rudimentary term to its first-order graph.  The first `n`
coordinates are the term parameters and the last coordinate is the output.
-/
def graphFormula {n : Nat} : RudimentaryTerm (Fin n) → FOFormula (n + 1)
  | .var i => .eq (Fin.last n) i.castSucc
  | .app op left right =>
      .ex (.ex
        (.conj
          (FOFormula.rename (leftGraphRename n) (graphFormula left))
          (.conj
            (FOFormula.rename (rightGraphRename n) (graphFormula right))
            (FOFormula.rename (opGraphRename n) (opGraphFormula op).toFO))))

/-- Correctness of the compiled graph in the ambient universe of ZFC sets. -/
theorem satisfies_graphFormula {n : Nat}
    (t : RudimentaryTerm (Fin n))
    (params : Tuple ZFSet.{u} n) (out : ZFSet.{u}) :
    FOFormula.Satisfies ZFMem (graphFormula t) (snoc params out) ↔
      out = eval params t := by
  induction t generalizing params out with
  | var i =>
      simp [graphFormula, eval]
  | app op left right ihLeft ihRight =>
      simp only [graphFormula, FOFormula.Satisfies,
        FOFormula.satisfies_rename]
      constructor
      · rintro ⟨leftValue, rightValue, hleft, hright, hop⟩
        rw [appTuple_comp_leftGraphRename] at hleft
        rw [appTuple_comp_rightGraphRename] at hright
        rw [appTuple_comp_opGraphRename] at hop
        have hleftEq := (ihLeft params leftValue).mp hleft
        have hrightEq := (ihRight params rightValue).mp hright
        have hopEq := (satisfies_toFO_opGraphFormula
          op out leftValue rightValue).mp hop
        simpa only [eval, hleftEq, hrightEq] using hopEq
      · intro hout
        let leftValue := eval params left
        let rightValue := eval params right
        refine ⟨leftValue, rightValue, ?_, ?_, ?_⟩
        · rw [appTuple_comp_leftGraphRename]
          exact (ihLeft params leftValue).mpr rfl
        · rw [appTuple_comp_rightGraphRename]
          exact (ihRight params rightValue).mpr rfl
        · rw [appTuple_comp_opGraphRename]
          apply (satisfies_toFO_opGraphFormula
            op out leftValue rightValue).mpr
          simpa only [eval, leftValue, rightValue] using hout

/--
A finite reification of a rudimentary term.  The tuple contains one parameter
for each variable occurrence, so no decidable equality on the variable type
is required.
-/
def finiteReification {α : Type u} :
    RudimentaryTerm α →
      Σ n : Nat, Tuple α n × RudimentaryTerm (Fin n)
  | .var a =>
      ⟨1, (fun _ => a), .var 0⟩
  | .app i left right =>
      match finiteReification left, finiteReification right with
      | ⟨nl, leftParams, leftTerm⟩, ⟨nr, rightParams, rightTerm⟩ =>
          ⟨nl + nr,
            Fin.addCases leftParams rightParams,
            .app i
              (leftTerm.rename (Fin.castAdd nr))
              (rightTerm.rename (Fin.natAdd nl))⟩

/-- Reification preserves the value of a term under every assignment. -/
@[simp]
theorem eval_finiteReification {α : Type u} (t : RudimentaryTerm α)
    (ρ : α → ZFSet.{v}) :
    let result := finiteReification t
    eval (ρ ∘ result.2.1) result.2.2 = eval ρ t := by
  induction t with
  | var a => rfl
  | app i left right ihLeft ihRight =>
      simp only [finiteReification, eval, eval_rename]
      rw [← ihLeft, ← ihRight]
      congr 2
      · funext j
        simp [Function.comp_def]
      · funext j
        simp [Function.comp_def]

/-- Every term admits a finite-variable presentation with identical evaluation. -/
theorem exists_finiteReification {α : Type u} (t : RudimentaryTerm α) :
    ∃ n : Nat, ∃ params : Tuple α n,
      ∃ body : RudimentaryTerm (Fin n),
        ∀ ρ : α → ZFSet.{v}, eval (ρ ∘ params) body = eval ρ t := by
  let result := finiteReification t
  refine ⟨result.1, result.2.1, result.2.2, ?_⟩
  intro ρ
  exact eval_finiteReification t ρ

/--
Every rudimentary term over an arbitrary variable type has a finite first-order
graph presentation in the ambient universe.  The syntax of `formula` is fixed
by `t`; an assignment only interprets its finite tuple of parameters.
-/
theorem exists_finite_graphFormula {α : Type u} (t : RudimentaryTerm α) :
    ∃ n : Nat, ∃ params : Tuple α n,
      ∃ body : RudimentaryTerm (Fin n), ∃ formula : FOFormula (n + 1),
        formula = graphFormula body ∧
        (∀ ρ : α → ZFSet.{v},
          eval (ρ ∘ params) body = eval ρ t) ∧
        ∀ (ρ : α → ZFSet.{v}) (out : ZFSet.{v}),
          FOFormula.Satisfies ZFMem formula (snoc (ρ ∘ params) out) ↔
            out = eval ρ t := by
  rcases exists_finiteReification t with
    ⟨n, params, body, hbody⟩
  refine ⟨n, params, body, graphFormula body, rfl, hbody, ?_⟩
  intro ρ out
  rw [satisfies_graphFormula, hbody ρ]

end RudimentaryTerm

end Constructible.Godel
