import Mathlib.Tactic.Linarith.Datatypes


open Lean

namespace Linarith


/-! ### Control -/


def Preprocessor.transformAugmented (pp : Preprocessor) (p : Term × Expr) : MetaM (List (Term × Expr)) := do
  let l ← pp.transform p.2
  let l' := l.map (Prod.mk p.1)
  pure l'

def Preprocessor.globalTransform (pp : Preprocessor) :
    List Expr → MetaM (List Expr) :=
  fun input ↦ do
    let l ← input.mapM pp.transform
    pure l.flatten

def Preprocessor.globalTransformAugmented (pp : Preprocessor) :
    List (Term × Expr) → MetaM (List (Term × Expr)) :=
  fun input ↦ do
    let l ← input.mapM pp.transformAugmented
    pure l.flatten
