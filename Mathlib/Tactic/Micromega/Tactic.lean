import Mathlib.Tactic.Micromega.Basic
import Lean.Expr
open Lean (Expr Name ToFormat)

namespace Micromega

-- coq: atom = AtomExpr
-- coq: EConstr.constr = Expr
-- coq: Names.Id.t = Name

-- coq: tag
def Tag := UInt32 deriving ToFormat

-- coq: formula
def Formula (α) := GFormula (AtomExpr α) Expr (Tag × Expr) Name

instance : ToFormat Kind where format
  | Kind.prop => "Prop"
  | Kind.bool => "Bool"

-- coq: pp_formula
partial def Formula.format : Formula α → Lean.Format :=
  have: ToFormat (GFormula _ _ _ _) := ⟨@format α⟩
  fun a : Formula α => match a with
  | GFormula.true Kind.prop => "True"
  | GFormula.true Kind.bool => "true"
  | GFormula.false Kind.prop => "False"
  | GFormula.false Kind.bool => "false"
  | GFormula.X k _ => f!"X {k}"
  | GFormula.A _ _ (t, _) => f!"A({t})"
  | GFormula.and _ f₁ f₂ => f!"AND({f₁}, {f₂})"
  | GFormula.or _ f₁ f₂ => f!"OR({f₁}, {f₂})"
  | GFormula.imp _ f₁ n f₂ => f!"IMP({f₁}, {n}, {f₂})"
  | GFormula.not _ f => f!"NOT({f})"
  | GFormula.iff _ f₁ f₂ => f!"IFF({f₁}, {f₂})"
  | GFormula.eq f₁ f₂ => f!"EQ({f₁}, {f₂})"
instance : ToFormat (Formula α) := ⟨Formula.format⟩

structure DomainSpec (stx pf : Type) where
  typ : Expr
  coeff : Expr
  dumpCoeff : stx → Expr
  proofTyp : Expr
  dumpProof : pf → Expr

-- structure Prover (opt α pf model : Type) where
--   name : String
--   getOption : opt
--   prover : opt → Array α →
