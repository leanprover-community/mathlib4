import Mathlib.Data.ENat.Basic

namespace OmegaExtensions.ENat

attribute [enat_omega_top_simps] OfNat.ofNat_ne_zero ne_eq not_false_eq_true
attribute [enat_omega_top_simps] ENat.coe_ne_top ENat.top_ne_coe ENat.coe_lt_top top_le_iff le_top
attribute [enat_omega_top_simps] top_add ENat.sub_top ENat.top_sub_coe ENat.mul_top ENat.top_mul

@[enat_omega_top_simps] lemma not_lt_top (x : ENat) :
    ¬(⊤ < x) := by cases x <;> simp

@[enat_omega_coe_simps] lemma coe_add' (m n : ℕ) :
    (m : ENat) + (n : ENat) = ((m + n : ℕ) : ENat) := (ENat.coe_add m n).symm

@[enat_omega_coe_simps] lemma coe_sub' (m n : ℕ) :
    (m : ENat) - (n : ENat) = ((m - n : ℕ) : ENat) := (ENat.coe_sub m n).symm

@[enat_omega_coe_simps] lemma coe_mul' (m n : ℕ) :
    (m : ENat) * (n : ENat) = ((m * n : ℕ) : ENat) := (ENat.coe_mul m n).symm

@[enat_omega_coe_simps] lemma coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : ENat) = (OfNat.ofNat n : ℕ) := rfl

@[enat_omega_coe_simps] lemma coe_zero' : (0 : ENat) = ((0 : ℕ) : ENat) := rfl

@[enat_omega_coe_simps] lemma coe_one' : (1 : ENat) = ((1 : ℕ) : ENat) := rfl

attribute [enat_omega_coe_simps] ENat.coe_inj ENat.coe_le_coe ENat.coe_lt_coe

open Qq Lean Elab Tactic Term Meta in
def casesFirstENat : TacticM Unit := withMainContext do
  let ctx ← getLCtx
  let decl? ← ctx.findDeclM? fun decl => do
    if ← (isExprDefEq (← inferType decl.toExpr) q(ENat)) then
      return Option.some decl
    else
      return Option.none
  let .some decl := decl? | throwError "No ENats"
  let x := mkIdent decl.userName
  evalTactic (← `(tactic| cases' $x:ident with $x:ident <;>
    try simp only [enat_omega_top_simps] at *))

elab "cases_first_ENat" : tactic => casesFirstENat

macro "enat_omega" : tactic => `(tactic| focus (
    (repeat' cases_first_ENat) <;>
    (try simp only [enat_omega_top_simps, enat_omega_coe_simps] at *) <;>
    try omega
  )
)

end OmegaExtensions.ENat
