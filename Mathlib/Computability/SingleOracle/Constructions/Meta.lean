/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
module

public import Mathlib.Computability.SingleOracle.Constructions.Basic
public import Mathlib.Computability.SingleOracle.Constructions.Dovetail
public import Mathlib.Computability.SingleOracle.Constructions.EvalAux
public import Mathlib.Computability.SingleOracle.Constructions.Primitive

/-!
# Meta.lean

This file constructs "meta-codes" (codes which implement functions from codes to codes) of various
functions.

We first define such codes for constructors of `Code`;
`cZero`, where `evalp O cZero = c2n zero`, `cSucc`, and so on.

Then, the meta-code for any subsequent code `c` can be
implemented by replacing each of its components with its corresponding meta-code.

For example, suppose `c = comp succ left`.

Then the meta-code, named `c_c`, will be: `c_c = cComp.comp₂ cSucc cLeft`.

## Notation/quirks

 - The meta-code for a code has `c_` attached as a prefix.

-/

@[expose] public section

open Oracle.Single.Code

section constructors
namespace Oracle.Single.Code
/-- This code defines the function `fun _ ↦ c2n zero`. -/
def cZero := cConst (c2n zero)
@[cp] theorem cZero_prim : IsPrim cZero := by unfold cZero; apply_cp
@[simp, evp_simps] theorem cZero_evp {O x} : evalp O cZero x = c2n zero := by simp [cZero]
@[simp, evp_simps] theorem cZero_evp' {O : ℕ → ℕ} : evalp O cZero = fun _ : ℕ => c2n zero := by
  funext x; simp
@[simp, ev_simps] theorem cZero_ev {O x} : eval O cZero x = c2n zero := by
  rw [← evalp_eq_eval cZero_prim]; simp
@[simp] theorem PrimrecIn.cZero {O : ℕ → ℕ} : PrimrecIn O (fun _ : ℕ => c2n zero) := by
  rw [←cZero_evp']; exact isPrim_prop
/-- This code defines the function `fun _ ↦ c2n succ`. -/
def cSucc := cConst (c2n succ)
@[cp] theorem cSucc_prim : IsPrim cSucc := by unfold cSucc; apply_cp
@[simp, evp_simps] theorem cSucc_evp {O x} : evalp O cSucc x = c2n succ := by simp [cSucc]
@[simp, evp_simps] theorem cSucc_evp' {O : ℕ → ℕ} : evalp O cSucc = fun _ : ℕ => c2n succ := by
  funext x; simp
@[simp, ev_simps] theorem cSucc_ev {O x} : eval O cSucc x = c2n succ := by
  rw [← evalp_eq_eval cSucc_prim]; simp
@[simp] theorem PrimrecIn.cSucc {O : ℕ → ℕ} : PrimrecIn O (fun _ : ℕ => c2n succ) := by
  rw [←cSucc_evp']; exact isPrim_prop
/-- This code defines the function `fun _ ↦ c2n left`. -/
def cLeft := cConst (c2n left)
@[cp] theorem cLeft_prim : IsPrim cLeft := by unfold cLeft; apply_cp
@[simp, evp_simps] theorem cLeft_evp {O x} : evalp O cLeft x = c2n left := by simp [cLeft]
@[simp, evp_simps] theorem cLeft_evp' {O : ℕ → ℕ} : evalp O cLeft = fun _ : ℕ => c2n left := by
  funext x; simp
@[simp, ev_simps] theorem cLeft_ev {O x} : eval O cLeft x = c2n left := by
  rw [← evalp_eq_eval cLeft_prim]; simp
@[simp] theorem PrimrecIn.cLeft {O : ℕ → ℕ} : PrimrecIn O (fun _ : ℕ => c2n left) := by
  rw [←cLeft_evp']; exact isPrim_prop
/-- This code defines the function `fun _ ↦ c2n right`. -/
def cRight := cConst (c2n right)
@[cp] theorem cRight_prim : IsPrim cRight := by unfold cRight; apply_cp
@[simp, evp_simps] theorem cRight_evp {O x} : evalp O cRight x = c2n right := by simp [cRight]
@[simp, evp_simps] theorem cRight_evp' {O : ℕ → ℕ} : evalp O cRight = fun _ : ℕ => c2n right := by
  funext x; simp
@[simp, ev_simps] theorem cRight_ev {O x} : eval O cRight x = c2n right := by
  rw [← evalp_eq_eval cRight_prim]; simp
@[simp] theorem PrimrecIn.cRight {O : ℕ → ℕ} : PrimrecIn O (fun _ : ℕ => c2n right) := by
  rw [←cRight_evp']; exact isPrim_prop
/-- This code defines the function `fun _ ↦ c2n oracle`. -/
def cOracle := cConst (c2n oracle)
@[cp] theorem cOracle_prim : IsPrim cOracle := by unfold cOracle; apply_cp
@[simp, evp_simps] theorem cOracle_evp {O x} : evalp O cOracle x = c2n oracle := by
  simp [cOracle]
@[simp, evp_simps] theorem cOracle_evp' {O : ℕ → ℕ} :
    evalp O cOracle = fun _ : ℕ => c2n oracle := by
  funext x; simp
@[simp, ev_simps] theorem cOracle_ev {O x} : eval O cOracle x = c2n oracle := by
  rw [← evalp_eq_eval cOracle_prim]; simp
@[simp] theorem PrimrecIn.cOracle {O : ℕ → ℕ} : PrimrecIn O (fun _ : ℕ => c2n oracle) := by
  rw [←cOracle_evp']; exact isPrim_prop

/-- This code defines the function `fun ⟪a, b⟫ ↦ c2n (pair (n2c a) (n2c b))`. -/
def cPair := cAdd.comp₂ (cMul2.comp <| cMul2) (cConst 5)
@[cp] theorem cPair_prim : IsPrim cPair := by unfold cPair; apply_cp
@[simp, evp_simps] theorem cPair_evp {O a b} :
  evalp O cPair ⟪a, b⟫ = c2n (pair (n2c a) (n2c b)) := by simp [c2n, cPair, Nat.mul_comm]
@[simp, evp_simps] theorem cPair_evp' {O : ℕ → ℕ} :
    evalp O cPair = fun ab : ℕ => c2n (pair (n2c ab.left) (n2c ab.right)) := by
  simp [c2n, cPair, Nat.mul_comm]
@[simp, ev_simps] theorem cPair_ev {O a b} :
    eval O cPair ⟪a, b⟫ = c2n (pair (n2c a) (n2c b)) := by
  rw [← evalp_eq_eval cPair_prim]; simp
@[simp] theorem PrimrecIn.cPair {O : ℕ → ℕ} :
    PrimrecIn O (fun ab : ℕ => c2n (pair (n2c ab.left) (n2c ab.right))) := by
  rw [←cPair_evp']; exact isPrim_prop

/-- This code defines the function `fun ⟪a, b⟫ ↦ c2n (comp (n2c a) (n2c b))`. -/
def cComp := cAdd.comp₂ (cMul2.comp <| cMul2) (cConst 6)
@[cp] theorem cComp_prim : IsPrim cComp := by unfold cComp; apply_cp
@[simp, evp_simps] theorem cComp_evp {O a b} :
  evalp O cComp ⟪a, b⟫ = c2n (comp (n2c a) (n2c b)) := by simp [c2n, cComp, Nat.mul_comm]
@[simp, evp_simps] theorem cComp_evp' {O : ℕ → ℕ} :
    evalp O cComp = fun ab : ℕ => c2n (comp (n2c ab.left) (n2c ab.right)) := by
  simp [c2n, cComp, Nat.mul_comm]
@[simp, ev_simps] theorem cComp_ev {O a b} :
    eval O cComp ⟪a, b⟫ = c2n (comp (n2c a) (n2c b)) := by
  rw [← evalp_eq_eval cComp_prim]; simp
@[simp] theorem PrimrecIn.cComp {O : ℕ → ℕ} :
    PrimrecIn O (fun ab : ℕ => c2n (comp (n2c ab.left) (n2c ab.right))) := by
  rw [←cComp_evp']; exact isPrim_prop

/-- This code defines the function `fun ⟪a, b⟫ ↦ c2n (prec (n2c a) (n2c b))`. -/
def cPrec := cAdd.comp₂ (cMul2.comp <| cMul2) (cConst 7)
@[cp] theorem cPrec_prim : IsPrim cPrec := by unfold cPrec; apply_cp
@[simp, evp_simps] theorem cPrec_evp {O a b} :
    evalp O cPrec ⟪a, b⟫ = c2n (prec (n2c a) (n2c b)) := by
  simpa [c2n, cPrec, evp_simps, Nat.mul_comm] using (by rfl)
@[simp, evp_simps] theorem cPrec_evp' {O : ℕ → ℕ} :
    evalp O cPrec = fun ab : ℕ => c2n (prec (n2c ab.left) (n2c ab.right)) := by
  simpa [c2n, cPrec, evp_simps, Nat.mul_comm] using (by rfl)
@[simp] theorem PrimrecIn.cPrec {O : ℕ → ℕ} :
    PrimrecIn O (fun ab : ℕ => c2n (prec (n2c ab.left) (n2c ab.right))) := by
  rw [← cPrec_evp']; exact isPrim_prop
@[simp, ev_simps] theorem cPrec_ev {O a b} :
    eval O cPrec ⟪a, b⟫ = c2n (prec (n2c a) (n2c b)) := by
  rw [← evalp_eq_eval cPrec_prim]; simp

/-- This code defines the function `fun c ↦ c2n (rfind' (n2c c))`. -/
def cRfind' := cAdd.comp₂ (cMul2.comp <| cMul2) (cConst 8)
@[cp] theorem cRfind'_prim : IsPrim cRfind' := by unfold cRfind'; apply_cp
@[simp, evp_simps] theorem cRfind'_evp {O c} : evalp O cRfind' c = c2n (rfind' <| n2c c) := by
  simpa [c2n, cRfind', evp_simps, Nat.mul_comm] using (by rfl)
@[simp, ev_simps] theorem cRfind'_ev {O c} : eval O cRfind' c = c2n (rfind' <| n2c c) := by
  rw [← evalp_eq_eval cRfind'_prim]; simp

/-- This code defines the function `fun n ↦ c2n (cConst n)`. -/
def cCConst := (cNatIterate (cComp.comp₂ (cConst <| c2n succ) (cId))).comp₂ zero cId
@[cp] theorem cCConst_prim : IsPrim cCConst := by unfold cCConst; apply_cp
@[simp, evp_simps] theorem cCConst_evp {O n} : evalp O cCConst n = c2n (cConst n) := by
  unfold cConst
  unfold cCConst
  simp only [n2c_c2n, evp_simps]
  induction n with
  | zero => simp [c2n]
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    rewrite [ih, cConst.eq_def, n2c_c2n]
    simp only
theorem cCConst_evp' {O : ℕ → ℕ} : evalp O cCConst = cConst := by
  funext x
  simpa only [cCConst_evp] using (by rfl)
@[simp, ev_simps] theorem cCConst_ev {O c} : eval O cCConst c = c2n (cConst c) := by
  rw [← evalp_eq_eval cCConst_prim]; simp
@[simp] theorem PrimrecIn.cConst {O : ℕ → ℕ} : PrimrecIn O cConst := by
  rw [← cCConst_evp']; exact isPrim_prop

/-- This code defines the function `fun ⟪e, x⟫ ↦ c2n (comp (n2c e) (cConst x))`. -/
def cEvConst := cComp.comp₂ left (cCConst.comp right)
@[cp] theorem cEvConst_prim : IsPrim cEvConst := by unfold cEvConst; apply_cp
theorem cEvConst_evp' {O x} :
    evalp O cEvConst x = c2n (comp (n2c x.left) (cConst x.right)) := by
  simp [cEvConst]
@[simp, evp_simps] theorem cEvConst_evp {O e x} :
  evalp O cEvConst ⟪e, x⟫ = c2n (comp (n2c e) (cConst x)) := by simp [cEvConst_evp']
theorem cEvConst_ev' {O x} : eval O cEvConst x = c2n (comp (n2c x.left) (cConst x.right)) := by
  rw [← evalp_eq_eval cEvConst_prim]; simp [cEvConst_evp']
@[simp, ev_simps] theorem cEvConst_ev {O x e} :
    eval O cEvConst ⟪e, x⟫ = c2n (comp (n2c e) (cConst x)) := by
  rw [← evalp_eq_eval cEvConst_prim]; simp
end Oracle.Single.Code
end constructors

namespace Oracle.Single.Code
section cComp₂
/-- This code defines the function `fun ⟪a, b, c⟫ ↦ c2n (comp₂ a b c)`. -/
def cComp₂ :=
  let a := left
  let b := left.comp right
  let c := right.comp right
  cComp.comp₂ a <| cPair.comp₂ b c
@[cp] theorem cComp₂_prim : IsPrim cComp₂ := by unfold cComp₂; apply_cp
@[simp, evp_simps] theorem cComp₂_evp {O a b c} : evalp O cComp₂ ⟪a,b,c⟫ = c2n (comp₂ a b c) := by
  simp [cComp₂]; rfl
@[simp, ev_simps] theorem cComp₂_ev {O a b c} : eval O cComp₂ ⟪a,b,c⟫ = c2n (comp₂ a b c) := by
  rw [← evalp_eq_eval cComp₂_prim]; simp
end cComp₂
section cComp₃
/-- This code defines the function `fun ⟪⟪a, b⟫, ⟪c, d⟫⟫ ↦ c2n (comp₃ a b c d)`. -/
def cComp₃ :=
  let a := left.comp left
  let b := left.comp right
  let c := right.comp left
  let d := right.comp right
  cComp.comp₂ (a) (cPair.comp₂ c (cPair.comp₂ b d))
@[cp] theorem cComp₃_prim : IsPrim cComp₃ := by unfold cComp₃; apply_cp
@[simp, evp_simps] theorem cComp₃_evp {O a b c d} :
    evalp O cComp₃ ⟪⟪a,b⟫,⟪c,d⟫⟫ = c2n (comp₃ a b c d) := by
  simp [cComp₃]; rfl
@[simp, ev_simps] theorem cComp₃_ev {O a b c d} :
    eval O cComp₃ ⟪⟪a,b⟫,⟪c,d⟫⟫ = c2n (comp₃ a b c d) := by
  rw [← evalp_eq_eval cComp₃_prim]; simp
end cComp₃

section cCRfind
/-- This code defines the function `fun x ↦ c2n (cRfind x)`. -/
@[irreducible] def cCRfind := cComp.comp₂ cRfind' (cPair.comp₂ (cConst cId) (cZero))
@[cp] theorem cCRfind_prim : IsPrim cCRfind := by unfold cCRfind; apply_cp
@[simp, evp_simps] theorem cCRfind_evp {O : ℕ → ℕ} :
    evalp O cCRfind = fun x : ℕ => c2n (cRfind x) := by
  simp [cCRfind, cRfind]
end cCRfind

/-- This code defines the function `fun c ↦ c2n (dovetailn (n2c c))`. -/
def cDovetailn := cCRfind.comp <|
  cComp₂.comp₃
  (cConst cIfEq')
  (cComp₃.comp₄
    (cConst cEvaln)
    (cPair.comp₂ cLeft (cComp.comp₂ cLeft cRight))
    (cCConst)
    (cComp.comp₂ cRight cRight))
  (cConst (cConst 1))
@[cp] theorem cDovetailn_prim : IsPrim cDovetailn := by unfold cDovetailn; apply_cp
@[simp, evp_simps] theorem cDovetailn_evp {O : ℕ → ℕ} :
  evalp O cDovetailn = fun x ↦ c2n (dovetailn <| n2c x) := by
  -- just doing simp [cDovetailn, dovetailn] should work, but gives a kernel recursion error. why?
  -- this was fixed by moving simp from def of comp_n to the comp_n_evp theorems.
  simp [cDovetailn, dovetailn]
/-- This code defines the function `fun c ↦ c2n (dovetail (n2c c))`. -/
def cDovetail := cComp.comp₂ cLeft cDovetailn
@[cp] theorem cDovetail_prim : IsPrim cDovetail := by unfold cDovetail; apply_cp
@[simp, evp_simps] theorem cDovetail_evp {O : ℕ → ℕ} :
  evalp O cDovetail = fun x ↦ c2n (dovetail <| n2c x) := by
  simp [cDovetail, dovetail]

/-- This code defines the function `fun x ↦ c2n (cIfdom x.left x.right)`. -/
def cCIfdom := cComp₂.comp₃ (cConst cAdd) (cComp.comp₂ cZero left) right
@[cp] theorem cCIfdom_prim : IsPrim cCIfdom := by unfold cCIfdom; apply_cp
@[simp, evp_simps] theorem cCIfdom_evp {O : ℕ → ℕ} :
    evalp O cCIfdom = fun x ↦ c2n (cIfdom x.left x.right) := by
  simp [cCIfdom, cIfdom]
end Oracle.Single.Code
