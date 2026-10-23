/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
module

public import Mathlib.Computability.SingleOracle.Constructions.Primitive
public import Mathlib.Computability.SingleOracle.Constructions.Eval

/-!
# Construction of codes of basic non-primrec functions

This file defines codes for basic functions which are not primitive recursive.

## Main declarations

- `cDiverge`: A code which diverges on all inputs.
- `cIte`: A code which implements if-then-else, where the entire computation
  does not necessarily diverge even if one the branches does.

-/

@[expose] public section

namespace Oracle.Single.Code

section diverge
/-- `cDiverge` is a code which diverges on all inputs. -/
def cDiverge := rfind' (cConst 1)
set_option backward.isDefEq.respectTransparency false in
@[simp, ev_simps] theorem cDiverge_ev {O x} : eval O cDiverge x = Part.none := by
  simp only [cDiverge, ev_simps]
  apply Part.eq_none_iff.mpr
  simp
theorem cDiverge_ev' {O : ℕ → ℕ} : eval O cDiverge = fun _ ↦ Part.none := by funext; simp
end diverge

section ifz1
/-- `cIfz1 c a b` evalutes code `c`; if it is zero, it returns `a`, otherwise `b`. -/
def cIfz1 (c : Code) (a b : ℕ) :=
  cAdd.comp₂ (cMul.comp₂ (cConst b) (cSg.comp c)) (cMul.comp₂ (cConst a) (cSg'.comp c))
set_option backward.isDefEq.respectTransparency false in
open Classical in
@[simp, ev_simps] theorem cIfz1_ev {O c a b x} (hc : IsTotal O c) :
    eval O (cIfz1 c a b) x = if (eval O c x=Part.some 0) then Part.some a else Part.some b := by
  simp only [cIfz1, ev_simps]
  simp? [Seq.seq] says
    simp only [Seq.seq, Part.coe_some, Part.map_eq_map, Part.map_some, Part.bind_eq_bind,
    Part.map_bind, PFun.coe_val, Nat.sg, Part.bind_some, Nat.unpaired2, Nat.mul_eq, Nat.sg']
  have : (eval O c x).Dom := hc x
  simp only [Part.Dom.bind (hc x), Part.bind_some, pair_l, pair_r, mul_ite, mul_zero, mul_one,
    PFun.coe_val, Nat.unpaired2, Nat.add_eq]
  split
  next h => simp [Part.get_eq_iff_eq_some.mp h]
  next h => aesop
theorem cIfz1_total {O c a b} (hc : IsTotal O c) : IsTotal O (cIfz1 c a b) := by
  intro x
  simp only [cIfz1_ev hc]
  split <;> simp_all only [Part.some_dom]
end ifz1

section ite
def cIte (c a b : Oracle.Single.Code) := cEval.comp₂ (cIfz1 c a.c2n b.c2n) (cId)
open Classical in
@[simp, ev_simps] theorem cIte_ev {O c a b x} (hc : IsTotal O c) :
    eval O (cIte c a b) x = if (eval O c x=Part.some 0) then (eval O a x) else (eval O b x) := by
  simp only [cIte, ev_simps]
  simp? [Seq.seq] says
    simp only [Seq.seq, Part.map_eq_map, Part.coe_some, Part.map_some, Part.bind_map,
      Part.bind_eq_bind]
  have d := @cIfz1_total O c a.c2n b.c2n hc x
  simp only [Part.Dom.bind d, Part.bind_some, pair_l, pair_r]
  simp only [cIfz1_ev hc]
  split <;> simp only [Part.get_some, n2c_c2n]
end ite

section if_le_te'
-- like cIfLeTe, but allows either branch to diverge
def cIfLeTe' (c1 c2 c3 c4 : Code) := cIte (cSub.comp₂ c1 c2) c3 c4
set_option backward.isDefEq.respectTransparency false in
@[simp, ev_simps] theorem cIfLeTe'_ev {O c1 c2 c3 c4 x}
    (hc1 : IsTotal O c1) (hc2 : IsTotal O c2) :
    eval O (cIfLeTe' c1 c2 c3 c4) x =
    if (eval O c1 x).get (hc1 x) ≤ (eval O c2 x).get (hc2 x)
    then (eval O c3 x)
    else (eval O c4 x) := by
  simp only [cIfLeTe', ev_simps]
  have : IsTotal O (cSub.comp₂ c1 c2) := by
    apply total_comp_of <| prim_total cSub_prim
    apply total_pair_of hc1 hc2
  simp only [this, ev_simps]
  congr
  simp only [ev_simps, Seq.seq]
  simp only [Part.map_eq_map, Part.bind_map, Part.bind_eq_bind, eq_iff_iff]
  simpa [Part.Dom.bind <| hc1 x, Part.Dom.bind <| hc2 x] using Nat.sub_eq_zero_iff_le
end if_le_te'

section if_eq_te'
-- like cIfEqTe, but allows either branch to diverge
def cIfEqTe' (c1 c2 c3 c4 : Code) := cIte (cDist.comp₂ c1 c2) c3 c4
set_option backward.isDefEq.respectTransparency false in
open Classical in
@[simp, ev_simps] theorem cIfEqTe'_ev {O c1 c2 c3 c4 x}
    (hc1 : IsTotal O c1) (hc2 : IsTotal O c2) :
    eval O (cIfEqTe' c1 c2 c3 c4) x =
    if (eval O c1 x).get (hc1 x) = (eval O c2 x).get (hc2 x)
    then (eval O c3 x)
    else (eval O c4 x) := by
  simp [cIfEqTe']
  have : IsTotal O (cDist.comp₂ c1 c2) := by
    apply total_comp_of <| prim_total cDist_prim
    apply total_pair_of hc1 hc2
  simp [this]
  simp [Seq.seq]
  simp [Part.Dom.bind <| hc1 x]
  simp [Part.Dom.bind <| hc2 x]
end if_eq_te'

section ifdom
/-- `cIfdom c a` evaluates code `c`, then code `a`. -/
def cIfdom (c a : Code) := cAdd.comp₂ (zero.comp c) a
set_option backward.isDefEq.respectTransparency false in
open Classical in
@[simp, ev_simps] theorem cIfdom_ev {O c a x} :
    eval O (cIfdom c a) x = if (eval O c x).Dom then (eval O a x) else Part.none := by
  split
  next h => simp [cIfdom, eval, Seq.seq, Part.Dom.bind h]
  next h => simp [cIfdom, eval, Seq.seq, Part.eq_none_iff'.mpr h]
end ifdom

section evaln₁
/-- `evaln₁` is a wrapper for `evaln`, which packs the steps, code and input into one argument. -/
def evaln₁ (O : ℕ → ℕ) : ℕ → ℕ :=
  fun abc => Encodable.encode (evaln O abc.right.right abc.left.n2c abc.right.left)
def cEvaln₁ := cEvaln.comp₃ (left.comp right) left (right.comp right)
theorem cEvaln₁_evp {O : ℕ → ℕ} : evalp O cEvaln₁ = evaln₁ O := by
  unfold evaln₁
  simp [cEvaln₁]
theorem prim_evaln₁ {O : ℕ → ℕ} : PrimrecIn O (evaln₁ O) := by
  simp [← cEvaln₁_evp]
end evaln₁

section eval₁
/-- `eval₁` is a wrapper for `eval`, which packs the code and input into one argument. -/
def eval₁ (O : ℕ → ℕ) : ℕ →. ℕ := fun ex => eval O ex.left.n2c ex.right
def cEval₁ := cEval
set_option backward.isDefEq.respectTransparency false in
@[simp, ev_simps] theorem cEval₁_ev {O : ℕ → ℕ} : eval O cEval₁ = eval₁ O := by
  unfold eval₁
  simp [cEval₁]
theorem rec_eval₁ {O : ℕ → ℕ} : RecursiveIn O (eval₁ O) := RecursiveIn.Rin.eval
end eval₁

end Oracle.Single.Code

open Oracle.Single.Code
namespace Oracle.Single.RecursiveIn
theorem exists_code_nat {O : ℕ → ℕ} {f : ℕ →. ℕ} :
    RecursiveIn O f ↔ ∃ c : ℕ , eval O c.n2c = f := by
  rw [@exists_code O f]
  exact Function.Surjective.exists n2c_sur
theorem exists_isTotal {O : ℕ → ℕ} {f : ℕ → ℕ} :
    RecursiveIn O f ↔ ∃ c , eval O c = f ∧ IsTotal O c := by
  constructor
  · intro h
    rcases exists_code.mp h with ⟨c,hc⟩
    use c
    constructor
    · exact hc
    intro x
    rw [hc]
    exact trivial
  intro h
  rcases h with ⟨c, hc, _⟩
  apply exists_code.mpr ⟨c, hc⟩
theorem Rin.ite {O : ℕ → ℕ} {f g : ℕ →. ℕ} {c : ℕ → ℕ}
    (hc : RecursiveIn O c) (hf : RecursiveIn O f) (hg : RecursiveIn O g) :
    RecursiveIn O fun a => if (c a=0) then (f a) else (g a) := by
  apply exists_code.mpr
  rcases exists_isTotal.mp hc with ⟨cc,hcc,hcct⟩
  rcases exists_code_nat.mp hf with ⟨ca,hca⟩
  rcases exists_code_nat.mp hg with ⟨cb,hcb⟩
  use cIte cc ca.n2c cb.n2c
  funext x
  simp [cIte_ev hcct]
  simp [hcc, hca, hcb]
set_option backward.isDefEq.respectTransparency false in
theorem Rin.evalRecInO' {O : ℕ → ℕ} {f : ℕ →. ℕ} (h : RecursiveIn O f) :
    RecursiveIn O (fun x => (f x) >>= (eval₁ O)) := by
  simp only [Part.bind_eq_bind]
  refine RecursiveIn.comp ?_ h
  apply rec_eval₁
theorem Rin.none {O : ℕ → ℕ} : RecursiveIn O fun _ => Part.none := by
  rw [← cDiverge_ev']
  exact RecursiveIn_of_eval
end Oracle.Single.RecursiveIn
