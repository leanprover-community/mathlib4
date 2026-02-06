/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Meta.ConstSimp
public import Mathlib.Tactic.ComputeAsymptotics.Meta.CompareReal
public import Mathlib.Tactic.ComputeAsymptotics.Meta.Misc

/-!
# Extraction of the head of a multiseries

In this file we simulate the lazy evaluation with multiseries and `LazySeries`.
The main function is `normalizeMultiseriesExpansion` that turns a given multiseries into a new one
in the normal form (`nil` or `cons`). The function `normalizeLS` does the same for `LazySeries`.
-/

public meta section

open Filter Asymptotics ComputeAsymptotics Stream' MultiseriesExpansion

open Lean Elab Meta Tactic Qq

namespace ComputeAsymptotics

namespace Normalization

/-- Result of the normalization of a `LazySeries`. -/
inductive ResultLS (s : Q(LazySeries))
| nil (h : Q($s = Seq.nil))
| cons (hd : Q(ℝ)) (tl : Q(LazySeries)) (h : Q($s = Seq.cons $hd $tl))

lemma ResultLS.consNormalize_aux {s : LazySeries} {hd hd' : ℝ} {tl : LazySeries}
    (h : s = Seq.cons hd tl) (h_hd : hd = hd') :
    s = Seq.cons hd' tl := by
  rw [h, h_hd]

/-- The same as `ResultLS.cons` but also normalizes the head as a real number. -/
def ResultLS.consNormalize {s : Q(LazySeries)} (hd : Q(ℝ)) (tl : Q(LazySeries))
    (h : Q($s = Seq.cons $hd $tl)) :
    TacticM (ResultLS s) := do
  let ⟨hd', pf_hd⟩ ← normalizeReal hd
  return .cons q($hd') q($tl) q(consNormalize_aux $h $pf_hd)

/-- Normalizes a `LazySeries`. -/
partial def normalizeLS (s : Q(LazySeries)) : TacticM (ResultLS s) := do
  match s with
  | ~q(Seq.nil) =>
    return .nil q(rfl)
  | ~q(Seq.cons $hd $tl) =>
    return ← ResultLS.consNormalize q($hd) q($tl) q(rfl)
  | ~q(invSeries) =>
    return ← ResultLS.consNormalize q(1) q(invSeries) q(invSeries_eq_cons_self)
  | ~q(powSeriesFrom $x $acc $n) =>
    return ← ResultLS.consNormalize q($acc)
      q(MultiseriesExpansion.powSeriesFrom $x ($acc * ($x - $n) / ($n + 1)) ($n + 1))
      q(powSeriesFrom_eq_cons)
  | ~q(powSeries $x) =>
    return ← ResultLS.consNormalize q(1) q(MultiseriesExpansion.powSeriesFrom $x $x 1)
      q(powSeries_eq_cons)
  | ~q(LazySeries.ofFnFrom $f $n) =>
    return ← ResultLS.consNormalize q($f $n) q(LazySeries.ofFnFrom $f ($n + 1))
      q(LazySeries.ofFnFrom_eq_cons)
  | ~q(logSeries) =>
    return ← ResultLS.consNormalize q(0) q(LazySeries.ofFnFrom (fun n ↦ -(-1) ^ n / n) 1)
      q(logSeries_eq_cons)
  | ~q(expSeries) =>
    return ← ResultLS.consNormalize q(1) q(LazySeries.ofFnFrom (fun n ↦ (n.factorial)⁻¹) 1)
      q(expSeries_eq_cons)
  | _ => panic! "normalizeLS: unexpected s"

/-- Result of the normalization of a `Multiseries`. -/
inductive Result {basis_hd : Q(ℝ → ℝ)} {basis_tl : Q(Basis)}
    (ms : Q(Multiseries $basis_hd $basis_tl))
| nil (h : Q($ms = .nil))
| cons (exp : Q(ℝ)) (coef : Q(MultiseriesExpansion $basis_tl))
    (tl : Q(Multiseries $basis_hd $basis_tl))
  (h : Q($ms = .cons $exp $coef $tl))

lemma consNormalize_aux_congr_exp {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : Multiseries basis_hd basis_tl}
    {exp exp' : ℝ} {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (h : ms = .cons exp coef tl) (h_exp : exp = exp') :
    ms = .cons exp' coef tl := by
  rw [h, h_exp]

/-- The same as `Result.cons` but also normalizes `exp` as a real number. -/
def consNormalizeExp {basis_hd : Q(ℝ → ℝ)} {basis_tl : Q(Basis)}
    {ms : Q(Multiseries $basis_hd $basis_tl)}
    (exp : Q(ℝ)) (coef : Q(MultiseriesExpansion $basis_tl))
    (tl : Q(Multiseries $basis_hd $basis_tl))
    (h : Q($ms = .cons $exp $coef $tl)) :
    TacticM (Result ms) := do
  let ⟨exp', pf_exp⟩ ← normalizeReal exp
  return .cons q($exp') q($coef) q($tl) q(consNormalize_aux_congr_exp $h $pf_exp)

/-- Turns a `Result` for `ms` into a `Result` for `ms'` given the proof of `ms' = ms`. -/
def Result.cast {basis_hd : Q(ℝ → ℝ)} {basis_tl : Q(Basis)}
    {ms ms' : Q(Multiseries $basis_hd $basis_tl)} (res : Result ms) (h : Q($ms' = $ms)) :
    Result ms' :=
  match res with
  | .nil h_ms => .nil q(($h).trans $h_ms)
  | .cons exp coef tl h_ms => .cons exp coef tl q(($h).trans $h_ms)

section lemmas

lemma extendBasisEnd_seq' {basis_hd : ℝ → ℝ} {basis_tl : List (ℝ → ℝ)} {b : ℝ → ℝ}
    {ms : MultiseriesExpansion (basis_hd :: basis_tl)} {s : Multiseries basis_hd basis_tl}
    (h : ms.seq = s) :
    (extendBasisEnd b ms).seq = Multiseries.extendBasisEnd b s := by
  simp [h]

lemma extendBasisEnd_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} (f : ℝ → ℝ)
    {ms : Multiseries basis_hd basis_tl} (h : ms = .nil) :
    Multiseries.extendBasisEnd f ms = .nil := by
  subst h
  rw [Multiseries.extendBasisEnd_nil]

lemma extendBasisEnd_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} (f : ℝ → ℝ)
    {exp : ℝ} {coef : MultiseriesExpansion basis_tl} {tl ms : Multiseries basis_hd basis_tl}
    (h : ms = .cons exp coef tl) :
    Multiseries.extendBasisEnd f ms =
    .cons exp (MultiseriesExpansion.extendBasisEnd f coef) (Multiseries.extendBasisEnd f tl) := by
  subst h
  simp [Multiseries.extendBasisEnd]

-- TODO: rename
lemma updateBasis_keep_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : Multiseries basis_hd basis_tl}
    (ex_tl : BasisExtension basis_tl)
    (h : ms = .nil) :
    ms.updateBasis ex_tl = .nil := by
  subst h
  rw [Multiseries.updateBasis_nil]

-- TODO: rename
lemma updateBasis_keep_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (ex_tl : BasisExtension basis_tl)
    {exp : ℝ} {coef : MultiseriesExpansion basis_tl} {tl ms : Multiseries basis_hd basis_tl}
    (h : ms = .cons exp coef tl) :
    ms.updateBasis ex_tl =
    .cons exp (MultiseriesExpansion.updateBasis ex_tl coef) (tl.updateBasis ex_tl) := by
  subst h
  rw [Multiseries.updateBasis_cons]

lemma monomial_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    Multiseries.monomial basis_hd basis_tl 0 = .cons 1 one .nil := by
  simp [Multiseries.monomial, Multiseries.monomialRpow]

lemma monomial_succ {basis_hd : ℝ → ℝ} {basis_tl : Basis} (n : ℕ) :
    Multiseries.monomial basis_hd basis_tl (n + 1) =
    .cons 0 (MultiseriesExpansion.monomial basis_tl n) .nil := by
  simp [Multiseries.monomial, Multiseries.monomialRpow]
  rfl

lemma monomialRpow_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} (r : ℝ) :
    Multiseries.monomialRpow basis_hd basis_tl 0 r =
    .cons r one .nil := by
  simp [Multiseries.monomialRpow]

lemma monomialRpow_succ {basis_hd : ℝ → ℝ} {basis_tl : Basis} (n : ℕ) (r : ℝ) :
    Multiseries.monomialRpow basis_hd basis_tl (n + 1) r =
    .cons 0 (MultiseriesExpansion.monomialRpow basis_tl n r) .nil := by
  simp [Multiseries.monomialRpow]

lemma neg_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
    (h : ms = .nil) : ms.neg = .nil := by
  subst h
  simp [Multiseries.neg]

lemma neg_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
    {exp : ℝ} {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (h : ms = .cons exp coef tl) : ms.neg = .cons exp (coef.neg) tl.neg := by
  subst h
  simp

lemma nil_add {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : Multiseries basis_hd basis_tl}
    (h : X = .nil) : X.add Y = Y := by
  subst h
  exact Multiseries.nil_add

lemma cons_add_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : Multiseries basis_hd basis_tl}
    {exp : ℝ} {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (hX : X = .cons exp coef tl) (hY : Y = .nil) :
    X.add Y = .cons exp coef tl := by
  subst hX hY
  exact Multiseries.add_nil

lemma cons_add_cons_right {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {X Y : Multiseries basis_hd basis_tl}
    {X_exp : ℝ} {X_coef : MultiseriesExpansion basis_tl} {X_tl : Multiseries basis_hd basis_tl}
    {Y_exp : ℝ} {Y_coef : MultiseriesExpansion basis_tl} {Y_tl : Multiseries basis_hd basis_tl}
    (hX : X = .cons X_exp X_coef X_tl) (hY : Y = .cons Y_exp Y_coef Y_tl)
    (h_exp : X_exp < Y_exp) :
    X.add Y = .cons Y_exp Y_coef ((Multiseries.cons X_exp X_coef X_tl).add Y_tl) := by
  subst hX hY
  convert Multiseries.add_cons_right _
  simpa [Multiseries.leadingExp_cons]

lemma cons_add_cons_left {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : Multiseries basis_hd basis_tl}
    {X_exp : ℝ} {X_coef : MultiseriesExpansion basis_tl} {X_tl : Multiseries basis_hd basis_tl}
    {Y_exp : ℝ} {Y_coef : MultiseriesExpansion basis_tl} {Y_tl : Multiseries basis_hd basis_tl}
    (hX : X = .cons X_exp X_coef X_tl) (hY : Y = .cons Y_exp Y_coef Y_tl)
    (h_exp : Y_exp < X_exp) :
    X.add Y = .cons X_exp X_coef ((X_tl.add (.cons Y_exp Y_coef Y_tl))) := by
  subst hX hY
  convert Multiseries.add_cons_left _
  simpa [Multiseries.leadingExp_cons]

lemma cons_add_cons_both {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : Multiseries basis_hd basis_tl}
    {X_exp : ℝ} {X_coef : MultiseriesExpansion basis_tl} {X_tl : Multiseries basis_hd basis_tl}
    {Y_exp : ℝ} {Y_coef : MultiseriesExpansion basis_tl} {Y_tl : Multiseries basis_hd basis_tl}
    (hX : X = .cons X_exp X_coef X_tl) (hY : Y = .cons Y_exp Y_coef Y_tl)
    (h_exp : X_exp = Y_exp) :
    X.add Y = .cons X_exp (X_coef.add Y_coef) ((X_tl.add Y_tl)) := by
  subst hX hY
  convert Multiseries.add_cons_cons using 1
  simp [h_exp, add_def]
  rfl

lemma nil_mul {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : Multiseries basis_hd basis_tl}
    (h : X = .nil) : X.mul Y = .nil := by
  subst h
  exact Multiseries.nil_mul

lemma mul_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : Multiseries basis_hd basis_tl}
    (h : Y = .nil) : X.mul Y = .nil := by
  subst h
  exact Multiseries.mul_nil

lemma cons_mul_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : Multiseries basis_hd basis_tl}
    {X_exp : ℝ} {X_coef : MultiseriesExpansion basis_tl} {X_tl : Multiseries basis_hd basis_tl}
    {Y_exp : ℝ} {Y_coef : MultiseriesExpansion basis_tl} {Y_tl : Multiseries basis_hd basis_tl}
    (hX : X = .cons X_exp X_coef X_tl) (hY : Y = .cons Y_exp Y_coef Y_tl) :
    X.mul Y = .cons (X_exp + Y_exp) (X_coef.mul Y_coef) ((X_tl.mulMonomial Y_coef Y_exp).add
      ((Multiseries.cons X_exp X_coef X_tl).mul Y_tl)) := by
  subst hX hY
  exact Multiseries.mul_cons_cons

lemma mulMonomial_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {B : Multiseries basis_hd basis_tl}
    {M_exp : ℝ} {M_coef : MultiseriesExpansion basis_tl} (h : B = .nil) :
    Multiseries.mulMonomial B M_coef M_exp = .nil := by
  subst h
  simp

lemma mulMonomial_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {B : Multiseries basis_hd basis_tl}
    {M_exp : ℝ} {M_coef : MultiseriesExpansion basis_tl} {B_exp : ℝ}
    {B_coef : MultiseriesExpansion basis_tl}
    {B_tl : Multiseries basis_hd basis_tl}
    (hB : B = .cons B_exp B_coef B_tl) :
    Multiseries.mulMonomial B M_coef M_exp =
    .cons (B_exp + M_exp) (B_coef.mul M_coef) (B_tl.mulMonomial M_coef M_exp) := by
  subst hB
  simp [Multiseries.mulMonomial]

lemma mulConst_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X : Multiseries basis_hd basis_tl}
    {c : ℝ} (h : X = .nil) : X.mulConst c = .nil := by
  subst h
  simp

lemma mulConst_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X : Multiseries basis_hd basis_tl}
    {c : ℝ} {exp : ℝ} {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (hX : X = .cons exp coef tl) :
    X.mulConst c = .cons exp (coef.mulConst c) (tl.mulConst c) := by
  subst hX
  simp

lemma powser_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
    {s : LazySeries} (h : s = .nil) : ms.powser s = .nil := by
  subst h
  simp [Multiseries.powser_nil]

lemma powser_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
    {s : LazySeries}
    {s_hd : ℝ} {s_tl : LazySeries} (h : s = Seq.cons s_hd s_tl) :
    ms.powser s = .cons 0 (MultiseriesExpansion.const _ s_hd) (ms.mul (ms.powser s_tl)) := by
  subst h
  simp [Multiseries.powser_cons]

lemma inv_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
    (h : ms = .nil) : ms.inv = .nil := by
  subst h
  simp [Multiseries.inv]

lemma inv_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
    {exp : ℝ} {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (h : ms = .cons exp coef tl) :
    ms.inv = .mulMonomial
      ((tl.neg.mulMonomial coef.inv (-exp)).powser invSeries) coef.inv (-exp) := by
  subst h
  simp [Multiseries.inv]

lemma pow_nil_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
    (h : ms = .nil) {a : ℝ} (ha : a = 0) :
    ms.pow a = .cons 0 MultiseriesExpansion.one .nil := by
  subst h ha
  simp [Multiseries.pow, MultiseriesExpansion.one, Multiseries.one, Multiseries.const]

lemma pow_nil_nonzero {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
    (h : ms = .nil) {a : ℝ} (ha : a ≠ 0) :
    ms.pow a = .nil := by
  subst h
  simp [Multiseries.pow]
  grind

lemma pow_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
    {exp : ℝ} {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (h : ms = .cons exp coef tl) (a : ℝ) :
    ms.pow a = Multiseries.mulMonomial ((tl.mulMonomial coef.inv (-exp)).powser
      (MultiseriesExpansion.powSeries a)) (coef.pow a) (exp * a) := by
  subst h
  simp [Multiseries.pow]

lemma log_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
    (logBasis : LogBasis (basis_hd :: basis_tl))
    (h : ms = .nil) : ms.log logBasis = .nil := by
  subst h
  unfold Multiseries.log
  rfl

lemma log_cons_basis_tl_nil {basis_hd : ℝ → ℝ} {ms : Multiseries basis_hd []}
    {exp : ℝ} {coef : MultiseriesExpansion []} {tl : Multiseries basis_hd []}
    (h : ms = .cons exp coef tl)
    (logBasis : LogBasis [basis_hd]) :
    ms.log logBasis =
      (Multiseries.const basis_hd [] (Real.log coef.toReal)).add
        ((tl.mulConst coef.toReal⁻¹ ).powser logSeries) := by
  subst h
  unfold Multiseries.log
  rfl

lemma log_cons_basis_tl_cons {basis_hd : ℝ → ℝ} {basis_tl_hd : ℝ → ℝ} {basis_tl_tl : Basis}
    {exp : ℝ} {coef : MultiseriesExpansion (basis_tl_hd :: basis_tl_tl)}
    {tl ms : Multiseries basis_hd (basis_tl_hd :: basis_tl_tl)}
    (h : ms = .cons exp coef tl)
    (logBasis_tl : LogBasis (basis_tl_hd :: basis_tl_tl))
    (log_hd : MultiseriesExpansion (basis_tl_hd :: basis_tl_tl)) :
    ms.log (LogBasis.cons basis_hd basis_tl_hd basis_tl_tl logBasis_tl log_hd) =
    Multiseries.add ((.cons 0 ((coef.log logBasis_tl).add <| log_hd.mulConst exp) .nil))
      ((tl.mulMonomial  coef.inv (-exp)).powser logSeries) := by
  subst h
  conv_lhs => unfold Multiseries.log
  rfl

lemma exp_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
    (h : ms = .nil) : ms.exp = .cons 0 MultiseriesExpansion.one .nil := by
  subst h
  simp [Multiseries.exp, MultiseriesExpansion.one, Multiseries.one, Multiseries.const]

lemma exp_cons_of_lt {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
    {exp : ℝ} {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (h : ms = .cons exp coef tl)
    (h_lt : exp < 0) :
    ms.exp = (Multiseries.cons exp coef tl).powser expSeries := by
  subst h
  simp [Multiseries.exp, h_lt]

lemma exp_cons_of_not_lt {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : Multiseries basis_hd basis_tl}
    {exp : ℝ} {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
    (h : ms = .cons exp coef tl)
    (h_not_lt : ¬ exp < 0) :
    ms.exp = ((tl.powser expSeries).mulMonomial coef.exp 0) := by
  subst h
  simp [Multiseries.exp, h_not_lt]

end lemmas


-- TODO: replace all nontrivial rfl-s with theorems
set_option linter.unusedVariables false in
/-- Normalizes a `Multiseries` and returns a `Result`. -/
partial def normalizeMultiseries {basis_hd : Q(ℝ → ℝ)} {basis_tl : Q(Basis)}
    (ms : Q(Multiseries $basis_hd $basis_tl)) : TacticM (Result ms) := do
  match ms.getAppFnArgs with
  | (``Multiseries.extendBasisEnd, #[(basis_hd' : Q(ℝ → ℝ)), (basis_tl' : Q(Basis)), (f : Q(ℝ → ℝ)),
    (ms' : Q(Multiseries $basis_hd' $basis_tl'))]) =>
    have : $basis_hd =Q $basis_hd' := ⟨⟩
    have : $basis_tl =Q $basis_tl' ++ [$f] := ⟨⟩
    let res ← normalizeMultiseries q($ms')
    match res with
    | .nil h =>
      return .nil (q(extendBasisEnd_nil $f $h) : Expr)
    | .cons exp coef tl h =>
      return ← consNormalizeExp q($exp) q(($coef).extendBasisEnd $f) q(($tl).extendBasisEnd $f)
        (q(extendBasisEnd_cons $f $h) : Expr)
  | (``Multiseries.updateBasis, #[(oldBasis_hd : Q(ℝ → ℝ)), (oldBasis_tl : Q(Basis)),
      (ex : Q(BasisExtension $oldBasis_tl)), (ms' : Q(Multiseries $oldBasis_hd $oldBasis_tl))]) =>
    have : $oldBasis_hd =Q $basis_hd := ⟨⟩
    have : $basis_tl =Q ($ex).getBasis := ⟨⟩
    let res ← normalizeMultiseries q($ms')
    match res with
    | .nil h =>
      return .nil (q(updateBasis_keep_nil $ex $h) : Expr)
    | .cons exp coef tl h =>
      return ← consNormalizeExp q($exp) q(($coef).updateBasis $ex) q(($tl).updateBasis $ex)
        (q(updateBasis_keep_cons $ex $h) : Expr)
  | _ =>
  match ms with
  | ~q(Multiseries.nil) => return .nil q(rfl)
  | ~q(Multiseries.cons $exp $coef $tl) => return .cons q($exp) q($coef) q($tl) q(rfl)
  | ~q(Multiseries.const _ _ $c) =>
    return .cons q(0) q(MultiseriesExpansion.const _ $c) q(Multiseries.nil)
      q(Multiseries.const.eq_def _ _ _)
  | ~q(Multiseries.one) =>
    return .cons q(0) q(MultiseriesExpansion.one) q(Multiseries.nil)
      q(Multiseries.const.eq_def _ _ _)
  | ~q(Multiseries.monomial _ _ $n) =>
    match (← getNatValue? (← withTransparency .all <| reduce n)).get! with
    | 0 =>
      have : $n =Q 0 := ⟨⟩
      return .cons q(1) q(MultiseriesExpansion.one) q(Multiseries.nil) q(monomial_zero)
    | m + 1 =>
      have : $n =Q $m + 1 := ⟨⟩
      return .cons q(0) q(MultiseriesExpansion.monomial _ $m) q(Multiseries.nil) q(monomial_succ $m)
  | ~q(Multiseries.monomialRpow _ _ $n $r) =>
    match (← getNatValue? (← withTransparency .all <| reduce n)).get! with
    | 0 =>
      have : $n =Q 0 := ⟨⟩
      return ← consNormalizeExp q($r) q(MultiseriesExpansion.one) q(Multiseries.nil)
        q(monomialRpow_zero $r)
    | m + 1 =>
      have : $n =Q $m + 1 := ⟨⟩
      return .cons q(0) q(MultiseriesExpansion.monomialRpow _ $m $r) q(Multiseries.nil)
        q(monomialRpow_succ $m $r)
  | ~q(Multiseries.neg $arg) =>
    let res ← normalizeMultiseries arg
    match res with
    | .nil h =>
      return .nil q(neg_nil $h)
    | .cons exp coef tl h =>
      return ← consNormalizeExp q($exp) q(MultiseriesExpansion.neg $coef) q(Multiseries.neg $tl)
        q(neg_cons $h)
  | ~q(Multiseries.add $arg1 $arg2) =>
    let res1 ← normalizeMultiseries arg1
    let res2 ← normalizeMultiseries arg2
    match res1 with
    | .nil h1 =>
      return res2.cast q(nil_add $h1)
    | .cons exp1 coef1 tl1 h1 =>
      match res2 with
      | .nil h2 =>
        return ← consNormalizeExp exp1 coef1 tl1 q(cons_add_nil $h1 $h2)
      | .cons exp2 coef2 tl2 h2 =>
        match ← compareTwoReals exp1 exp2 with
        | .lt h_exp =>
          return ← consNormalizeExp exp2 coef2
            q(Multiseries.add (Multiseries.cons $exp1 $coef1 $tl1) $tl2)
            q(cons_add_cons_right $h1 $h2 $h_exp)
        | .gt h_exp =>
          return ← consNormalizeExp exp1 coef1
            q(Multiseries.add $tl1 (Multiseries.cons $exp2 $coef2 $tl2))
            q(cons_add_cons_left $h1 $h2 $h_exp)
        | .eq h_exp =>
          return ← consNormalizeExp exp1 q(MultiseriesExpansion.add $coef1 $coef2)
            q(Multiseries.add $tl1 $tl2) q(cons_add_cons_both $h1 $h2 $h_exp)
  | ~q(Multiseries.mul $arg1 $arg2) =>
    let res1 ← normalizeMultiseries arg1
    match res1 with
    | .nil h1 => return .nil q(nil_mul $h1)
    | .cons exp1 coef1 tl1 h1 =>
      let res2 ← normalizeMultiseries arg2
      match res2 with
      | .nil h2 => return .nil q(mul_nil $h2)
      | .cons exp2 coef2 tl2 h2 =>
        return ← consNormalizeExp q($exp1 + $exp2) q(MultiseriesExpansion.mul $coef1 $coef2)
          q((Multiseries.mulMonomial $tl1 $coef2 $exp2).add
            ((Multiseries.cons $exp1 $coef1 $tl1).mul $tl2)) q(cons_mul_cons $h1 $h2)
  | ~q(Multiseries.mulMonomial $b $m_coef $m_exp) =>
    let res_b ← normalizeMultiseries b
    match res_b with
    | .nil hb =>
      return .nil q(mulMonomial_nil $hb)
    | .cons b_exp b_coef b_tl hb =>
      return ← consNormalizeExp q($b_exp + $m_exp) q(MultiseriesExpansion.mul $b_coef $m_coef)
        q(Multiseries.mulMonomial (basis_hd := $basis_hd) $b_tl $m_coef $m_exp)
        q(mulMonomial_cons $hb)
  | ~q(Multiseries.mulConst $c $arg) =>
    let res ← normalizeMultiseries arg
    match res with
    | .nil h => return .nil q(mulConst_nil $h)
    | .cons exp coef tl h =>
      return ← consNormalizeExp q($exp) q(MultiseriesExpansion.mulConst $c $coef)
        q(Multiseries.mulConst $c $tl) q(mulConst_cons $h)
  | ~q(Multiseries.powser $s $arg) =>
    let res_s ← normalizeLS s
    match res_s with
    | .nil hs =>
      return .nil q(powser_nil $hs)
    | .cons s_hd s_tl hs =>
      return .cons q(0) q(MultiseriesExpansion.const _ $s_hd)
        q(($arg).mul (Multiseries.powser $s_tl $arg)) q(powser_cons $hs)
  | ~q(Multiseries.inv $arg) =>
    let res ← normalizeMultiseries arg
    match res with
    | .nil h =>
      return .nil q(inv_nil $h)
    | .cons exp coef tl h =>
      let ms' : Q(Multiseries $basis_hd $basis_tl) :=
        q(Multiseries.mulMonomial
          (((Multiseries.neg $tl).mulMonomial ($coef).inv (-$exp)).powser invSeries)
          ($coef).inv (-$exp))
      let res' ← normalizeMultiseries ms'
      return res'.cast q(inv_cons $h)
  | ~q(Multiseries.pow $arg $a) =>
    let res ← normalizeMultiseries arg
    match res with
    | .nil h =>
      match ← CompareReal.checkZero a with
      | .eq ha =>
        return .cons q(0) q(MultiseriesExpansion.one) q(Multiseries.nil) q(pow_nil_zero $h $ha)
      | .neq ha => return .nil q(pow_nil_nonzero $h $ha)
    | .cons exp coef tl h =>
      let ms' : Q(Multiseries $basis_hd $basis_tl) := q(Multiseries.mulMonomial
        ((Multiseries.mulMonomial $tl ($coef).inv (-$exp)).powser (powSeries $a)) (($coef).pow $a)
        ($exp * $a))
      let res' ← normalizeMultiseries ms'
      return res'.cast q(pow_cons $h $a)
  | ~q(Multiseries.log $logBasis $arg) =>
    let res ← normalizeMultiseries arg
    match res with
    | .nil h =>
      return .nil q(log_nil $logBasis $h)
    | .cons exp coef tl h =>
      match basis_tl with
      | ~q(List.nil) =>
        let ms' : Q(Multiseries $basis_hd $basis_tl) :=
          q(Multiseries.add (Multiseries.const _ _ (Real.log ($coef).toReal)) <|
            (Multiseries.mulConst ($coef).toReal⁻¹ $tl).powser logSeries)
        let res' ← normalizeMultiseries ms'
        return res'.cast q(log_cons_basis_tl_nil $h $logBasis)
      | ~q(List.cons $basis_tl_hd $basis_tl_tl) =>
        let logBasis' ← reduceLogBasis logBasis
        have : $logBasis =Q $logBasis' := ⟨⟩
        let ~q(LogBasis.cons _ _ _ $logBasis_tl $log_hd) := logBasis'
          | panic! s!"normalizeMultiseries: unexpected logBasis: {← ppExpr logBasis'}"
        let logC := q(MultiseriesExpansion.log $logBasis_tl $coef)
        let ms' : Q(Multiseries $basis_hd $basis_tl) :=
          q(Multiseries.add (.cons 0 (($logC).add <| ($log_hd).mulConst $exp) .nil) <|
            (Multiseries.mulMonomial $tl ($coef).inv (-$exp)).powser logSeries)
        let res' ← normalizeMultiseries ms'
        return res'.cast q(log_cons_basis_tl_cons $h $logBasis_tl $log_hd)
  | ~q(Multiseries.exp $arg) =>
    let res ← normalizeMultiseries arg
    match res with
    | .nil h =>
      return .cons q(0) q(MultiseriesExpansion.one) q(Multiseries.nil) q(exp_nil $h)
    | .cons exp coef tl h =>
      match ← checkLtZero exp with
      | .lt h_exp =>
        let ms' : Q(Multiseries $basis_hd $basis_tl) :=
          q((Multiseries.cons $exp $coef $tl).powser expSeries)
        let res' ← normalizeMultiseries ms'
        return res'.cast q(exp_cons_of_lt $h $h_exp)
      | .not_lt h_exp =>
        let ms' : Q(Multiseries $basis_hd $basis_tl) :=
          q((Multiseries.powser expSeries $tl).mulMonomial ($coef).exp 0)
        let res' ← normalizeMultiseries ms'
        return res'.cast q(exp_cons_of_not_lt $h $h_exp)
  | _ => panic! s!"normalizeMultiseries: unexpected ms: {← ppExpr ms}"

set_option linter.unusedVariables false in
/-- Given an expression `ms` of type `MultiseriesExpansion basis`, returns the expression `f` of
type `ℝ → ℝ` and the proof that `ms.toFun = f`. -/
partial def getFun {basis : Q(Basis)} (ms : Q(MultiseriesExpansion $basis)) :
    TacticM <| (f : Q(ℝ → ℝ)) × Q(($ms).toFun = $f) := do
  match ms.getAppFnArgs with
  | (``MultiseriesExpansion.extendBasisEnd, #[(basis' : Q(Basis)), (f : Q(ℝ → ℝ)),
      (ms' : Q(MultiseriesExpansion $basis'))]) =>
    let ⟨f', h_f'⟩ ← getFun q($ms')
    have : $basis =Q $basis' ++ [$f] := ⟨⟩
    have : $ms =Q MultiseriesExpansion.extendBasisEnd $f $ms' := ⟨⟩
    return ⟨q($f'), q($h_f' ▸ MultiseriesExpansion.extendBasisEnd_toFun)⟩
  | (``MultiseriesExpansion.updateBasis,
      #[(oldBasis : Q(Basis)), (ex : Q(BasisExtension $oldBasis)),
      (ms' : Q(MultiseriesExpansion $oldBasis))]) =>
    let ⟨f, h_f⟩ ← getFun q($ms')
    have : $basis =Q ($ex).getBasis := ⟨⟩
    have : $ms =Q MultiseriesExpansion.updateBasis $ex $ms' := ⟨⟩
    return ⟨q($f), q($h_f ▸ MultiseriesExpansion.updateBasis_toFun)⟩
  | _ =>
  match basis with
  | ~q(List.nil) =>
    let ⟨c, hc⟩  := ← normalizeReal q(($ms).toReal)
    return ⟨q(fun _ ↦ $c), q($hc ▸ MultiseriesExpansion.const_toFun _)⟩
  | ~q(List.cons $basis_hd $basis_tl) =>
  match ms with
  | ~q(MultiseriesExpansion.mk $s $f) => return ⟨q($f), q(MultiseriesExpansion.mk_toFun)⟩
  | ~q(MultiseriesExpansion.replaceFun $ms $f) =>
    return ⟨q($f), q(MultiseriesExpansion.replaceFun_toFun _ _)⟩
  | ~q(MultiseriesExpansion.const _ $c) =>
    return ⟨q(fun _ ↦ $c), q(MultiseriesExpansion.const_toFun')⟩
  | ~q(MultiseriesExpansion.one) => return ⟨q(1), q(MultiseriesExpansion.one_toFun)⟩
  | ~q(MultiseriesExpansion.monomial _ $n) =>
    let nNat := (← getNatValue? (← withTransparency .all <| reduce n)).get!
    let nFin ← mkFin q($n) q(List.length ($basis_hd :: $basis_tl))
    let f ← getNth q($basis_hd :: $basis_tl) nNat
    return ⟨q($f),
      (q(MultiseriesExpansion.monomial_toFun' (basis := $basis_hd :: $basis_tl) (n := $nFin)) :
        Expr)⟩
  | ~q(MultiseriesExpansion.monomialRpow _ $n $r) =>
    let nNat := (← getNatValue? (← withTransparency .all <| reduce n)).get!
    let nFin ← mkFin q($n) q(List.length ($basis_hd :: $basis_tl))
    let f ← getNth q($basis_hd :: $basis_tl) nNat
    return ⟨q($f ^ $r),
      (q(@MultiseriesExpansion.monomialRpow_toFun ($basis_hd :: $basis_tl) $nFin $r) : Expr)⟩
  | ~q(MultiseriesExpansion.neg $arg) =>
    let ⟨f, h⟩ ← getFun q($arg)
    return ⟨q(-$f), q($h ▸ MultiseriesExpansion.neg_toFun)⟩
  | ~q(MultiseriesExpansion.add $arg₁ $arg₂) =>
    let ⟨f₁, h₁⟩ ← getFun q($arg₁)
    let ⟨f₂, h₂⟩ ← getFun q($arg₂)
    return ⟨q($f₁ + $f₂), q($h₁ ▸ $h₂ ▸ MultiseriesExpansion.add_toFun)⟩
  | ~q(MultiseriesExpansion.mul $arg₁ $arg₂) =>
    let ⟨f₁, h₁⟩ ← getFun q($arg₁)
    let ⟨f₂, h₂⟩ ← getFun q($arg₂)
    return ⟨q($f₁ * $f₂), q($h₁ ▸ $h₂ ▸ MultiseriesExpansion.mul_toFun)⟩
  | ~q(MultiseriesExpansion.mulMonomial $b $m_coef $m_exp) =>
    let ⟨f₁, h₁⟩ ← getFun q($b)
    let ⟨f₂, h₂⟩ ← getFun q($m_coef)
    return ⟨q($f₁ * $basis_hd ^ $m_exp * $f₂),
      q($h₁ ▸ $h₂ ▸ MultiseriesExpansion.mulMonomial_toFun)⟩
  | ~q(MultiseriesExpansion.mulConst $c $arg) =>
    let ⟨f, h⟩ ← getFun q($arg)
    return ⟨q($c • $f), q($h ▸ MultiseriesExpansion.mulConst_toFun)⟩
  | ~q(powser $s $arg) =>
    let ⟨f, h⟩ ← getFun q($arg)
    return ⟨q(($s).toFun ∘ $f), q($h ▸ MultiseriesExpansion.powser_toFun)⟩
  | ~q(MultiseriesExpansion.inv $arg) =>
    let ⟨f, h⟩ ← getFun q($arg)
    return ⟨q($f⁻¹), q($h ▸ MultiseriesExpansion.inv_toFun)⟩
  | ~q(MultiseriesExpansion.pow $arg $a) =>
    let ⟨f, h⟩ ← getFun q($arg)
    return ⟨q($f ^ $a), q($h ▸ MultiseriesExpansion.pow_toFun)⟩
  | ~q(MultiseriesExpansion.npow $arg $a) =>
    let ⟨f, h⟩ ← getFun q($arg)
    return ⟨q($f ^ $a), q($h ▸ MultiseriesExpansion.npow_toFun)⟩
  | ~q(MultiseriesExpansion.zpow $arg $a) =>
    let ⟨f, h⟩ ← getFun q($arg)
    return ⟨q($f ^ $a), q($h ▸ MultiseriesExpansion.zpow_toFun)⟩
  | ~q(MultiseriesExpansion.log $logBasis $arg) =>
    let ⟨f, h⟩ ← getFun q($arg)
    return ⟨q(Real.log ∘ $f), q($h ▸ MultiseriesExpansion.log_toFun)⟩
  | ~q(MultiseriesExpansion.exp $arg) =>
    let ⟨f, h⟩ ← getFun q($arg)
    return ⟨q(Real.exp ∘ $f), q($h ▸ MultiseriesExpansion.exp_toFun)⟩
  | _ => panic! s!"getFun: unexpected ms: {← ppExpr ms}"

/-- Given an expression `ms` of type `MultiseriesExpansion (basis_hd :: basis_tl)`, returns the
expression `s` of type `Multiseries basis_hd basis_tl` and the proof that `ms.seq = s`. -/
partial def getSeq {basis_hd : Q(ℝ → ℝ)} {basis_tl : Q(Basis)}
    (ms : Q(MultiseriesExpansion ($basis_hd :: $basis_tl))) :
    MetaM <| (s : Q(Multiseries $basis_hd $basis_tl)) × Q(($ms).seq = $s) := do
  match ms.getAppFnArgs with
  | (``MultiseriesExpansion.extendBasisEnd, #[(basis' : Q(Basis)), (f : Q(ℝ → ℝ)),
      (ms' : Q(MultiseriesExpansion $basis'))]) =>
    have : ($basis_hd :: $basis_tl) =Q $basis' ++ [$f] := ⟨⟩
    -- have : $ms =Q MultiseriesExpansion.extendBasisEnd $f $ms' := ⟨⟩
    match basis' with
    | ~q(List.nil) =>
      have : $basis_tl =Q [] := ⟨⟩
      have : $ms =Q MultiseriesExpansion.extendBasisEnd $f $ms' := ⟨⟩
      let h' : Q($ms = MultiseriesExpansion.mk (.cons 0 $ms' .nil) (fun _ ↦ ($ms'))) :=
        q(extendBasisEnd_const $f $ms')
      return ⟨q(Multiseries.cons 0 $ms' .nil), q($h' ▸ MultiseriesExpansion.mk_seq _ _)⟩
    | ~q(List.cons $basis_hd' $basis_tl') =>
      have : $basis_hd =Q $basis_hd' := ⟨⟩
      have : $basis_tl =Q $basis_tl' ++ [$f] := ⟨⟩
      let ⟨s, h⟩ ← getSeq q($ms')
      have : $ms =Q MultiseriesExpansion.extendBasisEnd $f $ms' := ⟨⟩
      return ⟨q(Multiseries.extendBasisEnd $f $s), q(extendBasisEnd_seq' $h)⟩
  | (``MultiseriesExpansion.updateBasis, #[(oldBasis : Q(Basis)),
      (ex : Q(BasisExtension $oldBasis)), (ms' : Q(MultiseriesExpansion $oldBasis))]) =>
    have : ($basis_hd :: $basis_tl) =Q ($ex).getBasis := ⟨⟩
    let oldBasis' : Q(Basis) ← reduceBasis oldBasis
    have : $oldBasis =Q $oldBasis' := ⟨⟩
    match oldBasis', ex with
    | ~q(List.cons $oldBasis_hd $oldBasis_tl), ~q(BasisExtension.keep _ $ex_tl) =>
      have : $basis_hd =Q $oldBasis_hd := ⟨⟩
      have : $basis_tl =Q ($ex_tl).getBasis := ⟨⟩
      let ⟨s, h⟩ ← getSeq q($ms')
      have : $ms =Q MultiseriesExpansion.updateBasis $ex $ms' := ⟨⟩
      return ⟨q(Multiseries.updateBasis $ex_tl $s),
        q($h ▸ MultiseriesExpansion.updateBasis_keep_seq)⟩
    | _, ~q(BasisExtension.insert $f $ex_tl) =>
      have : ($ex_tl).getBasis =Q $basis_tl := ⟨⟩
      have : $ms =Q MultiseriesExpansion.updateBasis $ex $ms' := ⟨⟩
      return ⟨q(Multiseries.cons 0 (($ms').updateBasis $ex_tl) .nil), q(updateBasis_insert_seq)⟩
    | _ =>
      panic!
        s!"getSeq: unexpected oldBasis and ex: {← ppExpr oldBasis} and {← ppExpr ex}"
  | _ =>
  match ms with
  | ~q(MultiseriesExpansion.mk $s $f) => return ⟨q($s), q(rfl)⟩
  | ~q(MultiseriesExpansion.replaceFun $arg $f) =>
    let ⟨s, h⟩ ← getSeq q($arg)
    return ⟨q($s), q($h ▸ MultiseriesExpansion.replaceFun_seq _ _)⟩
  | ~q(MultiseriesExpansion.const _ $c) =>
    return ⟨q(Multiseries.const _ _ $c), q(MultiseriesExpansion.const_seq)⟩
  | ~q(MultiseriesExpansion.one) => return ⟨q(Multiseries.one), q(MultiseriesExpansion.one_seq)⟩
  | ~q(MultiseriesExpansion.monomial _ $n) =>
    return ⟨q(Multiseries.monomial _ _ $n), q(MultiseriesExpansion.monomial_seq)⟩
  | ~q(MultiseriesExpansion.monomialRpow _ $n $r) =>
    return ⟨q(Multiseries.monomialRpow _ _ $n $r), q(MultiseriesExpansion.monomialRpow_seq)⟩
  | ~q(MultiseriesExpansion.neg $arg) =>
    let ⟨s, h⟩ ← getSeq q($arg)
    return ⟨q(Multiseries.neg $s), q($h ▸ MultiseriesExpansion.neg_seq)⟩
  | ~q(MultiseriesExpansion.add $arg₁ $arg₂) =>
    let ⟨s₁, h₁⟩ ← getSeq q($arg₁)
    let ⟨s₂, h₂⟩ ← getSeq q($arg₂)
    return ⟨q(Multiseries.add $s₁ $s₂), q($h₁ ▸ $h₂ ▸ MultiseriesExpansion.add_seq)⟩
  | ~q(MultiseriesExpansion.mul $arg₁ $arg₂) =>
    let ⟨s₁, h₁⟩ ← getSeq q($arg₁)
    let ⟨s₂, h₂⟩ ← getSeq q($arg₂)
    return ⟨q(Multiseries.mul $s₁ $s₂), q($h₁ ▸ $h₂ ▸ MultiseriesExpansion.mul_seq)⟩
  | ~q(MultiseriesExpansion.mulMonomial $b $m_coef $m_exp) =>
    let ⟨s₁, h₁⟩ ← getSeq q($b)
    return ⟨q(Multiseries.mulMonomial $s₁ $m_coef $m_exp),
      q($h₁ ▸ MultiseriesExpansion.mulMonomial_seq)⟩
  | ~q(MultiseriesExpansion.mulConst $c $arg) =>
    let ⟨s, h⟩ ← getSeq q($arg)
    return ⟨q(Multiseries.mulConst $c $s), q($h ▸ MultiseriesExpansion.mulConst_seq)⟩
  | ~q(powser $s $arg) =>
    let ⟨ms, h⟩ ← getSeq q($arg)
    return ⟨q(Multiseries.powser $s $ms), q($h ▸ MultiseriesExpansion.powser_seq)⟩
  | ~q(MultiseriesExpansion.inv $arg) =>
    let ⟨s, h⟩ ← getSeq q($arg)
    return ⟨q(Multiseries.inv $s), q($h ▸ MultiseriesExpansion.inv_seq)⟩
  | ~q(MultiseriesExpansion.pow $arg $a) =>
    let ⟨s, h⟩ ← getSeq q($arg)
    return ⟨q(Multiseries.pow $s $a), q($h ▸ MultiseriesExpansion.pow_seq)⟩
  | ~q(MultiseriesExpansion.npow $arg $a) =>
    let ⟨s, h⟩ ← getSeq q($arg)
    return ⟨q(Multiseries.pow $s $a), q($h ▸ MultiseriesExpansion.pow_seq)⟩
  | ~q(MultiseriesExpansion.zpow $arg $a) =>
    let ⟨s, h⟩ ← getSeq q($arg)
    return ⟨q(Multiseries.pow $s $a), q($h ▸ MultiseriesExpansion.pow_seq)⟩
  | ~q(MultiseriesExpansion.log $logBasis $arg) =>
    let ⟨s, h⟩ ← getSeq q($arg)
    return ⟨q(Multiseries.log $logBasis $s), q($h ▸ MultiseriesExpansion.log_seq)⟩
  | ~q(MultiseriesExpansion.exp $arg) =>
    let ⟨s, h⟩ ← getSeq q($arg)
    return ⟨q(Multiseries.exp $s), q($h ▸ MultiseriesExpansion.exp_seq)⟩
  | _ => panic! s!"getMultiseries: unexpected ms: {← ppExpr ms}"


/-- Given `ms : MultiseriesExpansion basis`, return `ms'` that is normalized
(either `MultiseriesExpansion.mk .nil f` or `MultiseriesExpansion.mk (.cons exp coef tl) f`),
and the proof of `ms' = ms`. -/
def normalizeMultiseriesExpansion {basis : Q(Basis)}
    (ms : Q(MultiseriesExpansion $basis)) :
    TacticM ((ms' : Q(MultiseriesExpansion $basis)) × Q($ms = $ms')) := do
  match basis with
  | ~q(List.nil) => return ⟨ms, q(rfl)⟩
  | ~q(List.cons $basis_hd $basis_tl) =>
    let ⟨f, hf⟩ ← getFun q($ms)
    let ⟨s, hs⟩ ← getSeq q($ms)
    let res ← normalizeMultiseries q($s)
    match res with
    | .nil h =>
      return ⟨q(MultiseriesExpansion.mk .nil $f), q((ms_eq_mk_iff _ _ _).mpr ⟨$h ▸ $hs, $hf⟩)⟩
    | .cons exp coef tl h =>
      return ⟨q(MultiseriesExpansion.mk (.cons $exp $coef $tl) $f),
        q((ms_eq_mk_iff _ _ _).mpr ⟨$h ▸ $hs, $hf⟩)⟩

end Normalization

end ComputeAsymptotics
