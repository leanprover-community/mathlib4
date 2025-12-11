/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Meta.ConstSimp
public import Mathlib.Tactic.ComputeAsymptotics.Meta.CompareReal
-- import Mathlib.Tactic.ComputeAsymptotics.Meta.Defs
public import Mathlib.Tactic.ComputeAsymptotics.Meta.Misc

/-!
# Extraction of the head of a multiseries

In this file we simulate the lazy evaluation with multiseries and `LazySeries`.
The main function is `normalizePreMS` that turns a given multiseries into a new one
in the normal form (`nil` or `cons`). The function `normalizeLS` does the same for `LazySeries`.
-/

public meta section

open Filter Asymptotics ComputeAsymptotics Stream' PreMS

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
      q(PreMS.powSeriesFrom $x ($acc * ($x - $n) / ($n + 1)) ($n + 1))
      q(powSeriesFrom_eq_cons)
  | ~q(powSeries $x) =>
    return ← ResultLS.consNormalize q(1) q(PreMS.powSeriesFrom $x $x 1) q(powSeries_eq_cons)
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

/-- Result of the normalization of a `PreMS`. -/
inductive Result {basis_hd : Q(ℝ → ℝ)} {basis_tl : Q(Basis)}
    (ms : Q(PreMS ($basis_hd :: $basis_tl)))
| nil (h : Q($ms = PreMS.nil))
| cons (exp : Q(ℝ)) (coef : Q(PreMS $basis_tl)) (tl : Q(PreMS ($basis_hd :: $basis_tl)))
  (h : Q($ms = PreMS.cons $exp $coef $tl))

lemma consNormalize_aux_congr_exp {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)}
    {exp exp' : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h : ms = PreMS.cons exp coef tl) (h_exp : exp = exp') :
    ms = PreMS.cons exp' coef tl := by
  rw [h, h_exp]

lemma consNormalize_aux_congr_coef {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)}
    {exp : ℝ} {coef coef' : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h : ms = PreMS.cons exp coef tl) (h_coef : coef = coef') :
    ms = PreMS.cons exp coef' tl := by
  rw [h, h_coef]

lemma consNormalize_aux_congr_exp_coef {basis_hd : ℝ → ℝ}
    {ms : PreMS [basis_hd]}
    {exp exp' : ℝ} {coef : PreMS []} {coef' : ℝ} {tl : PreMS [basis_hd]}
    (h : ms = PreMS.cons exp coef tl) (h_exp : exp = exp') (h_coef : coef = coef') :
    ms = PreMS.cons exp' coef' tl := by
  rw [h, h_exp, h_coef]

/-- The same as `Result.cons` but also normalizes `exp` as a real number,
and the `coef` if `basis_tl` is `[]`. -/
def consNormalize {basis_hd : Q(ℝ → ℝ)} {basis_tl : Q(Basis)}
    {ms : Q(PreMS ($basis_hd :: $basis_tl))}
    (exp : Q(ℝ)) (coef : Q(PreMS $basis_tl)) (tl : Q(PreMS ($basis_hd :: $basis_tl)))
    (h : Q($ms = PreMS.cons $exp $coef $tl)) :
    TacticM (Result ms) := do
  let ⟨exp', pf_exp⟩ ← normalizeReal exp
  match basis_tl with
  | ~q(List.nil) =>
    let ⟨coef', pf_coef⟩ ← normalizeReal coef
    return .cons q($exp') q($coef') q($tl) q(consNormalize_aux_congr_exp_coef $h $pf_exp $pf_coef)
  | _ =>
    return .cons q($exp') q($coef) q($tl) q(consNormalize_aux_congr_exp $h $pf_exp)

/-- The same as `Result.cons` but also normalizes the `coef` if `basis_tl` is `[]`. -/
def consNormalizeCoef {basis_hd : Q(ℝ → ℝ)} {basis_tl : Q(Basis)}
    {ms : Q(PreMS ($basis_hd :: $basis_tl))}
    (exp : Q(ℝ)) (coef : Q(PreMS $basis_tl)) (tl : Q(PreMS ($basis_hd :: $basis_tl)))
    (h : Q($ms = PreMS.cons $exp $coef $tl)) :
    TacticM (Result ms) := do
  match basis_tl with
  | ~q(List.nil) =>
    let ⟨coef', pf_coef⟩ ← normalizeReal coef
    return .cons q($exp) q($coef') q($tl) q(consNormalize_aux_congr_coef $h $pf_coef)
  | _ =>
    return .cons q($exp) q($coef) q($tl) q($h)

/-- Turns a `Result` for `ms` into a `Result` for `ms'` given the proof of `ms' = ms`. -/
def Result.cast {basis_hd : Q(ℝ → ℝ)} {basis_tl : Q(Basis)}
    {ms ms' : Q(PreMS ($basis_hd :: $basis_tl))} (res : Result ms) (h : Q($ms' = $ms)) :
    Result ms' :=
  match res with
  | .nil h_ms => .nil q(($h).trans $h_ms)
  | .cons exp coef tl h_ms => .cons exp coef tl q(($h).trans $h_ms)

section lemmas

lemma extendBasisEnd_const (f : ℝ → ℝ) (ms : PreMS []) :
    PreMS.extendBasisEnd f ms = PreMS.cons 0 ms PreMS.nil := by
  simp [PreMS.extendBasisEnd, PreMS.const]

lemma extendBasisEnd_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} (f : ℝ → ℝ)
    {ms : PreMS (basis_hd :: basis_tl)} (h : ms = PreMS.nil) :
    PreMS.extendBasisEnd f ms = PreMS.nil := by
  subst h
  simp [PreMS.extendBasisEnd]

lemma extendBasisEnd_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} (f : ℝ → ℝ)
    {exp : ℝ} {coef : PreMS basis_tl} {tl ms : PreMS (basis_hd :: basis_tl)}
    (h : ms = PreMS.cons exp coef tl) :
    PreMS.extendBasisEnd f ms =
    PreMS.cons exp (PreMS.extendBasisEnd f coef) (PreMS.extendBasisEnd f tl) := by
  subst h
  simp [PreMS.extendBasisEnd]

lemma updateBasis_keep_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    (ex_tl : BasisExtension basis_tl)
    (h : ms = PreMS.nil) :
    ms.updateBasis (.keep _ ex_tl) = PreMS.nil := by
  subst h
  simp [PreMS.updateBasis]

lemma updateBasis_keep_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (ex_tl : BasisExtension basis_tl)
    {exp : ℝ} {coef : PreMS basis_tl} {tl ms : PreMS (basis_hd :: basis_tl)}
    -- (ms : PreMS (basis_hd :: basis_tl))
    (h : ms = PreMS.cons exp coef tl) :
    ms.updateBasis (.keep _ ex_tl) =
    PreMS.cons exp (PreMS.updateBasis ex_tl coef) (tl.updateBasis (.keep _ ex_tl)) := by
  subst h
  simp [PreMS.updateBasis]

lemma updateBasis_insert_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (f : ℝ → ℝ)
    (ex_tl : BasisExtension (basis_hd :: basis_tl)) (ms : PreMS (basis_hd :: basis_tl)) :
    ms.updateBasis (.insert f ex_tl) = PreMS.cons 0 (ms.updateBasis ex_tl) PreMS.nil := by
  simp [PreMS.updateBasis]

lemma monomial_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    PreMS.monomial (basis_hd :: basis_tl) 0 = PreMS.cons 1 (PreMS.one basis_tl) PreMS.nil := by
  simp [PreMS.monomial]
  rfl

lemma monomial_succ {basis_hd : ℝ → ℝ} {basis_tl : Basis} (n : ℕ) :
    PreMS.monomial (basis_hd :: basis_tl) (n + 1) =
    PreMS.cons 0 (PreMS.monomial basis_tl n) PreMS.nil := by
  simp [PreMS.monomial]
  rfl

lemma monomial_rpow_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} (r : ℝ) :
    PreMS.monomial_rpow (basis_hd :: basis_tl) 0 r =
    PreMS.cons r (PreMS.one basis_tl) PreMS.nil := by
  simp [PreMS.monomial_rpow]

lemma monomial_rpow_succ {basis_hd : ℝ → ℝ} {basis_tl : Basis} (n : ℕ) (r : ℝ) :
    PreMS.monomial_rpow (basis_hd :: basis_tl) (n + 1) r =
    PreMS.cons 0 (PreMS.monomial_rpow basis_tl n r) PreMS.nil := by
  simp [PreMS.monomial_rpow]

lemma neg_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    (h : ms = PreMS.nil) : ms.neg = PreMS.nil := by
  subst h
  simp [PreMS.neg]

lemma neg_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    {exp : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h : ms = PreMS.cons exp coef tl) : ms.neg = PreMS.cons exp (coef.neg) tl.neg := by
  subst h
  simp [PreMS.neg]

lemma nil_add {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)}
    (h : X = PreMS.nil) : X.add Y = Y := by
  subst h
  exact PreMS.nil_add

lemma cons_add_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)}
    {exp : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (hX : X = PreMS.cons exp coef tl) (hY : Y = PreMS.nil) :
    X.add Y = PreMS.cons exp coef tl := by
  subst hX hY
  exact PreMS.add_nil

lemma cons_add_cons_right {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)}
    {X_exp : ℝ} {X_coef : PreMS basis_tl} {X_tl : PreMS (basis_hd :: basis_tl)}
    {Y_exp : ℝ} {Y_coef : PreMS basis_tl} {Y_tl : PreMS (basis_hd :: basis_tl)}
    (hX : X = PreMS.cons X_exp X_coef X_tl) (hY : Y = PreMS.cons Y_exp Y_coef Y_tl)
    (h_exp : X_exp < Y_exp) :
    X.add Y = PreMS.cons Y_exp Y_coef ((PreMS.cons X_exp X_coef X_tl).add Y_tl) := by
  subst hX hY
  convert PreMS.add_cons_right _
  simpa [leadingExp_cons]

lemma cons_add_cons_left {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)}
    {X_exp : ℝ} {X_coef : PreMS basis_tl} {X_tl : PreMS (basis_hd :: basis_tl)}
    {Y_exp : ℝ} {Y_coef : PreMS basis_tl} {Y_tl : PreMS (basis_hd :: basis_tl)}
    (hX : X = PreMS.cons X_exp X_coef X_tl) (hY : Y = PreMS.cons Y_exp Y_coef Y_tl)
    (h_exp : Y_exp < X_exp) :
    X.add Y = PreMS.cons X_exp X_coef ((X_tl.add (PreMS.cons Y_exp Y_coef Y_tl))) := by
  subst hX hY
  convert PreMS.add_cons_left _
  simpa [leadingExp_cons]

lemma cons_add_cons_both {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)}
    {X_exp : ℝ} {X_coef : PreMS basis_tl} {X_tl : PreMS (basis_hd :: basis_tl)}
    {Y_exp : ℝ} {Y_coef : PreMS basis_tl} {Y_tl : PreMS (basis_hd :: basis_tl)}
    (hX : X = PreMS.cons X_exp X_coef X_tl) (hY : Y = PreMS.cons Y_exp Y_coef Y_tl)
    (h_exp : X_exp = Y_exp) :
    X.add Y = PreMS.cons X_exp (X_coef.add Y_coef) ((X_tl.add Y_tl)) := by
  subst hX hY
  convert PreMS.add_cons_cons using 1
  simp [h_exp, add_def]
  rfl

lemma nil_mul {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)}
    (h : X = PreMS.nil) : X.mul Y = PreMS.nil := by
  subst h
  exact PreMS.nil_mul

lemma mul_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)}
    (h : Y = PreMS.nil) : X.mul Y = PreMS.nil := by
  subst h
  exact PreMS.mul_nil

lemma cons_mul_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)}
    {X_exp : ℝ} {X_coef : PreMS basis_tl} {X_tl : PreMS (basis_hd :: basis_tl)}
    {Y_exp : ℝ} {Y_coef : PreMS basis_tl} {Y_tl : PreMS (basis_hd :: basis_tl)}
    (hX : X = PreMS.cons X_exp X_coef X_tl) (hY : Y = PreMS.cons Y_exp Y_coef Y_tl) :
    X.mul Y = PreMS.cons (X_exp + Y_exp) (X_coef.mul Y_coef) ((mulMonomial Y_tl X_coef X_exp).add
      (X_tl.mul (PreMS.cons Y_exp Y_coef Y_tl))) := by
  subst hX hY
  exact PreMS.mul_cons_cons

lemma mulMonomial_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {B : PreMS (basis_hd :: basis_tl)}
    {M_exp : ℝ} {M_coef : PreMS basis_tl} (h : B = PreMS.nil) :
    PreMS.mulMonomial B M_coef M_exp = PreMS.nil := by
  subst h
  simp

lemma mulMonomial_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {B : PreMS (basis_hd :: basis_tl)}
    {M_exp : ℝ} {M_coef : PreMS basis_tl} {B_exp : ℝ} {B_coef : PreMS basis_tl}
    {B_tl : PreMS (basis_hd :: basis_tl)}
    (hB : B = PreMS.cons B_exp B_coef B_tl) :
    PreMS.mulMonomial B M_coef M_exp =
    PreMS.cons (M_exp + B_exp) (mul M_coef B_coef) (mulMonomial B_tl M_coef M_exp) := by
  subst hB
  simp [PreMS.mulMonomial]

lemma mulConst_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X : PreMS (basis_hd :: basis_tl)}
    {c : ℝ} (h : X = PreMS.nil) : X.mulConst c = PreMS.nil := by
  subst h
  simp [PreMS.mulConst]

lemma mulConst_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X : PreMS (basis_hd :: basis_tl)}
    {c : ℝ} {exp : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (hX : X = PreMS.cons exp coef tl) :
    X.mulConst c = PreMS.cons exp (coef.mulConst c) (tl.mulConst c) := by
  subst hX
  simp [PreMS.mulConst]

lemma apply_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    {s : LazySeries} (h : s = .nil) : s.apply ms = PreMS.nil := by
  subst h
  simp [LazySeries.apply_nil]

lemma apply_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    {s : LazySeries}
    {s_hd : ℝ} {s_tl : LazySeries} (h : s = Seq.cons s_hd s_tl) :
    s.apply ms = PreMS.cons 0 (PreMS.const _ s_hd) (ms.mul (s_tl.apply ms)) := by
  subst h
  simp [LazySeries.apply_cons]

lemma inv_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    (h : ms = PreMS.nil) : ms.inv = PreMS.nil := by
  subst h
  simp [PreMS.inv]

lemma inv_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    {exp : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h : ms = PreMS.cons exp coef tl) :
    ms.inv = PreMS.mulMonomial
      (PreMS.invSeries.apply (mulMonomial (neg tl) coef.inv (-exp))) coef.inv (-exp) := by
  subst h
  simp [PreMS.inv]

lemma pow_nil_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    (h : ms = PreMS.nil) {a : ℝ} (ha : a = 0) :
    ms.pow a = PreMS.cons 0 (PreMS.one _) PreMS.nil := by
  subst h ha
  simp [PreMS.pow, PreMS.one, PreMS.const]

lemma pow_nil_nonzero {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    (h : ms = PreMS.nil) {a : ℝ} (ha : a ≠ 0) :
    ms.pow a = PreMS.nil := by
  subst h
  simp [PreMS.pow]
  grind

lemma pow_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    {exp : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h : ms = PreMS.cons exp coef tl) (a : ℝ) :
    ms.pow a = PreMS.mulMonomial ((PreMS.powSeries a).apply
      (PreMS.mulMonomial tl coef.inv (-exp))) (coef.pow a) (exp * a) := by
  subst h
  simp [PreMS.pow]

lemma log_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    (logBasis : LogBasis (basis_hd :: basis_tl))
    (h : ms = PreMS.nil) : ms.log logBasis = PreMS.nil := by
  subst h
  unfold PreMS.log
  rfl

lemma log_cons_basis_tl_nil {basis_hd : ℝ → ℝ} {ms : PreMS [basis_hd]}
    {exp : ℝ} {coef : PreMS []} {tl : PreMS [basis_hd]}
    (h : ms = PreMS.cons exp coef tl)
    (logBasis : LogBasis [basis_hd]) : ms.log logBasis =
      (PreMS.const [basis_hd] (Real.log coef)).add
        (PreMS.logSeries.apply (PreMS.mulConst coef.toReal⁻¹ tl)) := by
  subst h
  unfold PreMS.log
  rfl

lemma log_cons_basis_tl_cons {basis_hd : ℝ → ℝ} {basis_tl_hd : ℝ → ℝ} {basis_tl_tl : Basis}
    {exp : ℝ} {coef : PreMS (basis_tl_hd :: basis_tl_tl)}
    {tl ms : PreMS (basis_hd :: basis_tl_hd :: basis_tl_tl)}
    (h : ms = PreMS.cons exp coef tl)
    (logBasis_tl : LogBasis (basis_tl_hd :: basis_tl_tl))
    (log_hd : PreMS (basis_tl_hd :: basis_tl_tl)) :
    ms.log (LogBasis.cons basis_hd basis_tl_hd basis_tl_tl logBasis_tl log_hd) =
    PreMS.add ((.cons 0 ((PreMS.log logBasis_tl coef).add <| log_hd.mulConst exp) .nil))
      (PreMS.logSeries.apply (PreMS.mulMonomial tl coef.inv (-exp))) := by
  subst h
  conv_lhs => unfold PreMS.log
  rfl

lemma exp_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    (h : ms = PreMS.nil) : ms.exp = PreMS.cons 0 (PreMS.one basis_tl) PreMS.nil := by
  subst h
  simp [PreMS.exp, PreMS.one, PreMS.const]

lemma exp_cons_of_lt {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    {exp : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h : ms = PreMS.cons exp coef tl)
    (h_lt : exp < 0) :
    ms.exp = PreMS.expSeries.apply (PreMS.cons exp coef tl) := by
  subst h
  simp [PreMS.exp, h_lt]

lemma exp_cons_of_not_lt {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    {exp : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h : ms = PreMS.cons exp coef tl)
    (h_not_lt : ¬ exp < 0) :
    ms.exp = (PreMS.expSeries.apply tl).mulMonomial coef.exp 0 := by
  subst h
  simp [PreMS.exp, h_not_lt]

end lemmas

/-- Normalizes a `PreMS` and returns a `Result`. -/
partial def normalizePreMSImp {basis_hd : Q(ℝ → ℝ)} {basis_tl : Q(Basis)}
    (ms : Q(PreMS ($basis_hd :: $basis_tl))) : TacticM (Result ms) := do
  match ms.getAppFnArgs with
  | (``PreMS.extendBasisEnd, #[(basis' : Q(Basis)), (f : Q(ℝ → ℝ)), (ms' : Q(PreMS $basis'))]) =>
    have : ($basis_hd :: $basis_tl) =Q $basis' ++ [$f] := ⟨⟩
    -- have : $ms =Q PreMS.extendBasisEnd $f $ms' := ⟨⟩
    match basis' with
    | ~q(List.nil) =>
      have : $basis_tl =Q [] := ⟨⟩
      let h' : Q(PreMS.extendBasisEnd $f $ms' = PreMS.cons 0 $ms' PreMS.nil) :=
        q(extendBasisEnd_const $f $ms')
      return ← consNormalizeCoef q(0) q($ms') q(PreMS.nil) (q($h') : Expr)
    | ~q(List.cons $basis_hd' $basis_tl') =>
      have : $basis_tl =Q $basis_tl' ++ [$f] := ⟨⟩
      let res := ← normalizePreMSImp (basis_hd := basis_hd') (basis_tl := basis_tl') ms'
      match res with
      | .nil h =>
        let h' : Q(PreMS.extendBasisEnd $f $ms' = PreMS.nil) := q(extendBasisEnd_nil $f $h)
        return .nil (q($h') : Expr)
      | .cons exp coef tl h =>
        let coef' : Q(PreMS $basis_tl) := q(PreMS.extendBasisEnd $f $coef)
        let tl' : Q(PreMS ($basis_hd :: $basis_tl)) := q(PreMS.extendBasisEnd $f $tl)
        let h' : Q(PreMS.extendBasisEnd $f $ms' = PreMS.cons $exp $coef' $tl') :=
          q(extendBasisEnd_cons $f $h)
        return ← consNormalize q($exp) q($coef') q($tl') (q($h') : Expr)
  | (``PreMS.updateBasis, #[(oldBasis : Q(Basis)), (ex : Q(BasisExtension $oldBasis)),
      (ms' : Q(PreMS $oldBasis))]) =>
    have : ($basis_hd :: $basis_tl) =Q ($ex).getBasis := ⟨⟩
    -- have : $ms =Q PreMS.updateBasis $ex $ms' := ⟨⟩
    let oldBasis' : Q(Basis) ← reduceBasis oldBasis
    have : $oldBasis =Q $oldBasis' := ⟨⟩
    match oldBasis, ex with
    | ~q(List.cons $oldBasis_hd $oldBasis_tl), ~q(BasisExtension.keep _ $ex_tl) =>
      let res := ← normalizePreMSImp (basis_hd := oldBasis_hd) (basis_tl := oldBasis_tl) ms'
      match res with
      | .nil h =>
        let h' : Q(PreMS.updateBasis $ex $ms' = PreMS.nil) := q(updateBasis_keep_nil $ex_tl $h)
        return .nil (q($h') : Expr)
      | .cons exp coef tl h =>
        have : ($ex_tl).getBasis =Q $basis_tl := ⟨⟩
        let coef' : Q(PreMS $basis_tl) := q(PreMS.updateBasis $ex_tl $coef)
        let tl' : Q(PreMS ($basis_hd :: $basis_tl)) := q(PreMS.updateBasis
          (basis := $oldBasis_hd :: $oldBasis_tl) (BasisExtension.keep $oldBasis_hd $ex_tl) $tl)
        let h' : Q(PreMS.updateBasis $ex $ms' = PreMS.cons $exp $coef' $tl') :=
          q(updateBasis_keep_cons $ex_tl $h)
        return ← consNormalize q($exp) q($coef') q($tl') (q($h') : Expr)
    | ~q(List.cons $oldBasis_hd $oldBasis_tl), ~q(BasisExtension.insert $f $ex_tl) =>
      have : ($ex_tl).getBasis =Q $basis_tl := ⟨⟩
      let coef' : Q(PreMS $basis_tl) := q(PreMS.updateBasis $ex_tl $ms')
      let h' : Q(PreMS.updateBasis $ex $ms' = PreMS.cons 0 $coef' PreMS.nil) :=
        q(updateBasis_insert_cons $f $ex_tl $ms')
      return ← consNormalizeCoef q(0) q($coef') q(PreMS.nil) (q($h') : Expr)
    | ~q(List.nil), _ =>
      have : ($ex).getBasis =Q ($basis_hd :: $basis_tl) := ⟨⟩
      let h' : Q(PreMS.updateBasis $ex $ms' = PreMS.const _ $ms') := q(updateBasis_const _ _)
      return ← consNormalizeCoef q(0) q(PreMS.const _ $ms') q(PreMS.nil) (q($h') : Expr)
    | _ =>
      panic!
        s!"normalizePreMS: unexpected oldBasis and ex: {← ppExpr oldBasis} and {← ppExpr ex}"
  | _ =>
  match ms with
  | ~q(PreMS.nil) => return .nil q(rfl)
  | ~q(PreMS.cons $exp $coef $tl) => return .cons q($exp) q($coef) q($tl) q(rfl)
  | ~q(PreMS.const _ $c) =>
    -- TODO: replace all nontrivial rfl-s with theorems
    return ← consNormalizeCoef q(0) q(PreMS.const _ $c) q(PreMS.nil) q(rfl)
  | ~q(PreMS.one _) =>
    return ← consNormalizeCoef q(0) q(PreMS.one _) q(PreMS.nil) q(rfl)
  | ~q(PreMS.monomial _ $n) =>
    match (← getNatValue? (← withTransparency .all <| reduce n)).get! with
    | 0 =>
      have : $n =Q 0 := ⟨⟩
      return ← consNormalizeCoef q(1) q(PreMS.one _) q(PreMS.nil) q(monomial_zero)
    | m + 1 =>
      have : $n =Q $m + 1 := ⟨⟩
      return ← consNormalizeCoef q(0) q(PreMS.monomial _ $m) q(PreMS.nil) q(monomial_succ $m)
  | ~q(PreMS.monomial_rpow _ $n $r) =>
    match (← getNatValue? (← withTransparency .all <| reduce n)).get! with
    | 0 =>
      have : $n =Q 0 := ⟨⟩
      return ← consNormalize q($r) q(PreMS.one _) q(PreMS.nil) q(monomial_rpow_zero $r)
    | m + 1 =>
      have : $n =Q $m + 1 := ⟨⟩
      return ← consNormalizeCoef q(0) q(PreMS.monomial_rpow _ $m $r) q(PreMS.nil)
        q(monomial_rpow_succ $m $r)
  | ~q(PreMS.neg $arg) =>
    let res ← normalizePreMSImp arg
    match res with
    | .nil h =>
      return .nil q(neg_nil $h)
    | .cons exp coef tl h =>
      return ← consNormalize q($exp) q(PreMS.neg $coef) q(PreMS.neg $tl) q(neg_cons $h)
  | ~q(PreMS.add $arg1 $arg2) =>
    let res1 ← normalizePreMSImp arg1
    let res2 ← normalizePreMSImp arg2
    match res1 with
    | .nil h1 =>
      return res2.cast q(nil_add $h1)
    | .cons exp1 coef1 tl1 h1 =>
      match res2 with
      | .nil h2 =>
        return ← consNormalize exp1 coef1 tl1 q(cons_add_nil $h1 $h2)
      | .cons exp2 coef2 tl2 h2 =>
        match ← compareTwoReals exp1 exp2 with
        | .lt h_exp =>
          return ← consNormalize exp2 coef2 q(PreMS.add (PreMS.cons $exp1 $coef1 $tl1) $tl2)
            q(cons_add_cons_right $h1 $h2 $h_exp)
        | .gt h_exp =>
          return ← consNormalize exp1 coef1 q(PreMS.add $tl1 (PreMS.cons $exp2 $coef2 $tl2))
            q(cons_add_cons_left $h1 $h2 $h_exp)
        | .eq h_exp =>
          return ← consNormalize exp1 q(PreMS.add $coef1 $coef2) q(PreMS.add $tl1 $tl2)
            q(cons_add_cons_both $h1 $h2 $h_exp)
  | ~q(PreMS.mul $arg1 $arg2) =>
    let res1 ← normalizePreMSImp arg1
    match res1 with
    | .nil h1 => return .nil q(nil_mul $h1)
    | .cons exp1 coef1 tl1 h1 =>
      let res2 ← normalizePreMSImp arg2
      match res2 with
      | .nil h2 => return .nil q(mul_nil $h2)
      | .cons exp2 coef2 tl2 h2 =>
        return ← consNormalize q($exp1 + $exp2) q(PreMS.mul $coef1 $coef2)
          q((mulMonomial $tl2 $coef1 $exp1).add
            (($tl1).mul (PreMS.cons $exp2 $coef2 $tl2))) q(cons_mul_cons $h1 $h2)
  | ~q(PreMS.mulMonomial $b $m_coef $m_exp) =>
    let res_b ← normalizePreMSImp b
    match res_b with
    | .nil hb =>
      return .nil q(mulMonomial_nil $hb)
    | .cons b_exp b_coef b_tl hb =>
      return ← consNormalize q($m_exp + $b_exp) q(PreMS.mul $m_coef $b_coef)
        q(PreMS.mulMonomial (basis_hd := $basis_hd) $b_tl $m_coef $m_exp) q(mulMonomial_cons $hb)
  | ~q(PreMS.mulConst $c $arg) =>
    let res ← normalizePreMSImp arg
    match res with
    | .nil h => return .nil q(mulConst_nil $h)
    | .cons exp coef tl h =>
      return ← consNormalize q($exp) q(PreMS.mulConst $c $coef) q(PreMS.mulConst $c $tl)
        q(mulConst_cons $h)
  | ~q(PreMS.LazySeries.apply $s $arg) =>
    let res_s ← normalizeLS s
    match res_s with
    | .nil hs =>
      return .nil q(apply_nil $hs)
    | .cons s_hd s_tl hs =>
      return ← consNormalizeCoef q(0) q(PreMS.const _ $s_hd)
        q(($arg).mul (PreMS.LazySeries.apply $s_tl $arg)) q(apply_cons $hs)
  | ~q(PreMS.inv $arg) =>
    let res ← normalizePreMSImp arg
    match res with
    | .nil h =>
      return .nil q(inv_nil $h)
    | .cons exp coef tl h =>
      let ms' : Q(PreMS ($basis_hd :: $basis_tl)) := q(mulMonomial
        (invSeries.apply (mulMonomial (neg $tl) ($coef).inv (-$exp))) ($coef).inv (-$exp))
      let res' ← normalizePreMSImp ms'
      return res'.cast q(inv_cons $h)
  | ~q(PreMS.pow $arg $a) =>
    let res ← normalizePreMSImp arg
    match res with
    | .nil h =>
      match ← checkZero a with
      | .eq ha => return ← consNormalizeCoef q(0) q(PreMS.one _) q(PreMS.nil) q(pow_nil_zero $h $ha)
      | .neq ha => return .nil q(pow_nil_nonzero $h $ha)
    | .cons exp coef tl h =>
      let ms' : Q(PreMS ($basis_hd :: $basis_tl)) := q(mulMonomial
        ((powSeries $a).apply (mulMonomial $tl ($coef).inv (-$exp))) (($coef).pow $a)
        ($exp * $a))
      let res' ← normalizePreMSImp ms'
      return res'.cast q(pow_cons $h $a)
  | ~q(PreMS.log $logBasis $arg) =>
    let res ← normalizePreMSImp arg
    match res with
    | .nil h =>
      return .nil q(log_nil $logBasis $h)
    | .cons exp coef tl h =>
      match basis_tl with
      | ~q(List.nil) =>
        let ms' : Q(PreMS ($basis_hd :: $basis_tl)) :=
          q(PreMS.add (PreMS.const _ (Real.log $coef)) <|
            PreMS.logSeries.apply (PreMS.mulConst ($coef).toReal⁻¹ $tl))
        let res' ← normalizePreMSImp ms'
        return res'.cast q(log_cons_basis_tl_nil $h $logBasis)
      | ~q(List.cons $basis_tl_hd $basis_tl_tl) =>
        let logBasis' ← reduceLogBasis logBasis
        have : $logBasis =Q $logBasis' := ⟨⟩
        let ~q(LogBasis.cons _ _ _ $logBasis_tl $log_hd) := logBasis'
          | panic! s!"normalizePreMS: unexpected logBasis: {← ppExpr logBasis'}"
        let logC := q(PreMS.log $logBasis_tl $coef)
        let ms' : Q(PreMS ($basis_hd :: $basis_tl)) :=
          q(PreMS.add (.cons 0 (($logC).add <| ($log_hd).mulConst $exp) .nil) <|
            logSeries.apply (mulMonomial $tl ($coef).inv (-$exp)))
        let res' ← normalizePreMSImp ms'
        return res'.cast q(log_cons_basis_tl_cons $h $logBasis_tl $log_hd)
  | ~q(PreMS.exp $arg) =>
    let res ← normalizePreMSImp arg
    match res with
    | .nil h =>
      return ← consNormalizeCoef q(0) q(PreMS.one _) q(PreMS.nil) q(exp_nil $h)
    | .cons exp coef tl h =>
      match ← checkLtZero exp with
      | .lt h_exp =>
        let ms' : Q(PreMS ($basis_hd :: $basis_tl)) :=
          q(PreMS.expSeries.apply (PreMS.cons $exp $coef $tl))
        let res' ← normalizePreMSImp ms'
        return res'.cast q(exp_cons_of_lt $h $h_exp)
      | .not_lt h_exp =>
        let ms' : Q(PreMS ($basis_hd :: $basis_tl)) :=
          q((expSeries.apply $tl).mulMonomial ($coef).exp 0)
        let res' ← normalizePreMSImp ms'
        return res'.cast q(exp_cons_of_not_lt $h $h_exp)
  | _ => panic! s!"normalizePreMS: unexpected ms: {← ppExpr ms}"

/-- Given `ms : PreMS basis`, return `ms'` that is normalized (either `PreMS.nil` or `PreMS.cons`),
and the proof of `ms' = ms`. -/
def normalizePreMS {basis : Q(Basis)}
    (ms : Q(PreMS $basis)) : TacticM ((ms' : Q(PreMS $basis)) × Q($ms = $ms')) := do
  match basis with
  | ~q(List.nil) => return ⟨ms, q(rfl)⟩
  | ~q(List.cons $basis_hd $basis_tl) =>
    let res ← normalizePreMSImp ms
    match res with
    | .nil h => return ⟨q(PreMS.nil), q($h)⟩
    | .cons exp coef tl h => return ⟨q(PreMS.cons $exp $coef $tl), q($h)⟩

end Normalization

end ComputeAsymptotics
