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
The main function is `normalizePreMS` that turns a given multiseries into a new one
in the normal form (`nil` or `cons`). The function `normalizeLS` does the same for `LazySeries`.
-/

set_option linter.style.longLine false

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
    (ms : Q(SeqMS $basis_hd $basis_tl))
| nil (h : Q($ms = .nil))
| cons (exp : Q(ℝ)) (coef : Q(PreMS $basis_tl)) (tl : Q(SeqMS $basis_hd $basis_tl))
  (h : Q($ms = .cons $exp $coef $tl))

lemma consNormalize_aux_congr_exp {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : SeqMS basis_hd basis_tl}
    {exp exp' : ℝ} {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl}
    (h : ms = .cons exp coef tl) (h_exp : exp = exp') :
    ms = .cons exp' coef tl := by
  rw [h, h_exp]

lemma consNormalize_aux_congr_coef {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : SeqMS basis_hd basis_tl}
    {exp : ℝ} {coef coef' : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl}
    (h : ms = .cons exp coef tl) (h_coef : coef = coef') :
    ms = .cons exp coef' tl := by
  rw [h, h_coef]

lemma consNormalize_aux_congr_exp_coef {basis_hd : ℝ → ℝ}
    {ms : SeqMS basis_hd []}
    {exp exp' : ℝ} {coef coef' : PreMS []} {tl : SeqMS basis_hd []}
    (h : ms = .cons exp coef tl) (h_exp : exp = exp') (h_coef : coef = coef') :
    ms = .cons exp' coef' tl := by
  rw [h, h_exp, h_coef]

/-- The same as `Result.cons` but also normalizes `exp` as a real number,
and the `coef` if `basis_tl` is `[]`. -/
def consNormalize {basis_hd : Q(ℝ → ℝ)} {basis_tl : Q(Basis)}
    {ms : Q(SeqMS $basis_hd $basis_tl)}
    (exp : Q(ℝ)) (coef : Q(PreMS $basis_tl)) (tl : Q(SeqMS $basis_hd $basis_tl))
    (h : Q($ms = .cons $exp $coef $tl)) :
    TacticM (Result ms) := do
  let ⟨exp', pf_exp⟩ ← normalizeReal exp
  match basis_tl with
  | ~q(List.nil) =>
    let ⟨coef', pf_coef⟩ ← normalizeReal q(($coef).toReal)
    return .cons q($exp') q($coef') q($tl) q(consNormalize_aux_congr_exp_coef $h $pf_exp $pf_coef)
  | _ =>
    return .cons q($exp') q($coef) q($tl) q(consNormalize_aux_congr_exp $h $pf_exp)

/-- The same as `Result.cons` but also normalizes the `coef` if `basis_tl` is `[]`. -/
def consNormalizeCoef {basis_hd : Q(ℝ → ℝ)} {basis_tl : Q(Basis)}
    {ms : Q(SeqMS $basis_hd $basis_tl)}
    (exp : Q(ℝ)) (coef : Q(PreMS $basis_tl)) (tl : Q(SeqMS $basis_hd $basis_tl))
    (h : Q($ms = .cons $exp $coef $tl)) :
    TacticM (Result ms) := do
  match basis_tl with
  | ~q(List.nil) =>
    let ⟨coef', pf_coef⟩ ← normalizeReal coef
    return .cons q($exp) q($coef') q($tl) q(consNormalize_aux_congr_coef $h $pf_coef)
  | _ =>
    return .cons q($exp) q($coef) q($tl) q($h)

/-- Turns a `Result` for `ms` into a `Result` for `ms'` given the proof of `ms' = ms`. -/
def Result.cast {basis_hd : Q(ℝ → ℝ)} {basis_tl : Q(Basis)}
    {ms ms' : Q(SeqMS $basis_hd $basis_tl)} (res : Result ms) (h : Q($ms' = $ms)) :
    Result ms' :=
  match res with
  | .nil h_ms => .nil q(($h).trans $h_ms)
  | .cons exp coef tl h_ms => .cons exp coef tl q(($h).trans $h_ms)

section lemmas

-- lemma extendBasisEnd_const (f : ℝ → ℝ) (ms : PreMS []) :
--     SeqMS.extendBasisEnd f ms = .cons 0 ms .nil := by
--   simp [PreMS.extendBasisEnd, PreMS.const]

lemma extendBasisEnd_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} (f : ℝ → ℝ)
    {ms : SeqMS basis_hd basis_tl} (h : ms = .nil) :
    SeqMS.extendBasisEnd f ms = .nil := by
  subst h
  rw [SeqMS.extendBasisEnd_nil]

lemma extendBasisEnd_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} (f : ℝ → ℝ)
    {exp : ℝ} {coef : PreMS basis_tl} {tl ms : SeqMS basis_hd basis_tl}
    (h : ms = .cons exp coef tl) :
    SeqMS.extendBasisEnd f ms =
    .cons exp (PreMS.extendBasisEnd f coef) (SeqMS.extendBasisEnd f tl) := by
  subst h
  simp [SeqMS.extendBasisEnd]

-- TODO: rename
lemma updateBasis_keep_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl}
    (ex_tl : BasisExtension basis_tl)
    (h : ms = .nil) :
    ms.updateBasis ex_tl = .nil := by
  subst h
  rw [SeqMS.updateBasis_nil]

-- TODO: rename
lemma updateBasis_keep_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (ex_tl : BasisExtension basis_tl)
    {exp : ℝ} {coef : PreMS basis_tl} {tl ms : SeqMS basis_hd basis_tl}
    (h : ms = .cons exp coef tl) :
    ms.updateBasis ex_tl =
    .cons exp (PreMS.updateBasis ex_tl coef) (tl.updateBasis ex_tl) := by
  subst h
  rw [SeqMS.updateBasis_cons]

-- lemma updateBasis_insert_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis}
--     (f : ℝ → ℝ)
--     (ex_tl : BasisExtension (basis_hd :: basis_tl)) (ms : PreMS (basis_hd :: basis_tl)) :
--     ms.updateBasis (.insert f ex_tl) = PreMS.cons 0 (ms.updateBasis ex_tl) PreMS.nil := by
--   simp [PreMS.updateBasis]

lemma monomial_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    SeqMS.monomial basis_hd basis_tl 0 = .cons 1 one .nil := by
  simp [SeqMS.monomial, SeqMS.monomialRpow]

lemma monomial_succ {basis_hd : ℝ → ℝ} {basis_tl : Basis} (n : ℕ) :
    SeqMS.monomial basis_hd basis_tl (n + 1) =
    .cons 0 (PreMS.monomial basis_tl n) .nil := by
  simp [SeqMS.monomial, SeqMS.monomialRpow]
  rfl

lemma monomialRpow_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} (r : ℝ) :
    SeqMS.monomialRpow basis_hd basis_tl 0 r =
    .cons r one .nil := by
  simp [SeqMS.monomialRpow]

lemma monomialRpow_succ {basis_hd : ℝ → ℝ} {basis_tl : Basis} (n : ℕ) (r : ℝ) :
    SeqMS.monomialRpow basis_hd basis_tl (n + 1) r =
    .cons 0 (PreMS.monomialRpow basis_tl n r) .nil := by
  simp [SeqMS.monomialRpow]

lemma neg_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl}
    (h : ms = .nil) : ms.neg = .nil := by
  subst h
  simp [SeqMS.neg]

lemma neg_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl}
    {exp : ℝ} {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl}
    (h : ms = .cons exp coef tl) : ms.neg = .cons exp (coef.neg) tl.neg := by
  subst h
  simp

lemma nil_add {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : SeqMS basis_hd basis_tl}
    (h : X = .nil) : X.add Y = Y := by
  subst h
  exact SeqMS.nil_add

lemma cons_add_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : SeqMS basis_hd basis_tl}
    {exp : ℝ} {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl}
    (hX : X = .cons exp coef tl) (hY : Y = .nil) :
    X.add Y = .cons exp coef tl := by
  subst hX hY
  exact SeqMS.add_nil

lemma cons_add_cons_right {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : SeqMS basis_hd basis_tl}
    {X_exp : ℝ} {X_coef : PreMS basis_tl} {X_tl : SeqMS basis_hd basis_tl}
    {Y_exp : ℝ} {Y_coef : PreMS basis_tl} {Y_tl : SeqMS basis_hd basis_tl}
    (hX : X = .cons X_exp X_coef X_tl) (hY : Y = .cons Y_exp Y_coef Y_tl)
    (h_exp : X_exp < Y_exp) :
    X.add Y = .cons Y_exp Y_coef ((SeqMS.cons X_exp X_coef X_tl).add Y_tl) := by
  subst hX hY
  convert SeqMS.add_cons_right _
  simpa [SeqMS.leadingExp_cons]

lemma cons_add_cons_left {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : SeqMS basis_hd basis_tl}
    {X_exp : ℝ} {X_coef : PreMS basis_tl} {X_tl : SeqMS basis_hd basis_tl}
    {Y_exp : ℝ} {Y_coef : PreMS basis_tl} {Y_tl : SeqMS basis_hd basis_tl}
    (hX : X = .cons X_exp X_coef X_tl) (hY : Y = .cons Y_exp Y_coef Y_tl)
    (h_exp : Y_exp < X_exp) :
    X.add Y = .cons X_exp X_coef ((X_tl.add (.cons Y_exp Y_coef Y_tl))) := by
  subst hX hY
  convert SeqMS.add_cons_left _
  simpa [SeqMS.leadingExp_cons]

lemma cons_add_cons_both {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : SeqMS basis_hd basis_tl}
    {X_exp : ℝ} {X_coef : PreMS basis_tl} {X_tl : SeqMS basis_hd basis_tl}
    {Y_exp : ℝ} {Y_coef : PreMS basis_tl} {Y_tl : SeqMS basis_hd basis_tl}
    (hX : X = .cons X_exp X_coef X_tl) (hY : Y = .cons Y_exp Y_coef Y_tl)
    (h_exp : X_exp = Y_exp) :
    X.add Y = .cons X_exp (X_coef.add Y_coef) ((X_tl.add Y_tl)) := by
  subst hX hY
  convert SeqMS.add_cons_cons using 1
  simp [h_exp, add_def]
  rfl

lemma nil_mul {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : SeqMS basis_hd basis_tl}
    (h : X = .nil) : X.mul Y = .nil := by
  subst h
  exact SeqMS.nil_mul

lemma mul_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : SeqMS basis_hd basis_tl}
    (h : Y = .nil) : X.mul Y = .nil := by
  subst h
  exact SeqMS.mul_nil

lemma cons_mul_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : SeqMS basis_hd basis_tl}
    {X_exp : ℝ} {X_coef : PreMS basis_tl} {X_tl : SeqMS basis_hd basis_tl}
    {Y_exp : ℝ} {Y_coef : PreMS basis_tl} {Y_tl : SeqMS basis_hd basis_tl}
    (hX : X = .cons X_exp X_coef X_tl) (hY : Y = .cons Y_exp Y_coef Y_tl) :
    X.mul Y = .cons (X_exp + Y_exp) (X_coef.mul Y_coef) ((X_tl.mulMonomial Y_coef Y_exp).add
      ((SeqMS.cons X_exp X_coef X_tl).mul Y_tl)) := by
  subst hX hY
  exact SeqMS.mul_cons_cons

lemma mulMonomial_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {B : SeqMS basis_hd basis_tl}
    {M_exp : ℝ} {M_coef : PreMS basis_tl} (h : B = .nil) :
    SeqMS.mulMonomial B M_coef M_exp = .nil := by
  subst h
  simp

lemma mulMonomial_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {B : SeqMS basis_hd basis_tl}
    {M_exp : ℝ} {M_coef : PreMS basis_tl} {B_exp : ℝ} {B_coef : PreMS basis_tl}
    {B_tl : SeqMS basis_hd basis_tl}
    (hB : B = .cons B_exp B_coef B_tl) :
    SeqMS.mulMonomial B M_coef M_exp =
    .cons (B_exp + M_exp) (B_coef.mul M_coef) (B_tl.mulMonomial M_coef M_exp) := by
  subst hB
  simp [SeqMS.mulMonomial]

lemma mulConst_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X : SeqMS basis_hd basis_tl}
    {c : ℝ} (h : X = .nil) : X.mulConst c = .nil := by
  subst h
  simp

lemma mulConst_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X : SeqMS basis_hd basis_tl}
    {c : ℝ} {exp : ℝ} {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl}
    (hX : X = .cons exp coef tl) :
    X.mulConst c = .cons exp (coef.mulConst c) (tl.mulConst c) := by
  subst hX
  simp

lemma apply_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl}
    {s : LazySeries} (h : s = .nil) : ms.apply s = .nil := by
  subst h
  simp [SeqMS.apply_nil]

lemma apply_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl}
    {s : LazySeries}
    {s_hd : ℝ} {s_tl : LazySeries} (h : s = Seq.cons s_hd s_tl) :
    ms.apply s = .cons 0 (PreMS.const _ s_hd) (ms.mul (ms.apply s_tl)) := by
  subst h
  simp [SeqMS.apply_cons]

lemma inv_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl}
    (h : ms = .nil) : ms.inv = .nil := by
  subst h
  simp [SeqMS.inv]

lemma inv_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl}
    {exp : ℝ} {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl}
    (h : ms = .cons exp coef tl) :
    ms.inv = .mulMonomial
      ((tl.neg.mulMonomial coef.inv (-exp)).apply invSeries) coef.inv (-exp) := by
  subst h
  simp [SeqMS.inv]

lemma pow_nil_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl}
    (h : ms = .nil) {a : ℝ} (ha : a = 0) :
    ms.pow a = .cons 0 PreMS.one .nil := by
  subst h ha
  simp [SeqMS.pow, PreMS.one, SeqMS.one, SeqMS.const]

lemma pow_nil_nonzero {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl}
    (h : ms = .nil) {a : ℝ} (ha : a ≠ 0) :
    ms.pow a = .nil := by
  subst h
  simp [SeqMS.pow]
  grind

lemma pow_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl}
    {exp : ℝ} {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl}
    (h : ms = .cons exp coef tl) (a : ℝ) :
    ms.pow a = SeqMS.mulMonomial ((tl.mulMonomial coef.inv (-exp)).apply
      (PreMS.powSeries a)) (coef.pow a) (exp * a) := by
  subst h
  simp [SeqMS.pow]

lemma log_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl}
    (logBasis : LogBasis (basis_hd :: basis_tl))
    (h : ms = .nil) : ms.log logBasis = .nil := by
  subst h
  unfold SeqMS.log
  rfl

lemma log_cons_basis_tl_nil {basis_hd : ℝ → ℝ} {ms : SeqMS basis_hd []}
    {exp : ℝ} {coef : PreMS []} {tl : SeqMS basis_hd []}
    (h : ms = .cons exp coef tl)
    (logBasis : LogBasis [basis_hd]) :
    ms.log logBasis =
      (SeqMS.const basis_hd [] (Real.log coef.toReal)).add
        ((tl.mulConst coef.toReal⁻¹ ).apply logSeries) := by
  subst h
  unfold SeqMS.log
  rfl

lemma log_cons_basis_tl_cons {basis_hd : ℝ → ℝ} {basis_tl_hd : ℝ → ℝ} {basis_tl_tl : Basis}
    {exp : ℝ} {coef : PreMS (basis_tl_hd :: basis_tl_tl)}
    {tl ms : SeqMS basis_hd (basis_tl_hd :: basis_tl_tl)}
    (h : ms = .cons exp coef tl)
    (logBasis_tl : LogBasis (basis_tl_hd :: basis_tl_tl))
    (log_hd : PreMS (basis_tl_hd :: basis_tl_tl)) :
    ms.log (LogBasis.cons basis_hd basis_tl_hd basis_tl_tl logBasis_tl log_hd) =
    SeqMS.add ((.cons 0 ((coef.log logBasis_tl).add <| log_hd.mulConst exp) .nil))
      ((tl.mulMonomial  coef.inv (-exp)).apply logSeries) := by
  subst h
  conv_lhs => unfold SeqMS.log
  rfl

lemma exp_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl}
    (h : ms = .nil) : ms.exp = .cons 0 PreMS.one .nil := by
  subst h
  simp [SeqMS.exp, PreMS.one, SeqMS.one, SeqMS.const]

lemma exp_cons_of_lt {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl}
    {exp : ℝ} {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl}
    (h : ms = .cons exp coef tl)
    (h_lt : exp < 0) :
    ms.exp = (SeqMS.cons exp coef tl).apply expSeries := by
  subst h
  simp [SeqMS.exp, h_lt]

lemma exp_cons_of_not_lt {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl}
    {exp : ℝ} {coef : PreMS basis_tl} {tl : SeqMS basis_hd basis_tl}
    (h : ms = .cons exp coef tl)
    (h_not_lt : ¬ exp < 0) :
    ms.exp = ((tl.apply expSeries).mulMonomial coef.exp 0) := by
  subst h
  simp [SeqMS.exp, h_not_lt]

end lemmas


-- TODO: replace all nontrivial rfl-s with theorems
/-- Normalizes a `SeqMS` and returns a `Result`. -/
partial def normalizeSeqMSImp {basis_hd : Q(ℝ → ℝ)} {basis_tl : Q(Basis)}
    (ms : Q(SeqMS $basis_hd $basis_tl)) : TacticM (Result ms) := do
  match ms.getAppFnArgs with
  | (``SeqMS.extendBasisEnd, #[(basis_hd' : Q(ℝ → ℝ)), (basis_tl' : Q(Basis)), (f : Q(ℝ → ℝ)),
    (ms' : Q(SeqMS $basis_hd' $basis_tl'))]) =>
    have : $basis_hd =Q $basis_hd' := ⟨⟩
    have : $basis_tl =Q $basis_tl' ++ [$f] := ⟨⟩
    let res ← normalizeSeqMSImp q($ms')
    match res with
    | .nil h =>
      return .nil (q(extendBasisEnd_nil $f $h) : Expr)
    | .cons exp coef tl h =>
      return ← consNormalize q($exp) q(($coef).extendBasisEnd $f) q(($tl).extendBasisEnd $f) (q(extendBasisEnd_cons $f $h) : Expr)
  | (``SeqMS.updateBasis, #[(oldBasis_hd : Q(ℝ → ℝ)), (oldBasis_tl : Q(Basis)), (ex : Q(BasisExtension $oldBasis_tl)),
      (ms' : Q(SeqMS $oldBasis_hd $oldBasis_tl))]) =>
    have : $oldBasis_hd =Q $basis_hd := ⟨⟩
    have : $basis_tl =Q ($ex).getBasis := ⟨⟩
    let res ← normalizeSeqMSImp q($ms')
    match res with
    | .nil h =>
      return .nil (q(updateBasis_keep_nil $ex $h) : Expr)
    | .cons exp coef tl h =>
      return ← consNormalize q($exp) q(($coef).updateBasis $ex) q(($tl).updateBasis $ex) (q(updateBasis_keep_cons $ex $h) : Expr)
  | _ =>
  match ms with
  | ~q(SeqMS.nil) => return .nil q(rfl)
  | ~q(SeqMS.cons $exp $coef $tl) => return .cons q($exp) q($coef) q($tl) q(rfl)
  | ~q(SeqMS.const _ _ $c) =>
    return ← consNormalizeCoef q(0) q(PreMS.const _ $c) q(SeqMS.nil) q(SeqMS.const.eq_def _ _ _)
  | ~q(SeqMS.one) =>
    return ← consNormalizeCoef q(0) q(PreMS.one) q(SeqMS.nil) q(SeqMS.const.eq_def _ _ _)
  | ~q(SeqMS.monomial _ _ $n) =>
    match (← getNatValue? (← withTransparency .all <| reduce n)).get! with
    | 0 =>
      have : $n =Q 0 := ⟨⟩
      return ← consNormalizeCoef q(1) q(PreMS.one) q(SeqMS.nil) q(monomial_zero)
    | m + 1 =>
      have : $n =Q $m + 1 := ⟨⟩
      return ← consNormalizeCoef q(0) q(PreMS.monomial _ $m) q(SeqMS.nil) q(monomial_succ $m)
  | ~q(SeqMS.monomialRpow _ _ $n $r) =>
    match (← getNatValue? (← withTransparency .all <| reduce n)).get! with
    | 0 =>
      have : $n =Q 0 := ⟨⟩
      return ← consNormalize q($r) q(PreMS.one) q(SeqMS.nil) q(monomialRpow_zero $r)
    | m + 1 =>
      have : $n =Q $m + 1 := ⟨⟩
      return ← consNormalizeCoef q(0) q(PreMS.monomialRpow _ $m $r) q(SeqMS.nil)
        q(monomialRpow_succ $m $r)
  | ~q(SeqMS.neg $arg) =>
    let res ← normalizeSeqMSImp arg
    match res with
    | .nil h =>
      return .nil q(neg_nil $h)
    | .cons exp coef tl h =>
      return ← consNormalize q($exp) q(PreMS.neg $coef) q(SeqMS.neg $tl) q(neg_cons $h)
  | ~q(SeqMS.add $arg1 $arg2) =>
    let res1 ← normalizeSeqMSImp arg1
    let res2 ← normalizeSeqMSImp arg2
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
          return ← consNormalize exp2 coef2 q(SeqMS.add (SeqMS.cons $exp1 $coef1 $tl1) $tl2)
            q(cons_add_cons_right $h1 $h2 $h_exp)
        | .gt h_exp =>
          return ← consNormalize exp1 coef1 q(SeqMS.add $tl1 (SeqMS.cons $exp2 $coef2 $tl2))
            q(cons_add_cons_left $h1 $h2 $h_exp)
        | .eq h_exp =>
          return ← consNormalize exp1 q(PreMS.add $coef1 $coef2) q(SeqMS.add $tl1 $tl2)
            q(cons_add_cons_both $h1 $h2 $h_exp)
  | ~q(SeqMS.mul $arg1 $arg2) =>
    let res1 ← normalizeSeqMSImp arg1
    match res1 with
    | .nil h1 => return .nil q(nil_mul $h1)
    | .cons exp1 coef1 tl1 h1 =>
      let res2 ← normalizeSeqMSImp arg2
      match res2 with
      | .nil h2 => return .nil q(mul_nil $h2)
      | .cons exp2 coef2 tl2 h2 =>
        return ← consNormalize q($exp1 + $exp2) q(PreMS.mul $coef1 $coef2)
          q((SeqMS.mulMonomial $tl1 $coef2 $exp2).add
            ((SeqMS.cons $exp1 $coef1 $tl1).mul $tl2)) q(cons_mul_cons $h1 $h2)
  | ~q(SeqMS.mulMonomial $b $m_coef $m_exp) =>
    let res_b ← normalizeSeqMSImp b
    match res_b with
    | .nil hb =>
      return .nil q(mulMonomial_nil $hb)
    | .cons b_exp b_coef b_tl hb =>
      return ← consNormalize q($b_exp + $m_exp) q(PreMS.mul $b_coef $m_coef)
        q(SeqMS.mulMonomial (basis_hd := $basis_hd) $b_tl $m_coef $m_exp) q(mulMonomial_cons $hb)
  | ~q(SeqMS.mulConst $c $arg) =>
    let res ← normalizeSeqMSImp arg
    match res with
    | .nil h => return .nil q(mulConst_nil $h)
    | .cons exp coef tl h =>
      return ← consNormalize q($exp) q(PreMS.mulConst $c $coef) q(SeqMS.mulConst $c $tl)
        q(mulConst_cons $h)
  | ~q(SeqMS.apply $s $arg) =>
    let res_s ← normalizeLS s
    match res_s with
    | .nil hs =>
      return .nil q(apply_nil $hs)
    | .cons s_hd s_tl hs =>
      return ← consNormalizeCoef q(0) q(PreMS.const _ $s_hd)
        q(($arg).mul (SeqMS.apply $s_tl $arg)) q(apply_cons $hs)
  | ~q(SeqMS.inv $arg) =>
    let res ← normalizeSeqMSImp arg
    match res with
    | .nil h =>
      return .nil q(inv_nil $h)
    | .cons exp coef tl h =>
      let ms' : Q(SeqMS $basis_hd $basis_tl) := q(SeqMS.mulMonomial
        (((SeqMS.neg $tl).mulMonomial ($coef).inv (-$exp)).apply invSeries) ($coef).inv (-$exp))
      let res' ← normalizeSeqMSImp ms'
      return res'.cast q(inv_cons $h)
  | ~q(SeqMS.pow $arg $a) =>
    let res ← normalizeSeqMSImp arg
    match res with
    | .nil h =>
      match ← CompareReal.checkZero a with
      | .eq ha => return ← consNormalizeCoef q(0) q(PreMS.one) q(SeqMS.nil) q(pow_nil_zero $h $ha)
      | .neq ha => return .nil q(pow_nil_nonzero $h $ha)
    | .cons exp coef tl h =>
      let ms' : Q(SeqMS $basis_hd $basis_tl) := q(SeqMS.mulMonomial
        ((SeqMS.mulMonomial $tl ($coef).inv (-$exp)).apply (powSeries $a)) (($coef).pow $a)
        ($exp * $a))
      let res' ← normalizeSeqMSImp ms'
      return res'.cast q(pow_cons $h $a)
  | ~q(SeqMS.log $logBasis $arg) =>
    let res ← normalizeSeqMSImp arg
    match res with
    | .nil h =>
      return .nil q(log_nil $logBasis $h)
    | .cons exp coef tl h =>
      match basis_tl with
      | ~q(List.nil) =>
        let ms' : Q(SeqMS $basis_hd $basis_tl) :=
          q(SeqMS.add (SeqMS.const _ _ (Real.log ($coef).toReal)) <|
            (SeqMS.mulConst ($coef).toReal⁻¹ $tl).apply logSeries)
        let res' ← normalizeSeqMSImp ms'
        return res'.cast q(log_cons_basis_tl_nil $h $logBasis)
      | ~q(List.cons $basis_tl_hd $basis_tl_tl) =>
        let logBasis' ← reduceLogBasis logBasis
        have : $logBasis =Q $logBasis' := ⟨⟩
        let ~q(LogBasis.cons _ _ _ $logBasis_tl $log_hd) := logBasis'
          | panic! s!"normalizeSeqMS: unexpected logBasis: {← ppExpr logBasis'}"
        let logC := q(PreMS.log $logBasis_tl $coef)
        let ms' : Q(SeqMS $basis_hd $basis_tl) :=
          q(SeqMS.add (.cons 0 (($logC).add <| ($log_hd).mulConst $exp) .nil) <|
            (SeqMS.mulMonomial $tl ($coef).inv (-$exp)).apply logSeries)
        let res' ← normalizeSeqMSImp ms'
        return res'.cast q(log_cons_basis_tl_cons $h $logBasis_tl $log_hd)
  | ~q(SeqMS.exp $arg) =>
    let res ← normalizeSeqMSImp arg
    match res with
    | .nil h =>
      return ← consNormalizeCoef q(0) q(PreMS.one) q(SeqMS.nil) q(exp_nil $h)
    | .cons exp coef tl h =>
      match ← checkLtZero exp with
      | .lt h_exp =>
        let ms' : Q(SeqMS $basis_hd $basis_tl) :=
          q((SeqMS.cons $exp $coef $tl).apply expSeries)
        let res' ← normalizeSeqMSImp ms'
        return res'.cast q(exp_cons_of_lt $h $h_exp)
      | .not_lt h_exp =>
        let ms' : Q(SeqMS $basis_hd $basis_tl) :=
          q((SeqMS.apply expSeries $tl).mulMonomial ($coef).exp 0)
        let res' ← normalizeSeqMSImp ms'
        return res'.cast q(exp_cons_of_not_lt $h $h_exp)
  | _ => panic! s!"normalizeSeqMS: unexpected ms: {← ppExpr ms}"

partial def getFun {basis : Q(Basis)} (ms : Q(PreMS $basis)) :
    MetaM <| (f : Q(ℝ → ℝ)) × Q(($ms).toFun = $f) := do
  match ms.getAppFnArgs with
  | (``PreMS.extendBasisEnd, #[(basis' : Q(Basis)), (f : Q(ℝ → ℝ)), (ms' : Q(PreMS $basis'))]) =>
    let ⟨f', h_f'⟩ ← getFun q($ms')
    return ⟨q($f'), q(sorry)⟩
  | (``PreMS.updateBasis, #[(oldBasis : Q(Basis)), (ex : Q(BasisExtension $oldBasis)),
      (ms' : Q(PreMS $oldBasis))]) =>
    let ⟨f, h_f⟩ ← getFun q($ms')
    return ⟨q($f), q(sorry)⟩
  | _ =>
  match basis with
  | ~q(List.nil) => return ⟨q(fun _ ↦ ($ms).toReal), q(by simp)⟩
  | ~q(List.cons $basis_hd $basis_tl) =>
  match ms with
  | ~q(PreMS.mk $s $f) => return ⟨q($f), q(PreMS.mk_toFun)⟩
  | ~q(PreMS.replaceFun $ms $f) =>
    return ⟨q($f), q(PreMS.replaceFun_toFun _ _)⟩
  | ~q(PreMS.const _ $c) => return ⟨q(fun _ ↦ $c), q(PreMS.const_toFun')⟩
  | ~q(PreMS.one) => return ⟨q(1), q(PreMS.one_toFun)⟩
  | ~q(PreMS.monomial _ $n) =>
    let nNat := (← getNatValue? (← withTransparency .all <| reduce n)).get!
    let nFin ← mkFin q($n) q(List.length ($basis_hd :: $basis_tl))
    let f ← getNth q($basis_hd :: $basis_tl) nNat

    -- haveI : Fin.val (n := List.length ($basis_hd :: $basis_tl)) $nFin =Q $nNat := ⟨⟩
    -- haveI : $f =Q ($basis_hd :: $basis_tl)[$nFin] := ⟨⟩
    return ⟨q($f), (q(PreMS.monomial_toFun (basis := $basis_hd :: $basis_tl) (n := $nFin)) : Expr)⟩
  --   match (← getNatValue? (← withTransparency .all <| reduce n)).get! with
  --   | 0 =>
  --     have : $n =Q 0 := ⟨⟩
  --     return ← consNormalizeCoef q(1) q(SeqMS.one _) q(SeqMS.nil) q(monomial_zero)
  --   | m + 1 =>
  --     have : $n =Q $m + 1 := ⟨⟩
  --     return ← consNormalizeCoef q(0) q(SeqMS.monomial _ $m) q(SeqMS.nil) q(monomial_succ $m)
  | ~q(PreMS.monomialRpow _ $n $r) =>
    let nNat := (← getNatValue? (← withTransparency .all <| reduce n)).get!
    let nFin ← mkFin q($n) q(List.length ($basis_hd :: $basis_tl))
    let f ← getNth q($basis_hd :: $basis_tl) nNat
    -- haveI : Fin.val (n := List.length ($basis_hd :: $basis_tl)) $nFin =Q $nNat := ⟨⟩
    -- haveI : $f =Q ($basis_hd :: $basis_tl)[$nFin] := ⟨⟩
    return ⟨q($f ^ $r), (q(PreMS.monomialRpow_toFun (basis := $basis_hd :: $basis_tl) (n := $nFin) (r := $r)) : Expr)⟩
  | ~q(PreMS.neg $arg) =>
    let ⟨f, h⟩ ← getFun q($arg)
    return ⟨q(-$f), q($h ▸ PreMS.neg_toFun)⟩
  | ~q(PreMS.add $arg₁ $arg₂) =>
    let ⟨f₁, h₁⟩ ← getFun q($arg₁)
    let ⟨f₂, h₂⟩ ← getFun q($arg₂)
    return ⟨q($f₁ + $f₂), q($h₁ ▸ $h₂ ▸ PreMS.add_toFun)⟩
  | ~q(PreMS.mul $arg₁ $arg₂) =>
    let ⟨f₁, h₁⟩ ← getFun q($arg₁)
    let ⟨f₂, h₂⟩ ← getFun q($arg₂)
    return ⟨q($f₁ * $f₂), q($h₁ ▸ $h₂ ▸ PreMS.mul_toFun)⟩
  | ~q(PreMS.mulMonomial $b $m_coef $m_exp) =>
    let ⟨f₁, h₁⟩ ← getFun q($b)
    let ⟨f₂, h₂⟩ ← getFun q($m_coef)
    return ⟨q($f₁ * $basis_hd ^ $m_exp * $f₂), q($h₁ ▸ $h₂ ▸ PreMS.mulMonomial_toFun)⟩
  | ~q(PreMS.mulConst $c $arg) =>
    let ⟨f, h⟩ ← getFun q($arg)
    return ⟨q($c • $f), q($h ▸ PreMS.mulConst_toFun)⟩
  | ~q(PreMS.apply $s $arg) =>
    let ⟨f, h⟩ ← getFun q($arg)
    return ⟨q(($s).toFun ∘ $f), q($h ▸ PreMS.apply_toFun)⟩
  | ~q(PreMS.inv $arg) =>
    let ⟨f, h⟩ ← getFun q($arg)
    return ⟨q($f⁻¹), q($h ▸ PreMS.inv_toFun)⟩
  | ~q(PreMS.pow $arg $a) =>
    let ⟨f, h⟩ ← getFun q($arg)
    return ⟨q($f ^ $a), q($h ▸ PreMS.pow_toFun)⟩
  | ~q(PreMS.npow $arg $a) =>
    let ⟨f, h⟩ ← getFun q($arg)
    return ⟨q($f ^ $a), q($h ▸ PreMS.npow_toFun)⟩
  | ~q(PreMS.zpow $arg $a) =>
    let ⟨f, h⟩ ← getFun q($arg)
    return ⟨q($f ^ $a), q($h ▸ PreMS.zpow_toFun)⟩
  | ~q(PreMS.log $logBasis $arg) =>
    let ⟨f, h⟩ ← getFun q($arg)
    return ⟨q(Real.log ∘ $f), q($h ▸ PreMS.log_toFun)⟩
  | ~q(PreMS.exp $arg) =>
    let ⟨f, h⟩ ← getFun q($arg)
    return ⟨q(Real.exp ∘ $f), q($h ▸ PreMS.exp_toFun)⟩
  | _ => panic! s!"getFun: unexpected ms: {← ppExpr ms}"

partial def getSeq {basis_hd : Q(ℝ → ℝ)} {basis_tl : Q(Basis)} (ms : Q(PreMS ($basis_hd :: $basis_tl))) :
    MetaM <| (s : Q(SeqMS $basis_hd $basis_tl)) × Q(($ms).seq = $s) := do
  match ms.getAppFnArgs with
  | (``PreMS.extendBasisEnd, #[(basis' : Q(Basis)), (f : Q(ℝ → ℝ)), (ms' : Q(PreMS $basis'))]) =>
    have : ($basis_hd :: $basis_tl) =Q $basis' ++ [$f] := ⟨⟩
    -- have : $ms =Q PreMS.extendBasisEnd $f $ms' := ⟨⟩
    match basis' with
    | ~q(List.nil) =>
      have : $basis_tl =Q [] := ⟨⟩
      let h' : Q(PreMS.extendBasisEnd $f $ms' = PreMS.mk (.cons 0 $ms' .nil) (fun _ ↦ ($ms'))) :=
        q(extendBasisEnd_const $f $ms')
      return ⟨q(SeqMS.cons 0 $ms' .nil), q(sorry)⟩
    | ~q(List.cons $basis_hd' $basis_tl') =>
      have : $basis_tl =Q $basis_tl' ++ [$f] := ⟨⟩
      let ⟨s, h⟩ ← getSeq q($ms')
      return ⟨q(SeqMS.extendBasisEnd $f $s), q(sorry)⟩
  | (``PreMS.updateBasis, #[(oldBasis : Q(Basis)), (ex : Q(BasisExtension $oldBasis)),
      (ms' : Q(PreMS $oldBasis))]) =>
    have : ($basis_hd :: $basis_tl) =Q ($ex).getBasis := ⟨⟩
    -- have : $ms =Q PreMS.updateBasis $ex $ms' := ⟨⟩
    let oldBasis' : Q(Basis) ← reduceBasis oldBasis
    have : $oldBasis =Q $oldBasis' := ⟨⟩
    match oldBasis', ex with
    | ~q(List.cons $oldBasis_hd $oldBasis_tl), ~q(BasisExtension.keep _ $ex_tl) =>
      have : $basis_hd =Q $oldBasis_hd := ⟨⟩
      have : $basis_tl =Q ($ex_tl).getBasis := ⟨⟩
      let ⟨s, h⟩ ← getSeq q($ms')
      let ke := q(SeqMS.updateBasis $ex_tl $s)
      return ⟨q(SeqMS.updateBasis $ex_tl $s), q(sorry)⟩
    | ~q(List.cons $oldBasis_hd $oldBasis_tl), ~q(BasisExtension.insert $f $ex_tl) =>
      have : ($ex_tl).getBasis =Q $basis_tl := ⟨⟩
      return ⟨q(SeqMS.cons 0 (($ms').updateBasis $ex_tl) .nil), q(sorry)⟩
    | ~q(List.nil), ~q(BasisExtension.insert $f $ex_tl) =>
      have : $basis_tl =Q ($ex_tl).getBasis := ⟨⟩
      return ⟨q(SeqMS.cons 0 (($ms').updateBasis $ex_tl) .nil), q(sorry)⟩
    | _ =>
      panic!
        s!"getSeq: unexpected oldBasis and ex: {← ppExpr oldBasis} and {← ppExpr ex}"
  | _ =>
  match ms with
  | ~q(PreMS.mk $s $f) => return ⟨q($s), q(rfl)⟩
  | ~q(PreMS.replaceFun $arg $f) =>
    let ⟨s, h⟩ ← getSeq q($arg)
    return ⟨q($s), q($h ▸ PreMS.replaceFun_seq _ _)⟩
  | ~q(PreMS.const _ $c) => return ⟨q(SeqMS.const _ _ $c), q(PreMS.const_seq)⟩
  | ~q(PreMS.one) => return ⟨q(SeqMS.one), q(PreMS.one_seq)⟩
  | ~q(PreMS.monomial _ $n) => return ⟨q(SeqMS.monomial _ _ $n), q(PreMS.monomial_seq)⟩
  | ~q(PreMS.monomialRpow _ $n $r) => return ⟨q(SeqMS.monomialRpow _ _ $n $r), q(PreMS.monomialRpow_seq)⟩
  | ~q(PreMS.neg $arg) =>
    let ⟨s, h⟩ ← getSeq q($arg)
    return ⟨q(SeqMS.neg $s), q($h ▸ PreMS.neg_seq)⟩
  | ~q(PreMS.add $arg₁ $arg₂) =>
    let ⟨s₁, h₁⟩ ← getSeq q($arg₁)
    let ⟨s₂, h₂⟩ ← getSeq q($arg₂)
    return ⟨q(SeqMS.add $s₁ $s₂), q($h₁ ▸ $h₂ ▸ PreMS.add_seq)⟩
  | ~q(PreMS.mul $arg₁ $arg₂) =>
    let ⟨s₁, h₁⟩ ← getSeq q($arg₁)
    let ⟨s₂, h₂⟩ ← getSeq q($arg₂)
    return ⟨q(SeqMS.mul $s₁ $s₂), q($h₁ ▸ $h₂ ▸ PreMS.mul_seq)⟩
  | ~q(PreMS.mulMonomial $b $m_coef $m_exp) =>
    let ⟨s₁, h₁⟩ ← getSeq q($b)
    return ⟨q(SeqMS.mulMonomial $s₁ $m_coef $m_exp), q($h₁ ▸ PreMS.mulMonomial_seq)⟩
  | ~q(PreMS.mulConst $c $arg) =>
    let ⟨s, h⟩ ← getSeq q($arg)
    return ⟨q(SeqMS.mulConst $c $s), q($h ▸ PreMS.mulConst_seq)⟩
  | ~q(PreMS.apply $s $arg) =>
    let ⟨ms, h⟩ ← getSeq q($arg)
    return ⟨q(SeqMS.apply $s $ms), q($h ▸ PreMS.apply_seq)⟩
  | ~q(PreMS.inv $arg) =>
    let ⟨s, h⟩ ← getSeq q($arg)
    return ⟨q(SeqMS.inv $s), q($h ▸ PreMS.inv_seq)⟩
  | ~q(PreMS.pow $arg $a) =>
    let ⟨s, h⟩ ← getSeq q($arg)
    return ⟨q(SeqMS.pow $s $a), q($h ▸ PreMS.pow_seq)⟩
  | ~q(PreMS.npow $arg $a) =>
    let ⟨s, h⟩ ← getSeq q($arg)
    return ⟨q(SeqMS.pow $s $a), q($h ▸ PreMS.pow_seq)⟩
  | ~q(PreMS.zpow $arg $a) =>
    let ⟨s, h⟩ ← getSeq q($arg)
    return ⟨q(SeqMS.pow $s $a), q($h ▸ PreMS.pow_seq)⟩
  | ~q(PreMS.log $logBasis $arg) =>
    let ⟨s, h⟩ ← getSeq q($arg)
    return ⟨q(SeqMS.log $logBasis $s), q($h ▸ PreMS.log_seq)⟩
  | ~q(PreMS.exp $arg) =>
    let ⟨s, h⟩ ← getSeq q($arg)
    return ⟨q(SeqMS.exp $s), q($h ▸ PreMS.exp_seq)⟩
  | _ => panic! s!"getSeqMS: unexpected ms: {← ppExpr ms}"


/-- Given `ms : PreMS basis`, return `ms'` that is normalized (either `PreMS.nil` or `PreMS.cons`),
and the proof of `ms' = ms`. -/
def normalizePreMS {basis : Q(Basis)}
    (ms : Q(PreMS $basis)) : TacticM ((ms' : Q(PreMS $basis)) × Q($ms = $ms')) := do
  match basis with
  | ~q(List.nil) => return ⟨ms, q(rfl)⟩
  | ~q(List.cons $basis_hd $basis_tl) =>
    let ⟨f, hf⟩ ← getFun q($ms)
    let ⟨s, hs⟩ ← getSeq q($ms)
    let res ← normalizeSeqMSImp q($s)
    match res with
    | .nil h =>
      return ⟨q(PreMS.mk .nil $f), q((ms_eq_mk_iff _ _ _).mpr ⟨$h ▸ $hs, $hf⟩)⟩
    | .cons exp coef tl h =>
      return ⟨q(PreMS.mk (.cons $exp $coef $tl) $f), q((ms_eq_mk_iff _ _ _).mpr ⟨$h ▸ $hs, $hf⟩)⟩

end Normalization

end ComputeAsymptotics
