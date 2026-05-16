/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries
public import Mathlib.Tactic.ComputeAsymptotics.Meta.Misc

/-!
# Multiseries on meta level
-/

public meta section

open Lean Elab Meta Qq

namespace Tactic.ComputeAsymptotics

/-- Multiseries on meta level. It contains
* the basis with the proof of well-formedness
* the log-basis with the proof of well-formedness
* the `MultiseriesExpansion` value with the proof of well-ordering
* the function `f` with the proof that the multiseries approximates it
-/
structure MS where
  /-- Basis of the multiseries. -/
  basis : Q(Basis)
  /-- Log-basis of the multiseries. -/
  logBasis : Q(LogBasis $basis)
  /-- `MultiseriesExpansion` value of the multiseries. -/
  val : Q(MultiseriesExpansion $basis)
  /-- Proof of well-ordering of the multiseries. -/
  h_sorted : Q(MultiseriesExpansion.Sorted $val)
  /-- Proof of approximation of the multiseries. -/
  h_approx : Q(MultiseriesExpansion.Approximates $val)
  /-- Proof of well-formedness of the basis. -/
  h_basis : Q(WellFormedBasis $basis)
  /-- Proof of well-formedness of the log-basis. -/
  h_logBasis : Q(LogBasis.WellFormed $logBasis)
deriving Inhabited

namespace MS

/-- Multiseries representing a constant function. -/
def const (basis : Q(Basis)) (logBasis : Q(LogBasis $basis)) (c : Q(ℝ))
    (h_basis : Q(WellFormedBasis $basis)) (h_logBasis : Q(LogBasis.WellFormed $logBasis)) : MS where
  basis := basis
  logBasis := logBasis
  val := q(MultiseriesExpansion.const $basis $c)
  -- f := q(fun _ ↦ $c)
  h_sorted := q(MultiseriesExpansion.const_Sorted)
  h_approx := q(MultiseriesExpansion.const_Approximates $h_basis)
  h_basis := h_basis
  h_logBasis := h_logBasis

/-- Multiseries representing `basis[n] ^ r`. -/
def monomialRpow (basis : Q(Basis)) (logBasis : Q(LogBasis $basis))
    (n : Q(Fin (List.length $basis))) (r : Q(ℝ))
    (h_basis : Q(WellFormedBasis $basis)) (h_logBasis : Q(LogBasis.WellFormed $logBasis)) : MS where
  basis := basis
  logBasis := logBasis
  val := q(MultiseriesExpansion.monomialRpow $basis $n $r)
  -- f := q(fun x ↦ (List.get $basis $n x)^$r)
  h_sorted := q(MultiseriesExpansion.monomialRpow_Sorted)
  h_approx := q(MultiseriesExpansion.monomialRpow_Approximates $h_basis)
  h_basis := h_basis
  h_logBasis := h_logBasis

/-- Multiseries representing `basis[n]`. -/
def monomial (basis : Q(Basis)) (logBasis : Q(LogBasis $basis)) (n : Q(Fin (List.length $basis)))
    (h_basis : Q(WellFormedBasis $basis)) (h_logBasis : Q(LogBasis.WellFormed $logBasis)) : MS where
  basis := basis
  logBasis := logBasis
  val := q(MultiseriesExpansion.monomial $basis $n)
  -- f := q(List.get $basis $n)
  h_sorted := q(MultiseriesExpansion.monomial_Sorted)
  h_approx := q(MultiseriesExpansion.monomial_Approximates $h_basis)
  h_basis := h_basis
  h_logBasis := h_logBasis

/-- Given a multiseries representing `f`, returns the multiseries representing `c • f`. -/
def mulConst (x : MS) (c : Q(ℝ)) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(MultiseriesExpansion.mulConst $c $x.val)
  -- f := q($c • $x.f)
  h_sorted := q(MultiseriesExpansion.mulConst_Sorted $x.h_sorted)
  h_approx := q(MultiseriesExpansion.mulConst_Approximates $x.h_approx)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

/-- Given a multiseries representing `f`, returns the multiseries representing `-f`. -/
def neg (x : MS) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(MultiseriesExpansion.neg $x.val)
  -- f := q(-$x.f)
  h_sorted := q(MultiseriesExpansion.neg_Sorted $x.h_sorted)
  h_approx := q(MultiseriesExpansion.neg_Approximates $x.h_approx)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

/-- Given two multiseries representing `f` and `g`, returns the multiseries representing `f + g`. -/
def add (x y : MS) : MS :=
  haveI : $x.basis =Q $y.basis := ⟨⟩
  {
    basis := x.basis
    logBasis := x.logBasis
    val := q(MultiseriesExpansion.add $x.val $y.val)
    -- f := q($x.f + $y.f)
    h_sorted := q(MultiseriesExpansion.add_Sorted $x.h_sorted $y.h_sorted)
    h_approx := q(MultiseriesExpansion.add_Approximates $x.h_approx $y.h_approx)
    h_basis := x.h_basis
    h_logBasis := x.h_logBasis
  }

/-- Given two multiseries representing `f` and `g`, returns the multiseries representing `f - g`. -/
def sub (x y : MS) : MS :=
  haveI : $x.basis =Q $y.basis := ⟨⟩
  {
    basis := x.basis
    logBasis := x.logBasis
    val := q(MultiseriesExpansion.add $x.val (MultiseriesExpansion.neg $y.val))
    -- f := q($x.f - $y.f)
    h_sorted := q(MultiseriesExpansion.sub_Sorted $x.h_sorted $y.h_sorted)
    h_approx := q(MultiseriesExpansion.sub_Approximates $x.h_approx $y.h_approx)
    h_basis := x.h_basis
    h_logBasis := x.h_logBasis
  }

/-- Given two multiseries representing `f` and `g`, returns the multiseries representing `f * g`. -/
def mul (x y : MS) : MS :=
  haveI : $x.basis =Q $y.basis := ⟨⟩
  {
    basis := x.basis
    logBasis := x.logBasis
    val := q(MultiseriesExpansion.mul $x.val $y.val)
    -- f := q($x.f * $y.f)
    h_sorted := q(MultiseriesExpansion.mul_Sorted $x.h_sorted $y.h_sorted)
    h_approx := q(MultiseriesExpansion.mul_Approximates $x.h_basis $x.h_approx $y.h_approx)
    h_basis := x.h_basis
    h_logBasis := x.h_logBasis
  }

/-- Given a multiseries representing `f`, returns the multiseries representing `f⁻¹`. -/
def inv (x : MS) (h_trimmed : Q(MultiseriesExpansion.Trimmed $x.val)) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(MultiseriesExpansion.inv $x.val)
  -- f := q($x.f⁻¹)
  h_sorted := q(MultiseriesExpansion.inv_Sorted $x.h_sorted)
  h_approx := q(MultiseriesExpansion.inv_Approximates $x.h_basis $x.h_sorted $x.h_approx $h_trimmed)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

/-- Given two multiseries representing `f` and `g`, returns the multiseries representing `f / g`. -/
def div (x y : MS) (h_trimmed : Q(MultiseriesExpansion.Trimmed $y.val)) : MS :=
  haveI : $x.basis =Q $y.basis := ⟨⟩
  {
    basis := x.basis
    logBasis := x.logBasis
    val := q(MultiseriesExpansion.mul $x.val (MultiseriesExpansion.inv $y.val))
    -- f := q($x.f / $y.f)
    h_sorted := q(MultiseriesExpansion.div_Sorted $x.h_sorted $y.h_sorted)
    h_approx := q(MultiseriesExpansion.div_Approximates $x.h_basis $y.h_sorted $h_trimmed
      $x.h_approx $y.h_approx)
    h_basis := x.h_basis
    h_logBasis := x.h_logBasis
  }

/-- Given a multiseries representing `f` and constant `a : ℕ`,
returns the multiseries representing `f ^ a`. -/
def npow (x : MS) (a : Q(ℕ)) (h_trimmed : Q(MultiseriesExpansion.Trimmed $x.val)) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(MultiseriesExpansion.npow $x.val $a)
  -- f := q($x.f ^ $a)
  h_sorted := q(MultiseriesExpansion.npow_Sorted $x.h_sorted)
  h_approx := q(MultiseriesExpansion.npow_Approximates $x.h_basis $x.h_sorted
    $x.h_approx $h_trimmed)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

/-- Given a multiseries representing `f` and constant `a : ℤ`,
returns the multiseries representing `f ^ a`. -/
def zpow (x : MS) (a : Q(ℤ)) (h_trimmed : Q(MultiseriesExpansion.Trimmed $x.val)) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(MultiseriesExpansion.zpow $x.val $a)
  -- f := q($x.f ^ $a)
  h_sorted := q(MultiseriesExpansion.zpow_Sorted $x.h_sorted)
  h_approx := q(MultiseriesExpansion.zpow_Approximates $x.h_basis $x.h_sorted
    $x.h_approx $h_trimmed)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

/-- Given a multiseries representing `f` and constant `a : ℝ`,
returns the multiseries representing `f ^ a`. -/
def rpow (x : MS) (a : Q(ℝ)) (h_trimmed : Q(MultiseriesExpansion.Trimmed $x.val))
    (h_pos : Q(0 < (MultiseriesExpansion.leadingMonomial $x.val).coef)) : MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(MultiseriesExpansion.pow $x.val $a)
  -- f := q($x.f ^ $a)
  h_sorted := q(MultiseriesExpansion.pow_Sorted $x.h_sorted)
  h_approx := q(MultiseriesExpansion.pow_Approximates $x.h_basis $x.h_sorted $x.h_approx
    $h_trimmed $h_pos)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

/-- Given a multiseries `ms` and a basis extension `ex`, returns the multiseries representing
the same function on the new basis. -/
def updateBasis (ms : MS) (ex : Q(BasisExtension $ms.basis))
    (logBasis : Q(LogBasis (BasisExtension.getBasis $ex)))
    (h_basis : Q(WellFormedBasis (BasisExtension.getBasis $ex)))
    (h_logBasis : Q(LogBasis.WellFormed $logBasis)) : MetaM MS := do
  let basis ← reduceBasis q(BasisExtension.getBasis $ex)
  haveI : $basis =Q BasisExtension.getBasis $ex := ⟨⟩
  return {
    basis := basis
    logBasis := logBasis
    val := q(MultiseriesExpansion.updateBasis $ex $ms.val)
    -- f := ms.f
    h_sorted := q(MultiseriesExpansion.updateBasis_Sorted $ms.h_sorted)
    h_approx := q(MultiseriesExpansion.updateBasis_Approximates $h_basis $ms.h_approx)
    h_basis := h_basis
    h_logBasis := h_logBasis
  }

/-- Given a multiseries `ms`, returns the multiseries representing the same function on the basis
extended by the last `log ∘ basis.getLast` element. -/
def insertLastLog (ms : MS) : MetaM MS := do
  let ~q(List.cons $basis_hd $basis_tl) := ms.basis | panic! "insertLastLog: unexpected basis"
  let .some last ← getLast (α := q(ℝ → ℝ)) ms.basis | panic! "insertLastLog: unexpected basis"
  haveI : List.getLast ($basis_hd :: $basis_tl) (List.cons_ne_nil _ _) =Q $last := ⟨⟩
  let basis := ← reduceBasis q($ms.basis ++ [Real.log ∘ $last])
  haveI : $basis =Q $ms.basis ++ [Real.log ∘ $last] := ⟨⟩
  let logBasis := ← reduceLogBasis q(LogBasis.insertLastLog (basis_hd := $basis_hd)
    (basis_tl := $basis_tl) $ms.logBasis)
  haveI : $logBasis =Q LogBasis.insertLastLog (basis_hd := $basis_hd) (basis_tl := $basis_tl)
    $ms.logBasis := ⟨⟩
  let h_basis : Q(WellFormedBasis $basis) := q(($ms.h_basis).push_log_last)
  let ms' : MS := {
    basis := q($basis)
    val := q(MultiseriesExpansion.extendBasisEnd (Real.log ∘ $last) $ms.val)
    h_sorted := q(MultiseriesExpansion.extendBasisEnd_Sorted $ms.h_sorted)
    h_approx := q(MultiseriesExpansion.extendBasisEnd_Approximates $h_basis $ms.h_approx)
    h_basis := q($h_basis)
    logBasis := q($logBasis)
    h_logBasis := q(LogBasis.insertLastLog_WellFormed $ms.h_basis $ms.h_logBasis)
  }
  return ms'

/-- Given a multiseries representing `f`, returns the multiseries representing `log ∘ f`. -/
def log (x : MS) (h_trimmed : Q(MultiseriesExpansion.Trimmed $x.val))
    (h_pos : Q(0 < (MultiseriesExpansion.leadingMonomial $x.val).coef))
    (h_last : Q(∀ a, (MultiseriesExpansion.leadingMonomial $x.val).unit.getLast? =
      .some a → a = 0)) : MS where
  basis := q($x.basis)
  val := q(MultiseriesExpansion.log $x.logBasis $x.val)
  -- f := q(Real.log ∘ $x.f)
  h_sorted := q(MultiseriesExpansion.log_Sorted $x.h_logBasis $h_last $x.h_sorted)
  h_approx := q(MultiseriesExpansion.log_Approximates $x.h_basis $x.h_logBasis $x.h_sorted
    $x.h_approx $h_trimmed $h_pos $h_last)
  h_basis := x.h_basis
  logBasis := q($x.logBasis)
  h_logBasis := x.h_logBasis

/-- Given a multiseries representing `f`, returns the multiseries representing `exp ∘ f`. -/
def exp (x : MS)
    (h_nonpos : Q(¬ (MultiseriesExpansion.leadingMonomial $x.val).unit.FirstNonzeroIsPos)) :
    MS where
  basis := x.basis
  logBasis := x.logBasis
  val := q(MultiseriesExpansion.exp $x.val)
  -- f := q(Real.exp ∘ $x.f)
  h_sorted := q(MultiseriesExpansion.exp_Sorted $x.h_sorted $h_nonpos)
  h_approx := q(MultiseriesExpansion.exp_Approximates $x.h_basis $x.h_sorted $x.h_approx $h_nonpos)
  h_basis := x.h_basis
  h_logBasis := x.h_logBasis

/-- Given a multiseries `ms` and a function `f`, returns the multiseries representing the same
function as `ms` but with the function `f`. -/
def replaceFun (ms : MS) (f : Q(ℝ → ℝ)) (h : Q(($ms.val).toFun =ᶠ[Filter.atTop] $f)) :
    MetaM MS := do
  let ~q($basis_hd :: $basis_tl) := ms.basis | panic! "replaceFun: unexpected basis"
  return {ms with
    val := q(MultiseriesExpansion.replaceFun $ms.val $f)
    h_sorted := q(MultiseriesExpansion.Sorted.replaceFun $ms.h_sorted)
    h_approx := q(MultiseriesExpansion.Approximates.replaceFun $h $ms.h_approx)
  }

/-- Given a multiseries `ms` and a function `f`, returns the multiseries `res` representing the same
function as `ms` but with the function `f`. It also returns the proof that `res.toFun = f`. -/
def replaceFun' (ms : MS) (f : Q(ℝ → ℝ)) (h : Q(($ms.val).toFun =ᶠ[Filter.atTop] $f)) :
    MetaM <| (res : MS) × Q(($res.val).toFun = $f) := do
  let ~q($basis_hd :: $basis_tl) := ms.basis | panic! "replaceFun: unexpected basis"
  let res ← ms.replaceFun q($f) q($h)
  have : $res.basis =Q $basis_hd :: $basis_tl := ⟨⟩
  have : $res.val =Q ($ms.val).replaceFun $f := ⟨⟩
  return ⟨res, q(MultiseriesExpansion.replaceFun_toFun _ _)⟩

end MS

end Tactic.ComputeAsymptotics
