/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Tactic.Algebra.Lemmas
public import Mathlib.Tactic.Ring.RingNF


/-!
# The `algebra` tactic
A suite of three tactics for solving equations in commutative algebras over commutative (semi)rings,
where the exponents can also contain variables.

Based largely on the implementation of `ring`. The `algebra` normal form mirrors that of `ring`
except that the constants are expressions in the base ring that are kept in ring normal form.

## Organization
This tactic is implemented using the machinery of `Ring.Common`

* Normalized expressions are stored as an `Common.ExSum`, with a custom type for
representing coefficients in `R`.
* While `ring` stores coefficients as rational numbers normalized by `norm_num`, `algebra` stores
coefficients as experssions in the base ring `R`, normalized by `ring`.
* These coefficients are sums, not products. The normal form of `a • x + b • x` is `(a + b) • x`.

This tactic is used internally to implement the `polynomial` tactic.

## Limitations
The main limitation of the current implementation is that it does not handle rational constants
when the algebra `A` is a field but the base ring `R` is not. This is never an issue when working
with polynomials, but would be an issue when working with a number field over its ring of integers.

When inferring the base ring, we assum that any two rings `R` and `S` that appear are comparable,
in the sense that either `R` is an `S`-algebra or `S` is an `R`-algebra.

-/

open Lean hiding Module
open Meta Elab Qq Mathlib.Tactic Mathlib.Meta AtomM

public meta section

namespace Mathlib.Tactic.Algebra

attribute [local instance] monadLiftOptionMetaM

open NormNum hiding Result

/-- This cache contains typeclasses required during `algebra`'s execution. These assumptions
  are stronger than `ring` because `algebra` occasionally requires commutativity to move between
  the base ring and the algebra. -/
structure Cache {u : Level} {A : Q(Type u)}
    (sA : Q(CommSemiring $A)) extends Ring.Common.Cache sA where
  /-- A Field instance on `A`, if available. -/
  field : Option Q(Field $A)

/-- Create a new cache for `A` by doing the necessary instance searches. -/
def mkCache {u : Level} {A : Q(Type u)} (sA : Q(CommSemiring $A)) : MetaM (Cache sA) := do return {
  field := (← trySynthInstanceQ q(Field $A)).toOption
  toCache := ← Ring.Common.mkCache sA
}

open Mathlib.Tactic.Ring hiding ExSum ExProd ExBase

section BaseType

variable {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
  {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A)) (a : Q($A)) (b : Q($A))

/-- The type used to store the coefficients of the algebra tactic, which are expressions in `R`
  kept in ring normal form and mapped into `A` by the algebraMap.

  Note that these are sums, not products! -/
inductive BaseType : (a : Q($A)) → Type
  | mk (r : Q($R)) (_ : Ring.ExSum q($sR) r) : BaseType q(algebraMap $R $A $r)

@[expose, inherit_doc Common.ExBase]
def ExBase := Common.ExBase (BaseType sAlg) sA
@[expose, inherit_doc Common.ExProd]
def ExProd := Common.ExProd (BaseType sAlg) sA
@[expose, inherit_doc Common.ExSum]
def ExSum := Common.ExSum (BaseType sAlg) sA

lemma lift_nz {n : ℕ} {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (h : (n : A) ≠ 0) : (n : R) ≠ 0 := by
  apply_fun algebraMap R A
  simp [h]

set_option linter.unusedVariables false in
variable {a} in
/-- Evaluates a numeric literal in the algebra `A` by lifting it through the base ring `R`. -/
def evalCast (cR : Algebra.Cache q($sR)) (cA : Algebra.Cache q($sA)):
    NormNum.Result a → Option (Common.Result (ExSum sAlg) q($a))
  | .isNat _ (.lit (.natVal 0)) p => do
    assumeInstancesCommute
    pure ⟨_, .zero, q(isNat_zero_eq $p)⟩
  | .isNat _ lit p => do
    assumeInstancesCommute
    let ⟨r, vr⟩ := Ring.ExProd.mkNat sR lit.natLit!
    -- Lift the literal to the base ring as a scalar multiple of 1
    pure ⟨_, (Common.ExProd.const ⟨_, (vr.toSum)⟩).toSum,
      have : $r =Q Nat.rawCast $lit := ⟨⟩
      (q(isNat_eq_rawCast $p))⟩
  | .isNegNat rA lit p => do
    let some crR := cR.rα | none
    let some crA := cA.rα | none
    let ⟨r, vr⟩ := Ring.ExProd.mkNegNat q($sR) q(inferInstance) lit.natLit!
    have : $r =Q Int.rawCast (Int.negOfNat $lit) := ⟨⟩
    assumeInstancesCommute
    pure ⟨_, (Common.ExProd.const ⟨_, vr.toSum⟩).toSum, (q(isInt_negOfNat_eq $p))⟩
  | .isNNRat rA q n d p => do
    let some dsR := cR.dsα | none
    let some dsA := cA.dsα | none
    assumeInstancesCommute
    let ⟨r, vr⟩ := Ring.ExProd.mkNNRat q($sR) q(inferInstance) q n d
      q(lift_nz (R := $R) <| IsNNRat.den_nz $p)
    have : $r =Q (NNRat.rawCast $n $d : $R) := ⟨⟩
    pure ⟨_, (Common.ExProd.const ⟨_, vr.toSum⟩).toSum, q(isNNRat_eq_rawCast (a := $a) $p)⟩
  | .isNegNNRat dA q n d p => do
    let some fR := cR.field | none
    let some fA := cA.field | none
    assumeInstancesCommute
    let ⟨r, vr⟩ := Ring.ExProd.mkNegNNRat q($sR) q(inferInstance) q n d
      q(lift_nz (R := $R) <| IsRat.den_nz $p)
    have : $r =Q (Rat.rawCast (.negOfNat $n) $d : $R) := ⟨⟩
    pure ⟨_, (Common.ExProd.const ⟨_, vr.toSum⟩).toSum, (q(isRat_eq_rawCast (a := $a) $p))⟩
  | _ => none

/-- Push `algebraMap`s into sums and products and convert `algebraMap`s from `ℕ`, `ℤ` and `ℚ`
into casts. -/
def pushCast (e : Expr) : MetaM Simp.Result := do
  -- collect the available `push_cast` lemmas
  let mut thms : SimpTheorems := ← NormCast.pushCastExt.getTheorems
  let simps : Array Name := #[``eq_natCast, ``eq_intCast, ``eq_ratCast]
  for thm in simps do
    let ⟨levelParams, _, proof⟩ ← abstractMVars (mkConst thm)
    thms ← thms.add (.stx (← mkFreshId) Syntax.missing) levelParams proof
  -- now run `simp` with these lemmas, and (importantly) *no* simprocs
  let ctx ← Simp.mkContext { failIfUnchanged := false } (simpTheorems := #[thms])
  let (r, _) ← simp e ctx (simprocs := #[])
  return r


/-- Handle scalar multiplication when the scalar ring `R'` doesn't match the base ring `R`.
Assumes `R` is an `R'`-algebra (i.e., `R'` is smaller), and casts the scalar using `algebraMap`. -/
def evalSMulCast {u u' v : Lean.Level} {R : Q(Type u)} {R' : Q(Type u')} {A : Q(Type v)}
    {sR : Q(CommSemiring $R)} {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A))
    (smul : Q(SMul $R' $A)) (r' : Q($R')) :
    MetaM <| Σ r : Q($R), Q(∀ a : $A, $r • a = $r' • a) := do
  trace[algebra.debug] m!"Running evalSMulCast on {r'}."
  if (← isDefEq R R') then
    have : u =QL u' := ⟨⟩
    have : $R =Q $R' := ⟨⟩
    assumeInstancesCommute
    return ⟨q($r'), q(fun _ => rfl)⟩
  let _sR' ← synthInstanceQ q(CommSemiring $R')
  let _algR'R ← synthInstanceQ q(Algebra $R' $R)
  let _mod ← synthInstanceQ q(Module $R' $A)
  let _ist ← synthInstanceQ q(IsScalarTower $R' $R $A)
  assumeInstancesCommute
  let r_cast : Q($R) := q(algebraMap $R' $R $r')
  let res ← pushCast r_cast
  have r₀ : Q($R) := res.expr
  let pf : Q($r_cast = $r₀) ← res.getProof
  return ⟨r₀, q(fun a ↦ $pf ▸ algebraMap_smul $R $r' a)⟩

namespace RingCompute

/-- Evaluate the sum of two normalized expressions in `R` using `ring`. -/
def add (cR : Common.Cache sR) {a b : Q($A)} (za : BaseType sAlg a) (zb : BaseType sAlg b) :
    MetaM (Common.Result (BaseType sAlg) q($a + $b) × Option Q(IsNat ($a + $b) 0)) := do
  trace[algebra.debug] m!"Running add on {a} and {b}."
  let ⟨r, vr⟩ := za
  let ⟨s, vs⟩ := zb
  let ⟨t, vt, pt⟩ ← Common.evalAdd (Ring.ringCompute cR) rcℕ vr vs
  match vt with
  | .zero =>
    have : $t =Q 0 := ⟨⟩
    return  ⟨⟨_, .mk _ vt, q(add_algebraMap $pt)⟩, some q(add_algebraMap_isNat_zero $pt)⟩
  | vt =>
    return ⟨⟨_, .mk _ vt, q(add_algebraMap $pt)⟩, none⟩

/-- Evaluate the product of two normalized expressions in `R` using `ring`. -/
def mul (cR : Common.Cache sR) {a b : Q($A)} (za : BaseType sAlg a) (zb : BaseType sAlg b) :
    MetaM (Common.Result (BaseType sAlg) q($a * $b)) := do
  trace[algebra.debug] m!"Running mul on {a} and {b}."
  let ⟨r, vr⟩ := za
  let ⟨s, vs⟩ := zb
  let ⟨t, vt, pt⟩ ← Common.evalMul (Ring.ringCompute cR) rcℕ vr vs
  return ⟨_, .mk _ vt, q(by simp [← $pt, map_mul])⟩

/-- Take an expression `r'` in a ring `R'` such that `R` is an `R'`-algebra and cast `r'` to `R`
using `algebraMap R' R`, so that the scalar multiplication action on `A` is preserved. -/
/- We include the CharZero argument to match the type signature of the ringCompute entry. -/
@[nolint unusedArguments]
def cast (cR : Algebra.Cache sR) (u' : Level) (R' : Q(Type u'))
    (_ : Q(CommSemiring $R')) (_smul : Q(SMul $R' $A)) (r' : Q($R')) :
    AtomM ((y : Q($A)) × Common.ExSum (BaseType sAlg) sA q($y) ×
      Q(∀ (a : $A), $r' • a = $y * a)) := do
  trace[algebra.debug] m!"Running cast on {r'} casting from {R'} to {R} to {A}."
  let ⟨r, pf_smul⟩ ← evalSMulCast q($sAlg) q($_smul) r'
  let ⟨_r'', vr, pr⟩ ←
    Common.eval rcℕ (Ring.ringCompute cR.toCache) cR.toCache q($r)
  match vr with
  | .zero .. =>
    assumeInstancesCommute
    return ⟨_, .zero, q(cast_zero_smul_eq_zero_mul $pr $pf_smul)⟩
  | vr =>
    assumeInstancesCommute
    return ⟨_, Common.ExSum.add (Common.ExProd.const (.mk _ vr)) .zero,
      q(cast_smul_eq_mul $pr $pf_smul)⟩

/-- Evaluate the product of two normalized expressions in `R` using `ring`. -/
def neg (cR : Algebra.Cache sR) {a : Q($A)} (_rA : Q(CommRing $A)) (za : BaseType sAlg a) :
    MetaM (Common.Result (BaseType sAlg) q(-$a)) := do
  trace[algebra.debug] m!"Running neg on {a}"
  let ⟨r, vr⟩ := za
  match cR.rα with
  | some rR =>
    let ⟨_, vt, pt⟩ ← Common.evalNeg (Ring.ringCompute cR.toCache) q($rR) vr
    assumeInstancesCommute
    return ⟨_, .mk _ vt, q(neg_algebraMap $pt)⟩
  | none => failure

/-- Raise a normalized expression in `R` to the power of a normalized natural number expression
using `ring`. -/
def pow (cR : Common.Cache sR) {a : Q($A)} {b : Q(ℕ)} (za : BaseType sAlg a)
    (vb : Common.ExProdNat q($b)) :
    OptionT MetaM (Common.Result (BaseType sAlg) q($a ^ $b)) := do
  trace[algebra.debug] m!"Running pow on {a} and {b}"
  let ⟨r, vr⟩ := za
  let ⟨_, vs, ps⟩ ← Common.evalPow₁ (Ring.ringCompute cR) rcℕ vr vb
  return ⟨_, ⟨_, vs⟩, q(pow_algebraMap $ps)⟩

/-- Evaluate the inverse of two normalized expressions in `R` using `ring`. -/
/- We include the CharZero argument to match the type signature of the ringCompute entry. -/
@[nolint unusedArguments]
def inv (cR : Algebra.Cache sR) {a : Q($A)} (_ : Option Q(CharZero $A)) (fA : Q(Semifield $A))
    (za : BaseType sAlg a) : AtomM (Option (Common.Result (BaseType sAlg) q($a⁻¹))) := do
  trace[algebra.debug] m!"Running inv on {a}"
  match cR.dsα with
  | some fR =>
    let ⟨r, vr⟩ := za
    let ⟨_, vs, ps⟩ ← Common.ExSum.evalInv (Ring.ringCompute cR.toCache) rcℕ q($fR) cR.czα vr
    assumeInstancesCommute
    return some ⟨_, ⟨_, vs⟩, q(inv_algebraMap $ps)⟩
  | none =>
    -- TODO: There are some situations we might still be able to make sense of.
    return none

/-- Evaluate constants in `A` using `norm_num`. -/
def derive (cR : Algebra.Cache sR) (cA : Algebra.Cache sA) (x : Q($A)) :
    MetaM (Common.Result (Common.ExSum (BaseType sAlg) sA) q($x)) := do
  trace[algebra.debug] m!"Running derive on {x}"
  let res ← NormNum.derive x
  let ⟨_, vr, pr⟩ ← evalCast sAlg cR cA res
  return ⟨_, vr, q($pr)⟩

/-- Decide if a coefficient is 1. -/
def isOne (cR : Common.Cache sR) {x : Q($A)} (zx : BaseType sAlg x) : Option Q(IsNat $x 1) :=
  let ⟨_, vx⟩ := zx
  match vx with
  | .add (.const c) .zero =>
    match (Ring.ringCompute cR).isOne c with
    | some pf => some q(isOne_algebraMap $pf)
    | none => none
  | .zero => none
  | _ => none

end RingCompute

open RingCompute in
/-- The data used by the `algebra` tactic to normalize the constant coefficients, which are
expressions in `R` normalized by `ring`. -/
def ringCompare :
    Common.RingCompare (BaseType sAlg) where
  eq := fun ⟨_, vx⟩ ⟨_, vy⟩ => vx.eq rcℕ Ring.ringCompare vy
  compare := fun ⟨_, vx⟩ ⟨_, vy⟩ => vx.cmp rcℕ Ring.ringCompare vy

open Algebra.RingCompute in
/-- The data used by the `algebra` tactic to normalize the constant coefficients, which are
expressions in `R` normalized by `ring`. -/
def ringCompute (cR : Algebra.Cache sR) (cA : Algebra.Cache sA) :
    Common.RingCompute (BaseType sAlg) sA where
  add := add sAlg cR.toCache
  mul := mul sAlg cR.toCache
  cast := cast sAlg cR
  neg := neg sAlg cR
  pow := pow sAlg cR.toCache
  inv := inv sAlg cR
  derive := derive sAlg cR cA
  isOne := isOne sAlg cR.toCache
  one :=
    let ⟨r, vr⟩ := Ring.ExProd.mkNat sR 1
    have hr : $r =Q (nat_lit 1).rawCast := ⟨⟩
    ⟨_, ⟨_, vr.toSum⟩, q(by simp +zetaDelta)⟩
  toRingCompare := ringCompare sAlg

end BaseType


open Lean Parser.Tactic Elab Command Elab.Tactic Meta Qq

theorem Nat.cast_eq_algebraMap (A : Type*) [CommSemiring A] (n : ℕ) :
    Nat.cast n = algebraMap ℕ A n := rfl

theorem Nat.algebraMap_eq_cast (A : Type*) [CommSemiring A] (n : ℕ) :
    algebraMap ℕ A n = Nat.cast n := rfl

theorem Int.cast_eq_algebraMap (A : Type*) [CommRing A] (n : ℤ) :
    Int.cast n = algebraMap ℤ A n := rfl

theorem Int.algebraMap_eq_cast (A : Type*) [CommRing A] (n : ℤ) :
    algebraMap ℤ A n = Int.cast n := rfl

theorem Rat.cast_eq_algebraMap {K : Type*} [Field K] [CharZero K] {q : ℚ} :
    q = algebraMap ℚ K q := rfl

initialize registerTraceClass `algebra.debug

/-- The head symbols that are to be navigated during the preprocessing step. -/
def heads : Std.HashSet Name := {
  ``HAdd.hAdd, ``Add.add,
  ``HMul.hMul, ``Mul.mul,
  ``HSMul.hSMul, ``SMul.smul,
  ``HPow.hPow, ``Pow.pow,
  ``Neg.neg,
  ``HSub.hSub, ``Sub.sub,
  ``Inv.inv,
  ``HDiv.hDiv, ``Div.div,
  ``Eq,
  ``DFunLike.coe,
  ``NatCast.natCast, ``IntCast.intCast, ``RatCast.ratCast
}

/-- A simproc that prevents simp from descending into any expressions whose head symbol is not in
`heads`. -/
simproc_decl guard (_) := fun e ↦  do
  trace[algebra.debug] m!"Guarding Expression {e}"
  let e' ← withReducible <| whnf e
  let .const n _ := e'.getAppFn
    | return .done { expr := e }
  trace[algebra.debug] m!"With head symbol {n}"
  unless n ∈ heads do return .done { expr := e }
  return .continue (some { expr := e' })

-- TODO: This preprocessing step runs on all subexpressions, even ones in would-be atoms.
-- Possible solution: Have a "guard" simproc that always fires and tells simp to skip
-- the subexpression if it doesn't have the right head.
/-- Remove some nonstandard spellings of `algebraMap` such as `Nat.cast` -/
def preprocess (mvarId : MVarId) : MetaM MVarId := do
  -- collect the available `push_cast` lemmas
  let thms : SimpTheorems := {}
  let thms ← [``Nat.cast_eq_algebraMap, ``Int.cast_eq_algebraMap, ``Rat.cast_eq_algebraMap,
    ``Algebra.algebraMap_eq_smul_one, ``_root_.smul_eq_mul].foldlM (·.addConst ·) thms
  let ctx ← Simp.mkContext { failIfUnchanged := false, zetaDelta := true } (simpTheorems := #[thms])
  let simprocs : Simp.Simprocs := {}
  let simprocs ← simprocs.add ``guard (post := false)
  let (some r, _) ← simpTarget mvarId ctx (simprocs := #[simprocs]) |
    throwError "internal error in algebra tactic: preprocessing should not close goals"
  return r

/-- Clean up the normal form into a more human-friendly format. This does everything
  `RingNF.cleanup` does and also pulls the scalar multiplication from the end of of each term to
  the start. i.e. x * y * (r • 1) → r • (x * y)
  Used by `cleanup`. -/
def cleanupSMul (cfg : RingNF.Config) (r : Simp.Result) : MetaM Simp.Result := do
  let thms : SimpTheorems := {}
  let thms ← [``add_zero, ``add_assoc_rev, ``_root_.mul_one, ``mul_assoc_rev, ``_root_.pow_one,
    ``mul_neg, ``add_neg, ``one_smul, ``mul_smul_comm, ``Nat.algebraMap_eq_cast,
    ``Int.algebraMap_eq_cast].foldlM (·.addConst ·) thms
  let thms ← [``nat_rawCast_0, ``nat_rawCast_1, ``nat_rawCast_2, ``int_rawCast_neg,
      ``nnrat_rawCast, ``rat_rawCast_neg].foldlM (·.addConst · (post := false)) thms
  let ctx ← Simp.mkContext { zetaDelta := cfg.zetaDelta }
    (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  pure <| ←
    r.mkEqTrans (← Simp.main r.expr ctx (methods := Lean.Meta.Simp.mkDefaultMethodsCore {})).1

/-- Turn scalar multiplication by an explicit constant in `R` into multiplication in `A`.

e.g. `(4 : ℚ) • x` becomes `4 * x` but `↑n • x` stays `↑n • x`.
-/
def cleanupConsts (cfg : RingNF.Config) (r : Simp.Result) : MetaM Simp.Result := do
  let thms : SimpTheorems := {}
  let thms ← [``add_zero, ``_root_.one_mul, ``_root_.mul_one,
    ``neg_mul, ``add_neg].foldlM (·.addConst ·) thms
  let thms ← [``ofNat_smul, ``neg_ofNat_smul, ``neg_1_smul, ``nnRat_ofNat_smul_1,
    ``nnRat_ofNat_smul_2, ``rat_ofNat_smul_1, ``rat_ofNat_smul_2
    ].foldlM (·.addConst · (post := false)) thms
  let ctx ← Simp.mkContext { zetaDelta := cfg.zetaDelta }
    (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  pure <| ←
    r.mkEqTrans (← Simp.main r.expr ctx (methods := Lean.Meta.Simp.mkDefaultMethodsCore {})).1

/-- A cleanup routine for `algebra_nf`, which simplifies normalized expressions
to a more human-friendly format. -/
def cleanup (cfg : RingNF.Config) (r : Simp.Result) : MetaM Simp.Result := do
  match cfg.mode with
  | .raw => pure r
  | .SOP => do
    /- These two routines cannot be combined into one because the rules
    "x * (n • y) → n • (x * y)" and "4 • x → 4 * x" are not confluent. -/
    let r ← cleanupSMul cfg r
    let r ← cleanupConsts cfg r
    return r

/-- Collect all scalar rings from scalar multiplications using a state monad for performance.

Note: The match in this definition should be kept up to date with the `Common.eval` function.
-/
partial def collectScalarRingsAux (e : Expr) : StateT (List Expr) MetaM Unit  := do
  match_expr e with
  | SMul.smul R _ _ _ a =>
    modify fun l ↦ R :: l
    collectScalarRingsAux a
  | DFunLike.coe _ _R _A _inst φ _ =>
      match_expr φ with
      | algebraMap R _ _ _ _ =>
        modify fun l ↦ R :: l
      | _ => return
  | HSMul.hSMul R _ _ _ _ a =>
    modify fun l ↦ R :: l
    collectScalarRingsAux a
  | Eq _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | HAdd.hAdd _ _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | Add.add _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | HMul.hMul _ _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | Mul.mul _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | HSub.hSub _ _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | Sub.sub _ _ _ a b => collectScalarRingsAux a; collectScalarRingsAux b
  | HPow.hPow _ _ _ _ a _ => collectScalarRingsAux a
  | Neg.neg _ _ a => collectScalarRingsAux a
  | _ => return

/-- Collect all scalar rings from scalar multiplications and `algebraMap` applications in the
expression. -/
partial def collectScalarRings (e : Expr) : MetaM (List Expr) := do
  let ⟨_, l⟩ ← (collectScalarRingsAux e).run []
  return l

/-- Given two rings, determine which is 'larger' in the sense that the larger is an algebra
over the smaller. Returns the second ring if they're the same or incompatible. -/
def pickLargerRing (r1 r2 : Σ u : Lean.Level, Q(Type u)) :
    MetaM (Σ u : Lean.Level, Q(Type u)) := do
  let ⟨u1, R1⟩ := r1
  let ⟨u2, R2⟩ := r2
  if ← withReducible <| isDefEq R1 R2 then
    return r1
  try
    let _i1 ← synthInstanceQ q(CommSemiring $R1)
    let _i2 ← synthInstanceQ q(Semiring $R2)
    let _i3 ← synthInstanceQ q(Algebra $R1 $R2)
    return r2
  catch _ => try
    let _i1 ← synthInstanceQ q(CommSemiring $R2)
    let _i2 ← synthInstanceQ q(Semiring $R1)
    let _i3 ← synthInstanceQ q(Algebra $R2 $R1)
    return r1
  catch _ =>
    return r2

variable {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
  {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A)) (a : Q($A)) (b : Q($A))

/-- Infer from the expression what base ring the normalization should use.
 Finds all scalar rings in the expression and picks the 'larger' one in the sense that
 it is an algebra over the smaller rings. -/
def inferBase (ca : Cache q($sA)) (e : Expr) : MetaM <| Σ u : Lean.Level, Q(Type u) := do
  let mut rings ← (← collectScalarRings e).mapM getLevelQ'
  rings.foldlM pickLargerRing <| ← do
    match ca.field, ca.czα, ca.dsα, ca.rα with
    | some _, some _, _, _ =>
      -- A is a Field
      pure ⟨0, q(ℚ)⟩
    | _, some _, some _, _ =>
      -- A is a Semifield
      pure ⟨0, q(ℚ≥0)⟩
    | _, _, _, some _ =>
      -- A is a CommRing
      pure ⟨0, q(ℤ)⟩
    | _, _, _, _ =>
      pure ⟨0, q(ℕ)⟩

/-- Frontend of `algebra`: attempt to close a goal `g`, assuming it is an equation of semirings. -/
def proveEq (base : Option (Σ u : Lean.Level, Q(Type u))) (g : MVarId) : AtomM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
    | throwError "algebra failed: not an equality"
  let ⟨v, A⟩ ← getLevelQ' α
  let sA ← synthInstanceQ q(CommSemiring $A)
  let cA ← Algebra.mkCache sA
  let ⟨u, R⟩ ←
    match base with
      | .some p => do pure p
      | none => do
        pure (← inferBase cA (← g.getType))
  trace[algebra.debug] m!"Working in ring {A} over {R}."
  -- This algorithm does not work well if R = A, and we should probably just call `ring`?
  /- This can happen for two reasons: either there is a scalar product with base ring `A`, or
  we inferred the base ring from the typeclass assumptions and `A` is one of `ℕ`, `ℤ` or `ℚ` -/
  /- TODO: Decide if we want to warn the user if this case fires and tell them to either pass the
  base ring explicitly or use ring directly. -/
  -- if ← isDefEq R A then
  --   trace[algebra.debug] m!"Both rings are the same, using `ring` instead."
  --   Ring.proveEq g
  --   return
  let sR ← synthInstanceQ q(CommSemiring $R)
  let sAlg ← synthInstanceQ q(Algebra $R $A)
  let cR ← Algebra.mkCache sR
  have e₁ : Q($A) := e₁; have e₂ : Q($A) := e₂
  let eq ← algCore q($sAlg) cR cA e₁ e₂
  g.assign eq
where
  /-- The core of `proveEq` takes expressions `e₁ e₂ : α` where `α` is a `CommSemiring`,
  and returns a proof that they are equal (or fails). -/
  algCore {u v : Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
      {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A))
      (cR : Cache q($sR)) (cA : Cache q($sA)) (e₁ e₂ : Q($A)) : AtomM Q($e₁ = $e₂) := do
    profileitM Exception "algebra" (← getOptions) do
      let ⟨a, va, pa⟩ ← Common.eval rcℕ (ringCompute sAlg cR cA) cA.toCache e₁
      let ⟨b, vb, pb⟩ ← Common.eval rcℕ (ringCompute sAlg cR cA) cA.toCache e₂
      unless va.eq rcℕ (ringCompute sAlg cR cA) vb do
        let g ← mkFreshExprMVar (← (← Ring.ringCleanupRef.get) q($a = $b))
        throwError "algebra failed, algebra expressions not equal\n{g.mvarId!}"
      have : $a =Q $b := ⟨⟩
      return q($pb ▸ $pa)

/-- `algebra` solves equalities in the language of algebras: ring operations and scalar
multiplications.

Given a goal which is an equality in a commutative `R`-algebra `A`, `algebra` parses the LHS and
RHS of the goal as polynomial expressions of `A`-atoms with coefficients in some semiring `R`, and
closes the goal if the two expressions are the same. The `R`-coefficients are put into ring normal
form.

By default, the scalar ring `R` is inferred automatically by looking for scalar multiplications and
`algebraMap`s present in the expressions. The inference procedure assumes that any two rings `R`
and `S` that appear are comparable, in the sense that either `R` is an `S`-algebra or `S` is an
`R`-algebra.

* `algebra with R` uses the term `R` as the scalar ring, instead of attempting to infer it
automatically.
 -/
elab (name := algebra) "algebra" tk:"!"?:tactic =>
  withMainContext do
    liftMetaTactic' preprocess
    let g ← getMainGoal
    trace[algebra.debug] m!"Preprocessing produced {← g.getType}"
    AtomM.run (if tk.isSome then .default else .reducible) (proveEq none g)

@[tactic_alt algebra]
elab (name := algebraWith) "algebra" tk:"!"? " with " R:term : tactic =>
  withMainContext do
    liftMetaTactic' preprocess
    let ⟨u, R⟩ ← getLevelQ' (← elabTerm R none)
    let g ← getMainGoal
    trace[algebra.debug] m!"Preprocessing produced {← g.getType}"
    AtomM.run (if tk.isSome then .default else .reducible) (proveEq (some ⟨u, R⟩) g)

/-- Check if an expression is an atom or can be simplified by `norm_num`, versus being an algebraic
operation that should be normalized by `eval`. Used by `algebra_nf`. -/
def isAtomOrDerivable (cr : Algebra.Cache sR) (ca : Algebra.Cache sA) (e : Q($A)) :
    AtomM (Option (Option (Common.Result (ExSum sAlg) e))) := do
  let els := try
      pure <| some (evalCast sAlg cr ca (← derive e))
    catch _ => pure (some none)
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n, ca.rα, cr.rα, ca.dsα with
  | ``HAdd.hAdd, _, _, _ | ``Add.add, _, _, _
  | ``HMul.hMul, _, _, _ | ``Mul.mul, _, _, _
  | ``HSMul.hSMul, _, _, _| ``SMul.smul, _, _, _
  | ``HPow.hPow, _, _, _ | ``Pow.pow, _, _, _
  | ``Neg.neg, some _, some _, _
  | ``HSub.hSub, some _, some _, _ | ``Sub.sub, some _, some _, _ => pure none
  | _, _, _, _ => els

/-- The core of `algebra_nf with R` - normalize the expression `e` over the base ring `R` -/
def evalExpr {u : Lean.Level} (R : Q(Type u)) (e : Expr) : AtomM Simp.Result := do
  let e ← withReducible <| whnf e
  _root_.guard e.isApp -- all interesting ring expressions are applications
  let ⟨v, A, e⟩ ← inferTypeQ' e
  let sA ← synthInstanceQ q(CommSemiring $A)
  let sR ← synthInstanceQ q(CommSemiring $R)
  let sAlg ← synthInstanceQ q(Algebra $R $A)
  let cr ← Algebra.mkCache sR
  let ca ← Algebra.mkCache sA
  assumeInstancesCommute
  let ⟨a, _, pa⟩ ← match ← isAtomOrDerivable q($sAlg) cr ca q($e) with
    -- `none` indicates that `eval` will find something algebraic.
  | none => Common.eval rcℕ (ringCompute sAlg cr ca) ca.toCache e
  | some none => failure -- No point rewriting atoms
  | some (some r) => pure r -- Nothing algebraic for `eval` to use, but `norm_num` simplifies.
  pure { expr := a, proof? := pa }

/-- The core of `algebra_nf` - normalize an expression while first inferring the base ring `R`.

This is somewhat unstable as the normal form will depend on `R` and the inferred ring depends
strongly on the form of the initial expression. For example: ⊢ P ((n : ℕ) • x) ∧ P ((n : ℤ) • x)
is unchanged by `algebra_nf` -/
def evalExprInfer (e : Expr) : AtomM Simp.Result := do
  let ⟨_, A, e⟩ ← inferTypeQ' e
  let sA ← synthInstanceQ q(CommSemiring $A)
  let cA ← mkCache q($sA)
  let ⟨_, R⟩ ← inferBase cA e
  evalExpr R e


/-- Attempt to normalize all expressions in an algebra over some fixed base ring. -/
elab (name := algebraNFWith) "algebra_nf" tk:"!"? " with " R:term loc:(location)?  : tactic =>
  withMainContext do
    liftMetaTactic' preprocess
    let mut cfg : RingNF.Config := {}
    let ⟨_u, R⟩ ← getLevelQ' (← elabTerm R none)
    if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
    let loc := (loc.map expandLocation).getD (.targets #[] true)
    let s ← IO.mkRef {}
    let m := AtomM.recurse s cfg.toConfig (wellBehavedDischarge := true)
      (evalExpr R) (cleanup cfg)
    transformAtLocation (m ·) "algebra_nf" loc cfg.ifUnchanged false

def findRings : Expr → MetaM (List Expr) := Expr.foldlM
  (fun l e ↦  do
    match_expr e with
    | HSMul.hSMul R _ _ _ _ _  =>  return R :: l
    | SMul.smul R _ _ _ _  =>  return R :: l
    | _ => return l)
  []

def inferBase' (e : Expr) : MetaM <| Option <| Σ u : Lean.Level, Q(Type u) := do
  let rings ← (← findRings e).mapM getLevelQ'
  let res ← match rings with
  | [] => pure none
  | r :: rs => rs.foldlM pickLargerRing r
  return res

-- set_option linter.unusedVariables false in
/-- Attempt to normalize all expressions in algebras over commutative rings.

The tactic attempts to infer the base ring from the expression being normalized, and may infer
different rings on different subexpressions. This makes the normal form unpredictable.

Use `algebra_nf with` instead. -/
elab (name := algebraNF) "algebra_nf" tk:"!"? loc:(location)?  : tactic =>
  withMainContext do
    liftMetaTactic' preprocess
    let e ← getMainTarget
    let R ← inferBase' e
    let R' : TSyntax `term := ← match R with
    | none => `(term|_)
    | some ⟨_, R⟩ => do
      let S ← PrettyPrinter.delab R
      `(term|$S)
    let suggestion : Tactic.TryThis.Suggestion := {
      suggestion := ← `(tactic| algebra_nf with $R')
      postInfo? := "\n\n 'algebra_nf' without specifying the base ring is unstable. \
      Use `algebra_nf with` instead." }
    Meta.Tactic.TryThis.addSuggestion (← getRef) suggestion (origSpan? := ← getRef)
    let mut cfg := {}
    if tk.isSome then cfg := { cfg with red := .default, zetaDelta := true }
    let loc := (loc.map expandLocation).getD (.targets #[] true)
    let s ← IO.mkRef {}
    let m := AtomM.recurse s cfg.toConfig (wellBehavedDischarge := true) evalExprInfer
      (cleanup cfg)
    transformAtLocation (m ·) "algebra_nf" loc cfg.ifUnchanged false



/-- Prove a monomial equals zero by setting its scalar equal to zero in a side goal.

Used by `match_scalars_alg`
-/
def ExProd.equateZero {a : Q($A)}
(va : ExProd q($sAlg) a) : MetaM <| Q($a = 0) × MVarId :=
  match va with
  | .const (e := a) va => match va with
    | .mk r vr => do
      let pf ← mkFreshExprMVarQ q($r = 0)
      return ⟨q(by subst_vars; simp), pf.mvarId!⟩
  | .mul (x := x) (e := e) vx ve vb => do
    let ⟨pf, ids⟩ ← equateZero vb
    return ⟨q(by subst_vars; simp), ids⟩

/-- Prove a polynomial equals zero by setting its scalars equal to zero as side goals.

Used by `match_scalars_alg`
-/
def equateZero {a : Q($A)} (va : ExSum q($sAlg) a) :
    MetaM <| Q($a = 0) × List MVarId :=
  match va with
  | .zero => do
    return ⟨q(rfl), []⟩
  | .add va₁ va₂ => do
    let ⟨pf, id⟩ ← ExProd.equateZero sAlg va₁
    let ⟨pf', mvars⟩ ← equateZero va₂
    return ⟨q(add_eq_zero $pf $pf'), id :: mvars⟩

/-- Prove two monomials are equal by equating their scalars in the base ring. Assumes the monomials
consist of the same factors.

Used by `match_scalars_alg`.
-/
def ExProd.equateScalarsProd {a b : Q($A)} (va : ExProd q($sAlg) a) (vb : ExProd q($sAlg) b) :
    MetaM <| Q($a = $b) × Option MVarId := do
  match va, vb with
  | .const (e := a) va, .const (e := b) vb => match va, vb with
    | .mk r vr, .mk s vs =>
      if vr.eq rcℕ Ring.ringCompare vs then
        have : $r =Q $s := ⟨⟩
        return ⟨q(rfl), none⟩
      else
        let prs ← mkFreshExprMVarQ q($r = $s)
        return ⟨q(algebraMap_eq_algebraMap' (A := $A) $prs), some prs.mvarId!⟩
  | .mul (x := xa) (e := ea) _vxa _vea va', .mul (x := xb) (e := eb) _vxb veb vb' =>
    -- For x^e * a' = x^e * b', we need a' = b' (bases and exponents already match)
    let ⟨pf, mvOpt⟩ ← equateScalarsProd va' vb'
    have : $xa =Q $xb := ⟨⟩
    have : $ea =Q $eb := ⟨⟩
    return ⟨q(mul_eq_mul_of_eq $pf), mvOpt⟩
  | _, _ =>
    -- This shouldn't happen - the caller should ensure structural equality
    throwError "equateScalarsProd: structure mismatch"



mutual -- partial only to speed up compilation

/-- Compare the structure of two `ExProd` values, ignoring scalar coefficients.
This is used by `equateScalarsSum` to determine if two monomials have the same structure. -/
partial def ExProd.cmpShape
    {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
    {sA : Q(CommSemiring $A)} {sAlg : Q(Algebra $R $A)} {a b : Q($A)} :
    ExProd sAlg a → ExProd sAlg b → Ordering
  | .const _, .const _ => .eq
  | .mul vx₁ ve₁ vb₁, .mul vx₂ ve₂ vb₂ =>
    (vx₁.cmp rcℕ (ringCompare sAlg) vx₂).then
      (ve₁.toExProd.2.cmp rcℕ rcℕ ve₂.toExProd.2) |>.then
      (ExProd.cmpShape vb₁ vb₂)
  | .const .., .mul .. => .lt
  | .mul .., .const .. => .gt

end


/-- Prove two polylnomials are equal by equating their scalars in the base ring as side goals.

Used by `match_scalars_alg`. -/
partial def equateScalarsSum {a b : Q($A)} (va : ExSum q($sAlg) a) (vb : ExSum q($sAlg) b) :
    MetaM <| Q($a = $b) × List MVarId := do
  match va, vb with
  | .zero, .zero => do
    return ⟨q(rfl), []⟩
  | va, .zero => do
    let ⟨pf, mvars⟩ ← equateZero _ va
    return ⟨q($pf), mvars⟩
  | .zero, vb => do
    let ⟨pf, mvars⟩ ← equateZero _ vb
    return ⟨q(Eq.symm $pf), mvars⟩
  | .add (a := a₁) (b := a₂) va₁ va₂, .add (a := b₁) (b := b₂) vb₁ vb₂ =>
    -- Compare the leading terms by shape (ignoring scalar coefficients)
    match ExProd.cmpShape va₁ vb₁ with
    | .lt =>
      -- va₁ < vb₁ in shape, so va₁ must be 0
      let ⟨pr, id⟩ ← ExProd.equateZero sAlg va₁
      let ⟨pf, ids⟩ ← equateScalarsSum va₂ (.add vb₁ vb₂)
      return ⟨q(add_eq_of_zero_add $pr $pf), id :: ids⟩
    | .gt =>
      -- vb₁ < va₁ in shape, so vb₁ must be 0
      let ⟨ps, id⟩ ← ExProd.equateZero sAlg vb₁
      let ⟨pf, ids⟩ ← equateScalarsSum (.add va₁ va₂) vb₂
      return ⟨q(add_eq_of_add_zero $ps $pf), id :: ids⟩
    | .eq =>
      -- The leading terms have the same structure, need to equate coefficients
      let ⟨pf, ids⟩ ← equateScalarsSum va₂ vb₂
      let ⟨pab, idOpt⟩ ← ExProd.equateScalarsProd sAlg va₁ vb₁
      return ⟨q(add_eq_of_eq_eq $pab $pf),
        match idOpt with
        | none => ids
        | some id => id :: ids
      ⟩

/-- Use `f` to simplify the type of a metavariable `g`. Does not recurse. -/
def applySimp (f : Simp.Result → MetaM Simp.Result) (g : MVarId) : MetaM MVarId := do
  let e ← g.getType
  let r ← f {expr := e, proof? := none}
  applySimpResultToTarget g e r

/-- The core of `match_scalars_alg`. Normalizes both sides of an equation and proves their equality
by creating side goals equating matching coefficients in the base ring. -/
def matchScalarsAux (base : Option (Σ u : Lean.Level, Q(Type u))) (g : MVarId) :
    MetaM (List MVarId) :=
  do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
    | throwError "algebra failed: not an equality"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have A : Q(Type v) := α
  let sA ← synthInstanceQ q(CommSemiring $A)
  let cA ← Algebra.mkCache sA
  let ⟨u, R⟩ ←
    match base with
      | .some p => do pure p
      | none => do
        pure (← inferBase cA (← g.getType))
  let sR ← synthInstanceQ q(CommSemiring $R)
  let cR ← Algebra.mkCache sR
  let sAlg ← synthInstanceQ q(Algebra $R $A)
  have e₁ : Q($A) := e₁; have e₂ : Q($A) := e₂
  let ⟨eq, mids⟩ ← AtomM.run .instances <| algCore q($sAlg) cR cA q($e₁) q($e₂)
  let res ← mids.mapM (applySimp (RingNF.cleanup {}))
  g.assign eq
  return res
where
  /-- The core of `matchScalarsAux` takes expressions `e₁ e₂ : α` where `α` is a `CommSemiring`,
  and returns a proof that they are equal (or fails). -/
  algCore {u v : Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
      {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A))
      (cR : Cache q($sR)) (cA : Cache q($sA)) (e₁ e₂ : Q($A)) :
      AtomM (Q($e₁ = $e₂) × List MVarId) := do
    profileitM Exception "algebra" (← getOptions) do
      let ⟨_a, va, pa⟩ ← Common.eval rcℕ (ringCompute sAlg cR cA) cA.toCache e₁
      let ⟨_b, vb, pb⟩ ← Common.eval rcℕ (ringCompute sAlg cR cA) cA.toCache e₂
      let ⟨pab, mvars⟩ ← equateScalarsSum sAlg va vb
      return ⟨q(eq_trans_trans $pa $pb $pab), mvars⟩

/-- Given a goal which is an equality in a commutative R-algebra A, parse the LHS and RHS of the
goal as linear combinations of A-atoms over some semiring R, and reduce the goal to the respective
equalities of the R-coefficients of each atom. The R-coefficients are put into ring normal form. -/
elab (name := matchScalarsAlgWith) "match_scalars_alg" " with " R:term :tactic =>
  withMainContext do
    liftMetaTactic' preprocess
    let ⟨u, R⟩ ← getLevelQ' (← elabTerm R none)
    Tactic.liftMetaTactic (matchScalarsAux <| .some ⟨u, R⟩)

/-- Given a goal which is an equality in a commutative R-algebra A, parse the LHS and RHS of the
goal as linear combinations of A-atoms over some semiring R, and reduce the goal to the respective
equalities of the R-coefficients of each atom. The R-coefficients are put into ring normal form.

The scalar ring R is inferred automatically by looking for scalar multiplications and algebraMaps
present in the expressions.
-/
elab (name := matchScalarsAlg) "match_scalars_alg" :tactic =>
  withMainContext do
    liftMetaTactic' preprocess
    Tactic.liftMetaTactic (matchScalarsAux .none)


end Mathlib.Tactic.Algebra

@[inherit_doc Mathlib.Tactic.Algebra.algebra]
macro (name := fakeRing) "ring":tactic => `(tactic| algebra)
