/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Tactic.Ring.RingNF

import Mathlib.Tactic.Algebra.Lemmas

/-!
# The `algebra` tactic
A suite of three tactics for solving equations in commutative algebras over commutative (semi)rings,
where the exponents can also contain variables.

Based largely on the implementation of `ring`. The `algebra` normal form mirrors that of `ring`
except that the constants are expressions in the base ring that are kept in ring normal form.

## Organization
The structure of this file closely matches that of `Ring.Basic`.

* Normalized expressions are stored as an `ExSum`, a type which is part of the inductive family of
types `ExSum`, `ExProd` and `ExBase`.
* We implement evaluation functions (`evalAdd`, `evalMul`, etc.) for all of the operations we
support, which take normalized expressions and return a new normalized expression together with
a proof that the new expression equals the operation applied to the input expressions.
* While `ring` stores coefficients as rational numbers normalized by `norm_num`, `algebra` stores
coefficients as experssions in the base ring `R`, normalized by `ring`.

This tactic is used internally to implement the `polynomial` tactic.

## Limitations
The main limitation of the current implementation is that it does not handle rational constants
when the algebra `A` is a field but the base ring `R` is not. This is never an issue when working
with polynomials, but would be an issue when working with a number field over its ring of integers.

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

inductive BaseType : (a : Q($A)) → Type
  | mk (r : Q($R)) (_ : Ring.ExSum q($sR) r) : BaseType q(algebraMap $R $A $r)

@[expose]
def ExBase := Common.ExBase (BaseType sAlg) sA
@[expose]
def ExProd := Common.ExProd (BaseType sAlg) sA
@[expose]
def ExSum := Common.ExSum (BaseType sAlg) sA

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
      (q(sorry))⟩
  | .isNegNat rA lit p => do
    let some crR := cR.rα | none
    let some crA := cA.rα | none
    -- let some rR := cR.rα | none
    let ⟨r, vr⟩ := Ring.ExProd.mkNegNat q($sR) q(inferInstance) lit.natLit!
    have : $r =Q Int.rawCast (Int.negOfNat $lit) := ⟨⟩
    assumeInstancesCommute
    pure ⟨_, (Common.ExProd.const ⟨_, vr.toSum⟩).toSum, (q(isInt_negOfNat_eq $p))⟩
  | .isNNRat rA q n d p => do
    -- TODO: use semifields here.
    let some dsR := cR.dsα | none
    let some dsA := cA.dsα | none
    assumeInstancesCommute
    let ⟨r, vr⟩ := Ring.ExProd.mkNNRat q($sR) q(inferInstance) q n d q(IsNNRat.den_nz (α := $A) $p)
    have : $r =Q (NNRat.rawCast $n $d : $R) := ⟨⟩
    pure ⟨_, (Common.ExProd.const ⟨_, vr.toSum⟩).toSum, q(isNNRat_eq_rawCast (a := $a) $p)⟩
  | .isNegNNRat dA q n d p => do
    let some fR := cR.field | none
    let some fA := cA.field | none
    assumeInstancesCommute
    let ⟨r, vr⟩ := Ring.ExProd.mkNegNNRat q($sR) q(inferInstance) q n d q(IsRat.den_nz $p)
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
    (smul : Q(HSMul $R' $A $A)) (r' : Q($R')) :
    MetaM <| Σ r : Q($R), Q(∀ a : $A, $r • a = $r' • a) := do
  if (← isDefEq R R') then
    have : u =QL u' := ⟨⟩
    have : $R =Q $R' := ⟨⟩
    assumeInstancesCommute
    return ⟨q($r'), q(fun _ => rfl)⟩
  let _sR' ← synthInstanceQ q(CommSemiring $R')
  -- Synthesize the algebra instance showing R is an R'-algebra
  let _algR'R ← synthInstanceQ q(Algebra $R' $R)
  -- TODO: Determine if I should be synthing this instance.
  let _mod ← synthInstanceQ q(Module $R' $A)
  let _ist ← synthInstanceQ q(IsScalarTower $R' $R $A)
  assumeInstancesCommute
  let r_cast : Q($R) := q(algebraMap $R' $R $r')
  let res ← pushCast r_cast
  have r₀ : Q($R) := res.expr
  let pf : Q($r₀ = $r_cast) ← res.getProof
  return ⟨r₀, q(fun a ↦ $pf ▸ algebraMap_smul $R $r' a)⟩

namespace RingCompute

def add (cR : Algebra.Cache sR) (a b : Q($A)) (za : BaseType sAlg a) (zb : BaseType sAlg b) :
    MetaM (Common.Result (BaseType sAlg) q($a + $b) × Option Q(IsNat ($a + $b) 0)) := do
  let ⟨r, vr⟩ := za
  let ⟨s, vs⟩ := zb
  let ⟨t, vt, pt⟩ ← Common.evalAdd (Ring.ringCompute sR) rcℕ vr vs
  match vt with
  | .zero =>
    -- TODO: Why doesn't the match substitute t?
    have : $t =Q 0 := ⟨⟩
    return  ⟨⟨_, .mk _ vt, q(sorry)⟩, some q(sorry)⟩
  | vt =>
    return ⟨⟨_, .mk _ vt, q(sorry)⟩, none⟩

def mul (a b : Q($A)) (za : BaseType sAlg a) (zb : BaseType sAlg b) :
    MetaM (Common.Result (BaseType sAlg) q($a * $b)) := do
  let ⟨r, vr⟩ := za
  let ⟨s, vs⟩ := zb
  let ⟨t, vt, pt⟩ ← Common.evalMul (Ring.ringCompute sR) rcℕ vr vs
  return ⟨_, .mk _ vt, q(by simp [← $pt, map_mul])⟩

def cast (cR : Algebra.Cache sR) (u' : Level) (R' : Q(Type u')) (sR' : Q(CommSemiring $R'))
    (_smul : Q(HSMul $R' $A $A)) (r' : Q($R'))
    (_rx : AtomM (Common.Result (Common.ExSum (Ring.BaseType sR') q($sR')) q($r'))) :
    AtomM ((y : Q($A)) × Common.ExSum (BaseType sAlg) sA q($y) ×
      Q(∀ (a : $A), $r' • a = $y * a)) := do
  let ⟨r, pf_smul⟩ ← evalSMulCast q($sAlg) q(inferInstance) r'
  have : u' =QL u := ⟨⟩
  /- Here's a terrifying error: Replacing the sR with q($sR) makes Qq believe that u = v,
    introducing kernel errors during runtime. -/
  let ⟨_r'', vr, pr⟩ ←
    Common.eval Ring.ringCompute rcℕ (Ring.ringCompute sR) cR.toCache q($r)
  return ⟨_, Common.ExSum.add (Common.ExProd.const (.mk _ vr)) .zero, q(sorry)⟩

def neg (cR : Algebra.Cache sR) (a : Q($A)) (_rA : Q(CommRing $A)) (za : BaseType sAlg a) :
    MetaM (Common.Result (BaseType sAlg) q(-$a)) := do
  let ⟨r, vr⟩ := za
  match cR.rα with
  | some rR =>
    let ⟨t, vt, pt⟩ ← Common.evalNeg (Ring.ringCompute sR) q($rR) vr
    return ⟨_, .mk _ vt, q(sorry)⟩
  | none => failure

def pow (a : Q($A)) (za : BaseType sAlg a) (b : Q(ℕ))
    (vb : Common.ExProd Common.btℕ Common.sℕ q($b)) :
    OptionT MetaM (Common.Result (BaseType sAlg) q($a ^ $b)) := do
  let ⟨r, vr⟩ := za
  let ⟨b', vb'⟩ := vb.toExProdNat
  have : $b =Q $b' := ⟨⟩
  let ⟨s, vs, ps⟩ ← Common.evalPow₁ (Ring.ringCompute sR) rcℕ vr (vb')
  return ⟨_, ⟨_, vs⟩, q(sorry)⟩

def inv {a : Q($A)} (czA : Option Q(CharZero $A)) (fA : Q(Semifield $A))
    (za : BaseType sAlg a) : AtomM (Option (Common.Result (BaseType sAlg) q($a⁻¹))) := do
  let ⟨r, vr⟩ := za
  let ⟨s, vs, ps⟩ ← Common.ExSum.evalInv (Ring.ringCompute sR) rcℕ fA czA vr
  return some ⟨_, ⟨_, vs⟩, q(sorry)⟩

def derive' (cR : Algebra.Cache sR) (cA : Algebra.Cache sA) (x : Q($A)) :
    MetaM (Common.Result (Common.ExSum (BaseType sAlg) sA) q($x)) := do
  let res ← NormNum.derive x
  return ← evalCast sAlg cR cA res

def isOne {x : Q($A)} (zx : BaseType sAlg x) : Option Q(IsNat $x 1) :=
  let ⟨_, vx⟩ := zx
  match vx with
  | .add (.const c) .zero =>
    match (Ring.ringCompute sR).isOne c with
    | some pf => some q(sorry)
    | none => none
  | .zero => none
  | _ => none

end RingCompute

open RingCompute in
def ringCompute (cR : Algebra.Cache sR) (cA : Algebra.Cache sA) :
    Common.RingCompute (BaseType sAlg) sA where
  add := add sAlg cR
  mul := mul sAlg
  cast := cast sAlg cR
  neg := neg sAlg cR
  pow := pow sAlg
  inv := inv sAlg
  derive := derive' sAlg cR cA
  eq := fun ⟨_, vx⟩ ⟨_, vy⟩ => vx.eq rcℕ (Ring.ringCompute sR) vy
  compare := fun ⟨_, vx⟩ ⟨_, vy⟩ => vx.cmp rcℕ (Ring.ringCompute sR) vy
  isOne := isOne sAlg
  one := ⟨_, ⟨_, (Ring.ExProd.mkNat sR 1).2.toSum⟩, q(by simp)⟩
  toString := fun ⟨_, vx⟩ ↦ s!"{vx.toString rcℕ (Ring.ringCompute sR)}"

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

/-- Remove some nonstandard spellings of `algebraMap` such as `Nat.cast` -/
def preprocess (mvarId : MVarId) : MetaM MVarId := do
  -- collect the available `push_cast` lemmas
  let thms : SimpTheorems := {}
  let thms ← [``Nat.cast_eq_algebraMap, ``Int.cast_eq_algebraMap,
    ``Algebra.algebraMap_eq_smul_one].foldlM (·.addConst ·) thms
  let ctx ← Simp.mkContext { failIfUnchanged := false } (simpTheorems := #[thms])
  let (some r, _) ← simpTarget mvarId ctx (simprocs := #[]) |
    throwError "internal error in polynomial tactic: preprocessing should not close goals"
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

/-- Collect all scalar rings from scalar multiplications using a state monad for performance. -/
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
over the smaller. Returns the first ring if they're the same or incompatible. -/
def pickLargerRing (r1 r2 : Σ u : Lean.Level, Q(Type u)) :
    MetaM (Σ u : Lean.Level, Q(Type u)) := do
  let ⟨u1, R1⟩ := r1
  let ⟨u2, R2⟩ := r2
  if ← withReducible <| isDefEq R1 R2 then
    return r1
  -- Try to show R2 is an R1-algebra (meaning R1 is smaller, so return R2)
  try
    let _i1 ← synthInstanceQ q(CommSemiring $R1)
    let _i2 ← synthInstanceQ q(Semiring $R2)
    let _i3 ← synthInstanceQ q(Algebra $R1 $R2)
    return r2
  catch _ => try
    -- Try to show R1 is an R2-algebra (meaning R2 is smaller, so return R1)
    let _i1 ← synthInstanceQ q(CommSemiring $R2)
    let _i2 ← synthInstanceQ q(Semiring $R1)
    let _i3 ← synthInstanceQ q(Algebra $R2 $R1)
    return r1
  catch _ =>
    -- If neither works, return the first ring
    return r1

variable {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
  {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A)) (a : Q($A)) (b : Q($A))

/-- Infer from the expression what base ring the normalization should use.
 Finds all scalar rings in the expression and picks the 'larger' one in the sense that
 it is an algebra over the smaller rings. -/
def inferBase (ca : Cache q($sA)) (e : Expr) : MetaM <| Σ u : Lean.Level, Q(Type u) := do
  let rings ← (← collectScalarRings e).mapM getLevelQ'
  let res ← match rings with
  | [] =>
    match ca.field, ca.czα, ca.rα with
    | some _, some _, _ =>
      -- A is a Field
      return ⟨0, q(ℚ)⟩
    | _, _, some _ =>
      -- A is a CommRing
      return ⟨0, q(ℤ)⟩
    | _, _, _ =>
      return ⟨0, q(ℕ)⟩
  | r :: rs => rs.foldlM pickLargerRing r
  return res

/-- Frontend of `algebra`: attempt to close a goal `g`, assuming it is an equation of semirings. -/
def proveEq (base : Option (Σ u : Lean.Level, Q(Type u))) (g : MVarId) : AtomM Unit := do
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
      let ⟨a, va, pa⟩ ← Common.eval Ring.ringCompute rcℕ (ringCompute sAlg cR cA) cA.toCache e₁
      let ⟨b, vb, pb⟩ ← Common.eval Ring.ringCompute rcℕ (ringCompute sAlg cR cA) cA.toCache e₂
      unless va.eq rcℕ (ringCompute sAlg cR cA) vb do
        -- let _ := va.eq vb
        let g ← mkFreshExprMVar (← (← Ring.ringCleanupRef.get) q($a = $b))
        -- let g ← mkFreshExprMVar (q($a = $b))
        throwError "algebra failed, algebra expressions not equal\n{g.mvarId!}"
      have : $a =Q $b := ⟨⟩
      -- let pb : Q($e₂ = $a) := pb
      return q($pb ▸ $pa)

/-- Given a goal which is an equality in a commutative R-algebra A, parse the LHS and RHS of the
goal as linear combinations of A-atoms over some semiring R, and close the goal if the two
expressions are the same. The R-coefficients are put into ring normal form.

The scalar ring R is inferred automatically by looking for scalar multiplications and algebraMaps
present in the expressions.
 -/
elab (name := algebra) "algebra":tactic =>
  withMainContext do
    liftMetaTactic' preprocess
    let g ← getMainGoal
    AtomM.run .default (proveEq none g)

/-- Given a goal which is an equality in a commutative R-algebra A, parse the LHS and RHS of the
goal as linear combinations of A-atoms over some semiring R, and close the goal if the two
expressions are the same. The R-coefficients are put into ring normal form. -/
elab (name := algebraWith) "algebra" " with " R:term : tactic =>
  withMainContext do
    liftMetaTactic' preprocess
    let ⟨u, R⟩ ← getLevelQ' (← elabTerm R none)
    let g ← getMainGoal
    AtomM.run .default (proveEq (some ⟨u, R⟩) g)

end Mathlib.Tactic.Algebra
