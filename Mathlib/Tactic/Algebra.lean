/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib.Tactic.Module

open Lean hiding Module
open Meta Elab Qq Mathlib.Tactic List Mathlib.Tactic.Module

namespace Mathlib.Tactic.Algebra

open Mathlib.Meta AtomM

attribute [local instance] monadLiftOptionMetaM

/-

Comments:

To implement `smul` need `mul` to handle the case where the two scalar rings are equal
To implement `mul` need `smul` to handle $(r₁ • s) * (r₂ • s') = (r₁ • r₂) • (s * s'), so is this
one big mutually inductive family?

Also need `add` to implement `mul` properly, so some work to be done.

There's a problem in `matchRingsSMul` when the two rings are defeq. I don't think there is a great
way to cast one of the ExProds to the other.
-/

section ExSum

set_option linter.style.longLine false


open Ring in
mutual

inductive ExSMul : ∀ {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {_ : Q(CommSemiring $R)}
  {_ : Q(CommSemiring $A)} (_ : Q(Algebra $R $A)), (a : Q($A)) → Type
  | smul
    {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)}
      {sR : Q(CommSemiring $R)}
      {sA : Q(CommSemiring $A)}
      {sAlg : Q(Algebra $R $A)} {r : Q($R)} {a : Q($A)} (vr : Ring.ExSum q($sR) q($r))
      (va : Ring.ExProd q($sA) q($a))
      : ExSMul q($sAlg) q($r • $a : $A)

/-- A polynomial expression, which is a sum of monomials. -/
inductive ExSum : ∀ {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {_ : Q(CommSemiring $R)}
  {_ : Q(CommSemiring $A)} (_ : Q(Algebra $R $A)), (a : Q($A)) → Type
  -- | unsafeCast {u v : Lean.Level} {A : Q(Type u)} (B : Q(Type v))
  --   {a : Q($A)} (va : ExSum A a) : ExSum q($B) (q($a):)
  | zero {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)}
      {sR : Q(CommSemiring $R)}
      {sA : Q(CommSemiring $A)}
      {sAlg : Q(Algebra $R $A)} : ExSum q($sAlg) q(0:$A)
  /-- A sum `a + b` is a polynomial if `a` is a monomial and `b` is another polynomial. -/
  | add {v w: Lean.Level} {R : Q(Type v)} {A : Q(Type w)}
    {sR : Q(CommSemiring $R)} {sA : Q(CommSemiring $A)}
    {a b : Q($A)} {sAlg : Q(Algebra $R $A)} :
    ExSMul q($sAlg) q($a) → ExSum q($sAlg) q($b) →
      ExSum q($sAlg) q($a + $b)

end

variable {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
  {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A)) (a : Q($A))



def one : Ring.ExSum q($sA) q(Nat.rawCast (nat_lit 1) + 0 : $A) :=
  -- have n : Q(ℕ) := mkRawNatLit 1
  -- have : $n =Q 1 := ⟨⟩
  .add (.const (e := q(Nat.rawCast (nat_lit 1) : $A)) 1 none) .zero

/-- WARNING : n should be a natural literal. -/
def mkNat (n : Q(ℕ)) : Ring.ExSum q($sA) q(Nat.rawCast $n + 0 : $A) :=
  -- have n : Q(ℕ) := mkRawNatLit 1
  -- have : $n =Q 1 := ⟨⟩
  .add (.const (e := q(Nat.rawCast ($n) : $A)) n.natLit! none) .zero

def _root_.Mathlib.Tactic.Ring.ExProd.one : Ring.ExProd q($sA) q((nat_lit 1).rawCast : $A) :=
  .const 1 none

def ExSMul.ofExProd (va : Ring.ExProd q($sA) q($a)) : ExSMul q($sAlg) q(((Nat.rawCast (nat_lit 1)) + 0:$R) • $a) :=
  .smul one va

def ExSMul.toExSum (va : ExSMul q($sAlg) q($a)) : ExSum q($sAlg) q($a + 0) :=
  .add va .zero

namespace ExSum

end ExSum
end ExSum

structure Result {u : Lean.Level} {A : Q(Type u)} (E : Q($A) → Type) (e : Q($A)) where
  /-- The normalized result. -/
  expr : Q($A)
  /-- The data associated to the normalization. -/
  val : E expr
  /-- A proof that the original expression is equal to the normalized result. -/
  proof : Q($e = $expr)

section Proofs
variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] {e e' ea a a' : A} {r er : R}

theorem atom_pf (h : e = a):
    e = ((nat_lit 1).rawCast : R) • (a ^ (nat_lit 1).rawCast * (nat_lit 1).rawCast) +
      (Nat.rawCast 0) := by
  simp [h]

theorem smul_zero_rawCast : r • ((nat_lit 0).rawCast : A) = (nat_lit 0).rawCast := by
  simp

theorem smul_congr (hr : r = er) (ha : a = ea) (h : er • ea = e'): r • a = e' := by
  rw [hr, ha, h]

theorem add_rawCast_zero : a + Nat.rawCast 0 = a := by
  simp


lemma mul_natCast_zero {R : Type*} [CommSemiring R] (r : R) :
    r * (Nat.rawCast 0 : R) = Nat.rawCast 0 := by
  simp

class LawfulHMul (R₁ R₂ : Type*) [CommSemiring R₁] [CommSemiring R₂] [HMul R₁ R₂ R₁] where
  mul_zero : ∀ r₁ : R₁, r₁ * (0 : R₂) = 0
  zero_mul : ∀ r₂ : R₂, (0 : R₁) * r₂ = 0
  mul_one : ∀ r₁ : R₁, r₁ * (1 : R₂) = r₁
  cast : R₁ → R₂
  cast_mul : ∀ r₁ : R₁, ∀ r₂ : R₂, cast (r₁ * r₂) = cast r₁ * r₂
  cast_one : cast 1 = 1
  cast_zero : cast 0 = 0

attribute [local simp] LawfulHMul.mul_zero LawfulHMul.zero_mul LawfulHMul.cast_mul
  LawfulHMul.cast_one LawfulHMul.cast_zero

-- theorem test [Algebra R ℕ] : r • 1 =

lemma hmul_zero_natCast {R₁ R₂ : Type*} [CommSemiring R₁] [CommSemiring R₂]
    [HMul R₁ R₂ R₁] [LawfulHMul R₁ R₂] (r₁ : R₁) :
  r₁ * (Nat.rawCast 0 : R₂) = Nat.rawCast 0 := by
  simp [LawfulHMul.mul_zero]

lemma hmul_cast_one_mul {R₁ R₂ : Type*} [CommSemiring R₁] [CommSemiring R₂]
    [HMul R₁ R₂ R₁] [LawfulHMul R₁ R₂] (r₂ : R₂) :
    (LawfulHMul.cast ((1:R₁) * r₂) : R₂) = (1 : ℕ) •  r₂ + (Nat.rawCast 0:R₂) := by
  simp

lemma hmul_cast_zero_mul {R₁ R₂ : Type*} [CommSemiring R₁] [CommSemiring R₂]
    [HMul R₁ R₂ R₁] [LawfulHMul R₁ R₂] (r₂ : R₂) :
    (LawfulHMul.cast ((Nat.rawCast 0:R₁) * r₂) : R₂) = (Nat.rawCast 0:R₂) := by
  simp

local instance {R : Type*} [CommSemiring R] : LawfulHMul R R where
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_one := mul_one
  cast := id
  cast_mul := fun _ _ ↦ rfl
  cast_one := rfl
  cast_zero := rfl

end Proofs

-- variable {u v w : Level} {R : Q(Type u)} {A : Q(Type v)} (sA : Q(CommSemiring $A))
--   (sR : Q(CommSemiring $R)) (sAlg : Q(Algebra $R $A))

variable {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
  {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A)) (a : Q($A)) (b : Q($A))

def evalAtom :
    AtomM (Result (ExSum q($sAlg)) q($a)) := do
  let r ← (← read).evalAtom a
  have e' : Q($A) := r.expr
  let (i, ⟨a', _⟩) ← addAtomQ e'
  let ve' : ExSum _ _ := ExSum.add
    (.ofExProd q($sAlg) _ <|
      (Ring.ExBase.atom i (e := a')).toProd (Ring.ExProd.mkNat Ring.sℕ 1).2) .zero
  pure ⟨_, ve', q(sorry)

  -- match r.proof? with
  -- | none =>
  --     have : $e =Q $a' := ⟨⟩
  --     (q(atom_pf rfl))
  -- | some (p : Q($e = $a')) => (q(atom_pf $p))

  ⟩

open NormNum
/--
Two monomials are said to "overlap" if they differ by a constant factor, in which case the
constants just add. When this happens, the constant may be either zero (if the monomials cancel)
or nonzero (if they add up); the zero case is handled specially.
-/
inductive Overlap (a : Q($A)) where
  /-- The expression `e` (the sum of monomials) is equal to `0`. -/
  | zero (_ : Q(IsNat $a (nat_lit 0)))
  /-- The expression `e` (the sum of monomials) is equal to another monomial
  (with nonzero leading coefficient). -/
  | nonzero (_ : Result (ExSMul q($sAlg)) a)

-- variable {a a' a₁ a₂ a₃ b b' b₁ b₂ b₃ c c₁ c₂ : R}

-- theorem add_overlap_pf (x : R) (e) (pq_pf : a + b = c) :
--     x ^ e * a + x ^ e * b = x ^ e * c := by subst_vars; simp [mul_add]

-- theorem add_overlap_pf_zero (x : R) (e) :
--     IsNat (a + b) (nat_lit 0) → IsNat (x ^ e * a + x ^ e * b) (nat_lit 0)
--   | ⟨h⟩ => ⟨by simp [h, ← mul_add]⟩

-- TODO: decide if this is a good idea globally in
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.60MonadLift.20Option.20.28OptionT.20m.29.60/near/469097834
private local instance {m} [Pure m] : MonadLift Option (OptionT m) where
  monadLift f := .mk <| pure f

def _root_.Mathlib.Tactic.Ring.ExSum.isZero (vr : Ring.ExSum sA a) : Bool := match vr with
| .zero .. => true
| _ => false

/--
Given monomials `va, vb`, attempts to add them together to get another monomial.
If the monomials are not compatible, returns `none`.
For example, `xy + 2xy = 3xy` is a `.nonzero` overlap, while `xy + xz` returns `none`
and `xy + -xy = 0` is a `.zero` overlap.
-/
def evalAddOverlap {a b : Q($A)} (va : ExSMul sAlg a) (vb : ExSMul sAlg b) :
    OptionT MetaM (Overlap q($sAlg) q($a + $b)) := do
  Lean.Core.checkSystem decl_name%.toString
  -- IO.println s!"Running evalAddOverlap on {← ppExpr a} and {← ppExpr b}"
  match va, vb with
  | .smul vr (r := r) (a := a) va, .smul vs (r := s) (a := b) vb => do
    guard (va.eq vb)
    -- IO.println "Running Ring.evalAdd"
    let ⟨t, vt, pt⟩ ← Ring.evalAdd q($sR) vr vs
    -- IO.println "Finished Ring.evalAdd"
    have : $a =Q $b := ⟨⟩
    match vt with
    | .zero .. =>
      -- IO.println s!"I think {← ppExpr a} + {← ppExpr b} = 0"
      return .zero q(sorry)
    | _ =>
      -- IO.println s!"I think {← ppExpr a} + {← ppExpr b} ≠ 0"
      return .nonzero ⟨_, .smul vt va, q(sorry)⟩



  -- | .const za ha, .const zb hb => do
  --   let ra := Result.ofRawRat za a ha; let rb := Result.ofRawRat zb b hb
  --   let res ← ra.add rb
  --   match res with
  --   | .isNat _ (.lit (.natVal 0)) p => pure <| .zero p
  --   | rc =>
  --     let ⟨zc, hc⟩ ← rc.toRatNZ
  --     let ⟨c, pc⟩ := rc.toRawEq
  --     pure <| .nonzero ⟨c, .const zc hc, pc⟩
  -- | .mul (x := a₁) (e := a₂) va₁ va₂ va₃, .mul vb₁ vb₂ vb₃ => do
  --   guard (va₁.eq vb₁ && va₂.eq vb₂)
  --   match ← evalAddOverlap va₃ vb₃ with
  --   | .zero p => pure <| .zero (q(add_overlap_pf_zero $a₁ $a₂ $p) : Expr)
  --   | .nonzero ⟨_, vc, p⟩ =>
  --     pure <| .nonzero ⟨_, .mul va₁ va₂ vc, (q(add_overlap_pf $a₁ $a₂ $p) : Expr)⟩
  -- | _, _ => OptionT.fail

-- theorem add_pf_zero_add (b : R) : 0 + b = b := by simp

-- theorem add_pf_add_zero (a : R) : a + 0 = a := by simp

-- theorem add_pf_add_overlap
--     (_ : a₁ + b₁ = c₁) (_ : a₂ + b₂ = c₂) : (a₁ + a₂ : R) + (b₁ + b₂) = c₁ + c₂ := by
--   subst_vars; simp [add_assoc, add_left_comm]

-- theorem add_pf_add_overlap_zero
--     (h : IsNat (a₁ + b₁) (nat_lit 0)) (h₄ : a₂ + b₂ = c) : (a₁ + a₂ : R) + (b₁ + b₂) = c := by
--   subst_vars; rw [add_add_add_comm, h.1, Nat.cast_zero, add_pf_zero_add]

-- theorem add_pf_add_lt (a₁ : R) (_ : a₂ + b = c) : (a₁ + a₂) + b = a₁ + c := by simp [*, add_assoc]

-- theorem add_pf_add_gt (b₁ : R) (_ : a + b₂ = c) : a + (b₁ + b₂) = b₁ + c := by
--   subst_vars; simp [add_left_comm]

variable {sAlg a b} in
partial def ExSMul.cmp :
    ExSMul sAlg a → ExSMul sAlg b → Ordering
  | .smul vr va, .smul vs vb => (va.cmp vb).then (vr.cmp vs)

partial def ExSum.cmp {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
  {sA : Q(CommSemiring $A)} {sAlg : Q(Algebra $R $A)} {a : Q($A)} {b : Q($A)} :
    ExSum sAlg a → ExSum sAlg b → Ordering
  | .zero, .zero => .eq
  | .add a₁ a₂, .add b₁ b₂ => (a₁.cmp b₁).then (a₂.cmp b₂)
  | .zero, .add .. => .lt
  | .add .., .zero => .gt

/-- Adds two polynomials `va, vb` together to get a normalized result polynomial.

* `0 + b = b`
* `a + 0 = a`
* `a * x + a * y = a * (x + y)` (for `x`, `y` coefficients; uses `evalAddOverlap`)
* `(a₁ + a₂) + (b₁ + b₂) = a₁ + (a₂ + (b₁ + b₂))` (if `a₁.lt b₁`)
* `(a₁ + a₂) + (b₁ + b₂) = b₁ + ((a₁ + a₂) + b₂)` (if not `a₁.lt b₁`)
-/
partial def evalAdd {a b : Q($A)} (va : ExSum sAlg a) (vb : ExSum sAlg b) :
    MetaM <| Result (ExSum sAlg) q($a + $b) := do
  Lean.Core.checkSystem decl_name%.toString
  -- IO.println s!"Running evalAdd on {← ppExpr a} and {← ppExpr b}"
  match va, vb with
  | .zero .., vb => return ⟨b, vb, q(sorry)⟩
  | va, .zero .. => return ⟨a, va, q(sorry)⟩
  | .add (a := a₁) (b := _a₂) va₁ va₂, .add (a := b₁) (b := _b₂) vb₁ vb₂ =>
    match ← (evalAddOverlap sAlg va₁ vb₁).run with
    | some (.nonzero ⟨_, vc₁, pc₁⟩) =>
      let ⟨_, vc₂, pc₂⟩ ← evalAdd va₂ vb₂
      return ⟨_, .add vc₁ vc₂, q(sorry)⟩
    | some (.zero pc₁) =>
      let ⟨c₂, vc₂, pc₂⟩ ← evalAdd va₂ vb₂
      return ⟨c₂, vc₂, q(sorry)⟩
    | none =>
      if let .lt := va₁.cmp vb₁ then
        have : $b =Q $b₁ + $_b₂ := ⟨⟩
        let ⟨_c, vc, pc⟩ ← evalAdd va₂ vb
        return ⟨_, .add va₁ vc, q(sorry)⟩
      else
        have : $a =Q $a₁ + $_a₂ := ⟨⟩
        let ⟨_c, vc, pc⟩ ← evalAdd va vb₂
        return ⟨_, .add vb₁ vc, q(sorry)⟩

partial def evalSMulSMul {r : Q($R)} {a : Q($A)} (vr : Ring.ExSum sR r) :
  ExSMul sAlg a →
  MetaM (Result (ExSMul q($sAlg)) q($r • $a))
  | .smul vs va => do
    let ⟨t, vt, pt⟩ ← Ring.evalMul sR vr vs
    return ⟨_, .smul vt va, q(sorry)⟩

partial def evalSMul {r : Q($R)} {a : Q($A)} (vr : Ring.ExSum sR r) :
  ExSum sAlg a →
  MetaM (Result (ExSum q($sAlg)) q($r • $a))
  | .zero .. =>
    pure ⟨_, .zero, q(sorry)⟩
  | .add vsmul vt => do
    let ⟨a, va, pa⟩ ← evalSMulSMul q($sAlg) vr vsmul
    let ⟨t, vt, pt⟩ ← evalSMul vr vt
    return ⟨_, .add va vt, q(sorry)⟩

def evalMul₂ {a b : Q($A)} (va : ExSMul sAlg a) (vb : ExSMul sAlg b) :
    MetaM <| Result (ExSMul sAlg) q($a * $b) := match va, vb with
  | .smul vr va', .smul vs vb' =>  do
    let ⟨_, vt, pt⟩ ← Ring.evalMul sR vr vs
    let ⟨_, vc, pc⟩ ← Ring.evalMulProd sA va' vb'
    return ⟨_, .smul vt vc, q(sorry)⟩

/-- Multiplies a monomial `va` to a polynomial `vb` to get a normalized result polynomial.

* `a * 0 = 0`
* `a * (b₁ + b₂) = (a * b₁) + (a * b₂)`
-/
def evalMul₁ {a b : Q($A)} (va : ExSMul sAlg a) (vb : ExSum sAlg b) :
    MetaM <| Result (ExSum sAlg) q($a * $b) := do
  match vb with
  | .zero => return ⟨_, .zero, q(mul_zero $a)⟩
  | .add vb₁ vb₂ =>
    let ⟨_, vb₁', pb₁'⟩ ← evalMul₂ sAlg va vb₁
    let ⟨_, vt, pt⟩ ← evalMul₁ va vb₂
    let ⟨_, vd, pd⟩ ← evalAdd sAlg vb₁'.toExSum vt
    return ⟨_, vd, q(sorry)⟩

/-- Multiplies two polynomials `va, vb` together to get a normalized result polynomial.

* `0 * b = 0`
* `(a₁ + a₂) * b = (a₁ * b) + (a₂ * b)`
-/
def evalMul {a b : Q($A)} (va : ExSum sAlg a) (vb : ExSum sAlg b) :
    MetaM <| Result (ExSum sAlg) q($a * $b) := do
  match va with
  | .zero => return ⟨_, .zero, q(zero_mul $b)⟩
  | .add va₁ va₂ =>
    let ⟨c₁, vc₁, pc₁⟩ ← evalMul₁ sAlg va₁ vb
    let ⟨c₂, vc₂, pc₂⟩ ← evalMul va₂ vb
    -- IO.println s!"TEST1 : evalMul is adding {← ppExpr c₁} and {← ppExpr c₂} "
    let ⟨_, vd, pd⟩ ← evalAdd sAlg vc₁ vc₂
    return ⟨_, vd, q(sorry)⟩

def _root_.Mathlib.Tactic.Ring.Cache.cast (c : Ring.Cache sR) :
  Ring.Cache sA where
    rα := c.rα
    dsα := c.dsα
    czα := c.czα

variable {a} in
def evalCast :
    NormNum.Result a → Option (Result (ExSum sAlg) a)
  | .isNat _ (.lit (.natVal 0)) p => do
    assumeInstancesCommute
    pure ⟨_, .zero, q(sorry)⟩
  | .isNat _ lit p => do
    assumeInstancesCommute
    -- Lift the literal to the base ring
    -- TODO: extract proof
    pure ⟨_, (ExSMul.smul (mkNat lit) Ring.ExProd.one).toExSum,
      (q(by simp [← Algebra.algebraMap_eq_smul_one]; exact ($p).out))⟩
  -- | .isNegNat rα lit p =>
  --   pure ⟨_, (ExProd.mkNegNat _ rα lit.natLit!).2.toSum, (q(cast_neg $p) : Expr)⟩
  -- We're not handling rational expressions in A.
  | _ => none

def evalPow {a : Q($A)} (b : ℕ) (va : ExSum sAlg a) :
    MetaM <| Result (ExSum q($sAlg)) q($a ^ $b) := do
  if h0 : b = 0 then
    -- is this the right way to do this?
    let p : Q($b = 0) := by rw[h0]; exact q(rfl)
    return ⟨_, .add (.smul one .one) .zero, q(sorry)⟩
  else
    let ⟨hf, vhf, phf⟩ ← evalPow (b/2) va
    let ⟨hf2, vhf2, phf2⟩ ← evalMul sAlg vhf vhf
    if hb : b % 2 = 1 then
      -- TODO: turn this into a `rfl` proof?
      let pb : Q($b % 2 = 1) ← mkDecideProofQ q($b % 2 = 1)
      let ⟨a', va', pa'⟩ ← evalMul sAlg va vhf2
      return ⟨a', va', q(sorry)⟩
    else
      let pb : Q($b % 2 = 0) ← mkDecideProofQ q($b % 2 = 0)
      return ⟨hf2, vhf2, q(sorry)⟩

partial def eval {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
    {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A)) (cacheR : Ring.Cache q($sR)) (e : Q($A)) :
    AtomM (Result (ExSum sAlg) e) := Lean.withIncRecDepth do
  let els := do
    try evalCast sAlg (← derive e)
    catch _ => evalAtom sAlg e
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n with
  | ``HSMul.hSMul | ``SMul.smul => match e with
    | ~q(@HSMul.hSMul $R' $A' _ $inst $r' $a') =>
      if ! (← isDefEq R R') then
        -- TODO: Handle case if R extends R'
        return ← els
      if ! (← isDefEq A A') then
        throwError "HSmul not implemented"
      have r : Q($R) := r'
      have a : Q($A) := a'
      let ⟨_, vr, pr⟩ ← Ring.eval q($sR) cacheR q($r)
      let ⟨_, va, pa⟩ ← eval q($sAlg) cacheR q($a)
      let ⟨ef, vf, pf⟩ ← evalSMul sAlg vr va
      have : v =QL u_2 := ⟨⟩
      have : $A =Q $A' := ⟨⟩
      have : u =QL u_1 := ⟨⟩
      have : $R =Q $R' := ⟨⟩
      have : $r =Q $r' := ⟨⟩
      return ⟨ef, vf, q(sorry)⟩
    | _ => els
  | ``HAdd.hAdd | ``Add.add => match e with
    | ~q($a + $b) =>
      -- throwError "add not implemented"
      let ⟨_, va, pa⟩ ← eval q($sAlg) cacheR q($a)
      let ⟨_, vb, pb⟩ ← eval q($sAlg) cacheR q($b)
      -- IO.println "running evalAdd"
      let ⟨_, vab, pab⟩ ← evalAdd q($sAlg) va vb
      return ⟨_, vab, q(sorry)⟩
    | _ => els
  | ``HMul.hMul | ``Mul.mul => match e with
    | ~q($a * $b) =>
      let ⟨_, va, pa⟩ ← eval sAlg cacheR a
      let ⟨_, vb, pb⟩ ← eval sAlg cacheR b
      let ⟨_, vab, pab⟩ ← evalMul sAlg va vb
      return ⟨_, vab, q(sorry)⟩
    | _ =>
      els
  | ``HPow.hPow | ``Pow.pow => match e with
    | ~q($a ^ ($eb : ℕ)) =>
      let ⟨blit, pf_isNat⟩ ← try NormNum.deriveNat eb q(Nat.instAddMonoidWithOne) catch
        | _ => throwError "Failed to normalize {eb} to a natural literal"
      if ! Expr.isRawNatLit blit then
        /- This code should be unreachable? -/
        throwError s!"Failed to normalize {eb} to a natural literal 3"
      have b : ℕ := blit.natLit!
      -- have : $b =Q $blit := ⟨⟩
      have pb : Q($blit = $b) := q(sorry) -- q(($pf_isNat).out.trans $this)
      let ⟨_, va, pa⟩ ← eval sAlg cacheR a
      let ⟨c, vc, p⟩ ← evalPow sAlg b va
      return ⟨c, vc, q(sorry)⟩
    | _ => els
  | _ =>
    els

open Lean Parser.Tactic Elab Command Elab.Tactic Meta Qq

theorem eq_congr {R : Type*} {a b a' b' : R} (ha : a = a') (hb : b = b') (h : a' = b') : a = b := by
  subst ha hb
  exact h

def normalize (goal : MVarId) {u v : Lean.Level} (R : Q(Type u)) (A : Q(Type v)) :
    AtomM MVarId := do
  -- let goal ← try getMainGoal catch
  --   | _ => return
  let some (A', e₁, e₂) :=
    (← whnfR <|← instantiateMVars <|← goal.getType).eq?
    | throwError "algebra failed: not an equality"
  -- IO.println s!"A' = {← ppExpr A'}"
  -- IO.println s!"A = {← ppExpr A}"
  guard (←isDefEq A A')
  have sA : Q(CommSemiring $A) := ← synthInstanceQ q(CommSemiring $A)
  have sR : Q(CommSemiring $R) := ← synthInstanceQ q(CommSemiring $R)
  have sAlg : Q(Algebra $R $A) := ← synthInstanceQ q(Algebra $R $A)

  -- IO.println "synthed"
  have e₁ : Q($A) := e₁
  have e₂ : Q($A) := e₂
  -- IO.println "test"
  let cr ← Ring.mkCache sR
  let ca ← Ring.mkCache sA

  let (⟨a, exa, pa⟩ : Result (ExSum sAlg) e₁) ← eval sAlg cr e₁
  let (⟨b, exb, pb⟩ : Result (ExSum sAlg) e₂) ← eval sAlg cr e₂

  let g' ← mkFreshExprMVarQ q($a = $b)
  goal.assign q(eq_congr $pa $pb $g' : $e₁ = $e₂)
  -- if ← isDefEq a b then
    -- have : $a =Q $b := ⟨⟩
    -- g'.mvarId!.assign (q(rfl : $a = $b) : Expr)
  return g'.mvarId!
  -- else throwError "algebra failed to normalize expression."
  -- let l ← ExSum.eq_exSum g'.mvarId! a b exa exb
  -- Tactic.pushGoals l
  /- TODO: we probably want to do some sort of normalization of intermediate expressions.
    `norm_num` does not seem set up to do this very well. Much of the work is actually done by
    `simp`, namely `a+0 -> a` and `a*1 -> a`. -/
  -- for g in l do
  --   let l ← evalTacticAt (← `(tactic| norm_num)) g
  --   Tactic.pushGoals l
    -- NormNum.normNumAt g (← getSimpContext)


def inferLevelQ (e : Expr) : MetaM (Σ u : Lean.Level, Q(Type u)) := do
  let .sort u ← whnf (← inferType e) | throwError "not a type{indentExpr e}"
  let some v := (← instantiateLevelMVars u).dec | throwError "not a Type{indentExpr e}"
  return ⟨v, e⟩

elab (name := algebra) "algebra " R:term ", " A:term : tactic =>
  withMainContext do
    let ⟨u, R⟩ ← inferLevelQ (← elabTerm R none)
    let ⟨v, A⟩ ← inferLevelQ (← elabTerm A none)
    -- IO.println s!"Rings are {← ppExpr R} : Type {u} and {← ppExpr A} : Type {v}"

    let g ← getMainGoal
    let g ← AtomM.run .default (normalize g R A)
    Tactic.pushGoal g


example {x : ℚ} {y : ℤ} : y • x + (1:ℤ) • x = (1 + y) • x := by
  algebra ℤ, ℚ
  rfl

example {S R A : Type*} [CommSemiring S] [CommSemiring R] [CommSemiring A] [Algebra S R]
    [Algebra R A] [Algebra S A] [IsScalarTower S R A] {r : R} {s : S} {a₁ a₂ : A} :
    (s • a₁) * (r • a₂) = (s • r) • (a₁ * a₂) := by
  simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_assoc]
  rw [smul_comm]


end Mathlib.Tactic.Algebra


example (x : ℚ) :  x + x = (2 : ℤ) • x := by
  algebra ℤ, ℚ
  -- match_scalars <;> simp
  rfl

example (x : ℚ) : x = 1 := by
  algebra ℤ, ℚ
  sorry

example (x y : ℚ) : x + y  = y + x := by
  algebra ℕ, ℚ
  rfl

example (x y : ℚ) : x + y*x + x + y  = (x + x) + (x*y + y) := by
  algebra ℕ, ℚ
  rfl

-- BUG: ExProd.one doesn't match with the empty product in sums.
example (x : ℚ) : x + x + x  = 3 * x := by
  algebra ℕ, ℚ
  sorry

example (x : ℚ) : (x + x) + (x + x)  = x + x + x + x := by
  algebra ℕ, ℚ
  -- simp
  simp only [Nat.rawCast, Nat.cast_one, pow_one, Nat.cast_ofNat, one_smul, Nat.cast_zero, add_zero,
    mul_one]

example (x y : ℚ) : x + (y)*(x+y) = 0 := by
  algebra ℕ, ℚ
  simp
  sorry

example (x y : ℚ) : x + (x)*(x+y) = 0 := by
  algebra ℕ, ℚ
  simp
  sorry


example (x y : ℚ) : (x * x + x * y) + (x * y + y * y) = 0 := by
  algebra ℕ, ℚ
  simp
  sorry

example (x y : ℚ) : (x + y)*(x+y) = x*x + 2 * x * y + y * y := by
  -- simp_rw [← SMul.smul_eq_hSMul]
  algebra ℕ, ℚ
  rfl

--   sorry

--   -- match_scalars <;> simp

example (x y : ℚ) : (x+y)*x = 1 := by
  -- simp_rw [← SMul.smul_eq_hSMul]
  algebra ℕ, ℚ
  simp only [show Nat.rawCast 1 = 1 by rfl]
  simp only [pow_one, Nat.rawCast, Nat.cast_one, mul_one, one_smul, Nat.cast_ofNat, Nat.cast_zero,
    add_zero]
  sorry

example (x y : ℚ) : (x+y)*y  = 1 := by
  -- simp_rw [← SMul.smul_eq_hSMul]
  algebra ℕ, ℚ
  simp only [show Nat.rawCast 1 = 1 by rfl]
  simp only [pow_one, Nat.rawCast, Nat.cast_one, mul_one, one_smul, Nat.cast_ofNat, Nat.cast_zero,
    add_zero]
  sorry


example (x : ℚ) : (x + 1)^3 = x^3 + 3*x^2 + 3*x + 1 := by
  algebra ℕ, ℚ
  rfl

example (x : ℚ) (hx : x = 0) : (x+1)^10 = 1 := by
  algebra ℕ, ℚ
  -- ring_nf
  simp [← add_assoc]

  simp [hx]
