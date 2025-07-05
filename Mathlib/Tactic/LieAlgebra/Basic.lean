/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Zixun Guo, Wanyi He, Jingting Wang
-/
import Mathlib.Algebra.Lie.Basic
import Qq

/-!
# The tactic on Lie Ring - lie_ring

The implementation of this tactic imitates the `ring` tactic, using the `Qq` package to implement a
a specific elimination procedure.

This part of the tactic only attempts to deal with `ℤ`-coefficients (which means only the `LieRing`
instance will be used), reducing everything to the linear combination of elements of the Lyndon
basis.

The elimination approach implemented here follows the theory of Hall sets and Lyndon words,
see for example, ‹https://personal.math.ubc.ca/~cass/research/pdf/Free.pdf›
-/

open Lean Meta Elab Tactic Qq

namespace Mathlib.Tactic.LieRing

attribute [local instance] Mathlib.Meta.monadLiftOptionMetaM

section inductiveTypes

/--
This inductive type represents nested Lie Brackets, and the implementation of the evalLie function
will ensure that it actually corresponds to a term in Lyndon normal form.
-/
inductive ExLie : ∀ {u : Lean.Level} {α : Q(Type u)}, Q(LieRing $α) → (e : Q($α)) → Type
  | atom {sα} {e} (id : ℕ) : ExLie sα e
  | lie {u : Lean.Level} {α : Q(Type u)} {sα : Q(LieRing $α)} {a b : Q($α)} :
    ExLie sα a → ExLie sα b → ExLie sα q(⁅$a, $b⁆)
deriving Repr

/--
This inductive type represents a simplified form of an expression produced by `lie_ring`,
but requires the coefficients to be integer literals.
-/
inductive ExSum : ∀ {u : Lean.Level} {α : Q(Type u)}, Q(LieRing $α) → (e : Q($α)) → Type
  | zero {u : Lean.Level} {α : Q(Type u)} {sα : Q(LieRing $α)} : ExSum sα q(0 : $α)
  | add {u : Lean.Level} {α : Q(Type u)} {sα : Q(LieRing $α)} {a : Q($α)} {b : Q($α)} :
    ExLie sα a → (coeff : ℤ) → ExSum sα b → ExSum sα q($coeff • $a + $b)
deriving Repr

end inductiveTypes

section Functions

/-- Check the boolean equality of two `ExLie` terms. -/
def ExLie.eq {u : Lean.Level} {α : Q(Type u)} {sα : Q(LieRing $α)} {a b : Q($α)} :
    ExLie sα a → ExLie sα b → Bool
  | .atom i, .atom j => i == j
  | .lie a₁ a₂, .lie b₁ b₂ => a₁.eq b₁ && a₂.eq b₂
  | _, _ => false

/-- Check the boolean equality of two `ExSum` terms. -/
def ExSum.eq {u : Lean.Level} {α : Q(Type u)} {sα : Q(LieRing $α)} {a b : Q($α)} :
    ExSum sα a → ExSum sα b → Bool
  | .zero, .zero => true
  | .add a₁ n₁ b₁, .add a₂ n₂ b₂ => a₁.eq a₂ && n₁ == n₂ && b₁.eq b₂
  | _, _ => false

/--
Given a nested bracket expression, flatten it into a list of natural numbers containing
the index of the atoms in the order they appear. (This function facilitates the `ExLie.cmp` function
that compares two `ExLie` elements)
-/
def ExLie.toListNat {u : Lean.Level} {α : Q(Type u)} {sα : Q(LieRing $α)} {a : Q($α)} :
    ExLie sα a → List Nat
  | .atom i => [i]
  | .lie a₁ a₂ => a₁.toListNat ++ a₂.toListNat

/-- Compare two `ExLie` elements using lexicographic order of their flattened list. -/
def ExLie.cmp {u : Lean.Level} {α : Q(Type u)} {sα : Q(LieRing $α)} {a : Q($α)} {b : Q($α)} :
    ExLie sα a → ExLie sα b → Ordering := fun x y ↦ compare x.toListNat y.toListNat

/--
Check whether an `ExLie` expression satisfies the Lyndon property (which in our case means that
the nested bracket term is already reduced). More information on this and how it's applied in
the algorithm can be seen in the reference link in the documentation.
-/
def ExLie.isLyndon {u : Lean.Level} {α : Q(Type u)} {sα : Q(LieRing $α)} {a : Q($α)} :
    ExLie sα a → Bool
  | .atom _ => true
  | .lie a₁ a₂ => a₁.isLyndon && a₂.isLyndon && (a₁.cmp a₂).isLT &&
    match a₁ with
    | .atom _ => true
    | .lie _ y => (a₂.cmp y).isLE

/-- Convert an `ExLie` element `v` to the `ExSum` element `(1 : ℤ) • v + 0`. -/
def ExLie.toExSum {u : Lean.Level} {α : Q(Type u)} {sα : Q(LieRing $α)} {a : Q($α)}
    (v : ExLie sα a) : ExSum sα q((1 : ℤ) • $a + 0) := .add v 1 .zero

end Functions

section Algorithm

variable {u : Lean.Level}

/-- A Structure to store the result of the normalization and the equality proof. -/
structure Result {α : Q(Type u)} (E : Q($α) → Type) (e : Q($α)) where
  /-- The normalized result. -/
  expr : Q($α)
  /-- The data associated to the normalization. -/
  val : E expr
  /-- A proof that the original expression is equal to the normalized result. -/
  proof : Q($e = $expr)

variable {α : Q(Type u)}

private lemma smul_aux {M : Type*} [AddCommGroup M] {a₁ a₂ a₃ : M} (n₁ n₂ n₃ : ℤ) :
    n₃ = n₁ * n₂ → n₁ • a₂ = a₃ → n₁ • (n₂ • a₁ + a₂) = n₃ • a₁ + a₃ :=
  fun _ _ ↦ (by subst_vars; simp [smul_smul])

/-- This function evaluates the `ℤ`-scaler multiple of an element of `ExSum` into normal form. -/
def evalSmul (sα : Q(LieRing $α)) {a : Q($α)} (va : ExSum sα a) (coeff : ℤ) :
    Result (ExSum sα) q($coeff • $a) :=
  match va with
  | .zero => ⟨q(0), .zero, q(smul_zero $coeff)⟩
  | .add (a := a₁) (b := a₂) va₁ n va₂ =>
    let coeff' : ℤ := coeff * n
    let ⟨c₁, vc₁, pc₁⟩ := evalSmul sα va₂ coeff
    ⟨q($coeff' • $a₁ + $c₁), .add va₁ coeff' vc₁, q(smul_aux $coeff $n $coeff' rfl $pc₁)⟩

section evalAdd

variable {α : Q(Type u)} {L : Type*} [AddCommGroup L]

variable {a a' a₁ a₂ a₃ b b' b₁ b₂ b₃ c c₁ c₂ : L}

variable {n₁ n₂ n₃ : ℤ}

private theorem add_pf_zero_add (b : L) : 0 + b = b := by simp

private theorem add_pf_add_zero (a : L) : a + 0 = a := by simp

private theorem add_pf_add_lt (a₁ : L) (_ : a₂ + (n₂ • b₁ + b₂) = c) :
    (n₁ • a₁ + a₂) + (n₂ • b₁ + b₂) = n₁ • a₁ + c := by simp [*, add_assoc]

private theorem add_pf_add_gt (b₁ : L) (_ : (n₁ • a₁ + a₂) + b₂ = c) :
    n₁ • a₁ + a₂ + (n₂ • b₁ + b₂) = n₂ • b₁ + c := by
  subst_vars; simp [add_left_comm]

private theorem add_pf_add_overlap_zero (h₀ : n₁ + n₂ = 0) (h₁ : a₁ = b₁) (h₂ : a₂ + b₂ = c) :
    n₁ • a₁ + a₂ + (n₂ • b₁ + b₂) = c := by
  have : n₁ • a₁ + n₂ • b₁ = 0 := by
    subst_vars; simp [← add_smul n₁ n₂ b₁, h₀]
  subst_vars; rw [add_add_add_comm, this, add_pf_zero_add]

private theorem add_pf_add_overlap (_ : a₁ = b₁) (_ : a₂ + b₂ = c₂) :
    (n₁ • a₁ + a₂ : L) + (n₂ • b₁ + b₂) = (n₁ + n₂) • a₁ + c₂ := by
  subst_vars; simp [add_assoc, add_left_comm, ← add_assoc, add_comm, add_assoc, ← add_smul]

/-- This function evaluates the sum of two `ExSum` expressions and reduce it to the normal form. The
"monomials" are sorted in the order of `ExLie.cmp`. -/
private partial def evalAdd (sα : Q(LieRing $α)) {a b : Q($α)} (va : ExSum sα a) (vb : ExSum sα b) :
    Lean.Core.CoreM <| Result (ExSum sα) q($a + $b) := do
  Lean.Core.checkSystem decl_name%.toString
  match va, vb with
  | .zero, vb => return ⟨b, vb, q(add_pf_zero_add $b)⟩
  | va, .zero => return ⟨a, va, q(add_pf_add_zero $a)⟩
  | .add (a := a₁) (b := _a₂) va₁ n₁ va₂, .add (a := b₁) (b := _b₂) vb₁ n₂ vb₂ =>
    if va₁.eq vb₁ then
      if n₁ + n₂ == 0 then
        let ⟨c, vc, pc⟩ ← evalAdd sα va₂ vb₂
        let n₃ : ℤ := n₁ + n₂
        let h : Q($n₁ + $n₂ = $n₃) := q(rfl (a := $n₃))
        let h' : Q($n₃ = (0 : ℤ)) := (q(rfl (a := $n₃)) : Expr)
        haveI' : $a₁ =Q $b₁ := ⟨⟩
        return ⟨c, vc, (q(add_pf_add_overlap_zero (Eq.trans $h $h') (rfl (a := $a₁)) $pc) : Expr)⟩
      else
        let ⟨_, vc, pc⟩ ← evalAdd sα va₂ vb₂
        haveI' : $a₁ =Q $b₁ := ⟨⟩
        return ⟨_, .add va₁ (n₁ + n₂) vc, q(add_pf_add_overlap rfl $pc)⟩
    else
      if let .lt := va₁.cmp vb₁ then
        let ⟨_c, vc, (pc : Q($_a₂ + ($n₂ • $b₁ + $_b₂) = $_c))⟩ ← evalAdd sα va₂ vb
        return ⟨_, .add va₁ n₁ vc, q(add_pf_add_lt $a₁ $pc)⟩
      else
        let ⟨_c, vc, (pc : Q($n₁ • $a₁ + $_a₂ + $_b₂ = $_c))⟩ ← evalAdd sα va vb₂
        return ⟨_, .add vb₁ n₂ vc, q(add_pf_add_gt $b₁ $pc)⟩

end evalAdd

private lemma lie_aux1 {L : Type*} [LieRing L] {a b₁ b₂ c₁ c₂ c₃ c₄ : L} {n : ℤ} :
    ⁅a, b₁⁆ = c₁ → n • c₁ = c₂ → ⁅a, b₂⁆ = c₃ → c₂ + c₃ = c₄ → ⁅a, n • b₁ + b₂⁆ = c₄ :=
  fun h₁ h₂ h₃ h₄ ↦ (by subst_vars; simp)

private lemma lie_aux2 {L : Type*} [LieRing L] {a₁ a₂ b c₁ c₂ c₃ c₄ : L} {n : ℤ} :
    ⁅a₁, b⁆ = c₁ → n • c₁ = c₂ → ⁅a₂, b⁆ = c₃ → c₂ + c₃ = c₄ → ⁅n • a₁ + a₂, b⁆ = c₄ :=
  fun h₁ h₂ h₃ h₄ ↦ (by subst_vars; simp)

private lemma lie_aux3 {L : Type*} [AddCommGroup L] (a : L) : a = (1 : ℤ) • a + 0 := by simp

private lemma lie_aux4 {L : Type*} [LieRing L] (a b : L) {c₁ c₂ : L} :
    ⁅b, a⁆ = c₁ → (-1) • c₁ = c₂ → ⁅a, b⁆ = c₂ := fun h₁ h₂ ↦ (by subst_vars; simp)

private lemma lie_aux5 {L : Type*} [LieRing L] {x y b c₁ c₂ c₃ c₄ c₅ : L} :
    ⁅x, b⁆ = c₁ → ⁅c₁, y⁆ = c₂ → ⁅y, b⁆ = c₃ → ⁅x, c₃⁆ = c₄ → c₂ + c₄ = c₅ → ⁅⁅x, y⁆, b⁆ = c₅ := by
  intros; subst_vars; rw [LieRing.leibniz_lie x y b, ← lie_skew y ⁅x, b⁆, ← add_assoc,
  add_comm, ← add_assoc, neg_add_cancel, zero_add]

mutual

/-- This function evaluates an expression of the form `⁅ExLie, ExLie⁆` into its normal form,
which is also the main part of the whole reduction algorithm. Termination of the function can be
actually proved, but it is written to be mutually recursive to speed up the implementation (and save
a lot of proving work). -/
partial def evalLieLie (sα : Q(LieRing $α)) {a b : Q($α)} (va : ExLie sα a) (vb : ExLie sα b) :
    Lean.Core.CoreM <| Result (ExSum sα) q(⁅$a, $b⁆) := do
  Lean.Core.checkSystem decl_name%.toString
  if va.eq vb then
    haveI' : $a =Q $b := ⟨⟩
    return ⟨q(0), .zero, q(lie_self $a)⟩
  if (va.cmp vb).isGT then
    let ⟨_, vc₁, pc₁⟩ ← evalLieLie sα vb va
    let ⟨_, vc₂, pc₂⟩ := evalSmul sα vc₁ (-1)
    return ⟨_, vc₂, q(lie_aux4 $a $b $pc₁ $pc₂)⟩
  if (ExLie.lie va vb).isLyndon then
    return ⟨q((1 : ℤ) • ⁅$a, $b⁆ + 0), (ExLie.lie va vb).toExSum, q(lie_aux3 ⁅$a, $b⁆)⟩
  match va with
  | .atom _ => unreachable!
  | .lie (a := x) (b := y) vx vy =>
    let ⟨_, vc₁, pc₁⟩ ← evalLieLie sα vx vb
    let ⟨_, vc₂, pc₂⟩ ← evalLie₂ sα vc₁ vy
    let ⟨_, vc₃, pc₃⟩ ← evalLieLie sα vy vb
    let ⟨_, vc₄, pc₄⟩ ← evalLie₁ sα vx vc₃
    let ⟨_, vc₅, pc₅⟩ ← evalAdd sα vc₂ vc₄
    return ⟨_, vc₅, q(lie_aux5 $pc₁ $pc₂ $pc₃ $pc₄ $pc₅)⟩

/-- This function evaluates an expression of the form `⁅ExLie, ExSum⁆` into its normal form. -/
partial def evalLie₁ (sα : Q(LieRing $α)) {a b : Q($α)} (va : ExLie sα a) (vb : ExSum sα b) :
    Lean.Core.CoreM <| Result (ExSum sα) q(⁅$a, $b⁆) := do
  match vb with
  | .zero =>
    return ⟨_, .zero, q(lie_zero $a)⟩
  | .add vb₁ n vb₂ =>
    let ⟨_, vc₁, pc₁⟩ ← evalLieLie sα va vb₁
    let ⟨_, vc₂, pc₂⟩ := evalSmul sα vc₁ n
    let ⟨_, vc₃, pc₃⟩ ← evalLie₁ sα va vb₂
    let ⟨_, vc₄, pc₄⟩ ← evalAdd sα vc₂ vc₃
    return ⟨_, vc₄, q(lie_aux1 $pc₁ $pc₂ $pc₃ $pc₄)⟩

/-- This function evaluates an expression of the form `⁅ExSum, ExLie⁆` into its normal form. -/
partial def evalLie₂ (sα : Q(LieRing $α)) {a b : Q($α)} (va : ExSum sα a) (vb : ExLie sα b) :
    Lean.Core.CoreM <| Result (ExSum sα) q(⁅$a, $b⁆) := do
  let ⟨_, vc, pc⟩ ← evalLie₁ sα vb va
  let ⟨_, vd, pd⟩ := evalSmul sα vc (-1)
  return ⟨_, vd, q(lie_aux4 $a $b $pc $pd)⟩

end

/-- This function evaluates an expression of the form `⁅ExSum, ExSum⁆` into its normal form. -/
partial def evalLie (sα : Q(LieRing $α)) {a b : Q($α)} (va : ExSum sα a) (vb : ExSum sα b) :
    Lean.Core.CoreM <| Result (ExSum sα) q(⁅$a, $b⁆) := do
  match va with
  | .zero => return ⟨_, .zero, q(zero_lie $b)⟩
  | .add va₁ n va₂ =>
    let ⟨_, vc₁, pc₁⟩ ← evalLie₁ sα va₁ vb
    let ⟨_, vc₂, pc₂⟩ := evalSmul sα vc₁ n
    let ⟨_, vc₃, pc₃⟩ ← evalLie sα va₂ vb
    let ⟨_, vc₄, pc₄⟩ ← evalAdd sα vc₂ vc₃
    return ⟨_, vc₄, q(lie_aux2 $pc₁ $pc₂ $pc₃ $pc₄)⟩

end Algorithm

section execution

variable {u : Lean.Level} {α : Q(Type u)}

private theorem atom_pf {L : Type*} [AddCommGroup L] (a : L) :
    a = (1 : ℤ) • a + 0 := by simp

/-- Evaluation function of expression that has been identified as an atom. -/
def evalAtom (sα : Q(LieRing ($α))) (e : Q($α)) : AtomM (Result (ExSum sα) e) := do
  let (i, ⟨a', _⟩) ← AtomM.addAtomQ e
  let ve' := (ExLie.atom i (e := a')).toExSum
  return ⟨_, ve', q(atom_pf $e)⟩

private theorem add_congr {L : Type*} [AddCommGroup L] {a a' b b' c : L} (_ : a = a') (_ : b = b')
    (_ : a' + b' = c) : a + b = c := by
  subst_vars; rfl

private lemma smul_congr {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {a : R}
    {b b' c : M} : b = b' → a • b' = c → a • b = c := fun h₁ h₂ ↦ by subst_vars; rfl

private lemma neg_congr {M : Type*} [AddCommGroup M] {a a' b : M} :
    a = a' → (-1) • a' = b → -a = b := fun h₁ h₂ ↦ by subst_vars; simp

private lemma sub_congr {M : Type*} [AddCommGroup M] {a a' b b' c₁ c₂ : M} :
    a = a' → b = b' → (-1) • b' = c₁ → a' + c₁ = c₂ → a - b = c₂ := by
  intros; subst_vars; simp [sub_eq_add_neg]

private lemma lie_congr {L : Type*} [LieRing L] {a a' b b' c : L} :
    a = a' → b = b' → ⁅a', b'⁆ = c → ⁅a, b⁆ = c := fun h₁ h₂ h₃ ↦ h₁ ▸ (h₂ ▸ h₃)

private lemma nsmul_congr {L : Type*} [AddCommGroup L] {a a' b : L} {n : ℕ} :
    a = a' → (n : ℤ) • a' = b → n • a = b := by intros; subst_vars; simp

private lemma zsmul_congr {L : Type*} [AddCommGroup L] {a a' b : L} {n : ℤ} :
    a = a' → (-n) • a' = b → (-n) • a = b := by intros; subst_vars; rfl

/-- This function is used in the `nf` version of this tactic for identifying atoms. -/
def isAtom {u} (α : Q(Type u)) (e : Q($α)) : AtomM Bool := do
  let .const n _ := (← withReducible <| whnf e).getAppFn | return true
  match n with
  | ``HAdd.hAdd | ``Add.add | ``HSMul.hSMul | ``Neg.neg
  | ``HSub.hSub | ``Sub.sub | ``Bracket.bracket => return false
  | _ => return true

/--
This function is the evaluation process that deals with the expression. It matches the outmost
operator with certain kinds that we process, and then handle the subterms recursively.

Notice that we can not `eval` the expression like `(r : ℤ) • ⁅a, b⁆` (where `r` is a variable),
because this function is designed to only handle bracket expression like `⁅a, ⁅b, c⁆⁆` and
(literal) `ℤ`-coefficients produced in the process.
-/
partial def eval {u : Lean.Level} {α : Q(Type u)} (sα : Q(LieRing $α))
    (e : Q($α)) : AtomM (Result (ExSum sα) e) := Lean.withIncRecDepth do
  /- the function evaluates to this `els` part if no applicable operator has been identified.
  In which case, this function will check if the expression is zero, and make the expression into
  an atom if it's not zero. -/
  let els := do match e with
    | ~q(0) => return ⟨_, .zero, q(Eq.refl 0)⟩
    | _ => evalAtom sα e
  -- `n` is the outmost operator here.
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  -- the following part matches `n` with operators that we can deal with.
  match n with
  | ``HAdd.hAdd | ``Add.add  => match e with
    | ~q($a + $b) =>
      let ⟨_, va, pa⟩ ← eval sα a
      let ⟨_, vb, pb⟩ ← eval sα b
      let ⟨c, vc, p⟩ ← evalAdd sα va vb
      pure ⟨c, vc, (q(add_congr $pa $pb $p) : Expr)⟩
    | _ => els
  | ``HSMul.hSMul => match e with
    | ~q(($n : ℕ) • $a) =>
      let n' : ℕ := (← whnf n).natLit!
      if n' == 0 then
        return ⟨q(0), .zero, (q(zero_nsmul $a) : Expr)⟩
      else
        let ⟨_, va, pa⟩ ← eval sα a
        let ⟨_, vb, pb⟩ := evalSmul sα va n'
        return ⟨_, vb, (q(nsmul_congr $pa $pb) : Expr)⟩
    | ~q(-($n : ℤ) • $a) =>
      let n' : ℤ := (← whnf n).intLit!
      if n' == 0 then
        return ⟨q(0), .zero, (q(zero_nsmul $a) : Expr)⟩
      else
        let ⟨_, va, pa⟩ ← eval sα a
        let ⟨_, vb, pb⟩ := evalSmul sα va (-n' : ℤ)
        return ⟨_, vb, (q(zsmul_congr $pa $pb) : Expr)⟩
    | ~q(($n : ℤ) • $a) =>
      let n' : ℤ := (← whnf n).intLit!
      if n' == 0 then
        return ⟨q(0), .zero, (q(zero_smul ℤ $a) : Expr)⟩
      else
        let ⟨_, va, pa⟩ ← eval sα a
        let ⟨_, vb, pb⟩ := evalSmul sα va n'
        return ⟨_, vb, (q(smul_congr $pa $pb) : Expr)⟩
    | _ => els
  | ``Neg.neg => match e with
    | ~q(-$a) =>
      let ⟨_, va, pa⟩ ← eval sα a
      let ⟨_, vb, pb⟩ := evalSmul sα va (-1)
      return ⟨_, vb, q(neg_congr $pa $pb)⟩
    | _ => els
  | ``HSub.hSub | ``Sub.sub => match e with
    | ~q($a - $b) =>
      let ⟨_, va, pa⟩ ← eval sα a
      let ⟨_, vb, pb⟩ ← eval sα b
      let ⟨_, vc₁, pc₁⟩ := evalSmul sα vb (-1)
      let ⟨_, vc₂, pc₂⟩ ← evalAdd sα va vc₁
      return ⟨_, vc₂, q(sub_congr $pa $pb $pc₁ $pc₂)⟩
    | _ => els
  | ``Bracket.bracket =>
    match e with
    | ~q(LieRing.toBracket.bracket $a $b) =>
      let ⟨_, va, pa⟩ ← eval sα a
      let ⟨_, vb, pb⟩ ← eval sα b
      let ⟨_, vc, pc⟩ ← evalLie sα va vb
      return ⟨_, vc, q(lie_congr $pa $pb $pc)⟩
    | _ => els
  | _ => els

private theorem eq_aux {α} {a b c : α} (_ : (a : α) = c) (_ : b = c) : a = b := by subst_vars; rfl

/-- Prove an equality in a `LieRing` by reducing two sides of the equation to Lyndon normal form. -/
def proveEq (g : MVarId) : AtomM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
    | throwError "lie_ring failed: not an equality"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← (try u.dec catch _ => throwError "not a type{indentExpr α}")
  have α : Q(Type v) := α
  let sα ←
    try Except.ok <$> synthInstanceQ q(LieRing $α)
    catch e => pure (.error e)
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let eq ← match sα with
  | .ok sα => lieCore sα e₁ e₂
  | .error e => throw e
  g.assign eq
where
  /-- Reducing two side of equation to the normal form and determine whether they are equal. -/
  lieCore {v : Level} {α : Q(Type v)} (sα : Q(LieRing $α))
      (e₁ e₂ : Q($α)) : AtomM Q($e₁ = $e₂) := do
    profileitM Exception "lie_ring" (← getOptions) do
      let ⟨a, va, pa⟩ ← eval sα e₁
      let ⟨_b, vb, pb⟩ ← eval sα e₂
      unless va.eq vb do
        throwError "tactic lie_ring failed, expressions are not equal, the left hand side is \
        simplified to {a} but the right hand side is simplified to {_b}\n"
      let pb : Q($e₂ = $a) := pb
      return q(eq_aux $pa $pb)

/--
A tactic which evaluate an equality of two expressions in the `LieRing` to the Lyndon normal form,
and check if they are equal.
Notice that it only handle expressions consisting only of addition, subtraction, literal
`ℤ` and `ℕ`-scalar multiplication, and Lie bracket.
To prove an equality in an Lie algebra, please try `lie_algebra`.
-/
elab (name := lie_ring) "lie_ring" : tactic =>
  withMainContext do
    let s ← saveState
    try
      liftMetaMAtMain fun g ↦ do
        AtomM.run .reducible (proveEq g)
    catch e =>
      restoreState s
      throw e

end execution

section command

/-- A Command which evaluates a `LieRing` expression to its Lyndon normal form. -/
syntax (name := lie_reduce_cmd) "#LieReduce" term : command

open Command in
@[command_elab lie_reduce_cmd] private def lieReduceCmdImpl :
  Command.CommandElab :=
  fun stx => withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_lie_reduce_cmd do
    match stx with
    | `(#LieReduce $e) =>
      try
        let e ← Term.elabTerm e none
        let α ← inferType e
        Term.synthesizeSyntheticMVarsNoPostponing
        let .sort u ← whnf (← inferType α) | unreachable!
        let v ← try u.dec catch _ => throwError "not a type {indentExpr α}"
        have α : Q(Type v) := α
        let sα ← synthInstanceQ q(LieRing $α)
        let ⟨a, _, _⟩ ← Mathlib.Tactic.AtomM.run .reducible (eval sα e)
        -- TryThis.addTermSuggestion stx a
        logInfo m!"the term is reduced to {a}"
        return
      catch e => throw e
    | _ => throwUnsupportedSyntax

end command

section elaborator

/-- An elaborator which evaluates a `LieRing` expression to its Lyndon normal form. -/
syntax (name := lie_reduce_term) "lie_reduce%" term : term

@[term_elab lie_reduce_term] private def lieReduceElabImpl : Elab.Term.TermElab := fun stx _ => do
  let e ← Term.elabTerm stx[1] none
  let α ← inferType e
  Term.synthesizeSyntheticMVarsNoPostponing
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type {indentExpr α}"
  have α : Q(Type v) := α
  let sα ← synthInstanceQ q(LieRing $α)
  -- logInfo m!"the expression is {e}"
  let ⟨a, _, _⟩ ← Mathlib.Tactic.AtomM.run .reducible (eval sα e)
  -- logInfo m!"the expression is simplified into {a}, with inner expression {repr va}"
  TryThis.addTermSuggestion stx a
  return a

end elaborator

end Mathlib.Tactic.LieRing
