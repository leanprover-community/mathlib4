import Mathlib.Tactic.DepRewrite

/-! Basic tests for `rewrite!`. -/

private axiom test_sorry : ∀ {α}, α

/-- Turn a term into a sort for testing. -/
private axiom P.{u} {α : Sort u} : α → Prop

/-- Non-deprecated copy of `Fin.ofNat` for testing. -/
private def finOfNat (n : Nat) (a : Nat) : Fin (n + 1) :=
  ⟨a % (n+1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩

open Lean Elab Term in
/-- Produce the annotation ``.mdata .. e`` for testing.
Standard elaborators may represent projections as ordinary functions instead. -/
elab "mdata% " e:term : term => do
  let e ← elabTerm e none
  return .mdata ({ : MData}.insert `abc "def") e

open Lean Elab Meta Term in
/-- Produce the projection ``.proj `Prod 0 e`` for testing.
Standard elaborators may represent projections as ordinary functions instead. -/
elab "fst% " e:term : term => do
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let α ← mkFreshExprMVar (some <| .sort u)
  let β ← mkFreshExprMVar (some <| .sort v)
  let tp := mkApp2 (.const ``Prod [u, v]) α β
  let e ← elabTerm e tp
  return .proj ``Prod 0 e

/-! Tests for proof-only mode. -/

variable {n m : Nat} (eq : n = m)

-- mdata
example (f : (k : Nat) → 0 < k → Type) (lt : 0 < n) : P (mdata% f n lt) := by
  rewrite! [eq]
  guard_target =ₐ P (mdata% f m (eq ▸ lt))
  exact test_sorry

-- app (fn)
/-- error: function expected
  any x -/
#guard_msgs in
example (any : (α : Type) → α) (eq : (Nat → Nat) = Bool) :
    P (any (Nat → Nat) 0) := by
  rewrite! [eq]
  exact test_sorry

-- app (arg)
example (f : (k : Nat) → Fin k → Type) (lt : 0 < n) : P (f n ⟨0, lt⟩) := by
  rewrite! [eq]
  guard_target =ₐ P (f m ⟨0, eq ▸ lt⟩)
  exact test_sorry

-- proj
example (lt : 0 < n) : P (fst% ((⟨0, lt⟩, ()) : Fin n × Unit)) := by
  rewrite! [eq]
  guard_target =ₐ P (fst% ((⟨0, eq ▸ lt⟩, ()) : Fin m × Unit))
  exact test_sorry

/-- error: projection type mismatch
  (any x).1 -/
#guard_msgs in
example (any : (α : Type) → α) (eq : (Nat × Nat) = Nat) :
    P (fst% any (Nat × Nat)) := by
  rw! [eq]
  exact test_sorry

-- let (value)
example (lt : 0 < n) :
    let A : Type := Fin n
    P (@id A ⟨0, lt⟩) := by
  rewrite! [eq]
  guard_target =ₐ
    let A : Type := Fin m
    P (@id A ⟨0, eq ▸ lt⟩)
  exact test_sorry

-- let (type)
example (lt : 0 < n) :
    let x : Fin n := ⟨0, lt⟩
    P (@id (Fin n) x) := by
  rewrite! [eq]
  guard_target =ₐ
    let x : Fin m := ⟨0, eq ▸ lt⟩
    P (@id (Fin m) x)
  exact test_sorry

-- let (proof)
example (lt' : 0 < n) : P (let lt : 0 < n := lt'; @Fin.mk n 0 (@id (0 < n) lt)) := by
  rewrite! [eq]
  guard_target = P (let lt : 0 < m := eq ▸ lt'; @Fin.mk m 0 (@id (0 < m) _))
  exact test_sorry

-- lam
example : P fun (y : Fin n) => y := by
  rewrite! [eq]
  guard_target =ₐ P fun (y : Fin m) => y
  exact test_sorry

-- lam (proof)
example : P fun (lt : 0 < n) => @Fin.mk n 0 (@id (0 < n) lt) := by
  rewrite! [eq]
  guard_target = P fun (lt : 0 < m) => @Fin.mk m 0 (@id (0 < m) _)
  exact test_sorry

-- forall
example : P (forall (lt : 0 < n), @Eq (Fin n) ⟨0, lt⟩ ⟨0, lt⟩) := by
  rewrite! [eq]
  guard_target =ₐ P (forall (lt : 0 < m), @Eq (Fin m) ⟨0, eq ▸ lt⟩ ⟨0, eq ▸ lt⟩)
  exact test_sorry

/-- error: Will not cast
  y
in cast mode 'proofs'. If inserting more casts is acceptable, use `(castMode := .all)`. -/
#guard_msgs in
example (Q : Fin n → Prop) (q : (x : Fin n) → Q x) :
    P fun y : Fin n => q y := by
  rewrite! [eq]
  exact test_sorry

/-- error:
Will not cast
  ⟨0, ⋯⟩
in cast mode 'proofs'. If inserting more casts is acceptable, use `(castMode := .all)`. -/
#guard_msgs in
example (f : (k : Nat) → Fin k → Type) (lt : 0 < n) : P (f n ⟨0, lt⟩) := by
  conv in Fin.mk .. => rewrite! [eq]
  exact test_sorry

/-! Tests for all-casts mode. -/

variable (B : Nat → Type)

-- app (polymorphic fn)
example (f : (k : Nat) → B k → Nat) (b : B n) : P (f n b) := by
  rewrite! (castMode := .all) [eq]
  guard_target = P (f m (eq ▸ b))
  exact test_sorry

-- app (monomorphic fn)
example (f : B n → Nat) (b : (k : Nat) → B k) : P (f (b n)) := by
  rewrite! (castMode := .all) [eq]
  guard_target = P (f (eq ▸ b m))
  exact test_sorry

-- lam
example (f : B n → Nat) : P fun y : B n => f y := by
  rewrite! (castMode := .all) [eq]
  guard_target = P fun y : B m => f (eq ▸ y)
  exact test_sorry

-- lam (as argument, contravariant)
example (F : (f : Fin n → Nat) → Nat) :
    P (F fun y : Fin n => y.1) := by
  rewrite! (castMode := .all) [eq]
  guard_target =ₐ P (F (eq ▸ fun y : Fin m => y.1))
  exact test_sorry

-- lam (as argument, covariant)
example (F : (f : Nat → Fin (n+1)) → Nat) :
    P (F fun k : Nat => finOfNat n k) := by
  rewrite! (castMode := .all) [eq]
  guard_target =ₐ P (F (eq ▸ fun k : Nat => finOfNat m k))
  exact test_sorry

-- lam (as argument, invariant)
example (b : (k : Nat) → B k) (F : (f : (k : Fin n) → B k.1) → Nat) :
    P (F fun k : Fin n => b k.1) := by
  rewrite! (castMode := .all) [eq]
  guard_target =ₐ P (F (eq ▸ fun k : Fin m => b k.1))
  exact test_sorry

/-- error: tactic 'depRewrite' failed, did not find instance of the pattern in the target expression
  n
n m : Nat
eq : n = m
B : Nat → Type
f : B n → Nat
b : B n
⊢ f b = f b -/
#guard_msgs in
example (f : B n → Nat) (b : B n) :
    f b = f b := by
  rewrite! [eq]
  exact test_sorry

/-! Tests for proof-only mode, rewriting compound terms (non-fvars). -/

variable {foo : Nat → Nat} {bar : Nat → Nat} (eq : foo n = bar m)

-- app (arg)
example (f : (k : Nat) → Fin k → Type) (lt : 0 < foo n) : P (f (foo n) ⟨0, lt⟩) := by
  rewrite! [eq]
  guard_target =ₐ P (f (bar m) ⟨0, eq ▸ lt⟩)
  exact test_sorry
