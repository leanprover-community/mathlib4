import Mathlib.Tactic.DepRewrite

/-! ## Basic tests for `rewrite!`. -/

private axiom test_sorry : ∀ {α}, α

/-- Turn a term into a sort for testing. -/
private axiom P.{u} {α : Sort u} : α → Prop

/-- Non-deprecated copy of `Fin.ofNat` for testing. -/
private def finOfNat (n : Nat) (a : Nat) : Fin (n + 1) :=
  ⟨a % (n+1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩

open Lean Elab Term in
/-- Produce the annotation ``.mdata .. e`` for testing. -/
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

/-! ## Tests for proof-only mode. -/

variable {n m : Nat} (eq : n = m)

-- Rewrite a term annotated with `mdata`.
example (f : (k : Nat) → 0 < k → Type) (lt : 0 < n) : P (mdata% f n lt) := by
  rewrite! [eq]
  guard_target =ₐ P (mdata% f m (eq ▸ lt))
  exact test_sorry

-- Rewrite the function in an application into a non-function.
example (any : (α : Type) → α) (eq : (Nat → Nat) = Bool) :
    P (any (Nat → Nat) 0) := by
  rewrite! [eq]
  guard_target =ₐ P ((eq.symm ▸ any Bool) 0)
  exact test_sorry

-- Rewrite the argument in an application.
example (f : (k : Nat) → Fin k → Type) (lt : 0 < n) : P (f n ⟨0, lt⟩) := by
  rewrite! [eq]
  guard_target =ₐ P (f m ⟨0, eq ▸ lt⟩)
  exact test_sorry

-- Rewrite the structure in a projection.
example (lt : 0 < n) : P (fst% ((⟨0, lt⟩, ()) : Fin n × Unit)) := by
  rewrite! [eq]
  guard_target =ₐ P (fst% ((⟨0, eq ▸ lt⟩, ()) : Fin m × Unit))
  exact test_sorry

private def prod (α : Type) := α × Nat

-- Ensure projection structures are detected modulo reduction.
example (tup : (α : Type) → α → prod Nat) :
    P (fst% tup Nat n) := by
  rewrite! [eq]
  guard_target =ₐ P (fst% tup Nat m)
  exact test_sorry

-- Rewrite the structure in a projection into a non-projectible structure.
example (any : (α : Type) → α) (eq : (Nat × Nat) = Nat) :
    P (fst% any (Nat × Nat)) := by
  rewrite! [eq]
  guard_target =ₐ P (fst% (Eq.rec (motive := fun T _ => T) (any Nat) eq.symm))
  exact test_sorry

-- Rewrite the value of a dependent let-binding.
example (lt : 0 < n) :
    let A : Type := Fin n
    P (@id A ⟨0, lt⟩) := by
  rewrite! [eq]
  guard_target =ₐ
    let A := Fin m
    P (@id A ⟨0, eq ▸ lt⟩)
  exact test_sorry

-- Rewrite the type of a nondependent let-binding.
example (lt : 0 < n) :
    let +nondep x : Fin n := ⟨0, lt⟩
    P (@id (Fin n) x) := by
  rewrite! [eq]
  guard_target =ₐ
    let +nondep x : Fin m := ⟨0, eq ▸ lt⟩
    P (@id (Fin m) x)
  exact test_sorry

-- Rewrite the type of a let-binding whose value is a proof.
example (lt' : 0 < n) : P (have lt : 0 < n := lt'; @Fin.mk n 0 (@id (0 < n) lt)) := by
  rewrite! [eq]
  guard_target =ₐ P <|
    have lt : 0 < m := eq ▸ lt'
    @Fin.mk m 0 (@id (0 < m) lt)
  exact test_sorry

-- Rewrite in the argument type of a function.
example : P fun (y : Fin n) => y := by
  rewrite! [eq]
  guard_target =ₐ P fun (y : Fin m) => y
  exact test_sorry

-- Rewrite in a function with a proof argument.
example : P fun (lt : 0 < n) => @Fin.mk n 0 (@id (0 < n) lt) := by
  rewrite! [eq]
  guard_target =ₐ P fun (lt : 0 < m) => @Fin.mk m 0 (@id (0 < m) lt)
  exact test_sorry

-- Rewrite in a quantifier.
example : P (forall (lt : 0 < n), @Eq (Fin n) ⟨0, lt⟩ ⟨0, lt⟩) := by
  rewrite! [eq]
  guard_target =ₐ P (forall (lt : 0 < m), @Eq (Fin m) ⟨0, lt⟩ ⟨0, lt⟩)
  exact test_sorry

-- Attempt to cast a non-proof in proof-only cast mode.
/-- error: Will not cast
  y
in cast mode 'proofs'. If inserting more casts is acceptable, use `rw! (castMode := .all)`. -/
#guard_msgs in
example (Q : Fin n → Prop) (q : (x : Fin n) → Q x) :
    P fun y : Fin n => q y := by
  rewrite! [eq]
  exact test_sorry

-- Attempt to cast a non-proof in proof-only cast mode.
/-- error:
Will not cast
  ⟨0, ⋯⟩
in cast mode 'proofs'. If inserting more casts is acceptable, use `rw! (castMode := .all)`. -/
#guard_msgs in
example (f : (k : Nat) → Fin k → Type) (lt : 0 < n) : P (f n ⟨0, lt⟩) := by
  conv in Fin.mk .. => rewrite! [eq]
  exact test_sorry

-- Ensure we traverse proof terms (ordinary `rw` succeeds here).
example
    (R : (n : Nat) → Prop)
    (Q : Prop)
    (r : (n : Nat) → R n)
    (q : (n : Nat) → R n → Q)
    (t : Q → Prop) :
    t (q n (r n)) := by
  rewrite! [eq]
  guard_target =ₐ t (q m (r m))
  exact test_sorry

-- Rewrite a more complex term (not just an fvar).
variable {foo : Nat → Nat} {bar : Nat → Nat} (eq : foo n = bar m) in
example (f : (k : Nat) → Fin k → Type) (lt : 0 < foo n) : P (f (foo n) ⟨0, lt⟩) := by
  rewrite! [eq]
  guard_target =ₐ P (f (bar m) ⟨0, eq ▸ lt⟩)
  exact test_sorry

/-! ## Tests for all-casts mode. -/

variable (B : Nat → Type)

-- Rewrite the arguments to a polymorphic function.
example (f : (k : Nat) → B k → Nat) (b : B n) : P (f n b) := by
  rewrite! (castMode := .all) [eq]
  guard_target =ₐ P (f m (eq ▸ b))
  exact test_sorry

-- Rewrite the argument to a monomorphic function.
example (f : B n → Nat) (b : (k : Nat) → B k) : P (f (b n)) := by
  rewrite! (castMode := .all) [eq]
  guard_target =ₐ P (f (eq ▸ b m))
  exact test_sorry

-- Rewrite a type-valued lambda.
example (f : B n → Nat) : P fun y : B n => f y := by
  rewrite! (castMode := .all) [eq]
  guard_target =ₐ P fun y : B m => f (eq ▸ y)
  exact test_sorry

-- Rewrite in contravariant position in a higher-order application.
example (F : (f : Fin n → Nat) → Nat) :
    P (F fun y : Fin n => y.1) := by
  rewrite! (castMode := .all) [eq]
  guard_target =ₐ P (F (eq ▸ fun y : Fin m => y.1))
  exact test_sorry

-- Rewrite in covariant position in a higher-order application.
example (F : (f : Nat → Fin (n+1)) → Nat) :
    P (F fun k : Nat => finOfNat n k) := by
  rewrite! (castMode := .all) [eq]
  guard_target =ₐ P (F (eq ▸ fun k : Nat => finOfNat m k))
  exact test_sorry

-- Rewrite in invariant position in a higher-order application.
example (b : (k : Nat) → B k) (F : (f : (k : Fin n) → B k.1) → Nat) :
    P (F fun k : Fin n => b k.1) := by
  rewrite! (castMode := .all) [eq]
  guard_target =ₐ P (F (eq ▸ fun k : Fin m => b k.1))
  exact test_sorry

-- Attempt to rewrite with an LHS that does not appear in the target,
-- but does appear in types of the target's subterms.
/--
error: Tactic `depRewrite` failed: did not find instance of the pattern in the target expression
  n

n m : Nat
eq : n = m
B : Nat → Type
f : B n → Nat
b : B n
⊢ f b = f b
-/
#guard_msgs in
example (f : B n → Nat) (b : B n) :
    f b = f b := by
  rewrite! [eq]
  exact test_sorry

-- Test casting twice (from the LHS to `x` and back).
theorem bool_dep_test
    (b : Bool)
    (β : Bool → Sort u)
    (f : ∀ b, β (b && false))
    (h : false = b) :
    @P (β false) (f false) := by
  rewrite! (castMode := .all) [h]
  guard_target =
    @P (β b) (h.rec (motive := fun x _ => β x) <|
      h.symm.rec (motive := fun x _ => β (x && false)) <|
        f b)
  exact test_sorry

-- Rewrite a `let` binding that requires generalization.
theorem let_defeq_test (b : Nat) (eq : 1 = b) (f : (n : Nat) → n = 1 → Nat) :
    let n := 1; P (f n rfl) := by
  rewrite! [eq]
  guard_target = let n := b; P (f n _)
  exact test_sorry

-- Test definitional equalities that get broken by rewriting.
example (b : Bool) (h : true = b)
    (s : Bool → Prop)
    (q : (c : Bool) → s c → Prop)
    (f : (h : s (true || !false)) → q true h → Bool) :
    ∀ (i : s (true || true)) (u : q (true || !true) i), s (f i u) := by
  rewrite! [h]
  guard_target = ∀ (i : s (b || b)) (u : q (b || !b) _), s (f _ _)
  exact test_sorry

-- As above.
example (b : Bool) (h : true = b)
    (s : Bool → Prop)
    (q : (c : Bool) → s c → Prop)
    (f : (h : s (true || !false)) → q true h → Bool)
    (j : (h : s (true || false)) → (i : q (!false) h) → (k : f h i = true) → False) :
    ∀ (i : s (true || true)) (u : q (true || !true) i)
      (k : f i u = true), False.elim.{1} (j i u k) := by
  rewrite! [h]
  guard_target = ∀ (i : s (b || b)) (u : q (b || !b) _) (k : f _ _ = b), False.elim.{1} _
  exact test_sorry

-- As above.
example (b : Bool) (h : true = b)
    (s : Bool → Prop)
    (q : (c : Bool) → s c → Prop)
    (f : (h : s (true || !false)) → q true h → Bool)
    (j : (c : Bool) → (h : s (true || c)) → (i : q (!false) h) → (k : f h i = !c) → False) :
    ∀ (i : s (true || true)) (u : q (true || !true) i)
      (k : f i u = true), False.elim.{1} (j (!true) i u k) := by
  rewrite! [h]
  guard_target = ∀ (i : s (b || b)) (u : q (b || !b) _) (k : f _ _ = b), False.elim.{1} _
  exact test_sorry

-- Rewrite in nested lets whose values and types depend on prior lets.
#guard_msgs in
example
    (F : Nat → Type)
    (G : (n : Nat) → F n → Type)
    (r : (n : Nat) → (f : F n) → G n f → Nat)
    (f : F n) (g : G n f) :
    P <|
      let a : Nat := n
      let B : Type := G a f
      let c : B := g
      let c' : G n f := g
      r n f c = r n f c' := by
  rewrite! (castMode := .all) [eq]
  exact test_sorry

/-! ## Tests for `occs` -/

-- Test `.pos`.
example (f : Nat → Nat → Nat) : P (f (id n) (id n)) := by
  rewrite! (occs := .pos [1]) [eq]
  guard_target =ₐ P (f (id m) (id n))
  exact test_sorry

-- Test `.neg`.
example (f : Nat → Nat → Nat) : P (f (id n) (id n)) := by
  rewrite! (occs := .neg [1]) [eq]
  guard_target =ₐ P (f (id n) (id m))
  exact test_sorry
