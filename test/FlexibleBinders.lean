import Mathlib.Util.FlexibleBinders
import Mathlib.Data.Set.Basic

-- On command line, tests format functions with => rather than ↦ without this.
set_option pp.unicode.fun true

structure Finset (α : Type _) where
  s : α → Prop

class Fintype (α : Type _) where
  univ : Finset α

def Finset.univ {α : Type _} [Fintype α] : Finset α := Fintype.univ

def Set.toFinset {α : Type _} (s : Set α) [Fintype s] : Finset α := .mk s

def Finset.sum {α : Type _} (_s : Finset α) (_f : α → Nat) : Nat := 0

def Finset.Nat.antidiagonal (_n : Nat) : Finset (Nat × Nat) := .mk fun _ => False

namespace Tests
open Lean Meta Mathlib.FlexibleBinders

/-- `finset% t` elaborates `t` as a `Finset`.
If `t` is a `Set`, then inserts `Set.toFinset`.
Does not make use of the expected type; useful for big operators over finsets.
```
#check finset% Finset.range 2 -- Finset Nat
#check finset% (Set.univ : Set Bool) -- Finset Bool
```
-/
elab (name := finsetStx) "finset% " t:term : term => do
  let u ← mkFreshLevelMVar
  let ty ← mkFreshExprMVar (mkSort (.succ u))
  let x ← Elab.Term.elabTerm t (mkApp (.const ``Finset [u]) ty)
  let xty ← whnfR (← inferType x)
  if xty.isAppOfArity ``Set 1 then
    Elab.Term.elabAppArgs (.const ``Set.toFinset [u]) #[] #[.expr x] none false false
  else
    return x

open Lean.Elab.Term.Quotation in
/-- `quot_precheck` for the `finset%` syntax. -/
@[quot_precheck ExtendedBinder2.finsetStx] def precheckFinsetStx : Precheck
  | `(finset% $t) => precheck t
  | _ => Elab.throwUnsupportedSyntax

/-- For the `finset` domain, `(x ∈ s)` is a binder over `s` as a `Finset`. -/
macro_rules
  | `(binder%(finset%, $e ∈ $s)) => do
    let (e, ty) ← destructAscription e
    `(binderResolved%($ty, $e, finset% $s))

/-- For the `finset` domain, `a + b = n` for sums over the antidiagonal. -/
macro_rules
  | `(binder%(finset%, $a + $b = $n)) =>
    `(binder%(finset%, ($a, $b) ∈ Finset.Nat.antidiagonal $n))


/--
info: binder (x : _)
---
info: binder (y : _)
---
info: binder (z : _)
-/
#guard_msgs in #test_flexible_binders type% => x y z
/--
info: binder (x : _)
---
info: binder (y : _)
---
info: binder (z : _)
-/
#guard_msgs in #test_flexible_binders finset% => x y z

/--
info: binder (x : α)
---
info: binder (y : α)
---
info: binder (z : α)
-/
#guard_msgs in #test_flexible_binders type% => x y z : α
/--
info: binder (x : α)
---
info: binder (y : α)
---
info: binder (z : α)
-/
#guard_msgs in #test_flexible_binders finset% => x y z : α

/--
info: binder (x : _)
---
info: prop binder (_ : x ∈ s)
---
info: binder (y : _)
---
info: prop binder (_ : y ∈ s)
---
info: binder (z : _)
---
info: prop binder (_ : z ∈ s)
-/
#guard_msgs in #test_flexible_binders type% => x y z ∈ s
/--
info: binder (x : _) ∈ finset% s
---
info: binder (y : _) ∈ finset% s
---
info: binder (z : _) ∈ finset% s
-/
#guard_msgs in #test_flexible_binders finset% => x y z ∈ s

/--
info: binder (x✝ : _)
---
info: prop binder (_ : x✝ ∈ s)
---
info: match x✝ with | (x, y) => ...
-/
#guard_msgs in #test_flexible_binders type% => (x, y) ∈ s
/--
info: binder (x✝ : _) ∈ finset% s
---
info: match x✝ with | (x, y) => ...
-/
#guard_msgs in #test_flexible_binders finset% => (x, y) ∈ s

/--
info: binder (x : Nat)
---
info: prop binder (_ : x ∈ s)
---
info: binder (y : Nat)
---
info: prop binder (_ : y ∈ s)
-/
#guard_msgs in #test_flexible_binders type% => (x : Nat) (y : Nat) ∈ s
/--
info: binder (x : Nat) ∈ finset% s
---
info: binder (y : Nat) ∈ finset% s
-/
#guard_msgs in #test_flexible_binders finset% => (x : Nat) (y : Nat) ∈ s
/--
info: binder (x : Nat)
---
info: prop binder (_ : x ∈ s)
---
info: binder (y : Nat)
---
info: prop binder (_ : y ∈ s)
-/
#guard_msgs in #test_flexible_binders type% => (x y : Nat) ∈ s
/--
info: binder (x : Nat) ∈ finset% s
---
info: binder (y : Nat) ∈ finset% s
-/
#guard_msgs in #test_flexible_binders finset% => (x y : Nat) ∈ s

/--
info: binder (x✝ : _)
---
info: match x✝ with | (rfl) => ...
-/
#guard_msgs in #test_flexible_binders type% => (rfl)
/-- info: binder (x : _) -/
#guard_msgs in #test_flexible_binders type% => (x)

/--
info: binder (x✝ : _) ∈ finset% Finset.Nat.antidiagonal✝ 5
---
info: match x✝ with | (x, y) => ...
-/
#guard_msgs in #test_flexible_binders finset% => x + y = 5
/--
info: binder (x✝ : _) ∈ finset% Finset.Nat.antidiagonal✝ 5
---
info: match x✝ with | (x, y) => ...
---
info: binder (z : _) ∈ finset% s x y
-/
#guard_msgs in #test_flexible_binders finset% => (x + y = 5) (z ∈ s x y)

/-- error: Unexpected type ascription -/
#guard_msgs in #test_flexible_binders type% => (x : Nat) : Nat
/-- error: Unexpected type ascription -/
#guard_msgs in #test_flexible_binders finset% => (x : Nat) : Nat
/-- error: Unexpected type ascription -/
#guard_msgs in #test_flexible_binders finset% => x ∈ s : Nat
/-- error: Unexpected type ascription -/
#guard_msgs in #test_flexible_binders finset% => (x ∈ s) : Nat

/--
info: binder (p : _)
---
info: prop binder (_ : p ∈ s)
---
info: binder (x : Fin p.1)
-/
#guard_msgs in #test_flexible_binders type% => (p ∈ s) (x : Fin p.1)
/--
info: binder (p : _) ∈ finset% s
---
info: binder (x : Fin p.1)
-/
#guard_msgs in #test_flexible_binders finset% => (p ∈ s) (x : Fin p.1)

macro "∃' " bs:flexibleBinders ", " t:term : term => do
  let res ← expandFlexibleBinders (← `(flexibleBindersDom| type%)) bs
  res.foldrM (init := t) fun
    | .std ty bind _, body => `(Exists fun ($bind : $ty) => $body)
    | .prop p, body => `($p ∧ $body)
    | .match discr patt, body => `(match $discr:term with | $patt => $body)
    | .letI x val, body => `(letI $x := $val; $body)

macro "∑ " bs:flexibleBinders ", " t:term : term => do
  let res ← expandFlexibleBinders (← `(flexibleBindersDom| finset%)) bs
  res.foldrM (init := t) fun
  | .std ty bind none, body => `(Finset.sum Finset.univ fun ($bind : $ty) => $body)
  | .std ty bind (some dom), body => `(Finset.sum $dom fun ($bind : $ty) => $body)
  | .prop p, body => `(if $p then $body else 0)
  | .match discr patt, body => `(match $discr:term with | $patt => $body)
  | .letI x val, body => `(letI $x := $val; $body)

section
variable (s : Set (Nat × Nat))
/-- info: ∃ p, p ∈ s ∧ ∃ x, ↑x = p.snd : Prop -/
#guard_msgs in #check ∃' (p ∈ s) (x : Fin p.1), x = p.2
/-- info: ∃ p, p ∈ s ∧ ∃ q, q ∈ s ∧ p.fst + q.snd = 10 : Prop -/
#guard_msgs in #check ∃' p q ∈ s, p.1 + q.2 = 10
/--
info: ∃ x,
  x ∈ s ∧
    match x with
    | (x, y) => x + y = 10 : Prop
-/
#guard_msgs in #check ∃' (x, y) ∈ s, x + y = 10
/-- info: ∃ p, p ∈ s ∧ True ∧ False : Prop -/
#guard_msgs in #check ∃' p ∈ s, True ∧ False
/-- info: ∃ x, x < 10 ∧ ∃ y, y < 10 ∧ ∃ z, z ≤ 5 ∧ x + y = z : Prop -/
#guard_msgs in #check ∃' ((x y : Nat) < 10) (z ≤ 5), x + y = z
end

section
instance (n : Nat) : Fintype (Fin n) := .mk (.mk fun _ => False)
variable (s : Finset Nat) (s' : Set Nat) [Fintype s'] (f : Fin 37 → Nat)

/-- info: Finset.sum s fun x ↦ Finset.sum s fun y ↦ x * y : ℕ -/
#guard_msgs in #check ∑ x y ∈ s, x * y
/-- info: Finset.sum (Set.toFinset s') fun x ↦ Finset.sum (Set.toFinset s') fun y ↦ x * y : ℕ -/
#guard_msgs in #check ∑ x y ∈ s', x * y
/--
info: Finset.sum (Finset.Nat.antidiagonal 10) fun x ↦
  match x with
  | (x, y) => x * y : ℕ
-/
#guard_msgs in #check ∑ x + y = 10, x * y
/--
info: Finset.sum Finset.univ fun x ↦
  Finset.sum Finset.univ fun x_1 ↦ Finset.sum Finset.univ fun x_2 ↦ Finset.sum Finset.univ fun x_3 ↦ ↑x_3 : ℕ
-/
#guard_msgs in #check ∑ (x : Fin 37) (x x x : Fin x), x.1
/-- info: Finset.sum s fun x ↦ Finset.sum s fun y ↦ x * y : ℕ -/
#guard_msgs in #check ∑ (x y : Nat) ∈ s, x * y
/-- info: fun t ↦ Finset.sum t fun x ↦ Finset.sum t fun y ↦ x * y : Finset ℕ → ℕ -/
#guard_msgs in #check fun t => ∑ (x y : Nat) ∈ t, x * y
/-- info: Finset.sum Finset.univ fun x ↦ f x : ℕ -/
#guard_msgs in #check ∑ x, f x
/-- info: Finset.sum Finset.univ fun x ↦ if x < 10 then f x else 0 : ℕ -/
#guard_msgs in #check ∑ x < 10, f x

/--
error: application type mismatch
  Finset.sum t fun y ↦ x * y
argument
  fun y ↦ x * y
has type
  ℕ → ℕ : Type
but is expected to have type
  Fin 37 → ℕ : Type
-/
#guard_msgs(error, drop all) in #check fun (t : Finset (Fin 37)) => ∑ (x y : Nat) ∈ t, x * y
end
