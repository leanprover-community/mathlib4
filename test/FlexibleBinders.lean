import Mathlib.Util.FlexibleBinders
--import Mathlib.Data.Finset.NatAntidiagonal
--import Mathlib.Algebra.BigOperators.Basic
--import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Basic

structure Finset (α : Type _) where
  s : α → Prop

class Fintype (α : Type _) where
  univ : Finset α

def Finset.univ {α : Type _} [Fintype α] : Finset α := Fintype.univ

def Set.toFinset {α : Type _} (s : Set α) [Fintype s] : Finset α := .mk s

def Finset.sum {α : Type _} (s : Finset α) (f : α → Nat) : Nat := 0

def Finset.Nat.antidiagonal (n : Nat) : Finset (Nat × Nat) := sorry

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
  | `(binder%(finset, $e ∈ $s)) => do
    let (e, ty) ← destructAscription e
    `(binderResolved%(finset% $s, $e, $ty))

/-- For the `finset` domain, `a + b = n` for sums over the antidiagonal. -/
macro_rules
  | `(binder%(finset, $a + $b = $n)) =>
    `(binder%(finset, ($a, $b) ∈ Finset.Nat.antidiagonal $n))


#test_flexible_binders type => x y z
#test_flexible_binders finset => x y z
#test_flexible_binders type => x y z : α
#test_flexible_binders finset => x y z : α
#test_flexible_binders type => x y z ∈ s
#test_flexible_binders finset => x y z ∈ s
#test_flexible_binders type => (x, y) ∈ s
#test_flexible_binders finset => (x, y) ∈ s

#test_flexible_binders type => (x : Nat) (y : Nat) ∈ s
#test_flexible_binders finset => (x : Nat) (y : Nat) ∈ s
#test_flexible_binders type => (x y : Nat) ∈ s
#test_flexible_binders finset => (x y : Nat) ∈ s

#test_flexible_binders type => (rfl)
#test_flexible_binders type => (x)

#test_flexible_binders finset => x + y = 5
#test_flexible_binders finset => (x + y = 5) (z ∈ s x y)

/-- error: Unexpected type ascription -/
#guard_msgs in #test_flexible_binders type => (x : Nat) : Nat
/-- error: Unexpected type ascription -/
#guard_msgs in #test_flexible_binders finset => (x : Nat) : Nat

#test_flexible_binders type => (p ∈ s) (x : Fin p.1)
#test_flexible_binders finset => (p ∈ s) (x : Fin p.1)

macro "∃' " bs:flexibleBinders ", " t:term : term => do
  let res ← expandFlexibleBinders `type bs
  res.foldrM (init := t) fun
    | .std dom bind _, body => `(Exists fun ($bind : $dom) => $body)
    | .prop dom, body => `($dom ∧ $body)
    | .match discr patt, body => `(match $discr:term with | $patt => $body)

macro "∑ " bs:flexibleBinders ", " t:term : term => do
  let res ← expandFlexibleBinders `finset bs
  res.foldrM (init := t) fun
  | .std dom bind none, body => `(Finset.sum (Finset.univ : Finset $dom) fun $bind => $body)
  | .std dom bind (some bindTy), body => `(Finset.sum $dom fun ($bind : $bindTy) => $body)
  | .prop dom, body => `(if $dom then $body else 0)
  | .match discr patt, body => `(match $discr:term with | $patt => $body)

section
variable (s : Set (Nat × Nat))
#check ∃' (p ∈ s) (x : Fin p.1), x = p.2
#check ∃' p q ∈ s, p.1 + q.2 = 10
#check ∃' (x, y) ∈ s, x + y = 10
#check ∃' p ∈ s, True ∧ False
end

section
instance (n : Nat) : Fintype (Fin n) := sorry
variable (s : Finset Nat) (s' : Set Nat) [Fintype s'] (f : Fin 37 → Nat)

#check ∑ x y ∈ s, x * y
#check ∑ x y ∈ s', x * y
#check ∑ x + y = 10, x * y
#check ∑ (x : Fin 37) (x x x : Fin x), x.1
#check ∑ (x y : Nat) ∈ s, x * y
#check fun t => ∑ (x y : Nat) ∈ t, x * y
#check ∑ x, f x
#check ∑ x < 10, f x

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
#guard_msgs (error) in #check fun (t : Finset (Fin 37)) => ∑ (x y : Nat) ∈ t, x * y
end
