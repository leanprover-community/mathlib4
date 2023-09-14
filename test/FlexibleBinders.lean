import Mathlib.Util.FlexibleBinders
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Basic

namespace Tests
open Lean Meta Mathlib.FlexibleBinders

/-- The default handler for the `finset` is to use `Finset.univ` and hope for the best! -/
macro_rules
  | `(binderDefault%(finset, $e)) => `(binderResolved%(Finset.univ, $e))

/-- For the `finset` domain, `(x : ty)` is a binder over `Finset.univ` for `ty`. -/
macro_rules
  | `(binder%(finset, ($e :%$c $ty))) => do
    if e matches `($_ $_*) then Macro.throwUnsupported
    if e matches `(($_ : $_)) then Macro.throwErrorAt c "Unexpected type ascription"
    `(binderResolved%((Finset.univ : Finset $ty), $e))

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
    if e matches `($_ $_*) then Macro.throwUnsupported
    `(binderResolved%((finset% $s : Finset $ty), $e))

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

#test_flexible_binders type => (x : Nat) : Nat
#test_flexible_binders finset => (x : Nat) : Nat

#test_flexible_binders type => (p ∈ s) (x : Fin p.1)


macro "∃' " bs:flexibleBinders ", " t:term : term => do
  let res ← expandFlexibleBinders `type bs
  res.foldrM (init := t) fun
    | .std dom bind, body => `(Exists fun ($bind : $dom) => $body)
    | .prop dom, body => `($dom ∧ $body)
    | .match discr patt, body => `(match $discr:term with | $patt => $body)

macro "∑ " bs:flexibleBinders ", " t:term : term => do
  let res ← expandFlexibleBinders `finset bs
  res.foldrM (init := t) fun
  | .std dom bind, body => `(Finset.sum $dom fun $bind => $body)
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
variable (s : Finset Nat) (s' : Set Nat) [Fintype s'] (f : Fin 37 → Nat)
#check ∑ x y ∈ s, x * y
#check ∑ x y ∈ s', x * y
#check ∑ x + y = 10, x * y
#check ∑ (x : Fin 37) (x x x : Fin x), x.1
#check ∑ (x y : Nat) ∈ s, x * y
#check ∑ x, f x
#check ∑ x < 10, f x
end
