import Lean.Meta.Tactic.Simp.Types
import Qq

open Lean Meta Qq

namespace Simp

open Simp

/-- `Qq` version of `Simp.Methods.discharge?`, which avoids having to use `~q` matching
on the proof expression returned by `Methods.discharge?`

`Methods.dischargeQ? (a : Q(Prop))` attempts to prove `a` using the discharger, returning
`some (pf : Q(a))` if a proof is found and `none` otherwise.
-/
def Methods.dischargeQ? (M : Methods) (a : Q(Prop)) : SimpM <| Option Q($a) := do
  match ← M.discharge? a with
  | some pf =>
    let ⟨0, ~q($a), pf⟩ ← inferTypeQ pf | return none
    return some pf
  | none => return none

--TODO(Paul-Lez): add tests
