/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Init
public import Lean.Meta.Tactic.Simp
public import Batteries.Logic

/-!
# `@[cast_data]` attribute and simproc for data projections through `Eq.rec`

This module defines the `@[cast_data]` attribute and a registered simproc that simplifies
expressions of the form `f ... (h ▸ x)` to `f ... x` for any constant `f` whose value is
independent of indices that may change under `Eq.rec`. Common examples include `Subtype.val`
and projection-style functions on indexed inductive types such as `GraphLike.Walk.edges`.

## Usage

```
attribute [cast_data] Subtype.val Walk.edges Walk.darts
```

After registration, ordinary `simp` will rewrite `(h ▸ x).val ↦ x.val` and similar through any
number of nested `Eq.rec` transports.

## Implementation

The rewrite is justified by the universal lemma `congr_eqRec` from Batteries, which has the
shape `f x' (Eq.rec y h) = f x y`. The simproc reconstructs the per-index family `f` from the
original expression by `kabstract`ing the changed index in the earlier arguments of the
projection. Soundness is enforced by the kernel: if a tagged constant is not actually invariant
under transport, the generated proof fails to typecheck and the simproc silently aborts.

The simproc only inspects the final argument of the projection, peeling one `Eq.rec` per
invocation. Nested transports (such as `hv ▸ hu ▸ p`) are handled by repeated `simp` passes.
-/

public meta section

open Lean Meta Simp

namespace Mathlib.Tactic.CastData

/-- Environment extension storing names of constants registered as `cast_data` projections. -/
initialize castDataExt : SimpleScopedEnvExtension Name NameSet ←
  registerSimpleScopedEnvExtension {
    initial := NameSet.insert {`Subtype.val} `Fin.val
    addEntry := fun s n => s.insert n
  }

/-- Returns `true` iff `n` is registered as a `cast_data` projection. -/
def isCastData (n : Name) : CoreM Bool :=
  return (castDataExt.getState (← getEnv)).contains n

/-- The `@[cast_data]` attribute marks a constant `f` as a "data projection" that is invariant
under `Eq.rec` transport of its final argument. The associated simproc then rewrites
`f ... (h ▸ x)` to `f ... x` whenever `f` is registered.

Soundness is enforced by the kernel via `congr_eqRec`: if `f`'s output actually depends on the
casted index, the generated proof will fail to typecheck and the simproc aborts. -/
syntax (name := castDataAttr) "cast_data" : attr

initialize registerBuiltinAttribute {
  name := `castDataAttr
  descr := "register a constant as a data projection invariant under Eq.rec"
  add := fun declName _ kind => MetaM.run' do
    castDataExt.add declName kind
}

end Mathlib.Tactic.CastData

open Mathlib.Tactic.CastData

/-- Simproc that rewrites `f ... (h ▸ x) ↦ f ... x` for any constant `f` registered via
`@[cast_data]`. Uses the universal `congr_eqRec` as the underlying lemma. -/
simproc castData (_) := fun e => do
  let head := e.getAppFn
  let .const dataName _ := head | return .continue
  unless ← isCastData dataName do return .continue
  let args := e.getAppArgs
  if args.isEmpty then return .continue
  let castArg ← withTransparency .all <| whnf args[args.size - 1]!
  unless castArg.isAppOfArity ``Eq.rec 6 do return .continue
  let #[ι, a, motive, x, b, h] := castArg.getAppArgs | return .continue
  -- Recover `β : ι → Sort _` from `motive : (i : ι) → a = i → Sort _`,
  -- assuming `motive`'s body does not depend on the equality binder. This is the standard form
  -- elaborated by `▸` for index transport.
  let .lam _ _ (.lam _ _ body _) _ := motive | return .continue
  if body.hasLooseBVar 0 then return .continue
  let β := Expr.lam `i ι (body.lowerLooseBVars 1 1) .default
  -- Build the proof speculatively: if the tagged constant is not actually invariant under
  -- `Eq.rec`, the kernel will reject `congr_eqRec` and `mkAppM` throws. We catch the failure
  -- so the simproc degrades to `.continue` instead of erroring out of `simp`.
  let earlyArgs := args.pop
  try
    let earlyArgsKab ← earlyArgs.mapM (kabstract · b)
    let f ← withTransparency .all <| withLocalDeclD `i ι fun iVar => do
      let earlyArgsAtI := earlyArgsKab.map (·.instantiate1 iVar)
      withLocalDeclD `z (β.beta #[iVar]) fun zVar => do
        mkLambdaFVars #[iVar, zVar] <| mkAppN head (earlyArgsAtI.push zVar)
    let proof ← withTransparency .all <| mkAppM ``congr_eqRec #[f, h, x]
    let earlyArgsAtA := earlyArgsKab.map (·.instantiate1 a)
    return .visit { expr := mkAppN head (earlyArgsAtA.push x), proof? := some proof }
  catch _ =>
    return .continue

end
