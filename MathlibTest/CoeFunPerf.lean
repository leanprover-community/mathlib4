module

import Mathlib

/-
Test that synthesis of `CoeFun` fails quickly.
Currently, it only tries the following instances:
- `DFunLike.toCoeFun`
- `RKHS.instFunLike`
- `EquivLike.toFunLike`

Hint: if this test fails, consider:
* using unbundled inheritance from `FunLike`: turn
   `class MyClass extends FunLike F A B where ...` into `class MyClass [FunLike F A B] where ...` or,
* reordering arguments so classes with fewer instances come first.
-/

set_option trace.Meta.synthInstance true

variable {F A B : Type _}

/--
error: failed to synthesize
  CoeFun F fun x => A → B

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
trace: [Meta.synthInstance] ❌️ CoeFun F fun x => A → B
  [Meta.synthInstance] ✅️ new goal CoeFun F _tc.1
    [Meta.synthInstance.instances] #[@DFunLike.toCoeFun]
  [Meta.synthInstance.apply] ✅️ apply @DFunLike.toCoeFun to CoeFun F fun x => (a : ?_) → ?_ a
    [Meta.synthInstance.tryResolve] ✅️ CoeFun F fun x => (a : ?_) → ?_ a ≟ CoeFun F fun x => (a : ?_) → ?_ a
    [Meta.synthInstance] ✅️ new goal DFunLike F _tc.2 _tc.3
      [Meta.synthInstance.instances] #[@EquivLike.toFunLike, @RKHS.instFunLike]
  [Meta.synthInstance.apply] ✅️ apply @RKHS.instFunLike to DFunLike F ?_ fun x => ?_
    [Meta.synthInstance.tryResolve] ✅️ DFunLike F ?_ fun x => ?_ ≟ DFunLike F ?_ fun x => ?_
    [Meta.synthInstance] ✅️ no instances for RKHS _tc.3 F _tc.4 _tc.5
      [Meta.synthInstance.instances] #[]
  [Meta.synthInstance.apply] ✅️ apply @EquivLike.toFunLike to DFunLike F ?_ fun x => ?_
    [Meta.synthInstance.tryResolve] ✅️ DFunLike F ?_ fun x => ?_ ≟ DFunLike F ?_ fun x => ?_
    [Meta.synthInstance] ✅️ no instances for EquivLike F _tc.2 _tc.3
      [Meta.synthInstance.instances] #[]
  [Meta.synthInstance] result <not-available>
-/
#guard_msgs in
#synth CoeFun F (fun _ ↦ A → B)
