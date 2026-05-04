module

import Mathlib.Util.Scope

#scope
  scope

set_option pp.mvars.anonymous false

set_option pp.mvars.delayed false

public meta section

#scope
  public meta scope
  set_options pp.mvars.anonymous false, pp.mvars.delayed false

/--
info: Try this:
  #scope
    @̵[̵e̵x̵p̵o̵s̵e̵]̵ ̵public m̲e̲t̲a̲ ̲scope
    set_options p̵p̵.̵u̵n̵i̵c̵o̵d̵e̵p̲p̲.̲m̲v̲a̲r̲s̲.̲a̲n̲o̲n̲y̲m̲o̲u̲s̲ ̲f̲a̲l̲s̲e̲,̲ ̲p̲p̲.̲m̲v̲a̲r̲s̲.̲d̲e̲l̲a̲y̲e̲d̲ false
-/
#guard_msgs in
#scope
  @[expose] public scope
  set_options pp.unicode false

universe u v w

namespace Foo
namespace Bar

@[expose] noncomputable section

section

open Bool

open scoped Nat

open Lean Elab Parser Command

/- Ignores whitespace: -/
variable (x : Nat := by exact (Nat.add /- hmm -/ 0 0)) (y : Nat) [Nonempty False] -- some comment

include x

omit y [Nonempty False] -- other comment

#scope
  @[expose] public noncomputable meta scope
  universe u v w
  namespace Foo.Bar
  open @Bool @Lean @Lean.Elab @Lean.Parser @Lean.Parser.Command @Lean.Elab.Command
  open scoped @Nat
  set_options pp.mvars.anonymous false, pp.mvars.delayed false
  variable (x : Nat := by exact (Nat.add 0 0)) (y : Nat) [Nonempty False]
  include x
  omit y [Nonempty False]
