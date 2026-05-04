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

/- Note: depending on your font, the `#guard_msgs` rendering may actually look slightly wrong here,
with underlines extending past the end of what is visible as colored according to the "added" part
of the diff in the infoview. This is due to issues with using combining marks on spaces. -/
/--
info: Try this:
  #scope
    @̲[̲e̲x̲p̲o̲s̲e̲]̲ ̲public noncomputable m̲e̲t̲a̲ ̲scope
    universe u v̲ ̲w
    namespace B̵a̵z̵F̲o̲o̲.̲B̲a̲r̲
    open @Bool @Lean @̲L̲e̲a̲n̲.̲E̲l̲a̲b̲ ̲@Lean.Parser @Lean.Parser.Command @Lean.Elab.Command
    open scoped @Nat
    set_options pp.mvars.anonymous f̲a̲l̲s̲e̲,̲ ̲p̲p̲.̲m̲v̲a̲r̲s̲.̲d̲e̲l̲a̲y̲e̲d̲ ̲false
    variable (x : Nat := by exact (Nat.add 0 0)) (̲y̲ ̲:̲ ̲N̲a̲t̲)̲ ̲[Nonempty False]
    o̵m̵i̵t̵ ̵y̵i̲n̲c̲l̲u̲d̲e̲ ̲x̲
  ̲ ̲ ̲o̲m̲i̲t̲ ̲y̲ ̲[̲N̲o̲n̲e̲m̲p̲t̲y̲ ̲F̲a̲l̲s̲e̲]̲
-/
#guard_msgs in
#scope
  public noncomputable scope
  universe u w
  namespace Baz
  open @Bool @Lean @Lean.Parser @Lean.Parser.Command @Lean.Elab.Command
  open scoped @Nat
  set_options pp.mvars.anonymous false
  variable (x : Nat := by exact (Nat.add 0 0)) [Nonempty False]
  omit y
