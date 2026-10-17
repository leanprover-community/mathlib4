/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.Tactic.NonemptyAttr
public import Mathlib.Logic.Nonempty

/-! Tests for the behavior of the `nonempty` attribute. -/

@[expose] public section

def Foo := Unit

@[nonempty] def F : Foo := .unit

/-- info: instNonemptyFoo : Nonempty Foo -/
#guard_msgs in #check instNonemptyFoo

/-- info: instNonemptyFoo -/
#guard_msgs in #synth Nonempty Foo

#guard_msgs in @[nonempty] def G : Foo := .unit

/-! testing if repeated application add suffixes -/

/-- info: instNonemptyFoo_1 : Nonempty Foo -/
#guard_msgs in #check instNonemptyFoo_1

def Bar := Unit

#guard_msgs in @[nonempty -inst] def H : Bar := .unit

/--
error: failed to synthesize
  Nonempty Bar

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in #synth Nonempty Bar

#guard_msgs in @[nonempty (priority := 100) -inst] def K : Bar := .unit

/-! Testing if named priority work -/

#guard_msgs in @[nonempty (priority := mid) -inst] def U : Bar := .unit

/-! Testing if manual name works -/

#guard_msgs in @[nonempty (priority := mid) (name := hello) -inst] def V : Bar := .unit

/-- info: hello : Nonempty Bar -/
#guard_msgs in #check hello

/-! Check that `scoped nonempty` correctly adds a scoped instance -/
section «scoped»

def Boz := Unit

namespace Boz

@[scoped nonempty] def foo : Boz := .unit

/-- info: instNonempty -/
#guard_msgs in #synth Nonempty Boz

end Boz

/--
error: failed to synthesize
  Nonempty Boz

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in #synth Nonempty Boz

/-- info: instNonempty -/
#guard_msgs in open scoped Boz in #synth Nonempty Boz

end «scoped»

end

/-! Check interaction of nonempty with private/public. -/

section

@[expose] public def Faa := Unit

@[nonempty] def faaAux : Faa := .unit

-- Should be private:

/--
info: private theorem instNonemptyFaa : Nonempty Faa :=
Nonempty.intro faaAux
-/
#guard_msgs in
#print instNonemptyFaa

@[nonempty (name := bar)] def faaAux' : Faa := .unit

/--
info: private theorem bar : Nonempty Faa :=
Nonempty.intro faaAux'
-/
#guard_msgs in #print bar

end
