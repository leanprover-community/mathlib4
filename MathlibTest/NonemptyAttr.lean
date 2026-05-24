/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.Tactic.NonemptyAttr
public import Mathlib.CategoryTheory.Functor.FullyFaithful

open CategoryTheory

@[expose] public section

variable (C : Type*) [Category* C]
def F : C ⥤ C where
  obj x := x
  map x := x

@[nonempty]
def Ff : (F C).FullyFaithful :=
  sorry

@[nonempty]
def Ff' : (F C).FullyFaithful :=
  sorry

instance (C : Type*) [Category* C] : Nonempty (F C).FullyFaithful := sorry
instance (C : Type*) [Category* C] : Nonempty (F C).FullyFaithful := sorry
instance (C : Type*) [Category* C] : Nonempty (F C).FullyFaithful := sorry

-- @[nonempty]
-- def Ff' : ∀ (C : Type*) [Category* C], (F C).FullyFaithful :=
--   sorry

section

#check Ff
-- #check instFullF
-- #check instFaithfulF

set_option trace.Meta.synthInstance true in
#synth Nonempty (F C).FullyFaithful
#synth (F C).Full
#synth (F C).Faithful

end

example : (F C).Full := inferInstance
example : (F C).Faithful := inferInstance

@[nonempty]
def Ff'' : Nat := sorry

end
