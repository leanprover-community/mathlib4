/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Category.Pointed.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Non-abelian group cohomology

Let `G` be a group acting on another (not necessarily abelian) group `A`, in this file we define
`H⁰(G, A)` and `H¹(G, A)`, and prove some basic properties about it.

## Main Results

## Reference

-/

universe u

open CategoryTheory

namespace groupCohomology

namespace NonAbelian

section basic

abbrev NonAbelianRep (G : Type u) [Monoid G] := Action AddGrp.{u} G

variable (G : Type u) [Monoid G]

instance : CoeSort (NonAbelianRep G) (Type u) := ⟨fun V ↦ V.V⟩

variable (A : NonAbelianRep G)

instance : AddGroup A := inferInstance

instance (A : NonAbelianRep G) : DistribMulAction G A := sorry

end basic

section H0

variable {G : Type u} [Monoid G]

def H0 (A : NonAbelianRep G) : AddSubmonoid A where
  carrier := setOf fun v => ∀ g : G, g • v = v
  add_mem' := sorry
  zero_mem' := sorry

instance (A : NonAbelianRep G) : DistribMulAction G (H0 A) := sorry

def H0.map (A B : NonAbelianRep G) (f : A →+[G] B) : H0 A →+[G] H0 B := sorry

end H0

section H1

variable (G : Type u) [Monoid G] (A : NonAbelianRep G)

def Z1 :=
  { f : G → A // ∀ g h : G, f (g * h) = f g + (g • f h : A)}

namespace Z1

instance zero : Zero (Z1 G A) := ⟨⟨0, fun g h => by simp⟩⟩
instance inhabited : Inhabited (Z1 G A) := ⟨0⟩

instance coeFun : CoeFun (Z1 G A) (fun _ ↦ G → A) :=
  ⟨fun f ↦ f.val⟩

variable {G} in
def cohomologous {A : NonAbelianRep G} (f g : Z1 G A) : Prop :=
  ∃ a : A, ∀ h : G, g h = - a + f h + (h • a)

def setoid (G : Type u) [Monoid G] (A : NonAbelianRep G) : Setoid (Z1 G A) :=
  { r := cohomologous,
    iseqv := sorry }

end Z1

def H1 (A : NonAbelianRep G) : Pointed where
  X := Quotient (Z1.setoid G A)
  point := ⟦0⟧

instance : Zero (H1 G A) := ⟨⟦0⟧⟩
instance : Inhabited (H1 G A) := ⟨0⟩

end H1

section connectHom

variable {G : Type u} [Group G] (S : ShortComplex (NonAbelianRep G))



end connectHom

end NonAbelian

end groupCohomology
