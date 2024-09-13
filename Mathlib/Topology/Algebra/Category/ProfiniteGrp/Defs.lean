/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Nailin Guan, Yuyang Zhao
-/
import Mathlib.Algebra.Category.FiniteGrp.Basic
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom


/-!

# Category of Profinite Groups

We say `G` is a profinite group if it is a topological group which is compact and totally
disconnected.

## Main definitions and results

* `ProfiniteGrp` is the type of profinite groups.

* `Pi.profiniteGrp` : The product of profinite groups is also a profinite group.

-/

suppress_compilation

universe u

open CategoryTheory Topology

/--
The category of profinite groups. A term of this type consists of a profinite
set with a topological group structure.
-/
@[pp_with_univ]
structure ProfiniteGrp where
  /-- The underlying profinite topological space. -/
  toProfinite : Profinite
  /-- The group structure. -/
  [group : Group toProfinite]
  /-- The above data together form a topological group. -/
  [topologicalGroup : TopologicalGroup toProfinite]

/--
The category of profinite add groups. A term of this type consists of a profinite
set with a topological add group structure.
-/
@[pp_with_univ]
structure ProfiniteAddGrp where
  /-- The underlying profinite topological space. -/
  toProfinite : Profinite
  /-- The add group structure. -/
  [addGroup : AddGroup toProfinite]
  /-- The above data together form a topological add group. -/
  [topologicalAddGroup : TopologicalAddGroup toProfinite]

attribute [to_additive] ProfiniteGrp

namespace ProfiniteGrp

@[to_additive]
instance : CoeSort ProfiniteGrp (Type u) where
  coe G := G.toProfinite

@[to_additive]
instance (G : ProfiniteGrp) : Group G := G.group

@[to_additive]
instance (G : ProfiniteGrp) : TopologicalGroup G := G.topologicalGroup

@[to_additive]
instance : Category ProfiniteGrp where
  Hom A B := ContinuousMonoidHom A B
  id A := ContinuousMonoidHom.id A
  comp f g := ContinuousMonoidHom.comp g f

@[to_additive]
instance (G H : ProfiniteGrp) : FunLike (G ⟶ H) G H :=
  inferInstanceAs <| FunLike (ContinuousMonoidHom G H) G H

@[to_additive]
instance (G H : ProfiniteGrp) : MonoidHomClass (G ⟶ H) G H :=
  inferInstanceAs <| MonoidHomClass (ContinuousMonoidHom G H) G H

@[to_additive]
instance (G H : ProfiniteGrp) : ContinuousMapClass (G ⟶ H) G H :=
  inferInstanceAs <| ContinuousMapClass (ContinuousMonoidHom G H) G H

@[to_additive]
instance : ConcreteCategory ProfiniteGrp where
  forget :=
  { obj := fun G => G
    map := fun f => f }
  forget_faithful :=
    { map_injective := by
        intro G H f g h
        exact DFunLike.ext _ _ <| fun x => congr_fun h x }

/--A topological group that is compact and totally disconnected is profinite-/
@[to_additive]
def of (G : Type u) [Group G] [TopologicalSpace G] [TopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] : ProfiniteGrp where
  toProfinite := .of G
  group := ‹_›
  topologicalGroup := ‹_›

/--A topological add group that is compact and totally disconnected is profinite-/
add_decl_doc ProfiniteAddGrp.of

@[to_additive (attr := simp)]
theorem coe_of (X : ProfiniteGrp) : (of X : Type _) = X :=
  rfl

@[to_additive (attr := simp)]
theorem coe_id (X : ProfiniteGrp) : (𝟙 ((forget ProfiniteGrp).obj X)) = id :=
  rfl

@[to_additive (attr := simp)]
theorem coe_comp {X Y Z : ProfiniteGrp} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((forget ProfiniteGrp).map f ≫ (forget ProfiniteGrp).map g) = g ∘ f :=
  rfl

/--A topological group when considered as a topological space is profinite is profinite-/
@[to_additive]
abbrev ofProfinite (G : Profinite) [Group G] [TopologicalGroup G] :
    ProfiniteGrp := of G

/--A topological add group when considered as a topological space is profinite is profinite-/
add_decl_doc ProfiniteAddGrp.ofProfinite

/--The product of profinite group is profinite-/
@[to_additive]
def pi {α : Type u} (β : α → ProfiniteGrp) : ProfiniteGrp :=
  let pitype := Profinite.pi fun (a : α) => (β a).toProfinite
  letI (a : α): Group (β a).toProfinite := (β a).group
  letI : Group pitype := Pi.group
  letI : TopologicalGroup pitype := Pi.topologicalGroup
  ofProfinite pitype

/--The product of profinite add group is profinite-/
add_decl_doc ProfiniteAddGrp.pi

/--A FiniteGrp when given the discrete topology can be condsidered as a profinite group-/
@[to_additive]
def ofFiniteGrp (G : FiniteGrp) : ProfiniteGrp :=
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  letI : TopologicalGroup G := {}
  of G

/--A FiniteAddGrp when given the discrete topology can be condsidered as a profinite add group-/
add_decl_doc ProfiniteAddGrp.ofFiniteAddGrp

@[to_additive]
instance : HasForget₂ FiniteGrp ProfiniteGrp where
  forget₂ :=
  { obj := ofFiniteGrp
    map := fun f => ⟨f, by continuity⟩ }

@[to_additive]
instance : HasForget₂ ProfiniteGrp Grp where
  forget₂ := {
    obj := fun P => ⟨P, P.group⟩
    map := fun f => f.toMonoidHom
  }

end ProfiniteGrp
