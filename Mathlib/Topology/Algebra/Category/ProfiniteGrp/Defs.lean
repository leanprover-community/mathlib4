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

* `FiniteGrp` is the type of finite groups.

* `Pi.profiniteGrp` : The product of profinite groups is also a profinite group.

-/

suppress_compilation

universe u v

open CategoryTheory Topology

/--Defining the structure of profinite group-/
@[pp_with_univ]
structure ProfiniteGrp where
  /--the underlying set is profinite-/
  toProfinite : Profinite
  /--it is also a topological group with the topology given-/
  [isGroup : Group toProfinite]
  [isTopologicalGroup : TopologicalGroup toProfinite]

namespace ProfiniteGrp

instance : CoeSort ProfiniteGrp (Type u) where
  coe G := G.toProfinite

instance (G : ProfiniteGrp) : Group G := G.isGroup

instance (G : ProfiniteGrp) : TopologicalGroup G := G.isTopologicalGroup

instance : Category ProfiniteGrp where
  Hom A B := ContinuousMonoidHom A B
  id A := ContinuousMonoidHom.id A
  comp f g := ContinuousMonoidHom.comp g f

instance (G H : ProfiniteGrp) : FunLike (G ⟶ H) G H :=
  inferInstanceAs <| FunLike (ContinuousMonoidHom G H) G H

instance (G H : ProfiniteGrp) : MonoidHomClass (G ⟶ H) G H :=
  inferInstanceAs <| MonoidHomClass (ContinuousMonoidHom G H) G H

instance (G H : ProfiniteGrp) : ContinuousMapClass (G ⟶ H) G H :=
  inferInstanceAs <| ContinuousMapClass (ContinuousMonoidHom G H) G H

instance : ConcreteCategory ProfiniteGrp where
  forget :=
  { obj := fun G => G
    map := fun f => f }
  forget_faithful :=
    { map_injective := by
        intro G H f g h
        exact DFunLike.ext _ _ <| fun x => congr_fun h x }

/--A topological group that is compact and totally disconnected is profinite-/
def of (G : Type u) [Group G] [TopologicalSpace G] [TopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] : ProfiniteGrp where
  toProfinite := .of G
  isGroup := ‹_›
  isTopologicalGroup := ‹_›

@[simp]
theorem coe_of (X : ProfiniteGrp) : (of X : Type _) = X :=
  rfl

@[simp]
theorem coe_id (X : ProfiniteGrp) : (𝟙 ((forget ProfiniteGrp).obj X)) = id :=
  rfl

@[simp]
theorem coe_comp {X Y Z : ProfiniteGrp} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((forget ProfiniteGrp).map f ≫ (forget ProfiniteGrp).map g) = g ∘ f :=
  rfl

/--A topological group when considered as a topological space is profinite is profinite-/
abbrev ofProfinite (G : Profinite) [Group G] [TopologicalGroup G] :
    ProfiniteGrp := of G

/--The product of profinite group is profinite-/
def Pi.profiniteGrp {α : Type u} (β : α → ProfiniteGrp) : ProfiniteGrp :=
  let pitype := Profinite.Pi.profinite fun (a : α) => (β a).toProfinite
  letI (a : α): Group (β a).toProfinite := (β a).isGroup
  letI : Group pitype := Pi.group
  letI : TopologicalGroup pitype := Pi.topologicalGroup
  ofProfinite pitype

/--A FiniteGrp when given the discrete topology can be condsidered as a profinite group-/
def ofFiniteGrp (G : FiniteGrp) : ProfiniteGrp :=
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  letI : TopologicalGroup G := {}
  of G

instance : HasForget₂ FiniteGrp ProfiniteGrp where
  forget₂ :=
  { obj := ofFiniteGrp
    map := fun f => ⟨f, by continuity⟩ }

end ProfiniteGrp
