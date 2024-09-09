/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Nailin Guan, Yuyang Zhao, Yongle Hu
-/
import Mathlib.Algebra.Category.Grp.Basic
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

@[pp_with_univ]
structure ProfiniteGrp where
  toProfinite : Profinite
  [isGroup : Group toProfinite]
  [isTopologicalGroup : TopologicalGroup toProfinite]

@[pp_with_univ]
structure FiniteGrp where
  toGrp : Grp
  [isFinite : Finite toGrp]

namespace FiniteGrp

instance : CoeSort FiniteGrp.{u} (Type u) where
  coe G := G.toGrp

instance : Category FiniteGrp := InducedCategory.category FiniteGrp.toGrp

instance : ConcreteCategory FiniteGrp := InducedCategory.concreteCategory FiniteGrp.toGrp

instance (G : FiniteGrp) : Group G := inferInstanceAs <| Group G.toGrp

instance (G : FiniteGrp) : Finite G := G.isFinite

instance (G H : FiniteGrp) : FunLike (G ⟶ H) G H :=
  inferInstanceAs <| FunLike (G →* H) G H

instance (G H : FiniteGrp) : MonoidHomClass (G ⟶ H) G H :=
  inferInstanceAs <| MonoidHomClass (G →* H) G H

def of (G : Type u) [Group G] [Finite G] : FiniteGrp where
  toGrp := Grp.of G
  isFinite := ‹_›

def ofHom {X Y : Type u} [Group X] [Finite X] [Group Y] [Finite Y] (f : X →* Y) : of X ⟶ of Y :=
  Grp.ofHom f

lemma ofHom_apply {X Y : Type u} [Group X] [Finite X] [Group Y] [Finite Y] (f : X →* Y) (x : X) :
    ofHom f x = f x :=
  rfl

end FiniteGrp

namespace ProfiniteGrp

instance : CoeSort ProfiniteGrp (Type u) where
  coe G := G.toProfinite

instance (G : ProfiniteGrp) : Group G := G.isGroup

instance (G : ProfiniteGrp) : TopologicalGroup G := G.isTopologicalGroup

def of (G : Type u) [Group G] [TopologicalSpace G] [TopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] : ProfiniteGrp where
  toProfinite := .of G
  isGroup := ‹_›
  isTopologicalGroup := ‹_›

def ofProfinite (G : Profinite) [Group G] [TopologicalGroup G] : ProfiniteGrp where
  toProfinite := G
  isGroup := inferInstanceAs <| Group G
  isTopologicalGroup := inferInstanceAs <| TopologicalGroup G

def Pi.profiniteGrp {α : Type u} (β : α → ProfiniteGrp) : ProfiniteGrp :=
  let pitype := Profinite.Pi.profinite fun (a : α) => (β a).toProfinite
  letI (a : α): Group (β a).toProfinite := (β a).isGroup
  letI : Group pitype := Pi.group
  letI : TopologicalGroup pitype := Pi.topologicalGroup
  ofProfinite pitype

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
    map := fun f => f.toFun }
  forget_faithful :=
    { map_injective := by
        intro G H f g h
        simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, id_eq] at h ⊢
        exact DFunLike.ext _ _ <| fun x => congr_fun h x }

def ofFiniteGrp (G : FiniteGrp) : ProfiniteGrp :=
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  letI : TopologicalGroup G := {}
  of G

instance : CategoryTheory.HasForget₂ FiniteGrp ProfiniteGrp where
  forget₂ :=
  { obj := ofFiniteGrp
    map := fun f => ⟨f, by continuity⟩ }

end ProfiniteGrp
