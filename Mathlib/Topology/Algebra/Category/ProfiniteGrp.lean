/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Nailin Guan, Yuyang Zhao
-/
import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Category.Profinite.Basic

/-!

# Category of Profinite Groups

We say `G` is a profinite group if it is a topological group which is compact and totally
disconnected.

## Main definitions and results

* `ProfiniteGrp` is the category of profinite groups.

* `ProfiniteGrp.pi` : The pi-type of profinite groups is also a profinite group.

* `ofFiniteGrp` : A `FiniteGrp` when given the discrete topology can be considered as a
  profinite group.

* `ofClosedSubgroup` : A closed subgroup of a profinite group is profinite.

-/

universe u v

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
The category of profinite additive groups. A term of this type consists of a profinite
set with a topological additive group structure.
-/
@[pp_with_univ]
structure ProfiniteAddGrp where
  /-- The underlying profinite topological space. -/
  toProfinite : Profinite
  /-- The additive group structure. -/
  [addGroup : AddGroup toProfinite]
  /-- The above data together form a topological additive group. -/
  [topologicalAddGroup : TopologicalAddGroup toProfinite]

attribute [to_additive] ProfiniteGrp

namespace ProfiniteGrp

@[to_additive]
instance : CoeSort ProfiniteGrp (Type u) where
  coe G := G.toProfinite

attribute [instance] group topologicalGroup
    ProfiniteAddGrp.addGroup ProfiniteAddGrp.topologicalAddGroup

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

/-- Construct a term of `ProfiniteGrp` from a type endowed with the structure of a
compact and totally disconnected topological group.
(The condition of being Hausdorff can be omitted here because totally disconnected implies that {1}
is a closed set, thus implying Hausdorff in a topological group.)-/
@[to_additive "Construct a term of `ProfiniteAddGrp` from a type endowed with the structure of a
compact and totally disconnected topological additive group.
(The condition of being Hausdorff can be omitted here because totally disconnected implies that {0}
is a closed set, thus implying Hausdorff in a topological additive group.)"]
def of (G : Type u) [Group G] [TopologicalSpace G] [TopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] : ProfiniteGrp where
  toProfinite := .of G
  group := ‹_›
  topologicalGroup := ‹_›

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

/-- Construct a term of `ProfiniteGrp` from a type endowed with the structure of a
profinite topological group. -/
@[to_additive "Construct a term of `ProfiniteAddGrp` from a type endowed with the structure of a
profinite topological additive group."]
abbrev ofProfinite (G : Profinite) [Group G] [TopologicalGroup G] :
    ProfiniteGrp := of G

/-- The pi-type of profinite groups is a profinite group. -/
@[to_additive "The pi-type of profinite additive groups is a
profinite additive group."]
def pi {α : Type u} (β : α → ProfiniteGrp) : ProfiniteGrp :=
  let pitype := Profinite.pi fun (a : α) => (β a).toProfinite
  letI (a : α): Group (β a).toProfinite := (β a).group
  letI : Group pitype := Pi.group
  letI : TopologicalGroup pitype := Pi.topologicalGroup
  ofProfinite pitype

/-- A `FiniteGrp` when given the discrete topology can be considered as a profinite group. -/
@[to_additive "A `FiniteAddGrp` when given the discrete topology can be considered as a
profinite additive group."]
def ofFiniteGrp (G : FiniteGrp) : ProfiniteGrp :=
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  letI : TopologicalGroup G := {}
  of G

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

/-!
# The projective limit of finite groups is profinite

* `ProfiniteGrp.limit` : the concretely constructed projective limit of finite groups
  as a subgroup of the pi-type

* `ofLimit`: projective limit of finite groups is a profinite group

* Verify that the constructed limit satisfies the universal property.
-/

section Profiniteoflimit

/- In this section, we prove that the projective limit of finite groups is profinite-/

universe w w'

namespace ProfiniteGrp

variable {J : Type v} [SmallCategory J] (F : J ⥤ ProfiniteGrp.{max v w'})

/-- Concretely constructing the limit of topological group as a subgroup of the  pi-type. -/
def limit : Subgroup (Π j : J, F.obj j) where
  carrier := {x | ∀ ⦃i j : J⦄ (π : i ⟶ j), F.map π (x i) = x j}
  mul_mem' hx hy _ _ π := by simp only [Pi.mul_apply, map_mul, hx π, hy π]
  one_mem' := by simp only [Set.mem_setOf_eq, Pi.one_apply, map_one, implies_true]
  inv_mem' h _ _ π := by simp only [Pi.inv_apply, map_inv, h π]

/--The functor mapping a profinite group to its underlying profinite space-/
def profiniteGrpToProfinite : ProfiniteGrp ⥤ Profinite where
  obj G := G.toProfinite
  map f := ⟨f, by continuity⟩

instance instProfiniteGrpToProfiniteFaithful : profiniteGrpToProfinite.Faithful := {
  map_injective := fun {_ _} _ _ h =>
    ConcreteCategory.hom_ext_iff.mpr (congrFun (congrArg ContinuousMap.toFun h)) }

instance : CompactSpace (limit F) := inferInstanceAs
  (CompactSpace (Profinite.limitCone (F ⋙ profiniteGrpToProfinite.{max v w'})).pt)

/-- Making the direct limit of `FiniteGrp` into a `ProfiniteGrp`. -/
def ofLimit : ProfiniteGrp := .of (ProfiniteGrp.limit F)

/-- Verify that the limit constructed above exist projections to the `FiniteGrps`
that are compatible with the morphisms between them. -/
def limitCone : Limits.Cone F where
  pt := ofLimit F
  π :=
  { app := fun j => {
      toFun := fun x => x.1 j
      map_one' := rfl
      map_mul' := fun x y => rfl
      continuous_toFun := by
        exact (continuous_apply j).comp (continuous_iff_le_induced.mpr fun U a => a)
    }
    naturality := by
      intro i j f
      simp only [Functor.const_obj_obj, Functor.comp_obj,
        Functor.const_obj_map, Category.id_comp, Functor.comp_map]
      congr
      exact funext fun x => (x.2 f).symm
  }

@[simp]
lemma limitCone_pt : (ProfiniteGrp.limitCone F).pt =
    ProfiniteGrp.ofLimit F := rfl

@[simp, nolint simpNF]
lemma limitCone_π_app_apply  (j : J) (x : ofLimit F) :
    ((ProfiniteGrp.limitCone F).π.app j) x = x.1 j := rfl

/-- Verify that the limit constructed above satisfies the universal property. -/
def limitConeIsLimit : Limits.IsLimit (limitCone F) where
  lift cone := {
    toFun := ((Profinite.limitConeIsLimit (F ⋙ profiniteGrpToProfinite)).lift
      (profiniteGrpToProfinite.mapCone cone)).toFun
    map_one' := by
      apply SetCoe.ext
      ext j
      exact map_one (cone.π.app j)
    map_mul' := fun _ _ ↦ by
      apply SetCoe.ext
      ext j
      exact map_mul (cone.π.app j) _ _
    continuous_toFun := ((Profinite.limitConeIsLimit (F ⋙ profiniteGrpToProfinite)).lift
      (profiniteGrpToProfinite.mapCone cone)).continuous }
  uniq cone m h := by
    apply instProfiniteGrpToProfiniteFaithful.map_injective
    simpa using (Profinite.limitConeIsLimit (F ⋙ profiniteGrpToProfinite)).uniq
      (profiniteGrpToProfinite.mapCone cone) (profiniteGrpToProfinite.map m)
      (fun j ↦ congrArg profiniteGrpToProfinite.map (h j))

@[simp, nolint simpNF]
lemma limitConeIsLimit_lift_toFun_coe (j : J) (cone : Limits.Cone F)
    (pt : ↑cone.pt.toProfinite.toTop) :
    (((ProfiniteGrp.limitConeIsLimit F).lift cone) pt).val j = (cone.π.app j) pt := rfl

instance : Limits.HasLimit F where
  exists_limit := Nonempty.intro
    { cone := limitCone F
      isLimit := limitConeIsLimit F }

end ProfiniteGrp

end Profiniteoflimit
