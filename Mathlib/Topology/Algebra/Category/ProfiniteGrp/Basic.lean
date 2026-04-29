/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Nailin Guan, Yuyang Zhao
-/
module

public import Mathlib.Algebra.Category.Grp.FiniteGrp
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.Separation.Connected
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

@[expose] public section

universe u v

open CategoryTheory Topology

/--
The category of profinite groups. A term of this type consists of a profinite
set with a topological group structure.
-/
@[pp_with_univ]
structure ProfiniteGrp where
  /-- The underlying profinite topological space. -/
  toProfinite : Profinite.{u}
  /-- The group structure. -/
  [group : Group toProfinite]
  /-- The above data together form a topological group. -/
  [topologicalGroup : IsTopologicalGroup toProfinite]

/--
The category of profinite additive groups. A term of this type consists of a profinite
set with a topological additive group structure.
-/
@[pp_with_univ]
structure ProfiniteAddGrp where
  /-- The underlying profinite topological space. -/
  toProfinite : Profinite.{u}
  /-- The additive group structure. -/
  [addGroup : AddGroup toProfinite]
  /-- The above data together form a topological additive group. -/
  [topologicalAddGroup : IsTopologicalAddGroup toProfinite]

attribute [to_additive] ProfiniteGrp

@[to_additive]
instance : CoeSort ProfiniteGrp (Type u) where
  coe G := G.toProfinite

attribute [instance] ProfiniteGrp.group ProfiniteGrp.topologicalGroup
    ProfiniteAddGrp.addGroup ProfiniteAddGrp.topologicalAddGroup

/-- Construct a term of `ProfiniteGrp` from a type endowed with the structure of a
compact and totally disconnected topological group.
(The condition of being Hausdorff can be omitted here because totally disconnected implies that
`{1}` is a closed set, thus implying Hausdorff in a topological group.) -/
@[to_additive /-- Construct a term of `ProfiniteAddGrp` from a type endowed with the structure of a
compact and totally disconnected topological additive group.
(The condition of being Hausdorff can be omitted here because totally disconnected implies that
`{0}` is a closed set, thus implying Hausdorff in a topological additive group.) -/]
abbrev ProfiniteGrp.of (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] : ProfiniteGrp.{u} where
  toProfinite := .of G
  group := ‹_›
  topologicalGroup := ‹_›

@[to_additive]
lemma ProfiniteGrp.coe_of (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] : (ProfiniteGrp.of G : Type u) = G :=
  rfl

@[to_additive ProfiniteAddGrp]
mk_concrete_category ProfiniteGrp (· →ₜ* ·) ContinuousMonoidHom.id ContinuousMonoidHom.comp
  with_of_hom {X Y : Type u} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
  [CompactSpace X] [TotallyDisconnectedSpace X] [Group Y] [TopologicalSpace Y]
  [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y]
  hom_type (X →ₜ* Y) from (ProfiniteGrp.of X) to (ProfiniteGrp.of Y)
  to_additive ProfiniteAddGrp (· →ₜ+ ·) ContinuousAddMonoidHom.id ContinuousAddMonoidHom.comp
  with_of_hom {X Y : Type u} [AddGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [CompactSpace X] [TotallyDisconnectedSpace X] [AddGroup Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y]
  hom_type (X →ₜ+ Y) from (ProfiniteAddGrp.of X) to (ProfiniteAddGrp.of Y)

namespace ProfiniteGrp

@[to_additive]
instance {M N : ProfiniteGrp.{u}} : CoeFun (M ⟶ N) (fun _ ↦ M → N) where
  coe f := f.hom

/- Provided for rewriting. -/
@[to_additive]
lemma id_apply (A : ProfiniteGrp.{u}) (a : A) :
    (𝟙 A : A ⟶ A) a = a := by simp

/- Provided for rewriting. -/
@[to_additive]
lemma comp_apply {A B C : ProfiniteGrp.{u}} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) := by
  simp only [hom_comp, ContinuousMonoidHom.comp_toFun]

@[to_additive (attr := ext)]
lemma hom_ext {A B : ProfiniteGrp.{u}} {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

variable {X Y Z : Type u} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [CompactSpace X] [TotallyDisconnectedSpace X] [Group Y] [TopologicalSpace Y]
    [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] [Group Z]
    [TopologicalSpace Z] [IsTopologicalGroup Z] [CompactSpace Z] [TotallyDisconnectedSpace Z]

@[to_additive (attr := simp)]
lemma ofHom_id : ofHom (ContinuousMonoidHom.id X) = 𝟙 (of X) := rfl

@[to_additive (attr := simp)]
lemma ofHom_comp (f : X →ₜ* Y) (g : Y →ₜ* Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

@[to_additive]
lemma ofHom_apply (f : X →ₜ* Y) (x : X) : ofHom f x = f x := rfl

@[to_additive]
lemma inv_hom_apply {A B : ProfiniteGrp.{u}} (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by
  simp

@[to_additive]
lemma hom_inv_apply {A B : ProfiniteGrp.{u}} (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by
  simp

@[to_additive (attr := simp)]
theorem coe_id (X : ProfiniteGrp) : (𝟙 X : X → X) = id :=
  rfl

@[to_additive (attr := simp)]
theorem coe_comp {X Y Z : ProfiniteGrp} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : X → Z) = g ∘ f :=
  rfl

/-- Construct a term of `ProfiniteGrp` from a type endowed with the structure of a
profinite topological group. -/
@[to_additive /-- Construct a term of `ProfiniteAddGrp` from a type endowed with the structure of a
profinite topological additive group. -/]
abbrev ofProfinite (G : Profinite) [Group G] [IsTopologicalGroup G] :
    ProfiniteGrp := of G

/-- The pi-type of profinite groups is a profinite group. -/
@[to_additive /-- The pi-type of profinite additive groups is a
profinite additive group. -/]
def pi {α : Type u} (β : α → ProfiniteGrp) : ProfiniteGrp :=
  let pitype := Profinite.pi fun (a : α) => (β a).toProfinite
  letI (a : α) : Group (β a).toProfinite := (β a).group
  letI : Group pitype := Pi.group
  letI : IsTopologicalGroup pitype := Pi.topologicalGroup
  ofProfinite pitype

/-- A `FiniteGrp` when given the discrete topology can be considered as a profinite group. -/
@[to_additive /-- A `FiniteAddGrp` when given the discrete topology can be considered as a
profinite additive group. -/]
def ofFiniteGrp (G : FiniteGrp) : ProfiniteGrp :=
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  letI : IsTopologicalGroup G := {}
  of G

/-- A morphism of `FiniteGrp` induces a morphism of the associated profinite groups. -/
@[to_additive /-- A morphism of `FiniteAddGrp` induces a morphism of the associated profinite
additive groups. -/]
def ofFiniteGrpHom {G H : FiniteGrp.{u}} (f : G ⟶ H) : ofFiniteGrp G ⟶ ofFiniteGrp H :=
  ConcreteCategory.ofHom ⟨f.hom.hom, by fun_prop⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[to_additive]
instance : HasForget₂ FiniteGrp ProfiniteGrp where
  forget₂ :=
  { obj := ofFiniteGrp
    map := ofFiniteGrpHom }

@[to_additive]
instance : HasForget₂ ProfiniteGrp GrpCat where
  forget₂.obj P := GrpCat.of P
  forget₂.map f := GrpCat.ofHom f.hom.toMonoidHom

/-- A closed subgroup of a profinite group is profinite. -/
@[to_additive /-- A closed additive subgroup of a profinite additive group is profinite. -/]
def ofClosedSubgroup {G : ProfiniteGrp} (H : ClosedSubgroup G) : ProfiniteGrp :=
  letI : CompactSpace H := inferInstance
  of H.1

/-- A topological group that has a `ContinuousMulEquiv` to a profinite group is profinite. -/
@[to_additive /-- A topological additive group that has a `ContinuousAddEquiv` to a
profinite additive group is profinite. -/]
def ofContinuousMulEquiv {G : ProfiniteGrp.{u}} {H : Type v} [TopologicalSpace H]
    [Group H] [IsTopologicalGroup H] (e : G ≃ₜ* H) : ProfiniteGrp.{v} :=
  let _ : CompactSpace H := Homeomorph.compactSpace e.toHomeomorph
  let _ : TotallyDisconnectedSpace H := Homeomorph.totallyDisconnectedSpace e.toHomeomorph
  .of H

/-- Build an isomorphism in the category `ProfiniteGrp` from
a `ContinuousMulEquiv` between `ProfiniteGrp`s. -/
def ContinuousMulEquiv.toProfiniteGrpIso {X Y : ProfiniteGrp} (e : X ≃ₜ* Y) : X ≅ Y where
  hom := ofHom e
  inv := ofHom e.symm

/-- The functor mapping a profinite group to its underlying profinite space. -/
@[to_additive]
instance : HasForget₂ ProfiniteGrp Profinite where
  forget₂ := {
    obj G := G.toProfinite
    map f := CompHausLike.ofHom _ ⟨f, by continuity⟩}

@[to_additive]
instance : (forget₂ ProfiniteGrp Profinite).Faithful := {
  map_injective := fun {_ _} _ _ h =>
    ConcreteCategory.hom_ext _ _ fun x ↦ CategoryTheory.congr_fun h x }


instance : (forget₂ ProfiniteGrp Profinite).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget₂ ProfiniteGrp Profinite).map f)
    let e : X ≃ₜ* Y :=
      { CompHausLike.homeoOfIso i with
          map_mul' := map_mul f.hom }
    exact (ContinuousMulEquiv.toProfiniteGrpIso e).isIso_hom

instance : (forget ProfiniteGrp.{u}).ReflectsIsomorphisms :=
  CategoryTheory.reflectsIsomorphisms_comp (forget₂ ProfiniteGrp Profinite) (forget Profinite)

end ProfiniteGrp

/-!
### Limits in the category of profinite groups

In this section, we construct limits in the category of profinite groups.

* `ProfiniteGrp.limitCone` : The explicit limit cone in `ProfiniteGrp`.

* `ProfiniteGrp.limitConeIsLimit`: `ProfiniteGrp.limitCone` is a limit cone.

-/

section Limits

namespace ProfiniteGrp

variable {J : Type v} [SmallCategory J] (F : J ⥤ ProfiniteGrp.{max v u})

/-- Auxiliary construction to obtain the group structure on the limit of profinite groups. -/
@[to_additive /-- Auxiliary construction to obtain the additive group structure on the limit of
profinite additive groups. -/]
def limitConePtAux : Subgroup (Π j : J, F.obj j) where
  carrier := {x | ∀ ⦃i j : J⦄ (π : i ⟶ j), F.map π (x i) = x j}
  mul_mem' hx hy _ _ π := by simp only [Pi.mul_apply, map_mul, hx π, hy π]
  one_mem' := by simp only [Set.mem_setOf_eq, Pi.one_apply, map_one, implies_true]
  inv_mem' h _ _ π := by simp only [Pi.inv_apply, map_inv, h π]

set_option backward.inferInstanceAs.wrap false in
@[to_additive]
instance : Group (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt :=
  inferInstanceAs (Group (limitConePtAux F))

@[to_additive]
instance : IsTopologicalGroup (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt :=
  inferInstanceAs (IsTopologicalGroup (limitConePtAux F))

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The explicit limit cone in `ProfiniteGrp`. -/
@[to_additive /-- The explicit limit cone in `ProfiniteAddGrp`. -/]
abbrev limitCone : Limits.Cone F where
  pt := ofProfinite (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt
  π :=
  { app := fun j => ⟨{
      toFun := fun x => x.1 j
      map_one' := rfl
      map_mul' := fun x y => rfl
      continuous_toFun := by
        exact (continuous_apply j).comp (continuous_iff_le_induced.mpr fun U a => a) }⟩
    naturality := fun i j f => by
      simp only [Functor.const_obj_obj, Functor.comp_obj,
        Functor.const_obj_map, Category.id_comp, Functor.comp_map]
      congr
      exact funext fun x => (x.2 f).symm }

/-- `ProfiniteGrp.limitCone` is a limit cone. -/
@[to_additive /-- `ProfiniteAddGrp.limitCone` is a limit cone. -/]
def limitConeIsLimit : Limits.IsLimit (limitCone F) where
  lift cone := ofHom
    { ((Profinite.limitConeIsLimit (F ⋙ (forget₂ ProfiniteGrp Profinite))).lift
        ((forget₂ ProfiniteGrp Profinite).mapCone cone)).hom.hom with
      map_one' := Subtype.ext (funext fun j ↦ map_one (cone.π.app j).hom)
      -- TODO: investigate whether it's possible to set up `ext` lemmas for the `TopCat`-related
      -- categories so that `by ext j; exact map_one (cone.π.app j)` works here, similarly below.
      map_mul' := fun _ _ ↦ Subtype.ext (funext fun j ↦ map_mul (cone.π.app j).hom _ _) }
  uniq cone m h := by
    apply (forget₂ ProfiniteGrp Profinite).map_injective
    simpa using (Profinite.limitConeIsLimit (F ⋙ (forget₂ ProfiniteGrp Profinite))).uniq
      ((forget₂ ProfiniteGrp Profinite).mapCone cone) ((forget₂ ProfiniteGrp Profinite).map m)
      (fun j ↦ congrArg (forget₂ ProfiniteGrp Profinite).map (h j))

@[to_additive]
instance : Limits.HasLimit F where
  exists_limit := Nonempty.intro
    { cone := limitCone F
      isLimit := limitConeIsLimit F }

@[to_additive]
instance : Limits.PreservesLimits (forget₂ ProfiniteGrp Profinite) where
  preservesLimitsOfShape := {
    preservesLimit := fun {F} ↦ CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone
      (limitConeIsLimit F) (Profinite.limitConeIsLimit (F ⋙ (forget₂ ProfiniteGrp Profinite))) }

set_option backward.inferInstanceAs.wrap false in
@[to_additive]
instance : CompactSpace (limitConePtAux F) :=
  inferInstanceAs (CompactSpace (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt)

/-- The abbreviation for the limit of `ProfiniteGrp`s. -/
@[to_additive /-- The abbreviation for the limit of `ProfiniteAddGrp`s. -/]
abbrev limit : ProfiniteGrp := ProfiniteGrp.of (ProfiniteGrp.limitConePtAux F)

@[to_additive (attr := ext)]
lemma limit_ext (x y : limit F) (hxy : ∀ j, x.val j = y.val j) : x = y :=
  Subtype.ext (funext hxy)

@[to_additive (attr := simp)]
lemma limit_one_val (j : J) : (1 : limit F).val j = 1 :=
  rfl

@[to_additive (attr := simp)]
lemma limit_mul_val (x y : limit F) (j : J) : (x * y).val j = x.val j * y.val j :=
  rfl

end ProfiniteGrp

end Limits
