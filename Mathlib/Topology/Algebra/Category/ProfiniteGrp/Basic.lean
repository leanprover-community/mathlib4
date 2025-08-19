/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Nailin Guan, Yuyang Zhao
-/
import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Separation.Connected
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
  [topologicalGroup : IsTopologicalGroup toProfinite]

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
  [topologicalAddGroup : IsTopologicalAddGroup toProfinite]

attribute [to_additive] ProfiniteGrp

@[to_additive]
instance : CoeSort ProfiniteGrp (Type u) where
  coe G := G.toProfinite

attribute [instance] ProfiniteGrp.group ProfiniteGrp.topologicalGroup
    ProfiniteAddGrp.addGroup ProfiniteAddGrp.topologicalAddGroup

/-- Construct a term of `ProfiniteGrp` from a type endowed with the structure of a
compact and totally disconnected topological group.
(The condition of being Hausdorff can be omitted here because totally disconnected implies that {1}
is a closed set, thus implying Hausdorff in a topological group.) -/
@[to_additive /-- Construct a term of `ProfiniteAddGrp` from a type endowed with the structure of a
compact and totally disconnected topological additive group.
(The condition of being Hausdorff can be omitted here because totally disconnected implies that {0}
is a closed set, thus implying Hausdorff in a topological additive group.) -/]
abbrev ProfiniteGrp.of (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] : ProfiniteGrp.{u} where
  toProfinite := .of G
  group := ‹_›
  topologicalGroup := ‹_›

@[to_additive]
lemma ProfiniteGrp.coe_of (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] : (ProfiniteGrp.of G : Type u) = G :=
  rfl

/-- The type of morphisms in `ProfiniteAddGrp`. -/
@[ext]
structure ProfiniteAddGrp.Hom (A B : ProfiniteAddGrp.{u}) where
  private mk ::
  /-- The underlying `ContinuousAddMonoidHom`. -/
  hom' : A →ₜ+ B

/-- The type of morphisms in `ProfiniteGrp`. -/
@[to_additive existing (attr := ext)]
structure ProfiniteGrp.Hom (A B : ProfiniteGrp.{u}) where
  private mk ::
  /-- The underlying `ContinuousMonoidHom`. -/
  hom' : A →ₜ* B

@[to_additive]
instance : Category ProfiniteGrp where
  Hom A B := ProfiniteGrp.Hom A B
  id A := ⟨ContinuousMonoidHom.id A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

@[to_additive]
instance : ConcreteCategory ProfiniteGrp (fun X Y ↦ X →ₜ* Y) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- The underlying `ContinuousMonoidHom`. -/
@[to_additive /-- The underlying `ContinuousAddMonoidHom`. -/]
abbrev ProfiniteGrp.Hom.hom {M N : ProfiniteGrp.{u}} (f : ProfiniteGrp.Hom M N) :
    M →ₜ* N :=
  ConcreteCategory.hom (C := ProfiniteGrp) f

/-- Typecheck a `ContinuousMonoidHom` as a morphism in `ProfiniteGrp`. -/
@[to_additive /-- Typecheck a `ContinuousAddMonoidHom` as a morphism in `ProfiniteAddGrp`. -/]
abbrev ProfiniteGrp.ofHom {X Y : Type u} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [CompactSpace X] [TotallyDisconnectedSpace X] [Group Y] [TopologicalSpace Y]
    [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y]
    (f : X →ₜ* Y) : ProfiniteGrp.of X ⟶ ProfiniteGrp.of Y :=
  ConcreteCategory.ofHom f

namespace ProfiniteGrp

@[to_additive]
instance {M N : ProfiniteGrp.{u}} : CoeFun (M ⟶ N) (fun _ ↦ M → N) where
  coe f := f.hom

@[to_additive (attr := simp)]
lemma hom_id {A : ProfiniteGrp.{u}} : (𝟙 A : A ⟶ A).hom = ContinuousMonoidHom.id A := rfl

/- Provided for rewriting. -/
@[to_additive]
lemma id_apply (A : ProfiniteGrp.{u}) (a : A) :
    (𝟙 A : A ⟶ A) a = a := by simp

@[to_additive (attr := simp)]
lemma hom_comp {A B C : ProfiniteGrp.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

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
lemma hom_ofHom (f : X →ₜ* Y) : (ofHom f).hom = f := rfl

@[to_additive (attr := simp)]
lemma ofHom_hom {A B : ProfiniteGrp.{u}} (f : A ⟶ B) :
    ofHom (Hom.hom f) = f := rfl

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
  let pitype := Profinite.pi fun (a : α) ↦ (β a).toProfinite
  letI (a : α): Group (β a).toProfinite := (β a).group
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

@[to_additive]
instance : HasForget₂ FiniteGrp ProfiniteGrp where
  forget₂ :=
  { obj := ofFiniteGrp
    map := fun f ↦ ⟨f.hom, by continuity⟩ }

@[to_additive]
instance : HasForget₂ ProfiniteGrp Grp where
  forget₂.obj P := Grp.of P
  forget₂.map f := Grp.ofHom f.hom.toMonoidHom

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
  map_injective := fun {_ _} _ _ h ↦
    ConcreteCategory.hom_ext _ _ (CategoryTheory.congr_fun h) }

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
# Limits in the category of profinite groups

In this section, we construct limits in the category of profinite groups.

* `ProfiniteGrp.limitCone` : The explicit limit cone in `ProfiniteGrp`.

* `ProfiniteGrp.limitConeIsLimit`: `ProfiniteGrp.limitCone` is a limit cone.

## TODO

* Figure out the reason that is causing `to_additive` to fail in most part of this section
  and generate the additive version correctly.

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

instance : Group (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt :=
  inferInstanceAs (Group (limitConePtAux F))

instance : IsTopologicalGroup (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt :=
  inferInstanceAs (IsTopologicalGroup (limitConePtAux F))

/-- The explicit limit cone in `ProfiniteGrp`. -/
abbrev limitCone : Limits.Cone F where
  pt := ofProfinite (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt
  π :=
  { app := fun j ↦ ⟨{
      toFun := fun x ↦ x.1 j
      map_one' := rfl
      map_mul' := fun x y ↦ rfl
      continuous_toFun := by
        exact (continuous_apply j).comp (continuous_iff_le_induced.mpr fun U a ↦ a) }⟩
    naturality := fun i j f ↦ by
      simp only [Functor.const_obj_obj, Functor.comp_obj,
        Functor.const_obj_map, Category.id_comp, Functor.comp_map]
      congr
      exact funext fun x ↦ (x.2 f).symm }

/-- `ProfiniteGrp.limitCone` is a limit cone. -/
def limitConeIsLimit : Limits.IsLimit (limitCone F) where
  lift cone := ofHom
    { ((Profinite.limitConeIsLimit (F ⋙ (forget₂ ProfiniteGrp Profinite))).lift
        ((forget₂ ProfiniteGrp Profinite).mapCone cone)).hom with
      map_one' := Subtype.ext (funext fun j ↦ map_one (cone.π.app j).hom)
      -- TODO: investigate whether it's possible to set up `ext` lemmas for the `TopCat`-related
      -- categories so that `by ext j; exact map_one (cone.π.app j)` works here, similarly below.
      map_mul' := fun _ _ ↦ Subtype.ext (funext fun j ↦ map_mul (cone.π.app j).hom _ _) }
  uniq cone m h := by
    apply (forget₂ ProfiniteGrp Profinite).map_injective
    simpa using (Profinite.limitConeIsLimit (F ⋙ (forget₂ ProfiniteGrp Profinite))).uniq
      ((forget₂ ProfiniteGrp Profinite).mapCone cone) ((forget₂ ProfiniteGrp Profinite).map m)
      (fun j ↦ congrArg (forget₂ ProfiniteGrp Profinite).map (h j))

instance : Limits.HasLimit F where
  exists_limit := Nonempty.intro
    { cone := limitCone F
      isLimit := limitConeIsLimit F }

instance : Limits.PreservesLimits (forget₂ ProfiniteGrp Profinite) where
  preservesLimitsOfShape := {
    preservesLimit := fun {F} ↦ CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone
      (limitConeIsLimit F) (Profinite.limitConeIsLimit (F ⋙ (forget₂ ProfiniteGrp Profinite))) }

instance : CompactSpace (limitConePtAux F) :=
  inferInstanceAs (CompactSpace (Profinite.limitCone (F ⋙ (forget₂ ProfiniteGrp Profinite))).pt)

/-- The abbreviation for the limit of `ProfiniteGrp`s. -/
abbrev limit : ProfiniteGrp := ProfiniteGrp.of (ProfiniteGrp.limitConePtAux F)

@[ext]
lemma limit_ext (x y : limit F) (hxy : ∀ j, x.val j = y.val j) : x = y :=
  Subtype.ext (funext hxy)

@[simp]
lemma limit_one_val (j : J) : (1 : limit F).val j = 1 :=
  rfl

@[simp]
lemma limit_mul_val (x y : limit F) (j : J) : (x * y).val j = x.val j * y.val j :=
  rfl

end ProfiniteGrp

end Limits
