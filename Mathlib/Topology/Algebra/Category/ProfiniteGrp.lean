/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Nailin Guan, Youle Fang, Yuyang Zhao
-/
import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.Topology.Algebra.ClosedSubgroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.OpenSubgroup
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

/-- A closed subgroup of a profinite group is profinite. -/
def ofClosedSubgroup {G : ProfiniteGrp} (H : ClosedSubgroup G)  : ProfiniteGrp :=
  letI : CompactSpace H := isCompact_iff_compactSpace.mp (IsClosed.isCompact H.isClosed')
  of H.1

/-- A topological group that has a ContinuousMulEquiv to a profinite group is profinite. -/
def ofContinuousMulEquivProfiniteGrp {G : ProfiniteGrp.{u}} {H : Type v} [TopologicalSpace H]
    [Group H] [TopologicalGroup H] (e : G ≃ₜ* H) : ProfiniteGrp.{v} :=
  letI : CompactSpace H := Homeomorph.compactSpace e.toHomeomorph
  letI : TotallyDisconnectedSpace G := Profinite.instTotallyDisconnectedSpaceαTopologicalSpaceToTop
  letI : TotallyDisconnectedSpace H := Homeomorph.totallyDisconnectedSpace e.toHomeomorph
  .of H

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

/-!
# A profinite group is the projective limit of finite groups
In a profinite group `P` :
* `QuotientOpenNormalSubgroup` : The functor that maps open normal subgroup of `P` to
  the quotient group of it (which is finite, as shown by previous lemmas).

* `CanonicalQuotientMap` : The continuous homomorphism from `P` to the limit of the quotient group
  of open normal subgroup ordered by inclusion of the open normal subgroup.

* `canonicalQuotientMap_surjective` : The `CanonicalQuotientMap` is surjective, proven by
  demonstrating that its range is dense and closed.

* `OpenNormalSubgroupSubClopenNhdsOfOne` : For any open neighborhood of `1` there is an
  open normal subgroup contained within it.

* `canonicalQuotientMap_injective` : The `CanonicalQuotientMap` is injective. This is proven by
  showing that for any element not equal to one, the image of it on the coordinate of
  the open normal subgroup that doesn't contain it is not equal to 1, thus not in the kernel.

* `ContinuousMulEquivLimitQuotientOpenNormalSubgroup` : The `CanonicalQuotientMap` can serve as a
  `ContinuousMulEquiv`, with the continuity of other side given by
  `Continuous.homeoOfEquivCompactToT2`.

-/

section limitofProfinite

namespace ProfiniteGrp

open TopologicalGroup

/-- The open normal subgroup contained in an open nhd of `1`
in a compact totallydisconnected topological group. -/
noncomputable def OpenNormalSubgroupSubOpenNhdsOfOne {G : Type*} [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {U : Set G}
    (UOpen : IsOpen U) (einU : 1 ∈ U) : OpenNormalSubgroup G :=
  let h := Classical.choose_spec ((Filter.HasBasis.mem_iff'
    ((nhds_basis_clopen (1 : G))) U ).mp <| mem_nhds_iff.mpr (by use U))
  OpenNormalSubgroupSubClopenNhdsOfOne h.1.2 h.1.1

theorem openNormalSubgroupSubOpenNhdsOfOne_spec {G : Type*} [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {U : Set G}
    (UOpen : IsOpen U) (einU : 1 ∈ U) :
    ((OpenNormalSubgroupSubOpenNhdsOfOne UOpen einU) : Set G) ⊆ U :=
  let ⟨⟨einW,WClopen⟩,WsubU⟩ := Classical.choose_spec <| (Filter.HasBasis.mem_iff'
    ((nhds_basis_clopen (1 : G))) U ).mp <| mem_nhds_iff.mpr (by use U)
  fun _ b ↦ WsubU (openNormalSubgroupSubClopenNhdsOfOne_spec WClopen einW b)

section

instance (P : ProfiniteGrp) : SmallCategory (OpenNormalSubgroup P) :=
  Preorder.smallCategory (OpenNormalSubgroup ↑P.toProfinite.toTop)

/-- Define the functor from OpenNormalSubgroup of a profinite group to the quotient group of it as
  a `FiniteGrp` -/
def QuotientOpenNormalSubgroup (P : ProfiniteGrp) :
    OpenNormalSubgroup P ⥤ FiniteGrp := {
    obj := fun H => FiniteGrp.of (P ⧸ H.toSubgroup)
    map := fun {H K} fHK => QuotientGroup.map H.toSubgroup K.toSubgroup (.id _) <|
        Subgroup.comap_id (N := P) K ▸ leOfHom fHK
    map_id := fun H => by
      simp only [QuotientGroup.map_id]
      rfl
    map_comp := fun {X Y Z} f g => (QuotientGroup.map_comp_map
      X.toSubgroup Y.toSubgroup Z.toSubgroup (.id _) (.id _)
      (Subgroup.comap_id Y.toSubgroup ▸ leOfHom f)
      (Subgroup.comap_id Z.toSubgroup ▸ leOfHom g)).symm
  }


/-- Defining the canonical projection from a profinite group to the limit of the quotient groups
as a subgroup of the product space -/
def CanonicalQuotientMap (P : ProfiniteGrp.{u}) : P ⟶
    ofLimit ((QuotientOpenNormalSubgroup P) ⋙ (forget₂ FiniteGrp ProfiniteGrp)) where
  toFun := fun p => {
    val := fun H => QuotientGroup.mk p
    property := fun A B _ => rfl
  }
  map_one' := Subtype.val_inj.mp (by ext H; rfl)
  map_mul' := fun x y => Subtype.val_inj.mp (by ext H; rfl)
  continuous_toFun := by
    apply continuous_induced_rng.mpr (continuous_pi _)
    intro H
    dsimp
    apply Continuous.mk
    intro s _
    rw [← (Set.biUnion_preimage_singleton QuotientGroup.mk s)]
    apply isOpen_iUnion
    intro i
    apply isOpen_iUnion
    intro _
    convert IsOpen.leftCoset H.toOpenSubgroup.isOpen' (Quotient.out' i)
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    nth_rw 1 [← QuotientGroup.out_eq' i, eq_comm, QuotientGroup.eq]
    symm
    apply Set.mem_smul_set_iff_inv_smul_mem

theorem canonicalQuotientMap_dense (P : ProfiniteGrp.{u}) : Dense <|
    Set.range (CanonicalQuotientMap P) :=
  dense_iff_inter_open.mpr
    fun U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩ => (by
      let uMemPiOpen := isOpen_pi_iff.mp hsO
      simp_rw [← hsv] at uDefaultSpec
      rw [Set.mem_preimage] at uDefaultSpec
      specialize uMemPiOpen _ uDefaultSpec
      rcases uMemPiOpen with ⟨J, fJ, h_ok_and_in_s⟩
      let M := iInf (fun (j : J) => j.1.1.1)
      haveI hM : M.Normal := Subgroup.normal_iInf_normal fun j => j.1.isNormal'
      haveI hMOpen : IsOpen (M : Set P) := by
        rw [Subgroup.coe_iInf]
        exact isOpen_iInter_of_finite fun i => i.1.1.isOpen'
      let m : OpenNormalSubgroup P := { M with isOpen' := hMOpen }
      rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
      use (CanonicalQuotientMap P).toFun origin
      constructor
      · rw [← hsv]
        apply h_ok_and_in_s.2
        exact fun a a_in_J => by
          let M_to_Na : m ⟶ a := (iInf_le (fun (j : J) => j.1.1.1) ⟨a, a_in_J⟩).hom
          rw [← (P.CanonicalQuotientMap.toFun origin).property M_to_Na]
          show (P.QuotientOpenNormalSubgroup.map M_to_Na) (QuotientGroup.mk' M origin) ∈ _
          rw [horigin]
          exact Set.mem_of_eq_of_mem (hspc M_to_Na) (h_ok_and_in_s.1 a a_in_J).2
      · exact ⟨origin, rfl⟩
    )

theorem canonicalQuotientMap_surjective (P : ProfiniteGrp.{u}) :
    Function.Surjective (CanonicalQuotientMap P) := by
  have : IsClosedMap P.CanonicalQuotientMap := P.CanonicalQuotientMap.continuous_toFun.isClosedMap
  haveI compact_s: IsCompact (Set.univ : Set P) := CompactSpace.isCompact_univ
  have : IsClosed (P.CanonicalQuotientMap '' Set.univ) := this _ <| IsCompact.isClosed compact_s
  apply closure_eq_iff_isClosed.mpr at this
  rw [Set.image_univ, Dense.closure_eq <| canonicalQuotientMap_dense P] at this
  exact Set.range_iff_surjective.mp (id this.symm)

theorem canonicalQuotientMap_injective (P : ProfiniteGrp.{u}) :
    Function.Injective (CanonicalQuotientMap P) := by
  show Function.Injective (CanonicalQuotientMap P).toMonoidHom
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro x h
  by_contra xne1
  have : (1 : P) ∈ ({x}ᶜ : Set P) := Set.mem_compl_singleton_iff.mpr fun a => xne1 (id (Eq.symm a))
  let H := OpenNormalSubgroupSubOpenNhdsOfOne (isOpen_compl_singleton) this
  have xninH : x ∉ H := fun a =>
    (openNormalSubgroupSubOpenNhdsOfOne_spec (isOpen_compl_singleton) this) a rfl
  have xinKer : (CanonicalQuotientMap P).toMonoidHom x = 1 := h
  simp only [CanonicalQuotientMap, MonoidHom.coe_mk, OneHom.coe_mk] at xinKer
  apply Subtype.val_inj.mpr at xinKer
  have xinH := congrFun xinKer H
  rw [OneMemClass.coe_one, Pi.one_apply, QuotientGroup.eq_one_iff] at xinH
  exact xninH xinH

/-- Make the equivilence into a ContinuousMulEquiv -/
noncomputable def ContinuousMulEquivLimitQuotientOpenNormalSubgroup (P : ProfiniteGrp.{u}) :
    P ≃ₜ* (ofLimit ((QuotientOpenNormalSubgroup P) ⋙ (forget₂ FiniteGrp ProfiniteGrp))) := {
  (Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ ⟨canonicalQuotientMap_injective P, canonicalQuotientMap_surjective P⟩)
    P.CanonicalQuotientMap.continuous_toFun)
  with
  map_mul' := (CanonicalQuotientMap P).map_mul'
  }

end

end ProfiniteGrp

end limitofProfinite
