/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Nailin Guan, Yi Song, Xuchun Li
-/
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Sets.Opens

/-!
# Open subgroups of a topological group

This files builds the lattice `OpenSubgroup G` of open subgroups in a topological group `G`,
and its additive version `OpenAddSubgroup`.  This lattice has a top element, the subgroup of all
elements, but no bottom element in general. The trivial subgroup which is the natural candidate
bottom has no reason to be open (this happens only in discrete groups).

Note that this notion is especially relevant in a non-archimedean context, for instance for
`p`-adic groups.

## Main declarations

* `OpenSubgroup.isClosed`: An open subgroup is automatically closed.
* `Subgroup.isOpen_mono`: A subgroup containing an open subgroup is open.
                           There are also versions for additive groups, submodules and ideals.
* `OpenSubgroup.comap`: Open subgroups can be pulled back by a continuous group morphism.

## TODO
* Prove that the identity component of a locally path connected group is an open subgroup.
  Up to now this file is really geared towards non-archimedean algebra, not Lie groups.
-/


open TopologicalSpace Topology Function

/-- The type of open subgroups of a topological additive group. -/
structure OpenAddSubgroup (G : Type*) [AddGroup G] [TopologicalSpace G] extends AddSubgroup G where
  isOpen' : IsOpen carrier

/-- The type of open subgroups of a topological group. -/
@[to_additive]
structure OpenSubgroup (G : Type*) [Group G] [TopologicalSpace G] extends Subgroup G where
  isOpen' : IsOpen carrier

/-- Reinterpret an `OpenSubgroup` as a `Subgroup`. -/
add_decl_doc OpenSubgroup.toSubgroup

/-- Reinterpret an `OpenAddSubgroup` as an `AddSubgroup`. -/
add_decl_doc OpenAddSubgroup.toAddSubgroup

attribute [coe] OpenSubgroup.toSubgroup OpenAddSubgroup.toAddSubgroup

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {U V : OpenSubgroup G} {g : G}

@[to_additive]
instance hasCoeSubgroup : CoeTC (OpenSubgroup G) (Subgroup G) :=
  ⟨toSubgroup⟩

@[to_additive]
theorem toSubgroup_injective : Injective ((↑) : OpenSubgroup G → Subgroup G)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

@[to_additive]
instance : SetLike (OpenSubgroup G) G where
  coe U := U.1
  coe_injective' _ _ h := toSubgroup_injective <| SetLike.ext' h

@[to_additive]
instance : SubgroupClass (OpenSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

/-- Coercion from `OpenSubgroup G` to `Opens G`. -/
@[to_additive (attr := coe) /-- Coercion from `OpenAddSubgroup G` to `Opens G`. -/]
def toOpens (U : OpenSubgroup G) : Opens G := ⟨U, U.isOpen'⟩

@[to_additive]
instance hasCoeOpens : CoeTC (OpenSubgroup G) (Opens G) := ⟨toOpens⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_toOpens : ((U : Opens G) : Set G) = U :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_toSubgroup : ((U : Subgroup G) : Set G) = U := rfl

@[to_additive (attr := simp, norm_cast)]
theorem mem_toOpens : g ∈ (U : Opens G) ↔ g ∈ U := Iff.rfl

@[to_additive (attr := simp, norm_cast)]
theorem mem_toSubgroup : g ∈ (U : Subgroup G) ↔ g ∈ U := Iff.rfl

@[to_additive (attr := ext)]
theorem ext (h : ∀ x, x ∈ U ↔ x ∈ V) : U = V :=
  SetLike.ext h

variable (U)

@[to_additive]
protected theorem isOpen : IsOpen (U : Set G) :=
  U.isOpen'

@[to_additive]
theorem mem_nhds_one : (U : Set G) ∈ 𝓝 (1 : G) :=
  U.isOpen.mem_nhds U.one_mem

variable {U}

@[to_additive] instance : Top (OpenSubgroup G) := ⟨⟨⊤, isOpen_univ⟩⟩

@[to_additive (attr := simp)]
theorem mem_top (x : G) : x ∈ (⊤ : OpenSubgroup G) :=
  trivial

@[to_additive (attr := simp, norm_cast)]
theorem coe_top : ((⊤ : OpenSubgroup G) : Set G) = Set.univ :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem toSubgroup_top : ((⊤ : OpenSubgroup G) : Subgroup G) = ⊤ :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem toOpens_top : ((⊤ : OpenSubgroup G) : Opens G) = ⊤ :=
  rfl

@[to_additive]
instance : Inhabited (OpenSubgroup G) :=
  ⟨⊤⟩

@[to_additive]
theorem isClosed [ContinuousMul G] (U : OpenSubgroup G) : IsClosed (U : Set G) := by
  apply isOpen_compl_iff.1
  refine isOpen_iff_forall_mem_open.2 fun x hx ↦ ⟨(fun y ↦ y * x⁻¹) ⁻¹' U, ?_, ?_, ?_⟩
  · refine fun u hux hu ↦ hx ?_
    simp only [Set.mem_preimage, SetLike.mem_coe] at hux hu ⊢
    convert U.mul_mem (U.inv_mem hux) hu
    simp
  · exact U.isOpen.preimage (continuous_mul_right _)
  · simp [one_mem]

@[to_additive]
theorem isClopen [ContinuousMul G] (U : OpenSubgroup G) : IsClopen (U : Set G) :=
  ⟨U.isClosed, U.isOpen⟩

section

variable {H : Type*} [Group H] [TopologicalSpace H]

/-- The product of two open subgroups as an open subgroup of the product group. -/
@[to_additive prod
/-- The product of two open subgroups as an open subgroup of the product group. -/]
def prod (U : OpenSubgroup G) (V : OpenSubgroup H) : OpenSubgroup (G × H) :=
  ⟨.prod U V, U.isOpen.prod V.isOpen⟩

@[deprecated (since := "2025-03-11")]
alias _root_.OpenAddSubgroup.sum := OpenAddSubgroup.prod

@[to_additive (attr := simp, norm_cast) coe_prod]
theorem coe_prod (U : OpenSubgroup G) (V : OpenSubgroup H) :
    (U.prod V : Set (G × H)) = (U : Set G) ×ˢ (V : Set H) :=
  rfl

@[deprecated (since := "2025-03-11")]
alias _root_.OpenAddSubgroup.coe_sum := OpenAddSubgroup.coe_prod

@[to_additive (attr := simp, norm_cast) toAddSubgroup_prod]
theorem toSubgroup_prod (U : OpenSubgroup G) (V : OpenSubgroup H) :
    (U.prod V : Subgroup (G × H)) = (U : Subgroup G).prod V :=
  rfl

@[deprecated (since := "2025-03-11")]
alias _root_.OpenAddSubgroup.toAddSubgroup_sum := OpenAddSubgroup.toAddSubgroup_prod

end

@[to_additive]
instance instInfOpenSubgroup : Min (OpenSubgroup G) :=
  ⟨fun U V ↦ ⟨U ⊓ V, U.isOpen.inter V.isOpen⟩⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_inf : (↑(U ⊓ V) : Set G) = (U : Set G) ∩ V :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem toSubgroup_inf : (↑(U ⊓ V) : Subgroup G) = ↑U ⊓ ↑V :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem toOpens_inf : (↑(U ⊓ V) : Opens G) = ↑U ⊓ ↑V :=
  rfl

@[to_additive (attr := simp)]
theorem mem_inf {x} : x ∈ U ⊓ V ↔ x ∈ U ∧ x ∈ V :=
  Iff.rfl

@[to_additive]
instance instPartialOrderOpenSubgroup : PartialOrder (OpenSubgroup G) := inferInstance

-- We override `toPartialorder` to get better `le`
@[to_additive]
instance instSemilatticeInfOpenSubgroup : SemilatticeInf (OpenSubgroup G) :=
  { SetLike.coe_injective.semilatticeInf ((↑) : OpenSubgroup G → Set G) fun _ _ ↦ rfl with
    toPartialOrder := instPartialOrderOpenSubgroup }

@[to_additive]
instance : OrderTop (OpenSubgroup G) where
  top := ⊤
  le_top _ := Set.subset_univ _

@[to_additive (attr := simp, norm_cast)]
theorem toSubgroup_le : (U : Subgroup G) ≤ (V : Subgroup G) ↔ U ≤ V :=
  Iff.rfl

variable {N : Type*} [Group N] [TopologicalSpace N]

/-- The preimage of an `OpenSubgroup` along a continuous `Monoid` homomorphism
  is an `OpenSubgroup`. -/
@[to_additive /-- The preimage of an `OpenAddSubgroup` along a continuous `AddMonoid` homomorphism
is an `OpenAddSubgroup`. -/]
def comap (f : G →* N) (hf : Continuous f) (H : OpenSubgroup N) : OpenSubgroup G :=
  ⟨.comap f H, H.isOpen.preimage hf⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_comap (H : OpenSubgroup N) (f : G →* N) (hf : Continuous f) :
    (H.comap f hf : Set G) = f ⁻¹' H :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem toSubgroup_comap (H : OpenSubgroup N) (f : G →* N) (hf : Continuous f) :
    (H.comap f hf : Subgroup G) = (H : Subgroup N).comap f :=
  rfl

@[to_additive (attr := simp)]
theorem mem_comap {H : OpenSubgroup N} {f : G →* N} {hf : Continuous f} {x : G} :
    x ∈ H.comap f hf ↔ f x ∈ H :=
  Iff.rfl

@[to_additive]
theorem comap_comap {P : Type*} [Group P] [TopologicalSpace P] (K : OpenSubgroup P) (f₂ : N →* P)
    (hf₂ : Continuous f₂) (f₁ : G →* N) (hf₁ : Continuous f₁) :
    (K.comap f₂ hf₂).comap f₁ hf₁ = K.comap (f₂.comp f₁) (hf₂.comp hf₁) :=
  rfl

end OpenSubgroup
namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

@[to_additive]
theorem isOpen_of_mem_nhds [ContinuousMul G] (H : Subgroup G) {g : G} (hg : (H : Set G) ∈ 𝓝 g) :
    IsOpen (H : Set G) := by
  refine isOpen_iff_mem_nhds.2 fun x hx ↦ ?_
  have hg' : g ∈ H := SetLike.mem_coe.1 (mem_of_mem_nhds hg)
  have : Filter.Tendsto (fun y ↦ y * (x⁻¹ * g)) (𝓝 x) (𝓝 g) :=
    (continuous_id.mul continuous_const).tendsto' _ _ (mul_inv_cancel_left _ _)
  simpa only [SetLike.mem_coe, Filter.mem_map',
    H.mul_mem_cancel_right (H.mul_mem (H.inv_mem hx) hg')] using this hg

@[to_additive]
theorem isOpen_mono [ContinuousMul G] {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂)
    (h₁ : IsOpen (H₁ : Set G)) : IsOpen (H₂ : Set G) :=
  isOpen_of_mem_nhds _ <| Filter.mem_of_superset (h₁.mem_nhds <| one_mem H₁) h

@[to_additive]
theorem isOpen_of_openSubgroup
    [ContinuousMul G] (H : Subgroup G) {U : OpenSubgroup G} (h : ↑U ≤ H) :
    IsOpen (H : Set G) :=
  isOpen_mono h U.isOpen

/-- If a subgroup of a topological group has `1` in its interior, then it is open. -/
@[to_additive /-- If a subgroup of an additive topological group has `0` in its interior, then it is
open. -/]
theorem isOpen_of_one_mem_interior [ContinuousMul G] (H : Subgroup G)
    (h_1_int : (1 : G) ∈ interior (H : Set G)) : IsOpen (H : Set G) :=
  isOpen_of_mem_nhds H <| mem_interior_iff_mem_nhds.1 h_1_int

@[to_additive]
lemma isClosed_of_isOpen [ContinuousMul G] (U : Subgroup G) (h : IsOpen (U : Set G)) :
    IsClosed (U : Set G) :=
  OpenSubgroup.isClosed ⟨U, h⟩

@[to_additive]
lemma subgroupOf_isOpen (U K : Subgroup G) (h : IsOpen (K : Set G)) :
    IsOpen (K.subgroupOf U : Set U) :=
  Continuous.isOpen_preimage (continuous_iff_le_induced.mpr fun _ ↦ id) _ h

@[to_additive]
lemma discreteTopology [ContinuousMul G] (U : Subgroup G) (h : IsOpen (U : Set G)) :
    DiscreteTopology (G ⧸ U) := by
  refine discreteTopology_iff_isOpen_singleton.mpr (fun g ↦ ?_)
  induction g using Quotient.inductionOn with | h g =>
  change IsOpen (QuotientGroup.mk ⁻¹' {QuotientGroup.mk g})
  convert_to IsOpen ((g * ·) '' U)
  · ext g'
    simp only [Set.mem_preimage, Set.mem_singleton_iff, QuotientGroup.eq, Set.image_mul_left]
    rw [← U.inv_mem_iff]
    simp
  · exact Homeomorph.mulLeft g |>.isOpen_image |>.mpr h

@[to_additive]
instance [ContinuousMul G] (U : OpenSubgroup G) : DiscreteTopology (G ⧸ U.toSubgroup) :=
  discreteTopology U.toSubgroup U.isOpen

@[to_additive]
lemma quotient_finite_of_isOpen [ContinuousMul G] [CompactSpace G] (U : Subgroup G)
    (h : IsOpen (U : Set G)) : Finite (G ⧸ U) :=
  have : DiscreteTopology (G ⧸ U) := U.discreteTopology h
  finite_of_compact_of_discrete

@[to_additive]
instance [ContinuousMul G] [CompactSpace G] (U : OpenSubgroup G) : Finite (G ⧸ U.toSubgroup) :=
  quotient_finite_of_isOpen U.toSubgroup U.isOpen

@[to_additive]
lemma quotient_finite_of_isOpen' [IsTopologicalGroup G] [CompactSpace G] (U : Subgroup G)
    (K : Subgroup U) (hUopen : IsOpen (U : Set G)) (hKopen : IsOpen (K : Set U)) :
    Finite (U ⧸ K) :=
  have : CompactSpace U := isCompact_iff_compactSpace.mp <| IsClosed.isCompact <|
    U.isClosed_of_isOpen hUopen
  K.quotient_finite_of_isOpen hKopen

@[to_additive]
instance [IsTopologicalGroup G] [CompactSpace G] (U : OpenSubgroup G) (K : OpenSubgroup U) :
    Finite (U ⧸ K.toSubgroup) :=
  quotient_finite_of_isOpen' U.toSubgroup K.toSubgroup U.isOpen K.isOpen

end Subgroup

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]

@[to_additive]
instance : Max (OpenSubgroup G) :=
  ⟨fun U V ↦ ⟨U ⊔ V, Subgroup.isOpen_mono (le_sup_left : U.1 ≤ U.1 ⊔ V.1) U.isOpen⟩⟩

@[to_additive (attr := simp, norm_cast)]
theorem toSubgroup_sup (U V : OpenSubgroup G) : (↑(U ⊔ V) : Subgroup G) = ↑U ⊔ ↑V := rfl

-- We override `toPartialorder` to get better `le`
@[to_additive]
instance : Lattice (OpenSubgroup G) :=
  { instSemilatticeInfOpenSubgroup,
    toSubgroup_injective.semilatticeSup ((↑) : OpenSubgroup G → Subgroup G) fun _ _ ↦ rfl with
    toPartialOrder := instPartialOrderOpenSubgroup }

end OpenSubgroup

namespace Submodule

open OpenAddSubgroup

variable {R : Type*} {M : Type*} [CommRing R]
variable [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [Module R M]

theorem isOpen_mono {U P : Submodule R M} (h : U ≤ P) (hU : IsOpen (U : Set M)) :
    IsOpen (P : Set M) :=
  @AddSubgroup.isOpen_mono M _ _ _ U.toAddSubgroup P.toAddSubgroup h hU

end Submodule

namespace Ideal

variable {R : Type*} [CommRing R]
variable [TopologicalSpace R] [IsTopologicalRing R]

theorem isOpen_of_isOpen_subideal {U I : Ideal R} (h : U ≤ I) (hU : IsOpen (U : Set R)) :
    IsOpen (I : Set R) :=
  @Submodule.isOpen_mono R R _ _ _ _ Semiring.toModule _ _ h hU

end Ideal

/-!
# Open normal subgroups of a topological group

This section builds the lattice `OpenNormalSubgroup G` of open subgroups in a topological group `G`,
and its additive version `OpenNormalAddSubgroup`.

-/

section

universe u

/-- The type of open normal subgroups of a topological group. -/
@[ext]
structure OpenNormalSubgroup (G : Type u) [Group G] [TopologicalSpace G]
  extends OpenSubgroup G where
  isNormal' : toSubgroup.Normal := by infer_instance

/-- The type of open normal subgroups of a topological additive group. -/
@[ext]
structure OpenNormalAddSubgroup (G : Type u) [AddGroup G] [TopologicalSpace G]
  extends OpenAddSubgroup G where
  isNormal' : toAddSubgroup.Normal := by infer_instance

attribute [to_additive] OpenNormalSubgroup

namespace OpenNormalSubgroup

variable {G : Type u} [Group G] [TopologicalSpace G]

@[to_additive]
instance (H : OpenNormalSubgroup G) : H.toSubgroup.Normal := H.isNormal'

@[to_additive]
theorem toSubgroup_injective : Function.Injective
    (fun H ↦ H.toOpenSubgroup.toSubgroup : OpenNormalSubgroup G → Subgroup G) :=
  fun A B h ↦ by
  ext
  dsimp at h
  rw [h]

@[to_additive]
instance : SetLike (OpenNormalSubgroup G) G where
  coe U := U.1
  coe_injective' _ _ h := toSubgroup_injective <| SetLike.ext' h

@[to_additive]
instance : SubgroupClass (OpenNormalSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem U := U.one_mem'
  inv_mem := Subgroup.inv_mem' _

@[to_additive]
instance : Coe (OpenNormalSubgroup G) (Subgroup G) where
  coe H := H.toOpenSubgroup.toSubgroup

@[to_additive]
instance instPartialOrderOpenNormalSubgroup : PartialOrder (OpenNormalSubgroup G) := inferInstance

@[to_additive]
instance instInfOpenNormalSubgroup : Min (OpenNormalSubgroup G) :=
  ⟨fun U V ↦ ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup,
    Subgroup.normal_inf_normal U.toSubgroup V.toSubgroup⟩⟩

@[to_additive]
instance instSemilatticeInfOpenNormalSubgroup : SemilatticeInf (OpenNormalSubgroup G) :=
  SetLike.coe_injective.semilatticeInf ((↑) : OpenNormalSubgroup G → Set G) fun _ _ ↦ rfl

@[to_additive]
instance [ContinuousMul G] : Max (OpenNormalSubgroup G) :=
  ⟨fun U V ↦ ⟨U.toOpenSubgroup ⊔ V.toOpenSubgroup,
    Subgroup.sup_normal U.toOpenSubgroup.1 V.toOpenSubgroup.1⟩⟩

@[to_additive]
instance instSemilatticeSupOpenNormalSubgroup [ContinuousMul G] :
    SemilatticeSup (OpenNormalSubgroup G) :=
  toSubgroup_injective.semilatticeSup _ (fun _ _ ↦ rfl)

@[to_additive]
instance [ContinuousMul G] : Lattice (OpenNormalSubgroup G) :=
  { instSemilatticeInfOpenNormalSubgroup,
    instSemilatticeSupOpenNormalSubgroup with
    toPartialOrder := instPartialOrderOpenNormalSubgroup}

end OpenNormalSubgroup

end

/-!
# Existence of an open subgroup in any clopen neighborhood of the neutral element

This section proves the lemma `IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one`, which
states that in a compact topological group, for any clopen neighborhood of 1,
there exists an open subgroup contained within it.
-/

open scoped Pointwise

variable {G : Type*} [TopologicalSpace G]

structure IsTopologicalAddGroup.addNegClosureNhd (T W : Set G) [AddGroup G] : Prop where
  nhds : T ∈ 𝓝 0
  neg : -T = T
  isOpen : IsOpen T
  add : W + T ⊆ W

/-- For a set `W`, `T` is a neighborhood of `1` which is open, stable under inverse and satisfies
`T * W ⊆ W`. -/
@[to_additive
/-- For a set `W`, `T` is a neighborhood of `0` which is open, stable under negation and satisfies
`T + W ⊆ W`. -/]
structure IsTopologicalGroup.mulInvClosureNhd (T W : Set G) [Group G] : Prop where
  nhds : T ∈ 𝓝 1
  inv : T⁻¹ = T
  isOpen : IsOpen T
  mul : W * T ⊆ W

namespace IsTopologicalGroup

variable [Group G] [IsTopologicalGroup G] [CompactSpace G]

open Set Filter

@[to_additive]
lemma exist_mul_closure_nhds {W : Set G} (WClopen : IsClopen W) : ∃ T ∈ 𝓝 (1 : G), W * T ⊆ W := by
  apply WClopen.isClosed.isCompact.induction_on (p := fun S ↦ ∃ T ∈ 𝓝 (1 : G), S * T ⊆ W)
    ⟨Set.univ, by simp only [univ_mem, empty_mul, empty_subset, and_self]⟩
    (fun _ _ huv ⟨T, hT, mem⟩ ↦ ⟨T, hT, (mul_subset_mul_right huv).trans mem⟩)
    fun U V ⟨T₁, hT₁, mem1⟩ ⟨T₂, hT₂, mem2⟩ ↦ ⟨T₁ ∩ T₂, inter_mem hT₁ hT₂, by
      rw [union_mul]
      exact union_subset (mul_subset_mul_left inter_subset_left |>.trans mem1)
        (mul_subset_mul_left inter_subset_right |>.trans mem2) ⟩
  intro x memW
  have : (x, 1) ∈ (fun p ↦ p.1 * p.2) ⁻¹' W := by simp [memW]
  rcases isOpen_prod_iff.mp (continuous_mul.isOpen_preimage W <| WClopen.2) x 1 this with
    ⟨U, V, Uopen, Vopen, xmemU, onememV, prodsub⟩
  have h6 : U * V ⊆ W := mul_subset_iff.mpr (fun _ hx _ hy ↦ prodsub (mk_mem_prod hx hy))
  exact ⟨U ∩ W, ⟨U, Uopen.mem_nhds xmemU, W, fun _ a ↦ a, rfl⟩,
    V, IsOpen.mem_nhds Vopen onememV, fun _ a ↦ h6 ((mul_subset_mul_right inter_subset_left) a)⟩

@[deprecated (since := "2025-05-22")] alias exist_mul_closure_nhd := exist_mul_closure_nhds
@[deprecated (since := "2025-05-22")] alias _root_.IsTopologicalAddGroup.exist_add_closure_nhd :=
  IsTopologicalAddGroup.exist_add_closure_nhds

@[to_additive]
lemma exists_mulInvClosureNhd {W : Set G} (WClopen : IsClopen W) :
    ∃ T, mulInvClosureNhd T W := by
  rcases exist_mul_closure_nhds WClopen with ⟨S, Smemnhds, mulclose⟩
  rcases mem_nhds_iff.mp Smemnhds with ⟨U, UsubS, Uopen, onememU⟩
  use U ∩ U⁻¹
  constructor
  · simp [Uopen.mem_nhds onememU, inv_mem_nhds_one]
  · simp [inter_comm]
  · exact Uopen.inter Uopen.inv
  · exact fun a ha ↦ mulclose (mul_subset_mul_left UsubS (mul_subset_mul_left inter_subset_left ha))

@[to_additive]
theorem exist_openSubgroup_sub_clopen_nhds_of_one {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    ∃ H : OpenSubgroup G, (H : Set G) ⊆ W := by
  rcases exists_mulInvClosureNhd WClopen with ⟨V, hV⟩
  let S : Subgroup G := {
    carrier := ⋃ n, V ^ (n + 1)
    mul_mem' := fun ha hb ↦ by
      rcases mem_iUnion.mp ha with ⟨k, hk⟩
      rcases mem_iUnion.mp hb with ⟨l, hl⟩
      apply mem_iUnion.mpr
      use k + 1 + l
      rw [add_assoc, pow_add]
      exact Set.mul_mem_mul hk hl
    one_mem' := by
      apply mem_iUnion.mpr
      use 0
      simp [mem_of_mem_nhds hV.nhds]
    inv_mem' := fun ha ↦ by
      rcases mem_iUnion.mp ha with ⟨k, hk⟩
      apply mem_iUnion.mpr
      use k
      rw [← hV.inv]
      simpa only [inv_pow, Set.mem_inv, inv_inv] using hk }
  have : IsOpen (⋃ n, V ^ (n + 1)) := by
    refine isOpen_iUnion (fun n ↦ ?_)
    rw [pow_succ]
    exact hV.isOpen.mul_left
  use ⟨S, this⟩
  have mulVpow (n : ℕ) : W * V ^ (n + 1) ⊆ W := by
    induction n with
    | zero => simp [hV.mul]
    | succ n ih =>
      rw [pow_succ, ← mul_assoc]
      exact (Set.mul_subset_mul_right ih).trans hV.mul
  have (n : ℕ) : V ^ (n + 1) ⊆ W * V ^ (n + 1) := by
    intro x xin
    rw [Set.mem_mul]
    use 1, einW, x, xin
    rw [one_mul]
  apply iUnion_subset fun i _ a ↦ mulVpow i (this i a)

@[deprecated (since := "2025-05-22")]
alias exist_openSubgroup_sub_clopen_nhd_of_one := exist_openSubgroup_sub_clopen_nhds_of_one

@[deprecated (since := "2025-05-22")]
alias _root_.IsTopologicalAddGroup.exist_openAddSubgroup_sub_clopen_nhd_of_zero :=
  IsTopologicalAddGroup.exist_openAddSubgroup_sub_clopen_nhds_of_zero

end IsTopologicalGroup
