/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Nailin Guan
-/
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Sets.Opens

/-!
# Open subgroups of a topological groups

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
@[to_additive (attr := coe) "Coercion from `OpenAddSubgroup G` to `Opens G`."]
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
@[to_additive "The product of two open subgroups as an open subgroup of the product group."]
def prod (U : OpenSubgroup G) (V : OpenSubgroup H) : OpenSubgroup (G × H) :=
  ⟨.prod U V, U.isOpen.prod V.isOpen⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_prod (U : OpenSubgroup G) (V : OpenSubgroup H) :
    (U.prod V : Set (G × H)) = (U : Set G) ×ˢ (V : Set H) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem toSubgroup_prod (U : OpenSubgroup G) (V : OpenSubgroup H) :
    (U.prod V : Subgroup (G × H)) = (U : Subgroup G).prod V :=
  rfl

end

@[to_additive]
instance instInfOpenSubgroup : Inf (OpenSubgroup G) :=
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

-- Porting note: we override `toPartialorder` to get better `le`
@[to_additive]
instance instSemilatticeInfOpenSubgroup : SemilatticeInf (OpenSubgroup G) :=
  { SetLike.coe_injective.semilatticeInf ((↑) : OpenSubgroup G → Set G) fun _ _ ↦ rfl with
    toInf := instInfOpenSubgroup
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
@[to_additive "The preimage of an `OpenAddSubgroup` along a continuous `AddMonoid` homomorphism
is an `OpenAddSubgroup`."]
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
theorem isOpen_of_openSubgroup [ContinuousMul G] (H: Subgroup G) {U : OpenSubgroup G} (h : ↑U ≤ H) :
    IsOpen (H : Set G) :=
  isOpen_mono h U.isOpen

/-- If a subgroup of a topological group has `1` in its interior, then it is open. -/
@[to_additive "If a subgroup of an additive topological group has `0` in its interior, then it is
open."]
theorem isOpen_of_one_mem_interior [ContinuousMul G] (H: Subgroup G)
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
  refine singletons_open_iff_discrete.mp (fun g ↦ ?_)
  induction' g using Quotient.inductionOn with g
  show IsOpen (QuotientGroup.mk ⁻¹' {QuotientGroup.mk g})
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
lemma quotient_finite_of_isOpen' [TopologicalGroup G] [CompactSpace G] (U : Subgroup G)
    (K : Subgroup U) (hUopen : IsOpen (U : Set G)) (hKopen : IsOpen (K : Set U)) :
    Finite (U ⧸ K) :=
  have : CompactSpace U := isCompact_iff_compactSpace.mp <| IsClosed.isCompact <|
    U.isClosed_of_isOpen hUopen
  K.quotient_finite_of_isOpen hKopen

@[to_additive]
instance [TopologicalGroup G] [CompactSpace G] (U : OpenSubgroup G) (K : OpenSubgroup U) :
    Finite (U ⧸ K.toSubgroup) :=
  quotient_finite_of_isOpen' U.toSubgroup K.toSubgroup U.isOpen K.isOpen

end Subgroup

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]

@[to_additive]
instance : Sup (OpenSubgroup G) :=
  ⟨fun U V ↦ ⟨U ⊔ V, Subgroup.isOpen_mono (le_sup_left : U.1 ≤ U.1 ⊔ V.1) U.isOpen⟩⟩

@[to_additive (attr := simp, norm_cast)]
theorem toSubgroup_sup (U V : OpenSubgroup G) : (↑(U ⊔ V) : Subgroup G) = ↑U ⊔ ↑V := rfl

-- Porting note: we override `toPartialorder` to get better `le`
@[to_additive]
instance : Lattice (OpenSubgroup G) :=
  { instSemilatticeInfOpenSubgroup,
    toSubgroup_injective.semilatticeSup ((↑) : OpenSubgroup G → Subgroup G) fun _ _ ↦ rfl with
    toPartialOrder := instPartialOrderOpenSubgroup }

end OpenSubgroup

namespace Submodule

open OpenAddSubgroup

variable {R : Type*} {M : Type*} [CommRing R]
variable [AddCommGroup M] [TopologicalSpace M] [TopologicalAddGroup M] [Module R M]

theorem isOpen_mono {U P : Submodule R M} (h : U ≤ P) (hU : IsOpen (U : Set M)) :
    IsOpen (P : Set M) :=
  @AddSubgroup.isOpen_mono M _ _ _ U.toAddSubgroup P.toAddSubgroup h hU

end Submodule

namespace Ideal

variable {R : Type*} [CommRing R]
variable [TopologicalSpace R] [TopologicalRing R]

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
instance instInfOpenNormalSubgroup : Inf (OpenNormalSubgroup G) :=
  ⟨fun U V ↦ ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup,
    Subgroup.normal_inf_normal U.toSubgroup V.toSubgroup⟩⟩

@[to_additive]
instance instSemilatticeInfOpenNormalSubgroup : SemilatticeInf (OpenNormalSubgroup G) :=
  SetLike.coe_injective.semilatticeInf ((↑) : OpenNormalSubgroup G → Set G) fun _ _ ↦ rfl

@[to_additive]
instance [ContinuousMul G] : Sup (OpenNormalSubgroup G) :=
  ⟨fun U V ↦ ⟨U.toOpenSubgroup ⊔ V.toOpenSubgroup,
    Subgroup.sup_normal U.toOpenSubgroup.1 V.toOpenSubgroup.1⟩⟩

@[to_additive]
instance instSemilatticeSupOpenNormalSubgroup [ContinuousMul G] :
    SemilatticeSup (OpenNormalSubgroup G) :=
  toSubgroup_injective.semilatticeSup
    (fun (H : OpenNormalSubgroup G) ↦ ↑H.toOpenSubgroup) (fun _ _ ↦ rfl)

@[to_additive]
instance [ContinuousMul G] : Lattice (OpenNormalSubgroup G) :=
  { instSemilatticeInfOpenNormalSubgroup,
    instSemilatticeSupOpenNormalSubgroup with
    toPartialOrder := instPartialOrderOpenNormalSubgroup}

end OpenNormalSubgroup

end
