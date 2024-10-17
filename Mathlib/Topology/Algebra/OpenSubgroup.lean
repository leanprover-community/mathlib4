/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Nailin Guan, Yi Song, Xuchun Li
-/
import Mathlib.RingTheory.Ideal.Basic
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
  coe := fun H ↦ H.toOpenSubgroup.toSubgroup

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

/-!
## The Open Subgroup in a Clopen Neighborhood of One
This section define `OpenSubgroupSubClopenNhdsOfOne` (`OpenNormalSubgroupSubClopenNhdsOfOne`),
which can pick an open subgroup contained in a clopen neighborhood of `1`.
-/

namespace TopologicalGroup

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Define the largest symmetric (self inverse) subset of a set. -/
@[to_additive]
def symmCore (V : Set G) : Set G := V ∩ V⁻¹

@[to_additive]
lemma symmCore_spec (V : Set G) : (symmCore V) = (symmCore V)⁻¹ := by
  ext
  simp only [symmCore, Set.mem_inter_iff, Set.mem_inv, Set.inter_inv, inv_inv, and_comm]

@[to_additive]
lemma iInter_symmCore_symm {α : Type*}
    (S : Set α) (V : α → Set G) : ⋂ a ∈ S, symmCore (V a) = (⋂ a ∈ S, symmCore (V a))⁻¹ := by
  ext x
  constructor <;>
  · intro h
    simp only [Set.iInter_coe_set, Set.mem_iInter, Set.iInter_inv, Set.mem_inv] at h ⊢
    intro s hs
    rw [symmCore_spec]
    simp only [Set.mem_inv, inv_inv, h s hs]

/-- Define the set of tuples `(x,y)` in a set `W` which `x * y` is in `W` too. -/
private def mulClosurePairs (W : Set G) : Set (G × G) :=
  (fun (x, y) ↦ x * y)⁻¹' W ∩ (W ×ˢ W)

private lemma mulClosurePairs_open [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) : IsOpen (mulClosurePairs W) := by
  let μ : G × G → G := fun (x, y) ↦ x * y
  have μCont : Continuous μ := continuous_mul
  simp only [mulClosurePairs]
  apply IsOpen.inter (μCont.isOpen_preimage W <| WOpen) _
  apply IsOpen.prod <;> (exact WOpen)

private lemma mem_mulClosurePairs
    {W : Set G} (einW : 1 ∈ W) (w : W) : ((w : G), 1) ∈ mulClosurePairs W := by
  simp only [mulClosurePairs, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, mul_one,
    Subtype.coe_prop, Subtype.coe_prop, einW, and_self]

/-- Define the first side of rectangle neighborhood of `(w,1)` in `mulClosurePairs`. -/
private def nhdProdSide [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) : Set G :=
  Classical.choose <| isOpen_prod_iff.mp
    (mulClosurePairs_open WOpen) w 1 (mem_mulClosurePairs einW w)

/-- Define the second side of rectangle neighborhood of `(w,1)` in `mulClosurePairs`. -/
private def nhdProdSideOne [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) : Set G :=
  Classical.choose <| Classical.choose_spec <| isOpen_prod_iff.mp
    (mulClosurePairs_open WOpen) w 1 (mem_mulClosurePairs einW w)

private lemma nhdProdSide_open [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) :
    IsOpen (nhdProdSide WOpen einW w) :=
  (Classical.choose_spec <| Classical.choose_spec <| isOpen_prod_iff.mp
    (mulClosurePairs_open WOpen) w 1 (mem_mulClosurePairs einW w)).1

private lemma nhdProdSideOne_open [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) :
    IsOpen (nhdProdSideOne WOpen einW w) :=
  (Classical.choose_spec <| Classical.choose_spec <| isOpen_prod_iff.mp
    (mulClosurePairs_open WOpen) w 1 (mem_mulClosurePairs einW w)).2.1

private lemma mem_nhdProdSide [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) :
    w.1 ∈ (nhdProdSide WOpen einW w) :=
    (Classical.choose_spec <| Classical.choose_spec <| isOpen_prod_iff.mp
      (mulClosurePairs_open WOpen) w 1 (mem_mulClosurePairs einW w)).2.2.1

private lemma one_mem_nhdProdSideOne [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) :
    1 ∈ (nhdProdSideOne WOpen einW w) :=
    (Classical.choose_spec <| Classical.choose_spec <| isOpen_prod_iff.mp
      (mulClosurePairs_open WOpen) w 1 (mem_mulClosurePairs einW w)).2.2.2.1

private lemma nhds_side_mul_sub [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) :
    (nhdProdSide WOpen einW w) ×ˢ (nhdProdSideOne WOpen einW w) ⊆ mulClosurePairs W :=
  (Classical.choose_spec <| Classical.choose_spec <| isOpen_prod_iff.mp
    (mulClosurePairs_open WOpen) w 1 (mem_mulClosurePairs einW w)).2.2.2.2

/-- The symm core of `nhdProdSideOne`. -/
private def nhdProdSideOneCore [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) : Set G :=
  symmCore (nhdProdSideOne WOpen einW w)

private lemma nhdProdSideOneCore_open [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) :
    IsOpen (nhdProdSideOneCore WOpen einW w) := by
  simp only [nhdProdSideOneCore, symmCore]
  apply IsOpen.inter (nhdProdSideOne_open WOpen einW w)
    (IsOpen.inv (nhdProdSideOne_open WOpen einW w))

private lemma one_mem_nhdProdSideOneCore [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) :
    1 ∈ (nhdProdSideOneCore WOpen einW w) := by
  simp only [nhdProdSideOneCore, symmCore, Set.mem_inter_iff, Set.mem_inv, inv_one, and_self]
  exact (one_mem_nhdProdSideOne WOpen einW w)

private lemma nhds_side_sub [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) :
    (nhdProdSide WOpen einW w) ⊆ W ∧ (nhdProdSideOne WOpen einW w) ⊆ W:= by
  have mulClosurePairssubWp : mulClosurePairs W ⊆ (W ×ˢ W) := Set.inter_subset_right
  have := Set.Subset.trans (nhds_side_mul_sub WOpen einW w) mulClosurePairssubWp
  rw [Set.prod_subset_prod_iff] at this
  rcases this with h | e1 | e2
  · exact h
  · absurd e1
    exact ne_of_mem_of_not_mem' (mem_nhdProdSide WOpen einW w) fun a ↦ a
  · absurd e2
    exact ne_of_mem_of_not_mem' (one_mem_nhdProdSideOne WOpen einW w) fun a ↦ a

private lemma nhdProdSide_sub [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) :
    (nhdProdSide WOpen einW w) ⊆ W := (nhds_side_sub WOpen einW w).1

private lemma nhdProdSideOneCore_sub [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) (w : W) :
    (nhdProdSideOneCore WOpen einW w) ⊆ W := by
  simp only [nhdProdSideOneCore, symmCore]
  exact Set.Subset.trans Set.inter_subset_left (nhds_side_sub WOpen einW w).2

private lemma nhdProdSide_cover [TopologicalSpace G]  [TopologicalGroup G]
    {W : Set G} (WOpen : IsOpen W) (einW : 1 ∈ W) :
    W ⊆ ⋃ w : W, (nhdProdSide WOpen einW w) := by
  intro x xinW
  simp only [Set.iUnion_coe_set, Set.mem_iUnion]
  exact ⟨x, xinW, (mem_nhdProdSide WOpen einW ⟨x, xinW⟩)⟩

/-- The index of the finite subcover of the rectangle neighbors covering `(W,1)`. -/
noncomputable def openSymmSubClopenNhdsOfOneIndex [TopologicalSpace G]  [TopologicalGroup G]
    [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) : Finset W :=
  Classical.choose (IsCompact.elim_finite_subcover (IsClosed.isCompact (IsClopen.isClosed WClopen))
    _ (fun (w : W) ↦
    (nhdProdSide_open WClopen.isOpen einW w)) (nhdProdSide_cover WClopen.isOpen einW))

lemma openSymmSubClopenNhdsOfOneIndex_spec [TopologicalSpace G]  [TopologicalGroup G]
    [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    W ⊆ ⋃ i ∈ (openSymmSubClopenNhdsOfOneIndex WClopen einW), nhdProdSide WClopen.isOpen einW i :=
  Classical.choose_spec (IsCompact.elim_finite_subcover (IsClosed.isCompact
  (IsClopen.isClosed WClopen)) _ (fun (w : W) ↦ (nhdProdSide_open WClopen.isOpen einW w))
  (nhdProdSide_cover WClopen.isOpen einW))

/-- Define an open symmetric neighborhood of `1` such that it is contained in a given
  clopen neighborhood of `1` and the given neighborhood is closed under multiplying by
  an element in it. -/
def openSymmSubClopenNhdsOfOne [TopologicalSpace G]  [TopologicalGroup G]
    [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) : Set G :=
  ⋂ w ∈ (openSymmSubClopenNhdsOfOneIndex WClopen einW) , nhdProdSideOneCore WClopen.isOpen einW w

namespace openSymmSubClopenNhdsOfOne

variable [TopologicalSpace G]  [TopologicalGroup G]

lemma isopen [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    IsOpen (openSymmSubClopenNhdsOfOne WClopen einW) :=
  isOpen_biInter_finset (fun w _ ↦ nhdProdSideOneCore_open WClopen.isOpen einW w)

lemma symm [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    (openSymmSubClopenNhdsOfOne WClopen einW) = (openSymmSubClopenNhdsOfOne WClopen einW)⁻¹ := by
  simp only [openSymmSubClopenNhdsOfOne, nhdProdSideOneCore]
  apply iInter_symmCore_symm

lemma one_mem [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    1 ∈ (openSymmSubClopenNhdsOfOne WClopen einW) := by
  simp only [openSymmSubClopenNhdsOfOne, Set.mem_iInter]
  exact fun w _ ↦ one_mem_nhdProdSideOneCore WClopen.isOpen einW w

lemma mul_sub [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    W * (openSymmSubClopenNhdsOfOne WClopen einW) ⊆ W := by
  rintro a ⟨x,xinW,y,yinInter,xmuly⟩
  have := openSymmSubClopenNhdsOfOneIndex_spec WClopen einW xinW
  simp only [Set.mem_iUnion] at this
  rcases this with ⟨w,winfin,xinU⟩
  simp only [openSymmSubClopenNhdsOfOne, Set.iUnion_coe_set, Set.iInter_coe_set,
    Set.mem_iInter ] at yinInter
  have yinV := Set.mem_of_mem_inter_left (yinInter w w.2 winfin)
  simpa only [Set.mem_preimage, xmuly] using Set.mem_of_mem_inter_left <|
    nhds_side_mul_sub WClopen.isOpen einW w <| Set.mk_mem_prod xinU yinV

lemma sub [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    (openSymmSubClopenNhdsOfOne WClopen einW) ⊆ W :=
  Set.Subset.trans (Set.subset_mul_right (openSymmSubClopenNhdsOfOne WClopen einW) einW)
    (mul_sub WClopen einW)

end openSymmSubClopenNhdsOfOne

end TopologicalGroup

section

open scoped Pointwise

open TopologicalGroup

private lemma iUnion_pow {G : Type*} [Group G] {V : Set G} (einV : 1 ∈ V) :
    {x : G | ∃ n : ℕ, x ∈ V ^ n} = ⋃ n , V ^ (n + 1) := by
  ext x
  rw [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  all_goals rintro ⟨n,hn⟩
  · by_cases h : n = 0
    · use 0
      simp only [h, pow_zero, Set.mem_one] at hn
      simpa only [zero_add, pow_one, hn] using einV
    · use n - 1
      rwa [Nat.sub_add_cancel <| Nat.one_le_iff_ne_zero.mpr h]
  · use n + 1

namespace TopologicalGroup

/-- Define an open symmetric neighborhood of `1` that is contained in a given
  clopen neighborhood of `1`. -/
def OpenSubgroupSubClopenNhdsOfOne {G : Type*} [Group G] [TopologicalSpace G]  [TopologicalGroup G]
    [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) : OpenSubgroup G where
  carrier := {x : G | ∃ n : ℕ, x ∈ (openSymmSubClopenNhdsOfOne WClopen einW) ^ n}
  mul_mem':= by
    rintro a b ⟨na, hna⟩ ⟨nb, hnb⟩
    simp only [Set.mem_setOf_eq] at *
    use na + nb
    rw [pow_add]
    exact Set.mul_mem_mul hna hnb
  one_mem':= by
    use 1
    simp only [pow_one, openSymmSubClopenNhdsOfOne.one_mem WClopen einW]
  inv_mem':= by
    simp only [Set.mem_setOf_eq, forall_exists_index] at *
    intro x m hm
    use m
    rw [TopologicalGroup.openSymmSubClopenNhdsOfOne.symm]
    simpa only [inv_pow, Set.mem_inv, inv_inv] using hm
  isOpen' := by
    set V := (openSymmSubClopenNhdsOfOne WClopen einW)
    simp only [iUnion_pow (openSymmSubClopenNhdsOfOne.one_mem WClopen einW)]
    apply isOpen_iUnion
    intro n
    rw [pow_succ]
    exact IsOpen.mul_left (openSymmSubClopenNhdsOfOne.isopen WClopen einW)

theorem openSubgroupSubClopenNhdsOfOne_spec {G : Type*} [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [CompactSpace G] {W : Set G} (WClopen : IsClopen W) (einW : 1 ∈ W) :
    ((OpenSubgroupSubClopenNhdsOfOne WClopen einW) : Set G) ⊆ W := by
  let V := (openSymmSubClopenNhdsOfOne WClopen einW)
  show {x : G | ∃ n : ℕ, x ∈ V ^ n} ⊆ W
  simp_rw [iUnion_pow (openSymmSubClopenNhdsOfOne.one_mem WClopen einW), Set.iUnion_subset_iff]
  intro n nge
  have mulVpow: W * V ^ (n + 1) ⊆ W := by
    induction' n with n ih
    · simp only [zero_add, pow_one]
      exact openSymmSubClopenNhdsOfOne.mul_sub WClopen einW
    · rw [pow_succ, ← mul_assoc]
      exact le_trans (Set.mul_subset_mul_right ih) <|
        openSymmSubClopenNhdsOfOne.mul_sub WClopen einW
  apply le_trans _ mulVpow
  intro x xin
  rw [Set.mem_mul]
  use 1, einW, x, xin
  rw [one_mul]

end TopologicalGroup

end
