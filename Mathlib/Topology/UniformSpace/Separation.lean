/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Prod
import Mathlib.Init
import Mathlib.Order.Filter.Ker
import Mathlib.Order.Filter.Lift
import Mathlib.Order.Filter.Map
import Mathlib.Order.Filter.Prod
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Closure
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.NhdsSet

/-!
# Hausdorff properties of uniform spaces. Separation quotient.

Two points of a topological space are called `Inseparable`,
if their neighborhoods filter are equal.
Equivalently, `Inseparable x y` means that any open set that contains `x` must contain `y`
and vice versa.

In a uniform space, points `x` and `y` are inseparable
if and only if `(x, y)` belongs to all entourages,
see `inseparable_iff_ker_uniformity`.

A uniform space is a regular topological space,
hence separation axioms `T0Space`, `T1Space`, `T2Space`, and `T3Space`
are equivalent for uniform spaces,
and Lean typeclass search can automatically convert from one assumption to another.
We say that a uniform space is *separated*, if it satisfies these axioms.
If you need an `Iff` statement (e.g., to rewrite),
then see `R1Space.t0Space_iff_t2Space` and `RegularSpace.t0Space_iff_t3Space`.

In this file we prove several facts
that relate `Inseparable` and `Specializes` to the uniformity filter.
Most of them are simple corollaries of `Filter.HasBasis.inseparable_iff_uniformity`
for different filter bases of `𝓤 α`.

Then we study the Kolmogorov quotient `SeparationQuotient X` of a uniform space.
For a general topological space,
this quotient is defined as the quotient by `Inseparable` equivalence relation.
It is the maximal T₀ quotient of a topological space.

In case of a uniform space, we equip this quotient with a `UniformSpace` structure
that agrees with the quotient topology.
We also prove that the quotient map induces uniformity on the original space.

Finally, we turn `SeparationQuotient` into a functor
(not in terms of `CategoryTheory.Functor` to avoid extra imports)
by defining `SeparationQuotient.lift'` and `SeparationQuotient.map` operations.

## Main definitions

* `SeparationQuotient.instUniformSpace`: uniform space structure on `SeparationQuotient α`,
  where `α` is a uniform space;

* `SeparationQuotient.lift'`: given a map `f : α → β`
  from a uniform space to a separated uniform space,
  lift it to a map `SeparationQuotient α → β`;
  if the original map is not uniformly continuous, then returns a constant map.

* `SeparationQuotient.map`: given a map `f : α → β` between uniform spaces,
  returns a map `SeparationQuotient α → SeparationQuotient β`.
  If the original map is not uniformly continuous, then returns a constant map.
  Otherwise, `SeparationQuotient.map f (SeparationQuotient.mk x) = SeparationQuotient.mk (f x)`.

## Main results

* `SeparationQuotient.uniformity_eq`: the uniformity filter on `SeparationQuotient α`
  is the push forward of the uniformity filter on `α`.
* `SeparationQuotient.comap_mk_uniformity`: the quotient map `α → SeparationQuotient α`
  induces uniform space structure on the original space.
* `SeparationQuotient.uniformContinuous_lift'`: factoring a uniformly continuous map through the
  separation quotient gives a uniformly continuous map.
* `SeparationQuotient.uniformContinuous_map`: maps induced between separation quotients are
  uniformly continuous.

## Implementation notes

This file used to contain definitions of `separationRel α` and `UniformSpace.SeparationQuotient α`.
These definitions were equal (but not definitionally equal)
to `{x : α × α | Inseparable x.1 x.2}` and `SeparationQuotient α`, respectively,
and were added to the library before their generalizations to topological spaces.

In https://github.com/leanprover-community/mathlib4/pull/10644, we migrated from these definitions
to more general `Inseparable` and `SeparationQuotient`.

## TODO

Definitions `SeparationQuotient.lift'` and `SeparationQuotient.map`
rely on `UniformSpace` structures in the domain and in the codomain.
We should generalize them to topological spaces.
This generalization will drop `UniformContinuous` assumptions in some lemmas,
and add these assumptions in other lemmas,
so it was not done in https://github.com/leanprover-community/mathlib4/pull/10644 to keep it reasonably sized.

## Keywords

uniform space, separated space, Hausdorff space, separation quotient
-/

@[expose] public section

open Filter Set Function Topology Uniformity UniformSpace

noncomputable section

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
variable [UniformSpace α] [UniformSpace β] [UniformSpace γ]

/-!
### Separated uniform spaces
-/

instance (priority := 100) UniformSpace.to_regularSpace : RegularSpace α :=
  .of_hasBasis
    (fun _ ↦ nhds_basis_uniformity' uniformity_hasBasis_closed)
    fun a _V hV ↦ isClosed_ball a hV.2

/--
If the uniformity has a linearly ordered basis, then the space is completely normal.
-/
theorem UniformSpace.completelyNormalSpace_of_hasAntitoneBasis {ι : Type*} [LinearOrder ι]
    {B : ι → SetRel α α} (hB : (uniformity α).HasAntitoneBasis B) : CompletelyNormalSpace α where
  completely_normal s t hSt hsT := by
    let S (b : Bool) : Set α := b.casesOn (false := s) (true := t)
    have hx (b : Bool) (x : S b) : ∃ i, Disjoint (ball x.1 ((B i).comp (B i).inv)) (S (!b)) := by
      have hST : Disjoint (S b) (closure (S !b)) := b.casesOn (false := hsT) (true := hSt.symm)
      rw [← disjoint_nhdsSet_principal, disjoint_principal_right] at hST
      obtain ⟨U, hUu, hU⟩ := UniformSpace.mem_nhds_iff.1 (nhds_le_nhdsSet x.2 hST)
      obtain ⟨(V : SetRel α α), hV, hVs, hVU⟩ := comp_symm_mem_uniformity_sets hUu
      obtain ⟨i, hi⟩ := hB.mem_iff.1 hV
      refine ⟨i, subset_compl_iff_disjoint_right.1 (subset_trans (ball_mono ?_ x.1) hU)⟩
      exact subset_trans (SetRel.comp_subset_comp hi (V.inv_eq_self ▸ (SetRel.inv_mono hi))) hVU
    choose U hU using hx
    have hUS (b : Bool) : ⋃ x, ball x.1 (B (U b x)) ∈ nhdsSet (S b) := by
      rw [mem_nhdsSet_iff_forall]
      intro x hx
      apply mem_of_superset (ball_mem_nhds x (hB.mem (U b ⟨x, hx⟩)))
      exact subset_iUnion (fun x => ball x.1 (B (U b x))) ⟨x, hx⟩
    rw [Filter.disjoint_iff]
    refine ⟨_, hUS false, _, hUS true, ?_⟩
    have hdj (b : Bool) (x : S b) (y : S (!b)) (hxy : U b x ≤ U (!b) y) :
        Disjoint (ball x.1 (B (U b x))) (ball y.1 (B (U (!b) y))) := by
      rw [Set.disjoint_iff]
      intro z hz
      exact (hU b x).notMem_of_mem_left (mem_ball_comp hz.1 (hB.antitone hxy hz.2)) y.2
    simp_rw [disjoint_iUnion_left, disjoint_iUnion_right]
    intro x y
    exact (le_total (U false x) (U true y)).elim
      (fun h => hdj false x y h) (fun h => (hdj true y x h).symm)

instance (priority := 100) UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity
    [(uniformity α).IsCountablyGenerated] : CompletelyNormalSpace α :=
  (has_seq_basis α).elim fun _ hB =>
    UniformSpace.completelyNormalSpace_of_hasAntitoneBasis hB.1

theorem Filter.HasBasis.specializes_iff_uniformity {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)}
    (h : (𝓤 α).HasBasis p s) {x y : α} : x ⤳ y ↔ ∀ i, p i → (x, y) ∈ s i :=
  (nhds_basis_uniformity h).specializes_iff

theorem Filter.HasBasis.inseparable_iff_uniformity {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)}
    (h : (𝓤 α).HasBasis p s) {x y : α} : Inseparable x y ↔ ∀ i, p i → (x, y) ∈ s i :=
  specializes_iff_inseparable.symm.trans h.specializes_iff_uniformity

theorem inseparable_iff_ker_uniformity {x y : α} : Inseparable x y ↔ (x, y) ∈ (𝓤 α).ker :=
  (𝓤 α).basis_sets.inseparable_iff_uniformity

protected theorem Inseparable.nhds_le_uniformity {x y : α} (h : Inseparable x y) :
    𝓝 (x, y) ≤ 𝓤 α := by
  rw [h.prod rfl]
  apply nhds_le_uniformity

theorem inseparable_iff_clusterPt_uniformity {x y : α} :
    Inseparable x y ↔ ClusterPt (x, y) (𝓤 α) := by
  refine ⟨fun h ↦ .of_nhds_le h.nhds_le_uniformity, fun h ↦ ?_⟩
  simp_rw [uniformity_hasBasis_closed.inseparable_iff_uniformity, isClosed_iff_clusterPt]
  exact fun U ⟨hU, hUc⟩ ↦ hUc _ <| h.mono <| le_principal_iff.2 hU

theorem t0Space_iff_uniformity :
    T0Space α ↔ ∀ x y, (∀ r ∈ 𝓤 α, (x, y) ∈ r) → x = y := by
  simp only [t0Space_iff_inseparable, inseparable_iff_ker_uniformity, mem_ker]

theorem t0Space_iff_uniformity' :
    T0Space α ↔ Pairwise fun x y ↦ ∃ r ∈ 𝓤 α, (x, y) ∉ r := by
  simp [t0Space_iff_not_inseparable, inseparable_iff_ker_uniformity]

theorem t0Space_iff_ker_uniformity : T0Space α ↔ (𝓤 α).ker = diagonal α := by
  simp_rw [t0Space_iff_uniformity, subset_antisymm_iff, diagonal_subset_iff, subset_def,
    Prod.forall, Filter.mem_ker, mem_diagonal_iff, iff_self_and]
  exact fun _ x s hs ↦ refl_mem_uniformity hs

theorem eq_of_uniformity {α : Type*} [UniformSpace α] [T0Space α] {x y : α}
    (h : ∀ {V}, V ∈ 𝓤 α → (x, y) ∈ V) : x = y :=
  t0Space_iff_uniformity.mp ‹T0Space α› x y @h

theorem eq_of_uniformity_basis {α : Type*} [UniformSpace α] [T0Space α] {ι : Sort*}
    {p : ι → Prop} {s : ι → Set (α × α)} (hs : (𝓤 α).HasBasis p s) {x y : α}
    (h : ∀ {i}, p i → (x, y) ∈ s i) : x = y :=
  (hs.inseparable_iff_uniformity.2 @h).eq

theorem eq_of_forall_symmetric {α : Type*} [UniformSpace α] [T0Space α] {x y : α}
    (h : ∀ {V}, V ∈ 𝓤 α → SetRel.IsSymm V → (x, y) ∈ V) : x = y :=
  eq_of_uniformity_basis hasBasis_symmetric (by simpa)

theorem eq_of_clusterPt_uniformity [T0Space α] {x y : α} (h : ClusterPt (x, y) (𝓤 α)) : x = y :=
  (inseparable_iff_clusterPt_uniformity.2 h).eq

theorem Filter.Tendsto.inseparable_iff_uniformity {β} {l : Filter β} [NeBot l] {f g : β → α}
    {a b : α} (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b)) :
    Inseparable a b ↔ Tendsto (fun x ↦ (f x, g x)) l (𝓤 α) := by
  refine ⟨fun h ↦ (ha.prodMk_nhds hb).mono_right h.nhds_le_uniformity, fun h ↦ ?_⟩
  rw [inseparable_iff_clusterPt_uniformity]
  exact (ClusterPt.of_le_nhds (ha.prodMk_nhds hb)).mono h

theorem isClosed_of_spaced_out [T0Space α] {V₀ : Set (α × α)} (V₀_in : V₀ ∈ 𝓤 α) {s : Set α}
    (hs : s.Pairwise fun x y => (x, y) ∉ V₀) : IsClosed s := by
  rcases comp_symm_mem_uniformity_sets V₀_in with ⟨V₁, V₁_in, V₁_symm, h_comp⟩
  apply isClosed_of_closure_subset
  intro x hx
  rw [mem_closure_iff_ball] at hx
  rcases hx V₁_in with ⟨y, hy, hy'⟩
  suffices x = y by rwa [this]
  apply eq_of_forall_symmetric
  intro V V_in _
  rcases hx (inter_mem V₁_in V_in) with ⟨z, hz, hz'⟩
  obtain rfl : z = y := by
    by_contra hzy
    exact hs hz' hy' hzy (h_comp <| mem_comp_of_mem_ball (ball_inter_left x _ _ hz) hy)
  exact ball_inter_right x _ _ hz

theorem isClosed_range_of_spaced_out {ι} [T0Space α] {V₀ : Set (α × α)} (V₀_in : V₀ ∈ 𝓤 α)
    {f : ι → α} (hf : Pairwise fun x y => (f x, f y) ∉ V₀) : IsClosed (range f) :=
  isClosed_of_spaced_out V₀_in <| by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    exact hf (ne_of_apply_ne f h)

/-!
### Separation quotient
-/

namespace SeparationQuotient

theorem comap_map_mk_uniformity : comap (Prod.map mk mk) (map (Prod.map mk mk) (𝓤 α)) = 𝓤 α := by
  refine le_antisymm ?_ le_comap_map
  refine ((((𝓤 α).basis_sets.map _).comap _).le_basis_iff uniformity_hasBasis_open).2 fun U hU ↦ ?_
  refine ⟨U, hU.1, fun (x₁, x₂) ⟨(y₁, y₂), hyU, hxy⟩ ↦ ?_⟩
  simp only [Prod.map, Prod.ext_iff, mk_eq_mk] at hxy
  exact ((hxy.1.prod hxy.2).mem_open_iff hU.2).1 hyU

instance instUniformSpace : UniformSpace (SeparationQuotient α) where
  uniformity := map (Prod.map mk mk) (𝓤 α)
  symm := tendsto_map' <| tendsto_map.comp tendsto_swap_uniformity
  comp := fun t ht ↦ by
    rcases comp_open_symm_mem_uniformity_sets ht with ⟨U, hU, hUo, -, hUt⟩
    refine mem_of_superset (mem_lift' <| image_mem_map hU) ?_
    simp only [subset_def, Prod.forall, SetRel.mem_comp, mem_image, Prod.ext_iff]
    rintro _ _ ⟨_, ⟨⟨x, y⟩, hxyU, rfl, rfl⟩, ⟨⟨y', z⟩, hyzU, hy, rfl⟩⟩
    have : y' ⤳ y := (mk_eq_mk.1 hy).specializes
    exact @hUt (x, z) ⟨y', this.mem_open (UniformSpace.isOpen_ball _ hUo) hxyU, hyzU⟩
  nhds_eq_comap_uniformity := surjective_mk.forall.2 fun x ↦ comap_injective surjective_mk <| by
    conv_lhs => rw [comap_mk_nhds_mk, nhds_eq_comap_uniformity, ← comap_map_mk_uniformity]
    simp only [Filter.comap_comap, Function.comp_def, Prod.map_apply]

theorem uniformity_eq : 𝓤 (SeparationQuotient α) = (𝓤 α).map (Prod.map mk mk) := rfl

theorem uniformContinuous_mk : UniformContinuous (mk : α → SeparationQuotient α) :=
  le_rfl

theorem uniformContinuous_dom {f : SeparationQuotient α → β} :
    UniformContinuous f ↔ UniformContinuous (f ∘ mk) :=
  .rfl

theorem uniformContinuous_dom₂ {f : SeparationQuotient α × SeparationQuotient β → γ} :
    UniformContinuous f ↔ UniformContinuous fun p : α × β ↦ f (mk p.1, mk p.2) := by
  simp only [UniformContinuous, uniformity_prod_eq_prod, uniformity_eq, prod_map_map_eq,
    tendsto_map'_iff]
  rfl

theorem uniformContinuous_lift {f : α → β} (h : ∀ a b, Inseparable a b → f a = f b) :
    UniformContinuous (lift f h) ↔ UniformContinuous f :=
  .rfl

theorem uniformContinuous_uncurry_lift₂ {f : α → β → γ}
    (h : ∀ a c b d, Inseparable a b → Inseparable c d → f a c = f b d) :
    UniformContinuous (uncurry <| lift₂ f h) ↔ UniformContinuous (uncurry f) :=
  uniformContinuous_dom₂

theorem comap_mk_uniformity : (𝓤 (SeparationQuotient α)).comap (Prod.map mk mk) = 𝓤 α :=
  comap_map_mk_uniformity

open Classical in
/-- Factoring functions to a separated space through the separation quotient.

TODO: unify with `SeparationQuotient.lift`. -/
def lift' [T0Space β] (f : α → β) : SeparationQuotient α → β :=
  if hc : UniformContinuous f then lift f fun _ _ h => (h.map hc.continuous).eq
  else fun x => f (Nonempty.some ⟨x.out⟩)

theorem lift'_mk [T0Space β] {f : α → β} (h : UniformContinuous f) (a : α) :
    lift' f (mk a) = f a := by rw [lift', dif_pos h, lift_mk]

theorem uniformContinuous_lift' [T0Space β] (f : α → β) : UniformContinuous (lift' f) := by
  by_cases hf : UniformContinuous f
  · rwa [lift', dif_pos hf, uniformContinuous_lift]
  · rw [lift', dif_neg hf]
    exact uniformContinuous_of_const fun a _ => rfl

/-- The separation quotient functor acting on functions. -/
def map (f : α → β) : SeparationQuotient α → SeparationQuotient β := lift' (mk ∘ f)

theorem map_mk {f : α → β} (h : UniformContinuous f) (a : α) : map f (mk a) = mk (f a) := by
  rw [map, lift'_mk (uniformContinuous_mk.comp h)]; rfl

theorem uniformContinuous_map (f : α → β) : UniformContinuous (map f) :=
  uniformContinuous_lift' _

set_option backward.isDefEq.respectTransparency false in
theorem map_unique {f : α → β} (hf : UniformContinuous f)
    {g : SeparationQuotient α → SeparationQuotient β} (comm : mk ∘ f = g ∘ mk) : map f = g := by
  ext ⟨a⟩
  calc
    map f ⟦a⟧ = ⟦f a⟧ := map_mk hf a
    _ = g ⟦a⟧ := congr_fun comm a

@[simp]
theorem map_id : map (@id α) = id := map_unique uniformContinuous_id rfl

theorem map_comp {f : α → β} {g : β → γ} (hf : UniformContinuous f) (hg : UniformContinuous g) :
    map g ∘ map f = map (g ∘ f) :=
  (map_unique (hg.comp hf) <| by simp only [Function.comp_def, map_mk, hf, hg]).symm

end SeparationQuotient

namespace IndiscreteTopology

variable {α : Type*} [u : UniformSpace α]

theorem of_uniformity_eq_top (h : uniformity α = ⊤) : IndiscreteTopology α :=
  ⟨(UniformSpace.ext h.symm : ⊤ = u) ▸ rfl⟩

lemma eq_top_uniformSpace [IndiscreteTopology α] : u = ⊤ := by
  refine UniformSpace.ext ?_
  rw [top_uniformity, ← Filter.ker_eq_univ]
  ext x
  rw [← inseparable_iff_ker_uniformity]
  simp

lemma eq_top_iff_indiscrete : u = ⊤ ↔ IndiscreteTopology α :=
  ⟨fun h ↦ IndiscreteTopology.mk <| h ▸ UniformSpace.toTopologicalSpace_top (α := α),
  fun _ ↦ eq_top_uniformSpace⟩

lemma uniformContinuous [IndiscreteTopology β] {f : α → β} : UniformContinuous f := by
  rw [UniformContinuous, eq_top_uniformSpace (α := β), top_uniformity]
  exact Filter.tendsto_top

end IndiscreteTopology
