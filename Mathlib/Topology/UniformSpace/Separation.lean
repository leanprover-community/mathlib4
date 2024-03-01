/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot
-/
import Mathlib.Tactic.ApplyFun
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.Separation

#align_import topology.uniform_space.separation from "leanprover-community/mathlib"@"0c1f285a9f6e608ae2bdffa3f993eafb01eba829"

/-!
# Hausdorff properties of uniform spaces. Separation quotient.

This file studies uniform spaces whose underlying topological spaces are separated
(also known as Hausdorff or T₂).
This turns out to be equivalent to asking that the intersection of all entourages
is the diagonal only. This condition actually implies the stronger separation property
that the space is T₃, hence those conditions are equivalent for topologies coming from
a uniform structure.

More generally, the intersection `𝓢 X` of all entourages of `X`, which has type `Set (X × X)` is an
equivalence relation on `X`. Points which are equivalent under the relation are basically
undistinguishable from the point of view of the uniform structure. For instance any uniformly
continuous function will send equivalent points to the same value.

The quotient `SeparationQuotient X` of `X` by `𝓢 X` has a natural uniform structure which is
separated, and satisfies a universal property: every uniformly continuous function
from `X` to a separated uniform space uniquely factors through `SeparationQuotient X`.
As usual, this allows to turn `SeparationQuotient` into a functor (but we don't use the
category theory library in this file).

These notions admit relative versions, one can ask that `s : Set X` is separated, this
is equivalent to asking that the uniform structure induced on `s` is separated.

## Main definitions

* `separationRel X : Set (X × X)`: the separation relation
* `SeparatedSpace X`: a predicate class asserting that `X` is separated
* `SeparationQuotient X`: the maximal separated quotient of `X`.
* `SeparationQuotient.lift f`: factors a map `f : X → Y` through the separation quotient of `X`.
* `SeparationQuotient.map f`: turns a map `f : X → Y` into a map between the separation quotients
  of `X` and `Y`.

## Main results

* `separated_iff_t2`: the equivalence between being separated and being Hausdorff for uniform
  spaces.
* `SeparationQuotient.uniformContinuous_lift`: factoring a uniformly continuous map through the
  separation quotient gives a uniformly continuous map.
* `SeparationQuotient.uniformContinuous_map`: maps induced between separation quotients are
  uniformly continuous.

## Notations

Localized in `uniformity`, we have the notation `𝓢 X` for the separation relation
on a uniform space `X`,

## Implementation notes

The separation setoid `separationSetoid` is not declared as a global instance.
It is made a local instance while building the theory of `SeparationQuotient`.
The factored map `SeparationQuotient.lift f` is defined without imposing any condition on
`f`, but returns junk if `f` is not uniformly continuous (constant junk hence it is always
uniformly continuous).

-/

open Filter Set Function Topology Uniformity UniformSpace
open scoped Classical

noncomputable section

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
variable [UniformSpace α] [UniformSpace β] [UniformSpace γ]

/-!
### Separated uniform spaces
-/

instance (priority := 100) UniformSpace.to_regularSpace : RegularSpace α :=
  .ofBasis
    (fun _ => nhds_basis_uniformity' uniformity_hasBasis_closed)
    fun _ _ h => h.2.preimage <| continuous_const.prod_mk continuous_id
#align uniform_space.to_regular_space UniformSpace.to_regularSpace

#align separation_rel Inseparable
#noalign separated_equiv
#noalign filter.has_basis.mem_separation_rel
#noalign separation_rel_iff_specializes
#noalign separation_rel_iff_inseparable

theorem Filter.HasBasis.specializes_iff_uniformity {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)}
    (h : (𝓤 α).HasBasis p s) {x y : α} : x ⤳ y ↔ ∀ i, p i → (x, y) ∈ s i :=
  (nhds_basis_uniformity h).specializes_iff

theorem Filter.HasBasis.inseparable_iff_uniformity {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)}
    (h : (𝓤 α).HasBasis p s) {x y : α} : Inseparable x y ↔ ∀ i, p i → (x, y) ∈ s i :=
  specializes_iff_inseparable.symm.trans h.specializes_iff_uniformity

protected theorem Inseparable.nhds_le_uniformity {x y : α} (h : Inseparable x y) :
    𝓝 (x, y) ≤ 𝓤 α := by
  rw [h.prod rfl]
  apply nhds_le_uniformity

theorem inseparable_iff_clusterPt_uniformity {x y : α} :
    Inseparable x y ↔ ClusterPt (x, y) (𝓤 α) := by
  refine ⟨fun h ↦ .of_nhds_le h.nhds_le_uniformity, fun h ↦ ?_⟩
  simp_rw [uniformity_hasBasis_closed.inseparable_iff_uniformity, isClosed_iff_clusterPt]
  exact fun U ⟨hU, hUc⟩ ↦ hUc _ <| h.mono <| le_principal_iff.2 hU

#align separated_space T0Space
#noalign separated_space_iff

theorem t0Space_iff_uniformity :
    T0Space α ↔ ∀ x y, (∀ r ∈ 𝓤 α, (x, y) ∈ r) → x = y := by
  simp only [t0Space_iff_inseparable, (𝓤 α).basis_sets.inseparable_iff_uniformity, id]
#align separated_def t0Space_iff_uniformity

theorem t0Space_iff_uniformity' :
    T0Space α ↔ Pairwise fun x y ↦ ∃ r ∈ 𝓤 α, (x, y) ∉ r := by
  simp [t0Space_iff_not_inseparable, (𝓤 α).basis_sets.inseparable_iff_uniformity]
#align separated_def' t0Space_iff_uniformity'

theorem eq_of_uniformity {α : Type*} [UniformSpace α] [T0Space α] {x y : α}
    (h : ∀ {V}, V ∈ 𝓤 α → (x, y) ∈ V) : x = y :=
  t0Space_iff_uniformity.mp ‹T0Space α› x y @h
#align eq_of_uniformity eq_of_uniformity

theorem eq_of_uniformity_basis {α : Type*} [UniformSpace α] [T0Space α] {ι : Sort*}
    {p : ι → Prop} {s : ι → Set (α × α)} (hs : (𝓤 α).HasBasis p s) {x y : α}
    (h : ∀ {i}, p i → (x, y) ∈ s i) : x = y :=
  (hs.inseparable_iff_uniformity.2 @h).eq
#align eq_of_uniformity_basis eq_of_uniformity_basis

theorem eq_of_forall_symmetric {α : Type*} [UniformSpace α] [T0Space α] {x y : α}
    (h : ∀ {V}, V ∈ 𝓤 α → SymmetricRel V → (x, y) ∈ V) : x = y :=
  eq_of_uniformity_basis hasBasis_symmetric (by simpa)
#align eq_of_forall_symmetric eq_of_forall_symmetric

theorem eq_of_clusterPt_uniformity [T0Space α] {x y : α} (h : ClusterPt (x, y) (𝓤 α)) : x = y :=
  (inseparable_iff_clusterPt_uniformity.2 h).eq
#align eq_of_cluster_pt_uniformity eq_of_clusterPt_uniformity

theorem Filter.Tendsto.inseparable_iff_uniformity {l : Filter β} [NeBot l] {f g : β → α} {a b : α}
    (ha : Tendsto f l (𝓝 a)) (hb : Tendsto g l (𝓝 b)) :
    Inseparable a b ↔ Tendsto (fun x ↦ (f x, g x)) l (𝓤 α) := by
  refine ⟨fun h ↦ (ha.prod_mk_nhds hb).mono_right h.nhds_le_uniformity, fun h ↦ ?_⟩
  rw [inseparable_iff_clusterPt_uniformity]
  exact (ClusterPt.of_le_nhds (ha.prod_mk_nhds hb)).mono h

#align id_rel_sub_separation_relation Inseparable.rfl
#align separation_rel_comap Inducing.inseparable_iff
#noalign filter.has_basis.separation_rel
#noalign separation_rel_eq_inter_closure
#align is_closed_separation_rel isClosed_setOf_inseparable
#noalign separated_iff_t2
#noalign separated_t3
#align subtype.separated_space Subtype.t0Space

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
    exact hs hz' hy' hzy (h_comp <| mem_comp_of_mem_ball V₁_symm (ball_inter_left x _ _ hz) hy)
  exact ball_inter_right x _ _ hz
#align is_closed_of_spaced_out isClosed_of_spaced_out

theorem isClosed_range_of_spaced_out {ι} [T0Space α] {V₀ : Set (α × α)} (V₀_in : V₀ ∈ 𝓤 α)
    {f : ι → α} (hf : Pairwise fun x y => (f x, f y) ∉ V₀) : IsClosed (range f) :=
  isClosed_of_spaced_out V₀_in <| by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    exact hf (ne_of_apply_ne f h)
#align is_closed_range_of_spaced_out isClosed_range_of_spaced_out

/-!
### Separation quotient
-/

#align uniform_space.separation_setoid inseparableSetoid

namespace SeparationQuotient

theorem comap_map_mk_uniformity : comap (Prod.map mk mk) (map (Prod.map mk mk) (𝓤 α)) = 𝓤 α := by
  refine le_antisymm ?_ le_comap_map
  refine ((((𝓤 α).basis_sets.map _).comap _).le_basis_iff uniformity_hasBasis_open).2 fun U hU ↦ ?_
  refine ⟨U, hU.1, fun (x₁, x₂) ⟨(y₁, y₂), hyU, hxy⟩ ↦ ?_⟩
  simp only [Prod.map, Prod.ext_iff, mk_eq_mk] at hxy
  exact ((hxy.1.prod hxy.2).mem_open_iff hU.2).1 hyU

instance instUniformSpace : UniformSpace (SeparationQuotient α) :=
  .ofNhdsEqComap
    { uniformity := map (Prod.map mk mk) (𝓤 α)
      refl := le_trans (by simpa using surjective_mk) (Filter.map_mono refl_le_uniformity)
      symm := tendsto_map' <| tendsto_map.comp tendsto_swap_uniformity
      comp := fun t ht ↦ by
        rcases comp_open_symm_mem_uniformity_sets ht with ⟨U, hU, hUo, -, hUt⟩
        refine mem_of_superset (mem_lift' <| image_mem_map hU) ?_
        simp only [subset_def, Prod.forall, mem_compRel, mem_image, Prod.ext_iff]
        rintro _ _ ⟨_, ⟨⟨x, y⟩, hxyU, rfl, rfl⟩, ⟨⟨y', z⟩, hyzU, hy, rfl⟩⟩
        have : y' ⤳ y := (mk_eq_mk.1 hy).specializes
        exact @hUt (x, z) ⟨y', this.mem_open (UniformSpace.isOpen_ball _ hUo) hxyU, hyzU⟩ }
    inferInstance <| surjective_mk.forall.2 fun x ↦ comap_injective surjective_mk <| by
      conv_lhs => rw [comap_mk_nhds_mk, nhds_eq_comap_uniformity, ← comap_map_mk_uniformity]
      simp only [Filter.comap_comap]; rfl

theorem uniformity_eq : 𝓤 (SeparationQuotient α) = (𝓤 α).map (Prod.map mk mk) := rfl
#align uniform_space.uniformity_quotient SeparationQuotient.uniformity_eq

theorem uniformContinuous_mk : UniformContinuous (mk : α → SeparationQuotient α) :=
  le_rfl
#align uniform_space.uniform_continuous_quotient_mk SeparationQuotient.uniformContinuous_mk

theorem uniformContinuous_dom {f : SeparationQuotient α → β} :
    UniformContinuous f ↔ UniformContinuous (f ∘ mk) :=
  .rfl
#align uniform_space.uniform_continuous_quotient SeparationQuotient.uniformContinuous_dom

theorem uniformContinuous_dom₂ {f : SeparationQuotient α × SeparationQuotient β → γ} :
    UniformContinuous f ↔ UniformContinuous fun p : α × β ↦ f (mk p.1, mk p.2) := by
  simp only [UniformContinuous, uniformity_prod_eq_prod, uniformity_eq, prod_map_map_eq,
    tendsto_map'_iff]
  rfl

theorem uniformContinuous_lift {f : α → β} (h : ∀ a b, Inseparable a b → f a = f b) :
    UniformContinuous (lift f h) ↔ UniformContinuous f :=
  .rfl
#align uniform_space.uniform_continuous_quotient_lift SeparationQuotient.uniformContinuous_lift

theorem uniformContinuous_uncurry_lift₂ {f : α → β → γ}
    (h : ∀ a c b d, Inseparable a b → Inseparable c d → f a c = f b d) :
    UniformContinuous (uncurry <| lift₂ f h) ↔ UniformContinuous (uncurry f) :=
  uniformContinuous_dom₂
#align uniform_space.uniform_continuous_quotient_lift₂ SeparationQuotient.uniformContinuous_uncurry_lift₂

#noalign uniform_space.comap_quotient_le_uniformity

theorem comap_mk_uniformity : (𝓤 (SeparationQuotient α)).comap (Prod.map mk mk) = 𝓤 α :=
  comap_map_mk_uniformity
#align uniform_space.comap_quotient_eq_uniformity SeparationQuotient.comap_mk_uniformity

#noalign uniform_space.separated_separation

#align uniform_space.separated_of_uniform_continuous Inseparable.map
#noalign uniform_space.eq_of_separated_of_uniform_continuous

#align uniform_space.separation_quotient SeparationQuotient
#noalign uniform_space.separation_quotient.mk_eq_mk

/-- Factoring functions to a separated space through the separation quotient.

TODO: unify with `SeparationQuotient.lift`. -/
def lift' [T0Space β] (f : α → β) : SeparationQuotient α → β :=
  if hc : UniformContinuous f then lift f fun _ _ h => (h.map hc.continuous).eq
  else fun x => f (Nonempty.some ⟨x.out'⟩)
#align uniform_space.separation_quotient.lift SeparationQuotient.lift'

theorem lift'_mk [T0Space β] {f : α → β} (h : UniformContinuous f) (a : α) :
    lift' f (mk a) = f a := by rw [lift', dif_pos h]; rfl
#align uniform_space.separation_quotient.lift_mk SeparationQuotient.lift'_mk

theorem uniformContinuous_lift' [T0Space β] (f : α → β) : UniformContinuous (lift' f) := by
  by_cases hf : UniformContinuous f
  · rwa [lift', dif_pos hf, uniformContinuous_lift]
  · rw [lift', dif_neg hf]
    exact uniformContinuous_of_const fun a _ => rfl
#align uniform_space.separation_quotient.uniform_continuous_lift SeparationQuotient.uniformContinuous_lift'

/-- The separation quotient functor acting on functions. -/
def map (f : α → β) : SeparationQuotient α → SeparationQuotient β := lift' (mk ∘ f)
#align uniform_space.separation_quotient.map SeparationQuotient.map

theorem map_mk {f : α → β} (h : UniformContinuous f) (a : α) : map f (mk a) = mk (f a) := by
  rw [map, lift'_mk (uniformContinuous_mk.comp h)]; rfl
#align uniform_space.separation_quotient.map_mk SeparationQuotient.map_mk

theorem uniformContinuous_map (f : α → β) : UniformContinuous (map f) :=
  uniformContinuous_lift' _
#align uniform_space.separation_quotient.uniform_continuous_map SeparationQuotient.uniformContinuous_map

theorem map_unique {f : α → β} (hf : UniformContinuous f)
    {g : SeparationQuotient α → SeparationQuotient β} (comm : mk ∘ f = g ∘ mk) : map f = g := by
  ext ⟨a⟩
  calc
    map f ⟦a⟧ = ⟦f a⟧ := map_mk hf a
    _ = g ⟦a⟧ := congr_fun comm a
#align uniform_space.separation_quotient.map_unique SeparationQuotient.map_unique

@[simp]
theorem map_id : map (@id α) = id := map_unique uniformContinuous_id rfl
#align uniform_space.separation_quotient.map_id SeparationQuotient.map_id

theorem map_comp {f : α → β} {g : β → γ} (hf : UniformContinuous f) (hg : UniformContinuous g) :
    map g ∘ map f = map (g ∘ f) :=
  (map_unique (hg.comp hf) <| by simp only [Function.comp, map_mk, hf, hg]).symm
#align uniform_space.separation_quotient.map_comp SeparationQuotient.map_comp

end SeparationQuotient

#align uniform_space.separation_prod inseparable_prod
#align uniform_space.separated.prod Prod.instT0Space
