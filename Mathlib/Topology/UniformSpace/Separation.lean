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
  RegularSpace.ofBasis
    (fun a => by
      rw [nhds_eq_comap_uniformity]
      exact uniformity_hasBasis_closed.comap _)
      -- 🎉 no goals
    fun a V hV => by exact hV.2.preimage <| continuous_const.prod_mk continuous_id
                     -- 🎉 no goals
#align uniform_space.to_regular_space UniformSpace.to_regularSpace

-- porting note: todo: use `Inseparable`
/-- The separation relation is the intersection of all entourages.
  Two points which are related by the separation relation are "indistinguishable"
  according to the uniform structure. -/
def separationRel (α : Type u) [UniformSpace α] := ⋂₀ (𝓤 α).sets
#align separation_rel separationRel

@[inherit_doc]
scoped[Uniformity] notation "𝓢" => separationRel

theorem separated_equiv : Equivalence fun x y => (x, y) ∈ 𝓢 α :=
  ⟨fun _ _ => refl_mem_uniformity, fun h _s hs => h _ (symm_le_uniformity hs),
    fun {x y z} (hxy : (x, y) ∈ 𝓢 α) (hyz : (y, z) ∈ 𝓢 α) s (hs : s ∈ 𝓤 α) =>
    let ⟨t, ht, (h_ts : compRel t t ⊆ s)⟩ := comp_mem_uniformity_sets hs
    h_ts <| show (x, z) ∈ compRel t t from ⟨y, hxy t ht, hyz t ht⟩⟩
#align separated_equiv separated_equiv

theorem Filter.HasBasis.mem_separationRel {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)}
    (h : (𝓤 α).HasBasis p s) {a : α × α} : a ∈ 𝓢 α ↔ ∀ i, p i → a ∈ s i :=
  h.forall_mem_mem
#align filter.has_basis.mem_separation_rel Filter.HasBasis.mem_separationRel

theorem separationRel_iff_specializes {a b : α} : (a, b) ∈ 𝓢 α ↔ a ⤳ b := by
  simp only [(𝓤 α).basis_sets.mem_separationRel, id, mem_setOf_eq,
    (nhds_basis_uniformity (𝓤 α).basis_sets).specializes_iff]
#align separation_rel_iff_specializes separationRel_iff_specializes

theorem separationRel_iff_inseparable {a b : α} : (a, b) ∈ 𝓢 α ↔ Inseparable a b :=
  separationRel_iff_specializes.trans specializes_iff_inseparable
#align separation_rel_iff_inseparable separationRel_iff_inseparable

/-- A uniform space is separated if its separation relation is trivial (each point
is related only to itself). -/
class SeparatedSpace (α : Type u) [UniformSpace α] : Prop where
  /-- The separation relation is equal to the diagonal `idRel`. -/
  out : 𝓢 α = idRel
#align separated_space SeparatedSpace

theorem separatedSpace_iff {α : Type u} [UniformSpace α] : SeparatedSpace α ↔ 𝓢 α = idRel :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align separated_space_iff separatedSpace_iff

theorem separated_def {α : Type u} [UniformSpace α] :
    SeparatedSpace α ↔ ∀ x y, (∀ r ∈ 𝓤 α, (x, y) ∈ r) → x = y := by
  simp only [separatedSpace_iff, Set.ext_iff, Prod.forall, mem_idRel, separationRel, mem_sInter]
  -- ⊢ (∀ (a b : α), (∀ (t : Set (α × α)), t ∈ (𝓤 α).sets → (a, b) ∈ t) ↔ a = b) ↔  …
  exact forall₂_congr fun _ _ => ⟨Iff.mp, fun h => ⟨h, fun H U hU => H ▸ refl_mem_uniformity hU⟩⟩
  -- 🎉 no goals
#align separated_def separated_def

theorem separated_def' {α : Type u} [UniformSpace α] :
    SeparatedSpace α ↔ ∀ x y, x ≠ y → ∃ r ∈ 𝓤 α, (x, y) ∉ r :=
  separated_def.trans <| forall₂_congr fun x y => by rw [← not_imp_not]; simp [not_forall]
                                                     -- ⊢ (¬x = y → ¬∀ (r : Set (α × α)), r ∈ 𝓤 α → (x, y) ∈ r) ↔ x ≠ y → ∃ r, r ∈ 𝓤 α …
                                                                         -- 🎉 no goals
#align separated_def' separated_def'

theorem eq_of_uniformity {α : Type*} [UniformSpace α] [SeparatedSpace α] {x y : α}
    (h : ∀ {V}, V ∈ 𝓤 α → (x, y) ∈ V) : x = y :=
  separated_def.mp ‹SeparatedSpace α› x y fun _ => h
#align eq_of_uniformity eq_of_uniformity

theorem eq_of_uniformity_basis {α : Type*} [UniformSpace α] [SeparatedSpace α] {ι : Type*}
    {p : ι → Prop} {s : ι → Set (α × α)} (hs : (𝓤 α).HasBasis p s) {x y : α}
    (h : ∀ {i}, p i → (x, y) ∈ s i) : x = y :=
  eq_of_uniformity fun V_in => let ⟨_, hi, H⟩ := hs.mem_iff.mp V_in; H (h hi)
#align eq_of_uniformity_basis eq_of_uniformity_basis

theorem eq_of_forall_symmetric {α : Type*} [UniformSpace α] [SeparatedSpace α] {x y : α}
    (h : ∀ {V}, V ∈ 𝓤 α → SymmetricRel V → (x, y) ∈ V) : x = y :=
  eq_of_uniformity_basis hasBasis_symmetric (by simpa [and_imp])
                                                -- 🎉 no goals
#align eq_of_forall_symmetric eq_of_forall_symmetric

theorem eq_of_clusterPt_uniformity [SeparatedSpace α] {x y : α} (h : ClusterPt (x, y) (𝓤 α)) :
    x = y :=
  eq_of_uniformity_basis uniformity_hasBasis_closed fun ⟨hV, hVc⟩ =>
    isClosed_iff_clusterPt.1 hVc _ <| h.mono <| le_principal_iff.2 hV
#align eq_of_cluster_pt_uniformity eq_of_clusterPt_uniformity

theorem idRel_sub_separationRel (α : Type*) [UniformSpace α] : idRel ⊆ 𝓢 α := by
  unfold separationRel
  -- ⊢ idRel ⊆ ⋂₀ (𝓤 α).sets
  rw [idRel_subset]
  -- ⊢ ∀ (a : α), (a, a) ∈ ⋂₀ (𝓤 α).sets
  intro x
  -- ⊢ (x, x) ∈ ⋂₀ (𝓤 α).sets
  suffices ∀ t ∈ 𝓤 α, (x, x) ∈ t by simpa only [refl_mem_uniformity]
  -- ⊢ ∀ (t : Set (α × α)), t ∈ 𝓤 α → (x, x) ∈ t
  exact fun t => refl_mem_uniformity
  -- 🎉 no goals
#align id_rel_sub_separation_relation idRel_sub_separationRel

theorem separationRel_comap {f : α → β}
    (h : ‹UniformSpace α› = UniformSpace.comap f ‹UniformSpace β›) :
    𝓢 α = Prod.map f f ⁻¹' 𝓢 β := by
  subst h
  -- ⊢ 𝓢 α = Prod.map f f ⁻¹' 𝓢 β
  dsimp [separationRel]
  -- ⊢ ⋂₀ (𝓤 α).sets = Prod.map f f ⁻¹' ⋂₀ (𝓤 β).sets
  simp_rw [uniformity_comap, (Filter.comap_hasBasis (Prod.map f f) (𝓤 β)).sInter_sets, ←
    preimage_iInter, sInter_eq_biInter]
  rfl
  -- 🎉 no goals
#align separation_rel_comap separationRel_comap

protected theorem Filter.HasBasis.separationRel {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)}
    (h : HasBasis (𝓤 α) p s) : 𝓢 α = ⋂ (i) (_ : p i), s i := by
  unfold separationRel
  -- ⊢ ⋂₀ (𝓤 α).sets = ⋂ (i : ι) (_ : p i), s i
  rw [h.sInter_sets]
  -- 🎉 no goals
#align filter.has_basis.separation_rel Filter.HasBasis.separationRel

theorem separationRel_eq_inter_closure : 𝓢 α = ⋂₀ (closure '' (𝓤 α).sets) := by
  simp [uniformity_hasBasis_closure.separationRel]
  -- 🎉 no goals
#align separation_rel_eq_inter_closure separationRel_eq_inter_closure

theorem isClosed_separationRel : IsClosed (𝓢 α) := by
  rw [separationRel_eq_inter_closure]
  -- ⊢ IsClosed (⋂₀ (closure '' (𝓤 α).sets))
  apply isClosed_sInter
  -- ⊢ ∀ (t : Set (α × α)), t ∈ closure '' (𝓤 α).sets → IsClosed t
  rintro _ ⟨t, -, rfl⟩
  -- ⊢ IsClosed (closure t)
  exact isClosed_closure
  -- 🎉 no goals
#align is_closed_separation_rel isClosed_separationRel

theorem separated_iff_t2 : SeparatedSpace α ↔ T2Space α := by
  constructor <;> intro h
  -- ⊢ SeparatedSpace α → T2Space α
                  -- ⊢ T2Space α
                  -- ⊢ SeparatedSpace α
  · rw [t2_iff_isClosed_diagonal, ← show 𝓢 α = diagonal α from h.1]
    -- ⊢ IsClosed (𝓢 α)
    exact isClosed_separationRel
    -- 🎉 no goals
  · rw [separated_def']
    -- ⊢ ∀ (x y : α), x ≠ y → ∃ r, r ∈ 𝓤 α ∧ ¬(x, y) ∈ r
    intro x y hxy
    -- ⊢ ∃ r, r ∈ 𝓤 α ∧ ¬(x, y) ∈ r
    rcases t2_separation hxy with ⟨u, v, uo, -, hx, hy, h⟩
    -- ⊢ ∃ r, r ∈ 𝓤 α ∧ ¬(x, y) ∈ r
    rcases isOpen_iff_ball_subset.1 uo x hx with ⟨r, hrU, hr⟩
    -- ⊢ ∃ r, r ∈ 𝓤 α ∧ ¬(x, y) ∈ r
    exact ⟨r, hrU, fun H => h.le_bot ⟨hr H, hy⟩⟩
    -- 🎉 no goals
#align separated_iff_t2 separated_iff_t2

-- see Note [lower instance priority]
instance (priority := 100) separated_t3 [SeparatedSpace α] : T3Space α :=
  haveI := separated_iff_t2.mp ‹_›
  ⟨⟩
#align separated_t3 separated_t3

instance Subtype.separatedSpace [SeparatedSpace α] (s : Set α) : SeparatedSpace s :=
  separated_iff_t2.mpr inferInstance
#align subtype.separated_space Subtype.separatedSpace

theorem isClosed_of_spaced_out [SeparatedSpace α] {V₀ : Set (α × α)} (V₀_in : V₀ ∈ 𝓤 α) {s : Set α}
    (hs : s.Pairwise fun x y => (x, y) ∉ V₀) : IsClosed s := by
  rcases comp_symm_mem_uniformity_sets V₀_in with ⟨V₁, V₁_in, V₁_symm, h_comp⟩
  -- ⊢ IsClosed s
  apply isClosed_of_closure_subset
  -- ⊢ closure s ⊆ s
  intro x hx
  -- ⊢ x ∈ s
  rw [mem_closure_iff_ball] at hx
  -- ⊢ x ∈ s
  rcases hx V₁_in with ⟨y, hy, hy'⟩
  -- ⊢ x ∈ s
  suffices x = y by rwa [this]
  -- ⊢ x = y
  apply eq_of_forall_symmetric
  -- ⊢ ∀ {V : Set (α × α)}, V ∈ 𝓤 α → SymmetricRel V → (x, y) ∈ V
  intro V V_in _
  -- ⊢ (x, y) ∈ V
  rcases hx (inter_mem V₁_in V_in) with ⟨z, hz, hz'⟩
  -- ⊢ (x, y) ∈ V
  obtain rfl : z = y := by
    by_contra hzy
    exact hs hz' hy' hzy (h_comp <| mem_comp_of_mem_ball V₁_symm (ball_inter_left x _ _ hz) hy)
  exact ball_inter_right x _ _ hz
  -- 🎉 no goals
#align is_closed_of_spaced_out isClosed_of_spaced_out

theorem isClosed_range_of_spaced_out {ι} [SeparatedSpace α] {V₀ : Set (α × α)} (V₀_in : V₀ ∈ 𝓤 α)
    {f : ι → α} (hf : Pairwise fun x y => (f x, f y) ∉ V₀) : IsClosed (range f) :=
  isClosed_of_spaced_out V₀_in <| by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    -- ⊢ ¬(f x, f y) ∈ V₀
    exact hf (ne_of_apply_ne f h)
    -- 🎉 no goals
#align is_closed_range_of_spaced_out isClosed_range_of_spaced_out

/-!
### Separation quotient
-/

namespace UniformSpace

/-- The separation relation of a uniform space seen as a setoid. -/
def separationSetoid (α : Type u) [UniformSpace α] : Setoid α :=
  ⟨fun x y => (x, y) ∈ 𝓢 α, separated_equiv⟩
#align uniform_space.separation_setoid UniformSpace.separationSetoid

attribute [local instance] separationSetoid

instance separationSetoid.uniformSpace {α : Type u} [UniformSpace α] :
    UniformSpace (Quotient (separationSetoid α)) where
  toTopologicalSpace := instTopologicalSpaceQuotient
  uniformity := map (fun p : α × α => (⟦p.1⟧, ⟦p.2⟧)) (𝓤 α)
  refl := le_trans (by simp [Quotient.exists_rep]) (Filter.map_mono refl_le_uniformity)
                       -- 🎉 no goals
  symm := tendsto_map' <| tendsto_map.comp tendsto_swap_uniformity
  comp s hs := by
    rcases comp_open_symm_mem_uniformity_sets hs with ⟨U, hU, hUo, -, hUs⟩
    -- ⊢ s ∈ Filter.lift' (map (fun p => (Quotient.mk (separationSetoid α) p.fst, Quo …
    refine' mem_of_superset (mem_lift' <| image_mem_map hU) ?_
    -- ⊢ (fun p => (Quotient.mk (separationSetoid α) p.fst, Quotient.mk (separationSe …
    simp only [subset_def, Prod.forall, mem_compRel, mem_image, Prod.ext_iff]
    -- ⊢ ∀ (a b : Quotient (separationSetoid α)), (∃ z, (∃ x, x ∈ U ∧ Quotient.mk (se …
    rintro _ _ ⟨_, ⟨⟨x, y⟩, hxyU, rfl, rfl⟩, ⟨⟨y', z⟩, hyzU, hy, rfl⟩⟩
    -- ⊢ (Quotient.mk (separationSetoid α) (x, y).fst, Quotient.mk (separationSetoid  …
    have : y' ⤳ y := separationRel_iff_specializes.1 (Quotient.exact hy)
    -- ⊢ (Quotient.mk (separationSetoid α) (x, y).fst, Quotient.mk (separationSetoid  …
    exact @hUs (x, z) ⟨y', this.mem_open (UniformSpace.isOpen_ball _ hUo) hxyU, hyzU⟩
    -- 🎉 no goals
  isOpen_uniformity s := isOpen_coinduced.trans <| by
    simp only [_root_.isOpen_uniformity, forall_quotient_iff, mem_map', mem_setOf_eq]
    -- ⊢ (∀ (x : α), x ∈ Quotient.mk' ⁻¹' s → {p | p.fst = x → p.snd ∈ Quotient.mk' ⁻ …
    refine forall₂_congr fun x _ => ⟨fun h => ?_, fun h => mem_of_superset h ?_⟩
    -- ⊢ {x_1 | Quotient.mk (separationSetoid α) x_1.fst = Quotient.mk (separationSet …
    · rcases comp_mem_uniformity_sets h with ⟨t, ht, hts⟩
      -- ⊢ {x_1 | Quotient.mk (separationSetoid α) x_1.fst = Quotient.mk (separationSet …
      refine mem_of_superset ht fun (y, z) hyz hyx => @hts (x, z) ⟨y, ?_, hyz⟩ rfl
      -- ⊢ ((x, z).fst, y) ∈ t
      exact Quotient.exact hyx.symm _ ht
      -- 🎉 no goals
    · exact fun y hy hyx => hy <| congr_arg _ hyx
      -- 🎉 no goals
#align uniform_space.separation_setoid.uniform_space UniformSpace.separationSetoid.uniformSpace

theorem uniformity_quotient :
    𝓤 (Quotient (separationSetoid α)) = (𝓤 α).map fun p : α × α => (⟦p.1⟧, ⟦p.2⟧) :=
  rfl
#align uniform_space.uniformity_quotient UniformSpace.uniformity_quotient

theorem uniformContinuous_quotient_mk' :
    UniformContinuous (Quotient.mk' : α → Quotient (separationSetoid α)) :=
  le_rfl
#align uniform_space.uniform_continuous_quotient_mk UniformSpace.uniformContinuous_quotient_mk'

theorem uniformContinuous_quotient_mk : UniformContinuous (Quotient.mk (separationSetoid α)) :=
  le_rfl

theorem uniformContinuous_quotient {f : Quotient (separationSetoid α) → β}
    (hf : UniformContinuous fun x => f ⟦x⟧) : UniformContinuous f :=
  hf
#align uniform_space.uniform_continuous_quotient UniformSpace.uniformContinuous_quotient

theorem uniformContinuous_quotient_lift {f : α → β} {h : ∀ a b, (a, b) ∈ 𝓢 α → f a = f b}
    (hf : UniformContinuous f) : UniformContinuous fun a => Quotient.lift f h a :=
  uniformContinuous_quotient hf
#align uniform_space.uniform_continuous_quotient_lift UniformSpace.uniformContinuous_quotient_lift

theorem uniformContinuous_quotient_lift₂ {f : α → β → γ}
    {h : ∀ a c b d, (a, b) ∈ 𝓢 α → (c, d) ∈ 𝓢 β → f a c = f b d}
    (hf : UniformContinuous fun p : α × β => f p.1 p.2) :
    UniformContinuous fun p : _ × _ => Quotient.lift₂ f h p.1 p.2 := by
  rw [UniformContinuous, uniformity_prod_eq_prod, uniformity_quotient, uniformity_quotient,
    Filter.prod_map_map_eq, Filter.tendsto_map'_iff, Filter.tendsto_map'_iff]
  rwa [UniformContinuous, uniformity_prod_eq_prod, Filter.tendsto_map'_iff] at hf
  -- 🎉 no goals
#align uniform_space.uniform_continuous_quotient_lift₂ UniformSpace.uniformContinuous_quotient_lift₂

theorem comap_quotient_le_uniformity :
    ((𝓤 <| Quotient <| separationSetoid α).comap fun p : α × α => (⟦p.fst⟧, ⟦p.snd⟧)) ≤ 𝓤 α :=
  ((((𝓤 α).basis_sets.map _).comap _).le_basis_iff uniformity_hasBasis_open).2 fun U hU =>
    ⟨U, hU.1, fun ⟨x, y⟩ ⟨⟨x', y'⟩, hx', h⟩ => by
      simp only [Prod.ext_iff, Quotient.eq] at h
      -- ⊢ (x, y) ∈ id U
      exact (((separationRel_iff_inseparable.1 h.1).prod
        (separationRel_iff_inseparable.1 h.2)).mem_open_iff hU.2).1 hx'⟩
#align uniform_space.comap_quotient_le_uniformity UniformSpace.comap_quotient_le_uniformity

theorem comap_quotient_eq_uniformity :
    ((𝓤 <| Quotient <| separationSetoid α).comap fun p : α × α => (⟦p.fst⟧, ⟦p.snd⟧)) = 𝓤 α :=
  le_antisymm comap_quotient_le_uniformity le_comap_map
#align uniform_space.comap_quotient_eq_uniformity UniformSpace.comap_quotient_eq_uniformity

instance separated_separation : SeparatedSpace (Quotient (separationSetoid α)) :=
  ⟨Set.ext fun ⟨a, b⟩ =>
      Quotient.inductionOn₂ a b fun a b =>
        ⟨fun h =>
          have : a ≈ b := fun s hs =>
            have :
              s ∈ (𝓤 <| Quotient <| separationSetoid α).comap fun p : α × α => (⟦p.1⟧, ⟦p.2⟧) :=
              comap_quotient_le_uniformity hs
            let ⟨t, ht, hts⟩ := this
            hts (by dsimp [preimage]; exact h t ht)
                    -- ⊢ (Quotient.mk (separationSetoid α) a, Quotient.mk (separationSetoid α) b) ∈ t
                                      -- 🎉 no goals
          show ⟦a⟧ = ⟦b⟧ from Quotient.sound this,
          fun heq : ⟦a⟧ = ⟦b⟧ => fun h hs => heq ▸ refl_mem_uniformity hs⟩⟩
#align uniform_space.separated_separation UniformSpace.separated_separation

theorem separated_of_uniformContinuous {f : α → β} {x y : α} (H : UniformContinuous f) (h : x ≈ y) :
    f x ≈ f y := fun _ h' => h _ (H h')
#align uniform_space.separated_of_uniform_continuous UniformSpace.separated_of_uniformContinuous

theorem eq_of_separated_of_uniformContinuous [SeparatedSpace β] {f : α → β} {x y : α}
    (H : UniformContinuous f) (h : x ≈ y) : f x = f y :=
  separated_def.1 (by infer_instance) _ _ <| separated_of_uniformContinuous H h
                      -- 🎉 no goals
#align uniform_space.eq_of_separated_of_uniform_continuous UniformSpace.eq_of_separated_of_uniformContinuous

/-- The maximal separated quotient of a uniform space `α`. -/
def SeparationQuotient (α : Type*) [UniformSpace α] :=
  Quotient (separationSetoid α)
#align uniform_space.separation_quotient UniformSpace.SeparationQuotient

namespace SeparationQuotient

instance : UniformSpace (SeparationQuotient α) :=
  separationSetoid.uniformSpace

instance : SeparatedSpace (SeparationQuotient α) :=
  UniformSpace.separated_separation

instance [Inhabited α] : Inhabited (SeparationQuotient α) :=
  inferInstanceAs (Inhabited (Quotient (separationSetoid α)))

lemma mk_eq_mk {x y : α} : (⟦x⟧ : SeparationQuotient α) = ⟦y⟧ ↔ Inseparable x y :=
  Quotient.eq'.trans separationRel_iff_inseparable
#align uniform_space.separation_quotient.mk_eq_mk UniformSpace.SeparationQuotient.mk_eq_mk

/-- Factoring functions to a separated space through the separation quotient. -/
def lift [SeparatedSpace β] (f : α → β) : SeparationQuotient α → β :=
  if h : UniformContinuous f then Quotient.lift f fun _ _ => eq_of_separated_of_uniformContinuous h
  else fun x => f (Nonempty.some ⟨x.out⟩)
#align uniform_space.separation_quotient.lift UniformSpace.SeparationQuotient.lift

theorem lift_mk [SeparatedSpace β] {f : α → β} (h : UniformContinuous f) (a : α) :
    lift f ⟦a⟧ = f a := by rw [lift, dif_pos h]; rfl
                           -- ⊢ Quotient.lift f (_ : ∀ (x x_1 : α), x ≈ x_1 → f x = f x_1) (Quotient.mk (sep …
                                                 -- 🎉 no goals
#align uniform_space.separation_quotient.lift_mk UniformSpace.SeparationQuotient.lift_mk

theorem uniformContinuous_lift [SeparatedSpace β] (f : α → β) : UniformContinuous (lift f) := by
  by_cases hf : UniformContinuous f
  -- ⊢ UniformContinuous (lift f)
  · rw [lift, dif_pos hf]
    -- ⊢ UniformContinuous (Quotient.lift f (_ : ∀ (x x_1 : α), x ≈ x_1 → f x = f x_1))
    exact uniformContinuous_quotient_lift hf
    -- 🎉 no goals
  · rw [lift, dif_neg hf]
    -- ⊢ UniformContinuous fun x => f (Nonempty.some (_ : Nonempty α))
    exact uniformContinuous_of_const fun a _ => rfl
    -- 🎉 no goals
#align uniform_space.separation_quotient.uniform_continuous_lift UniformSpace.SeparationQuotient.uniformContinuous_lift

/-- The separation quotient functor acting on functions. -/
def map (f : α → β) : SeparationQuotient α → SeparationQuotient β :=
  lift (Quotient.mk' ∘ f)
#align uniform_space.separation_quotient.map UniformSpace.SeparationQuotient.map

theorem map_mk {f : α → β} (h : UniformContinuous f) (a : α) : map f ⟦a⟧ = ⟦f a⟧ := by
  rw [map, lift_mk (uniformContinuous_quotient_mk'.comp h)]; rfl
  -- ⊢ (Quotient.mk' ∘ f) a = Quotient.mk (separationSetoid β) (f a)
                                                             -- 🎉 no goals
#align uniform_space.separation_quotient.map_mk UniformSpace.SeparationQuotient.map_mk

theorem uniformContinuous_map (f : α → β) : UniformContinuous (map f) :=
  uniformContinuous_lift (Quotient.mk' ∘ f)
#align uniform_space.separation_quotient.uniform_continuous_map UniformSpace.SeparationQuotient.uniformContinuous_map

theorem map_unique {f : α → β} (hf : UniformContinuous f)
    {g : SeparationQuotient α → SeparationQuotient β}
    (comm : Quotient.mk _ ∘ f = g ∘ Quotient.mk _) : map f = g := by
  ext ⟨a⟩
  -- ⊢ map f (Quot.mk Setoid.r a) = g (Quot.mk Setoid.r a)
  calc
    map f ⟦a⟧ = ⟦f a⟧ := map_mk hf a
    _ = g ⟦a⟧ := congr_fun comm a
#align uniform_space.separation_quotient.map_unique UniformSpace.SeparationQuotient.map_unique

theorem map_id : map (@id α) = id :=
  map_unique uniformContinuous_id rfl
#align uniform_space.separation_quotient.map_id UniformSpace.SeparationQuotient.map_id

theorem map_comp {f : α → β} {g : β → γ} (hf : UniformContinuous f) (hg : UniformContinuous g) :
    map g ∘ map f = map (g ∘ f) :=
  (map_unique (hg.comp hf) <| by simp only [Function.comp, map_mk, hf, hg]).symm
                                 -- 🎉 no goals
#align uniform_space.separation_quotient.map_comp UniformSpace.SeparationQuotient.map_comp

end SeparationQuotient

theorem separation_prod {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) ≈ (a₂, b₂) ↔ a₁ ≈ a₂ ∧ b₁ ≈ b₂ := by
  constructor
  -- ⊢ (a₁, b₁) ≈ (a₂, b₂) → a₁ ≈ a₂ ∧ b₁ ≈ b₂
  · intro h
    -- ⊢ a₁ ≈ a₂ ∧ b₁ ≈ b₂
    exact
      ⟨separated_of_uniformContinuous uniformContinuous_fst h,
        separated_of_uniformContinuous uniformContinuous_snd h⟩
  · rintro ⟨eqv_α, eqv_β⟩ r r_in
    -- ⊢ ((a₁, b₁), a₂, b₂) ∈ r
    rw [uniformity_prod] at r_in
    -- ⊢ ((a₁, b₁), a₂, b₂) ∈ r
    rcases r_in with ⟨t_α, ⟨r_α, r_α_in, h_α⟩, t_β, ⟨r_β, r_β_in, h_β⟩, rfl⟩
    -- ⊢ ((a₁, b₁), a₂, b₂) ∈ t_α ∩ t_β
    let p_α := fun p : (α × β) × α × β => (p.1.1, p.2.1)
    -- ⊢ ((a₁, b₁), a₂, b₂) ∈ t_α ∩ t_β
    let p_β := fun p : (α × β) × α × β => (p.1.2, p.2.2)
    -- ⊢ ((a₁, b₁), a₂, b₂) ∈ t_α ∩ t_β
    have key_α : p_α ((a₁, b₁), (a₂, b₂)) ∈ r_α := by simp [eqv_α r_α r_α_in]
    -- ⊢ ((a₁, b₁), a₂, b₂) ∈ t_α ∩ t_β
    have key_β : p_β ((a₁, b₁), (a₂, b₂)) ∈ r_β := by simp [eqv_β r_β r_β_in]
    -- ⊢ ((a₁, b₁), a₂, b₂) ∈ t_α ∩ t_β
    exact ⟨h_α key_α, h_β key_β⟩
    -- 🎉 no goals
#align uniform_space.separation_prod UniformSpace.separation_prod

instance Separated.prod [SeparatedSpace α] [SeparatedSpace β] : SeparatedSpace (α × β) :=
  separated_def.2 fun _ _ H =>
    Prod.ext (eq_of_separated_of_uniformContinuous uniformContinuous_fst H)
      (eq_of_separated_of_uniformContinuous uniformContinuous_snd H)
#align uniform_space.separated.prod UniformSpace.Separated.prod

end UniformSpace
