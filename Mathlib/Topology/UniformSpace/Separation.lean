/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot

! This file was ported from Lean 3 source module topology.uniform_space.separation
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.ApplyFun
import Mathbin.Topology.UniformSpace.Basic
import Mathbin.Topology.Separation

/-!
# Hausdorff properties of uniform spaces. Separation quotient.

This file studies uniform spaces whose underlying topological spaces are separated
(also known as Hausdorff or T₂).
This turns out to be equivalent to asking that the intersection of all entourages
is the diagonal only. This condition actually implies the stronger separation property
that the space is T₃, hence those conditions are equivalent for topologies coming from
a uniform structure.

More generally, the intersection `𝓢 X` of all entourages of `X`, which has type `set (X × X)` is an
equivalence relation on `X`. Points which are equivalent under the relation are basically
undistinguishable from the point of view of the uniform structure. For instance any uniformly
continuous function will send equivalent points to the same value.

The quotient `separation_quotient X` of `X` by `𝓢 X` has a natural uniform structure which is
separated, and satisfies a universal property: every uniformly continuous function
from `X` to a separated uniform space uniquely factors through `separation_quotient X`.
As usual, this allows to turn `separation_quotient` into a functor (but we don't use the
category theory library in this file).

These notions admit relative versions, one can ask that `s : set X` is separated, this
is equivalent to asking that the uniform structure induced on `s` is separated.

## Main definitions

* `separation_relation X : set (X × X)`: the separation relation
* `separated_space X`: a predicate class asserting that `X` is separated
* `separation_quotient X`: the maximal separated quotient of `X`.
* `separation_quotient.lift f`: factors a map `f : X → Y` through the separation quotient of `X`.
* `separation_quotient.map f`: turns a map `f : X → Y` into a map between the separation quotients
  of `X` and `Y`.

## Main results

* `separated_iff_t2`: the equivalence between being separated and being Hausdorff for uniform
  spaces.
* `separation_quotient.uniform_continuous_lift`: factoring a uniformly continuous map through the
  separation quotient gives a uniformly continuous map.
* `separation_quotient.uniform_continuous_map`: maps induced between separation quotients are
  uniformly continuous.

## Notations

Localized in `uniformity`, we have the notation `𝓢 X` for the separation relation
on a uniform space `X`,

## Implementation notes

The separation setoid `separation_setoid` is not declared as a global instance.
It is made a local instance while building the theory of `separation_quotient`.
The factored map `separation_quotient.lift f` is defined without imposing any condition on
`f`, but returns junk if `f` is not uniformly continuous (constant junk hence it is always
uniformly continuous).

-/


open Filter TopologicalSpace Set Classical Function UniformSpace

open Classical Topology uniformity Filter

noncomputable section

/- ./././Mathport/Syntax/Translate/Basic.lean:334:40: warning: unsupported option eqn_compiler.zeta -/
set_option eqn_compiler.zeta true

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
      exact uniformity_has_basis_closed.comap _)
    fun a V hV => hV.2.Preimage <| continuous_const.prod_mk continuous_id
#align uniform_space.to_regular_space UniformSpace.to_regularSpace

/-- The separation relation is the intersection of all entourages.
  Two points which are related by the separation relation are "indistinguishable"
  according to the uniform structure. -/
protected def separationRel (α : Type u) [u : UniformSpace α] :=
  ⋂₀ (𝓤 α).sets
#align separation_rel separationRel

-- mathport name: separation_rel
scoped[uniformity] notation "𝓢" => separationRel

theorem separated_equiv : Equivalence fun x y => (x, y) ∈ 𝓢 α :=
  ⟨fun x => fun s => refl_mem_uniformity, fun x y => fun h (s : Set (α × α)) hs =>
    have : preimage Prod.swap s ∈ 𝓤 α := symm_le_uniformity hs
    h _ this,
    fun x y z (hxy : (x, y) ∈ 𝓢 α) (hyz : (y, z) ∈ 𝓢 α) s (hs : s ∈ 𝓤 α) =>
    let ⟨t, ht, (h_ts : compRel t t ⊆ s)⟩ := comp_mem_uniformity_sets hs
    h_ts <| show (x, z) ∈ compRel t t from ⟨y, hxy t ht, hyz t ht⟩⟩
#align separated_equiv separated_equiv

theorem Filter.HasBasis.mem_separationRel {ι : Sort _} {p : ι → Prop} {s : ι → Set (α × α)}
    (h : (𝓤 α).HasBasis p s) {a : α × α} : a ∈ 𝓢 α ↔ ∀ i, p i → a ∈ s i :=
  h.forall_mem_mem
#align filter.has_basis.mem_separation_rel Filter.HasBasis.mem_separationRel

/-- A uniform space is separated if its separation relation is trivial (each point
is related only to itself). -/
class SeparatedSpace (α : Type u) [UniformSpace α] : Prop where
  out : 𝓢 α = idRel
#align separated_space SeparatedSpace

theorem separatedSpace_iff {α : Type u} [UniformSpace α] : SeparatedSpace α ↔ 𝓢 α = idRel :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align separated_space_iff separatedSpace_iff

theorem separated_def {α : Type u} [UniformSpace α] :
    SeparatedSpace α ↔ ∀ x y, (∀ r ∈ 𝓤 α, (x, y) ∈ r) → x = y := by
  simp [separatedSpace_iff, idRel_subset.2 separated_equiv.1, subset.antisymm_iff] <;>
    simp [subset_def, separationRel]
#align separated_def separated_def

theorem separated_def' {α : Type u} [UniformSpace α] :
    SeparatedSpace α ↔ ∀ x y, x ≠ y → ∃ r ∈ 𝓤 α, (x, y) ∉ r :=
  separated_def.trans <| forall₂_congr fun x y => by rw [← not_imp_not] <;> simp [not_forall]
#align separated_def' separated_def'

theorem eq_of_uniformity {α : Type _} [UniformSpace α] [SeparatedSpace α] {x y : α}
    (h : ∀ {V}, V ∈ 𝓤 α → (x, y) ∈ V) : x = y :=
  separated_def.mp ‹SeparatedSpace α› x y fun _ => h
#align eq_of_uniformity eq_of_uniformity

theorem eq_of_uniformity_basis {α : Type _} [UniformSpace α] [SeparatedSpace α] {ι : Type _}
    {p : ι → Prop} {s : ι → Set (α × α)} (hs : (𝓤 α).HasBasis p s) {x y : α}
    (h : ∀ {i}, p i → (x, y) ∈ s i) : x = y :=
  eq_of_uniformity fun V V_in =>
    let ⟨i, hi, H⟩ := hs.mem_iff.mp V_in
    H (h hi)
#align eq_of_uniformity_basis eq_of_uniformity_basis

theorem eq_of_forall_symmetric {α : Type _} [UniformSpace α] [SeparatedSpace α] {x y : α}
    (h : ∀ {V}, V ∈ 𝓤 α → SymmetricRel V → (x, y) ∈ V) : x = y :=
  eq_of_uniformity_basis hasBasis_symmetric (by simpa [and_imp] using fun _ => h)
#align eq_of_forall_symmetric eq_of_forall_symmetric

theorem eq_of_clusterPt_uniformity [SeparatedSpace α] {x y : α} (h : ClusterPt (x, y) (𝓤 α)) :
    x = y :=
  eq_of_uniformity_basis uniformity_hasBasis_closed fun V ⟨hV, hVc⟩ =>
    isClosed_iff_clusterPt.1 hVc _ <| h.mono <| le_principal_iff.2 hV
#align eq_of_cluster_pt_uniformity eq_of_clusterPt_uniformity

theorem idRel_sub_separation_relation (α : Type _) [UniformSpace α] : idRel ⊆ 𝓢 α :=
  by
  unfold separationRel
  rw [idRel_subset]
  intro x
  suffices ∀ t ∈ 𝓤 α, (x, x) ∈ t by simpa only [refl_mem_uniformity]
  exact fun t => refl_mem_uniformity
#align id_rel_sub_separation_relation idRel_sub_separation_relation

theorem separationRel_comap {f : α → β}
    (h : ‹UniformSpace α› = UniformSpace.comap f ‹UniformSpace β›) : 𝓢 α = Prod.map f f ⁻¹' 𝓢 β :=
  by
  subst h
  dsimp [separationRel]
  simp_rw [uniformity_comap, (Filter.comap_hasBasis (Prod.map f f) (𝓤 β)).interₛ_sets, ←
    preimage_Inter, sInter_eq_bInter]
  rfl
#align separation_rel_comap separationRel_comap

protected theorem Filter.HasBasis.separationRel {ι : Sort _} {p : ι → Prop} {s : ι → Set (α × α)}
    (h : HasBasis (𝓤 α) p s) : 𝓢 α = ⋂ (i) (hi : p i), s i :=
  by
  unfold separationRel
  rw [h.sInter_sets]
#align filter.has_basis.separation_rel Filter.HasBasis.separationRel

theorem separationRel_eq_inter_closure : 𝓢 α = ⋂₀ (closure '' (𝓤 α).sets) := by
  simp [uniformity_has_basis_closure.separation_rel]
#align separation_rel_eq_inter_closure separationRel_eq_inter_closure

theorem isClosed_separationRel : IsClosed (𝓢 α) :=
  by
  rw [separationRel_eq_inter_closure]
  apply isClosed_interₛ
  rintro _ ⟨t, t_in, rfl⟩
  exact isClosed_closure
#align is_closed_separation_rel isClosed_separationRel

theorem separated_iff_t2 : SeparatedSpace α ↔ T2Space α := by
  classical
    constructor <;> intro h
    · rw [t2_iff_isClosed_diagonal, ← show 𝓢 α = diagonal α from h.1]
      exact isClosed_separationRel
    · rw [separated_def']
      intro x y hxy
      rcases t2_separation hxy with ⟨u, v, uo, vo, hx, hy, h⟩
      rcases isOpen_iff_ball_subset.1 uo x hx with ⟨r, hrU, hr⟩
      exact ⟨r, hrU, fun H => h.le_bot ⟨hr H, hy⟩⟩
#align separated_iff_t2 separated_iff_t2

-- see Note [lower instance priority]
instance (priority := 100) separated_t3 [SeparatedSpace α] : T3Space α :=
  haveI := separated_iff_t2.mp ‹_›
  ⟨⟩
#align separated_t3 separated_t3

instance Subtype.separatedSpace [SeparatedSpace α] (s : Set α) : SeparatedSpace s :=
  separated_iff_t2.mpr Subtype.t2Space
#align subtype.separated_space Subtype.separatedSpace

theorem isClosed_of_spaced_out [SeparatedSpace α] {V₀ : Set (α × α)} (V₀_in : V₀ ∈ 𝓤 α) {s : Set α}
    (hs : s.Pairwise fun x y => (x, y) ∉ V₀) : IsClosed s :=
  by
  rcases comp_symm_mem_uniformity_sets V₀_in with ⟨V₁, V₁_in, V₁_symm, h_comp⟩
  apply isClosed_of_closure_subset
  intro x hx
  rw [mem_closure_iff_ball] at hx
  rcases hx V₁_in with ⟨y, hy, hy'⟩
  suffices x = y by rwa [this]
  apply eq_of_forall_symmetric
  intro V V_in V_symm
  rcases hx (inter_mem V₁_in V_in) with ⟨z, hz, hz'⟩
  obtain rfl : z = y := by
    by_contra hzy
    exact hs hz' hy' hzy (h_comp <| mem_comp_of_mem_ball V₁_symm (ball_inter_left x _ _ hz) hy)
  exact ball_inter_right x _ _ hz
#align is_closed_of_spaced_out isClosed_of_spaced_out

theorem isClosed_range_of_spaced_out {ι} [SeparatedSpace α] {V₀ : Set (α × α)} (V₀_in : V₀ ∈ 𝓤 α)
    {f : ι → α} (hf : Pairwise fun x y => (f x, f y) ∉ V₀) : IsClosed (range f) :=
  isClosed_of_spaced_out V₀_in <| by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    exact hf (ne_of_apply_ne f h)
#align is_closed_range_of_spaced_out isClosed_range_of_spaced_out

/-!
### Separation quotient
-/


namespace UniformSpace

/-- The separation relation of a uniform space seen as a setoid. -/
def separationSetoid (α : Type u) [UniformSpace α] : Setoid α :=
  ⟨fun x y => (x, y) ∈ 𝓢 α, separated_equiv⟩
#align uniform_space.separation_setoid UniformSpace.separationSetoid

attribute [local instance] separation_setoid

instance separationSetoid.uniformSpace {α : Type u} [u : UniformSpace α] :
    UniformSpace (Quotient (separationSetoid α))
    where
  toTopologicalSpace := u.toTopologicalSpace.coinduced fun x => ⟦x⟧
  uniformity := map (fun p : α × α => (⟦p.1⟧, ⟦p.2⟧)) u.uniformity
  refl := le_trans (by simp [Quotient.exists_rep]) (Filter.map_mono refl_le_uniformity)
  symm :=
    tendsto_map' <| by simp [Prod.swap, (· ∘ ·)] <;> exact tendsto_map.comp tendsto_swap_uniformity
  comp :=
    calc
      ((map (fun p : α × α => (⟦p.fst⟧, ⟦p.snd⟧)) u.uniformity).lift' fun s => compRel s s) =
          u.uniformity.lift' ((fun s => compRel s s) ∘ image fun p : α × α => (⟦p.fst⟧, ⟦p.snd⟧)) :=
        map_lift'_eq2 <| monotone_id.compRel monotone_id
      _ ≤
          u.uniformity.lift'
            ((image fun p : α × α => (⟦p.fst⟧, ⟦p.snd⟧)) ∘ fun s : Set (α × α) =>
              compRel s (compRel s s)) :=
        lift'_mono' fun s hs ⟨a, b⟩ ⟨c, ⟨⟨a₁, a₂⟩, ha, a_eq⟩, ⟨⟨b₁, b₂⟩, hb, b_eq⟩⟩ =>
          by
          simp at a_eq
          simp at b_eq
          have h : ⟦a₂⟧ = ⟦b₁⟧ := by rw [a_eq.right, b_eq.left]
          have h : (a₂, b₁) ∈ 𝓢 α := Quotient.exact h
          simp [Function.comp, Set.image, compRel, and_comm, and_left_comm, and_assoc]
          exact ⟨a₁, a_eq.left, b₂, b_eq.right, a₂, ha, b₁, h s hs, hb⟩
      _ =
          map (fun p : α × α => (⟦p.1⟧, ⟦p.2⟧))
            (u.uniformity.lift' fun s : Set (α × α) => compRel s (compRel s s)) :=
        by rw [map_lift'_eq] <;> exact monotone_id.comp_rel (monotone_id.comp_rel monotone_id)
      _ ≤ map (fun p : α × α => (⟦p.1⟧, ⟦p.2⟧)) u.uniformity := map_mono comp_le_uniformity3
      
  isOpen_uniformity s :=
    by
    have :
      ∀ a,
        ⟦a⟧ ∈ s →
          ({ p : α × α | p.1 = a → ⟦p.2⟧ ∈ s } ∈ 𝓤 α ↔ { p : α × α | p.1 ≈ a → ⟦p.2⟧ ∈ s } ∈ 𝓤 α) :=
      fun a ha =>
      ⟨fun h =>
        let ⟨t, ht, hts⟩ := comp_mem_uniformity_sets h
        have hts : ∀ {a₁ a₂}, (a, a₁) ∈ t → (a₁, a₂) ∈ t → ⟦a₂⟧ ∈ s := fun a₁ a₂ ha₁ ha₂ =>
          @hts (a, a₂) ⟨a₁, ha₁, ha₂⟩ rfl
        have ht' : ∀ {a₁ a₂}, a₁ ≈ a₂ → (a₁, a₂) ∈ t := fun a₁ a₂ h => interₛ_subset_of_mem ht h
        u.uniformity.sets_of_superset ht fun ⟨a₁, a₂⟩ h₁ h₂ => hts (ht' <| Setoid.symm h₂) h₁,
        fun h => u.uniformity.sets_of_superset h <| by simp (config := { contextual := true })⟩
    simp only [isOpen_coinduced, isOpen_uniformity, uniformity, forall_quotient_iff, mem_preimage,
      mem_map, preimage_set_of_eq, Quotient.eq']
    exact ⟨fun h a ha => (this a ha).mp <| h a ha, fun h a ha => (this a ha).mpr <| h a ha⟩
#align uniform_space.separation_setoid.uniform_space UniformSpace.separationSetoid.uniformSpace

theorem uniformity_quotient :
    𝓤 (Quotient (separationSetoid α)) = (𝓤 α).map fun p : α × α => (⟦p.1⟧, ⟦p.2⟧) :=
  rfl
#align uniform_space.uniformity_quotient UniformSpace.uniformity_quotient

theorem uniformContinuous_quotient_mk' :
    UniformContinuous (Quotient.mk' : α → Quotient (separationSetoid α)) :=
  le_rfl
#align uniform_space.uniform_continuous_quotient_mk UniformSpace.uniformContinuous_quotient_mk'

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
    UniformContinuous fun p : _ × _ => Quotient.lift₂ f h p.1 p.2 :=
  by
  rw [UniformContinuous, uniformity_prod_eq_prod, uniformity_quotient, uniformity_quotient,
    Filter.prod_map_map_eq, Filter.tendsto_map'_iff, Filter.tendsto_map'_iff]
  rwa [UniformContinuous, uniformity_prod_eq_prod, Filter.tendsto_map'_iff] at hf
#align uniform_space.uniform_continuous_quotient_lift₂ UniformSpace.uniformContinuous_quotient_lift₂

theorem comap_quotient_le_uniformity :
    ((𝓤 <| Quotient <| separationSetoid α).comap fun p : α × α => (⟦p.fst⟧, ⟦p.snd⟧)) ≤ 𝓤 α :=
  fun t' ht' =>
  let ⟨t, ht, tt_t'⟩ := comp_mem_uniformity_sets ht'
  let ⟨s, hs, ss_t⟩ := comp_mem_uniformity_sets ht
  ⟨(fun p : α × α => (⟦p.1⟧, ⟦p.2⟧)) '' s, (𝓤 α).sets_of_superset hs fun x hx => ⟨x, hx, rfl⟩,
    fun ⟨a₁, a₂⟩ ⟨⟨b₁, b₂⟩, hb, ab_eq⟩ =>
    have : ⟦b₁⟧ = ⟦a₁⟧ ∧ ⟦b₂⟧ = ⟦a₂⟧ := Prod.mk.inj ab_eq
    have : b₁ ≈ a₁ ∧ b₂ ≈ a₂ := And.imp Quotient.exact Quotient.exact this
    have ab₁ : (a₁, b₁) ∈ t := (Setoid.symm this.left) t ht
    have ba₂ : (b₂, a₂) ∈ s := this.right s hs
    tt_t'
      ⟨b₁, show ((a₁, a₂).1, b₁) ∈ t from ab₁, ss_t ⟨b₂, show ((b₁, a₂).1, b₂) ∈ s from hb, ba₂⟩⟩⟩
#align uniform_space.comap_quotient_le_uniformity UniformSpace.comap_quotient_le_uniformity

theorem comap_quotient_eq_uniformity :
    ((𝓤 <| Quotient <| separationSetoid α).comap fun p : α × α => (⟦p.fst⟧, ⟦p.snd⟧)) = 𝓤 α :=
  le_antisymm comap_quotient_le_uniformity le_comap_map
#align uniform_space.comap_quotient_eq_uniformity UniformSpace.comap_quotient_eq_uniformity

instance separated_separation : SeparatedSpace (Quotient (separationSetoid α)) :=
  ⟨Set.ext fun ⟨a, b⟩ =>
      Quotient.induction_on₂ a b fun a b =>
        ⟨fun h =>
          have : a ≈ b := fun s hs =>
            have :
              s ∈ (𝓤 <| Quotient <| separationSetoid α).comap fun p : α × α => (⟦p.1⟧, ⟦p.2⟧) :=
              comap_quotient_le_uniformity hs
            let ⟨t, ht, hts⟩ := this
            hts (by dsimp [preimage]; exact h t ht)
          show ⟦a⟧ = ⟦b⟧ from Quotient.sound this,
          fun heq : ⟦a⟧ = ⟦b⟧ => fun h hs => HEq ▸ refl_mem_uniformity hs⟩⟩
#align uniform_space.separated_separation UniformSpace.separated_separation

theorem separated_of_uniformContinuous {f : α → β} {x y : α} (H : UniformContinuous f) (h : x ≈ y) :
    f x ≈ f y := fun _ h' => h _ (H h')
#align uniform_space.separated_of_uniform_continuous UniformSpace.separated_of_uniformContinuous

theorem eq_of_separated_of_uniformContinuous [SeparatedSpace β] {f : α → β} {x y : α}
    (H : UniformContinuous f) (h : x ≈ y) : f x = f y :=
  separated_def.1 (by infer_instance) _ _ <| separated_of_uniformContinuous H h
#align uniform_space.eq_of_separated_of_uniform_continuous UniformSpace.eq_of_separated_of_uniformContinuous

/-- The maximal separated quotient of a uniform space `α`. -/
def SeparationQuotient (α : Type _) [UniformSpace α] :=
  Quotient (separationSetoid α)
#align uniform_space.separation_quotient UniformSpace.SeparationQuotient

namespace SeparationQuotient

instance : UniformSpace (SeparationQuotient α) :=
  separationSetoid.uniformSpace

instance : SeparatedSpace (SeparationQuotient α) :=
  UniformSpace.separated_separation

instance [Inhabited α] : Inhabited (SeparationQuotient α) :=
  Quotient.inhabited (separationSetoid α)

/-- Factoring functions to a separated space through the separation quotient. -/
def lift [SeparatedSpace β] (f : α → β) : SeparationQuotient α → β :=
  if h : UniformContinuous f then Quotient.lift f fun x y => eq_of_separated_of_uniformContinuous h
  else fun x => f (Nonempty.some ⟨x.out⟩)
#align uniform_space.separation_quotient.lift UniformSpace.SeparationQuotient.lift

theorem lift_mk' [SeparatedSpace β] {f : α → β} (h : UniformContinuous f) (a : α) :
    lift f ⟦a⟧ = f a := by rw [lift, dif_pos h] <;> rfl
#align uniform_space.separation_quotient.lift_mk UniformSpace.SeparationQuotient.lift_mk'

theorem uniformContinuous_lift [SeparatedSpace β] (f : α → β) : UniformContinuous (lift f) :=
  by
  by_cases hf : UniformContinuous f
  · rw [lift, dif_pos hf]
    exact uniform_continuous_quotient_lift hf
  · rw [lift, dif_neg hf]
    exact uniformContinuous_of_const fun a b => rfl
#align uniform_space.separation_quotient.uniform_continuous_lift UniformSpace.SeparationQuotient.uniformContinuous_lift

/-- The separation quotient functor acting on functions. -/
def map (f : α → β) : SeparationQuotient α → SeparationQuotient β :=
  lift (Quotient.mk' ∘ f)
#align uniform_space.separation_quotient.map UniformSpace.SeparationQuotient.map

theorem map_mk' {f : α → β} (h : UniformContinuous f) (a : α) : map f ⟦a⟧ = ⟦f a⟧ := by
  rw [map, lift_mk (uniform_continuous_quotient_mk.comp h)]
#align uniform_space.separation_quotient.map_mk UniformSpace.SeparationQuotient.map_mk'

theorem uniformContinuous_map (f : α → β) : UniformContinuous (map f) :=
  uniformContinuous_lift (Quotient.mk' ∘ f)
#align uniform_space.separation_quotient.uniform_continuous_map UniformSpace.SeparationQuotient.uniformContinuous_map

theorem map_unique {f : α → β} (hf : UniformContinuous f)
    {g : SeparationQuotient α → SeparationQuotient β} (comm : Quotient.mk' ∘ f = g ∘ Quotient.mk') :
    map f = g := by
  ext ⟨a⟩ <;>
    calc
      map f ⟦a⟧ = ⟦f a⟧ := map_mk hf a
      _ = g ⟦a⟧ := congr_fun comm a
      
#align uniform_space.separation_quotient.map_unique UniformSpace.SeparationQuotient.map_unique

theorem map_id : map (@id α) = id :=
  map_unique uniformContinuous_id rfl
#align uniform_space.separation_quotient.map_id UniformSpace.SeparationQuotient.map_id

theorem map_comp {f : α → β} {g : β → γ} (hf : UniformContinuous f) (hg : UniformContinuous g) :
    map g ∘ map f = map (g ∘ f) :=
  (map_unique (hg.comp hf) <| by simp only [(· ∘ ·), map_mk, hf, hg]).symm
#align uniform_space.separation_quotient.map_comp UniformSpace.SeparationQuotient.map_comp

end SeparationQuotient

theorem separation_prod {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) ≈ (a₂, b₂) ↔ a₁ ≈ a₂ ∧ b₁ ≈ b₂ :=
  by
  constructor
  · intro h
    exact
      ⟨separated_of_uniform_continuous uniformContinuous_fst h,
        separated_of_uniform_continuous uniformContinuous_snd h⟩
  · rintro ⟨eqv_α, eqv_β⟩ r r_in
    rw [uniformity_prod] at r_in
    rcases r_in with ⟨t_α, ⟨r_α, r_α_in, h_α⟩, t_β, ⟨r_β, r_β_in, h_β⟩, rfl⟩
    let p_α := fun p : (α × β) × α × β => (p.1.1, p.2.1)
    let p_β := fun p : (α × β) × α × β => (p.1.2, p.2.2)
    have key_α : p_α ((a₁, b₁), (a₂, b₂)) ∈ r_α := by simp [p_α, eqv_α r_α r_α_in]
    have key_β : p_β ((a₁, b₁), (a₂, b₂)) ∈ r_β := by simp [p_β, eqv_β r_β r_β_in]
    exact ⟨h_α key_α, h_β key_β⟩
#align uniform_space.separation_prod UniformSpace.separation_prod

instance Separated.prod [SeparatedSpace α] [SeparatedSpace β] : SeparatedSpace (α × β) :=
  separated_def.2 fun x y H =>
    Prod.ext (eq_of_separated_of_uniformContinuous uniformContinuous_fst H)
      (eq_of_separated_of_uniformContinuous uniformContinuous_snd H)
#align uniform_space.separated.prod UniformSpace.Separated.prod

end UniformSpace

