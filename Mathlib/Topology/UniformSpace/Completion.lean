/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathlib.Topology.UniformSpace.AbstractCompletion

#align_import topology.uniform_space.completion from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Hausdorff completions of uniform spaces

The goal is to construct a left-adjoint to the inclusion of complete Hausdorff uniform spaces
into all uniform spaces. Any uniform space `α` gets a completion `Completion α` and a morphism
(ie. uniformly continuous map) `(↑) : α → Completion α` which solves the universal
mapping problem of factorizing morphisms from `α` to any complete Hausdorff uniform space `β`.
It means any uniformly continuous `f : α → β` gives rise to a unique morphism
`Completion.extension f : Completion α → β` such that `f = Completion.extension f ∘ (↑)`.
Actually `Completion.extension f` is defined for all maps from `α` to `β` but it has the desired
properties only if `f` is uniformly continuous.

Beware that `(↑)` is not injective if `α` is not Hausdorff. But its image is always
dense. The adjoint functor acting on morphisms is then constructed by the usual abstract nonsense.
For every uniform spaces `α` and `β`, it turns `f : α → β` into a morphism
  `Completion.map f : Completion α → Completion β`
such that
  `(↑) ∘ f = (Completion.map f) ∘ (↑)`
provided `f` is uniformly continuous. This construction is compatible with composition.

In this file we introduce the following concepts:

* `CauchyFilter α` the uniform completion of the uniform space `α` (using Cauchy filters).
  These are not minimal filters.

* `Completion α := Quotient (separationSetoid (CauchyFilter α))` the Hausdorff completion.

## References

This formalization is mostly based on
  N. Bourbaki: General Topology
  I. M. James: Topologies and Uniformities
From a slightly different perspective in order to reuse material in topology.uniform_space.basic.
-/


noncomputable section

open Filter Set

universe u v w x

open scoped Classical
open Uniformity Topology Filter

/-- Space of Cauchy filters

This is essentially the completion of a uniform space. The embeddings are the neighbourhood filters.
This space is not minimal, the separated uniform space (i.e. quotiented on the intersection of all
entourages) is necessary for this.
-/
def CauchyFilter (α : Type u) [UniformSpace α] : Type u :=
  { f : Filter α // Cauchy f }
set_option linter.uppercaseLean3 false in
#align Cauchy CauchyFilter

namespace CauchyFilter

section

variable {α : Type u} [UniformSpace α]
variable {β : Type v} {γ : Type w}
variable [UniformSpace β] [UniformSpace γ]

instance (f : CauchyFilter α) : NeBot f.1 := f.2.1

/-- The pairs of Cauchy filters generated by a set. -/
def gen (s : Set (α × α)) : Set (CauchyFilter α × CauchyFilter α) :=
  { p | s ∈ p.1.val ×ˢ p.2.val }
set_option linter.uppercaseLean3 false in
#align Cauchy.gen CauchyFilter.gen

theorem monotone_gen : Monotone (gen : Set (α × α) → _) :=
  monotone_setOf fun p => @Filter.monotone_mem _ (p.1.val ×ˢ p.2.val)
set_option linter.uppercaseLean3 false in
#align Cauchy.monotone_gen CauchyFilter.monotone_gen

-- Porting note: this was a calc proof, but I could not make it work
private theorem symm_gen : map Prod.swap ((𝓤 α).lift' gen) ≤ (𝓤 α).lift' gen := by
  let f := fun s : Set (α × α) =>
        { p : CauchyFilter α × CauchyFilter α | s ∈ (p.2.val ×ˢ p.1.val : Filter (α × α)) }
  have h₁ : map Prod.swap ((𝓤 α).lift' gen) = (𝓤 α).lift' f := by
    delta gen
    simp [map_lift'_eq, monotone_setOf, Filter.monotone_mem, Function.comp,
      image_swap_eq_preimage_swap]
  have h₂ : (𝓤 α).lift' f ≤ (𝓤 α).lift' gen :=
    uniformity_lift_le_swap
      (monotone_principal.comp
        (monotone_setOf fun p => @Filter.monotone_mem _ (p.2.val ×ˢ p.1.val)))
      (by
        have h := fun p : CauchyFilter α × CauchyFilter α => @Filter.prod_comm _ _ p.2.val p.1.val
        simp [f, Function.comp, h, mem_map']
        exact le_rfl)
  exact h₁.trans_le h₂

private theorem compRel_gen_gen_subset_gen_compRel {s t : Set (α × α)} :
    compRel (gen s) (gen t) ⊆ (gen (compRel s t) : Set (CauchyFilter α × CauchyFilter α)) :=
  fun ⟨f, g⟩ ⟨h, h₁, h₂⟩ =>
  let ⟨t₁, (ht₁ : t₁ ∈ f.val), t₂, (ht₂ : t₂ ∈ h.val), (h₁ : t₁ ×ˢ t₂ ⊆ s)⟩ := mem_prod_iff.mp h₁
  let ⟨t₃, (ht₃ : t₃ ∈ h.val), t₄, (ht₄ : t₄ ∈ g.val), (h₂ : t₃ ×ˢ t₄ ⊆ t)⟩ := mem_prod_iff.mp h₂
  have : t₂ ∩ t₃ ∈ h.val := inter_mem ht₂ ht₃
  let ⟨x, xt₂, xt₃⟩ := h.property.left.nonempty_of_mem this
  (f.val ×ˢ g.val).sets_of_superset (prod_mem_prod ht₁ ht₄)
    fun ⟨a, b⟩ ⟨(ha : a ∈ t₁), (hb : b ∈ t₄)⟩ =>
    ⟨x, h₁ (show (a, x) ∈ t₁ ×ˢ t₂ from ⟨ha, xt₂⟩), h₂ (show (x, b) ∈ t₃ ×ˢ t₄ from ⟨xt₃, hb⟩)⟩

private theorem comp_gen : (((𝓤 α).lift' gen).lift' fun s => compRel s s) ≤ (𝓤 α).lift' gen :=
  calc
    (((𝓤 α).lift' gen).lift' fun s => compRel s s) =
        (𝓤 α).lift' fun s => compRel (gen s) (gen s) := by
      rw [lift'_lift'_assoc]
      · exact monotone_gen
      · exact monotone_id.compRel monotone_id
    _ ≤ (𝓤 α).lift' fun s => gen <| compRel s s :=
      lift'_mono' fun s _hs => compRel_gen_gen_subset_gen_compRel
    _ = ((𝓤 α).lift' fun s : Set (α × α) => compRel s s).lift' gen := by
      rw [lift'_lift'_assoc]
      · exact monotone_id.compRel monotone_id
      · exact monotone_gen
    _ ≤ (𝓤 α).lift' gen := lift'_mono comp_le_uniformity le_rfl

instance : UniformSpace (CauchyFilter α) :=
  UniformSpace.ofCore
    { uniformity := (𝓤 α).lift' gen
      refl := principal_le_lift'.2 fun _s hs ⟨a, b⟩ =>
        fun (a_eq_b : a = b) => a_eq_b ▸ a.property.right hs
      symm := symm_gen
      comp := comp_gen }

theorem mem_uniformity {s : Set (CauchyFilter α × CauchyFilter α)} :
    s ∈ 𝓤 (CauchyFilter α) ↔ ∃ t ∈ 𝓤 α, gen t ⊆ s :=
  mem_lift'_sets monotone_gen
set_option linter.uppercaseLean3 false in
#align Cauchy.mem_uniformity CauchyFilter.mem_uniformity

theorem basis_uniformity {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s) :
    (𝓤 (CauchyFilter α)).HasBasis p (gen ∘ s) :=
  h.lift' monotone_gen

theorem mem_uniformity' {s : Set (CauchyFilter α × CauchyFilter α)} :
    s ∈ 𝓤 (CauchyFilter α) ↔ ∃ t ∈ 𝓤 α, ∀ f g : CauchyFilter α, t ∈ f.1 ×ˢ g.1 → (f, g) ∈ s := by
  refine mem_uniformity.trans (exists_congr (fun t => and_congr_right_iff.mpr (fun _h => ?_)))
  exact ⟨fun h _f _g ht => h ht, fun h _p hp => h _ _ hp⟩
set_option linter.uppercaseLean3 false in
#align Cauchy.mem_uniformity' CauchyFilter.mem_uniformity'

/-- Embedding of `α` into its completion `CauchyFilter α` -/
def pureCauchy (a : α) : CauchyFilter α :=
  ⟨pure a, cauchy_pure⟩
set_option linter.uppercaseLean3 false in
#align Cauchy.pure_cauchy CauchyFilter.pureCauchy

theorem uniformInducing_pureCauchy : UniformInducing (pureCauchy : α → CauchyFilter α) :=
  ⟨have : (preimage fun x : α × α => (pureCauchy x.fst, pureCauchy x.snd)) ∘ gen = id :=
      funext fun s =>
        Set.ext fun ⟨a₁, a₂⟩ => by simp [preimage, gen, pureCauchy, prod_principal_principal]
    calc
      comap (fun x : α × α => (pureCauchy x.fst, pureCauchy x.snd)) ((𝓤 α).lift' gen) =
          (𝓤 α).lift' ((preimage fun x : α × α => (pureCauchy x.fst, pureCauchy x.snd)) ∘ gen) :=
        comap_lift'_eq
      _ = 𝓤 α := by simp [this]
      ⟩
set_option linter.uppercaseLean3 false in
#align Cauchy.uniform_inducing_pure_cauchy CauchyFilter.uniformInducing_pureCauchy

theorem uniformEmbedding_pureCauchy : UniformEmbedding (pureCauchy : α → CauchyFilter α) :=
  { uniformInducing_pureCauchy with
    inj := fun _a₁ _a₂ h => pure_injective <| Subtype.ext_iff_val.1 h }
set_option linter.uppercaseLean3 false in
#align Cauchy.uniform_embedding_pure_cauchy CauchyFilter.uniformEmbedding_pureCauchy

theorem denseRange_pureCauchy : DenseRange (pureCauchy : α → CauchyFilter α) := fun f => by
  have h_ex : ∀ s ∈ 𝓤 (CauchyFilter α), ∃ y : α, (f, pureCauchy y) ∈ s := fun s hs =>
    let ⟨t'', ht''₁, (ht''₂ : gen t'' ⊆ s)⟩ := (mem_lift'_sets monotone_gen).mp hs
    let ⟨t', ht'₁, ht'₂⟩ := comp_mem_uniformity_sets ht''₁
    have : t' ∈ f.val ×ˢ f.val := f.property.right ht'₁
    let ⟨t, ht, (h : t ×ˢ t ⊆ t')⟩ := mem_prod_same_iff.mp this
    let ⟨x, (hx : x ∈ t)⟩ := f.property.left.nonempty_of_mem ht
    have : t'' ∈ f.val ×ˢ pure x :=
      mem_prod_iff.mpr
        ⟨t, ht, { y : α | (x, y) ∈ t' }, h <| mk_mem_prod hx hx,
          fun ⟨a, b⟩ ⟨(h₁ : a ∈ t), (h₂ : (x, b) ∈ t')⟩ =>
          ht'₂ <| prod_mk_mem_compRel (@h (a, x) ⟨h₁, hx⟩) h₂⟩
    ⟨x, ht''₂ <| by dsimp [gen]; exact this⟩
  simp only [closure_eq_cluster_pts, ClusterPt, nhds_eq_uniformity, lift'_inf_principal_eq,
    Set.inter_comm _ (range pureCauchy), mem_setOf_eq]
  refine (lift'_neBot_iff ?_).mpr (fun s hs => ?_)
  · refine monotone_const.inter ?_
    simp_rw [UniformSpace.ball]
    exact monotone_preimage
  · let ⟨y, hy⟩ := h_ex s hs
    have : pureCauchy y ∈ range pureCauchy ∩ { y : CauchyFilter α | (f, y) ∈ s } :=
      ⟨mem_range_self y, hy⟩
    exact ⟨_, this⟩
set_option linter.uppercaseLean3 false in
#align Cauchy.dense_range_pure_cauchy CauchyFilter.denseRange_pureCauchy

theorem denseInducing_pureCauchy : DenseInducing (pureCauchy : α → CauchyFilter α) :=
  uniformInducing_pureCauchy.denseInducing denseRange_pureCauchy
set_option linter.uppercaseLean3 false in
#align Cauchy.dense_inducing_pure_cauchy CauchyFilter.denseInducing_pureCauchy

theorem denseEmbedding_pureCauchy : DenseEmbedding (pureCauchy : α → CauchyFilter α) :=
  uniformEmbedding_pureCauchy.denseEmbedding denseRange_pureCauchy
set_option linter.uppercaseLean3 false in
#align Cauchy.dense_embedding_pure_cauchy CauchyFilter.denseEmbedding_pureCauchy

theorem nonempty_cauchyFilter_iff : Nonempty (CauchyFilter α) ↔ Nonempty α := by
  constructor <;> rintro ⟨c⟩
  · have := eq_univ_iff_forall.1 denseEmbedding_pureCauchy.toDenseInducing.closure_range c
    obtain ⟨_, ⟨_, a, _⟩⟩ := mem_closure_iff.1 this _ isOpen_univ trivial
    exact ⟨a⟩
  · exact ⟨pureCauchy c⟩
set_option linter.uppercaseLean3 false in
#align Cauchy.nonempty_Cauchy_iff CauchyFilter.nonempty_cauchyFilter_iff

section

-- Porting note: I commented this
-- set_option eqn_compiler.zeta true

instance : CompleteSpace (CauchyFilter α) :=
  completeSpace_extension uniformInducing_pureCauchy denseRange_pureCauchy fun f hf =>
    let f' : CauchyFilter α := ⟨f, hf⟩
    have : map pureCauchy f ≤ (𝓤 <| CauchyFilter α).lift' (preimage (Prod.mk f')) :=
      le_lift'.2 fun s hs =>
        let ⟨t, ht₁, (ht₂ : gen t ⊆ s)⟩ := (mem_lift'_sets monotone_gen).mp hs
        let ⟨t', ht', (h : t' ×ˢ t' ⊆ t)⟩ := mem_prod_same_iff.mp (hf.right ht₁)
        have : t' ⊆ { y : α | (f', pureCauchy y) ∈ gen t } := fun x hx =>
          (f ×ˢ pure x).sets_of_superset (prod_mem_prod ht' hx) h
        f.sets_of_superset ht' <| Subset.trans this (preimage_mono ht₂)
    ⟨f', by simp [nhds_eq_uniformity]; assumption⟩

end

instance [Inhabited α] : Inhabited (CauchyFilter α) :=
  ⟨pureCauchy default⟩

instance [h : Nonempty α] : Nonempty (CauchyFilter α) :=
  h.recOn fun a => Nonempty.intro <| CauchyFilter.pureCauchy a

section Extend

/-- Extend a uniformly continuous function `α → β` to a function `CauchyFilter α → β`.
Outputs junk when `f` is not uniformly continuous. -/
def extend (f : α → β) : CauchyFilter α → β :=
  if UniformContinuous f then denseInducing_pureCauchy.extend f
  else fun x => f (nonempty_cauchyFilter_iff.1 ⟨x⟩).some
set_option linter.uppercaseLean3 false in
#align Cauchy.extend CauchyFilter.extend

section T0Space

variable [T0Space β]

theorem extend_pureCauchy {f : α → β} (hf : UniformContinuous f) (a : α) :
    extend f (pureCauchy a) = f a := by
  rw [extend, if_pos hf]
  exact uniformly_extend_of_ind uniformInducing_pureCauchy denseRange_pureCauchy hf _
set_option linter.uppercaseLean3 false in
#align Cauchy.extend_pure_cauchy CauchyFilter.extend_pureCauchy

end T0Space

variable [CompleteSpace β]

theorem uniformContinuous_extend {f : α → β} : UniformContinuous (extend f) := by
  by_cases hf : UniformContinuous f
  · rw [extend, if_pos hf]
    exact uniformContinuous_uniformly_extend uniformInducing_pureCauchy denseRange_pureCauchy hf
  · rw [extend, if_neg hf]
    exact uniformContinuous_of_const fun a _b => by congr
set_option linter.uppercaseLean3 false in
#align Cauchy.uniform_continuous_extend CauchyFilter.uniformContinuous_extend

end Extend

theorem inseparable_iff {f g : CauchyFilter α} : Inseparable f g ↔ f.1 ×ˢ g.1 ≤ 𝓤 α :=
  (basis_uniformity (basis_sets _)).inseparable_iff_uniformity

theorem inseparable_iff_of_le_nhds {f g : CauchyFilter α} {a b : α}
    (ha : f.1 ≤ 𝓝 a) (hb : g.1 ≤ 𝓝 b) : Inseparable a b ↔ Inseparable f g := by
  rw [← tendsto_id'] at ha hb
  rw [inseparable_iff, (ha.comp tendsto_fst).inseparable_iff_uniformity (hb.comp tendsto_snd)]
  rfl

theorem inseparable_lim_iff [CompleteSpace α] {f g : CauchyFilter α} :
    haveI := f.2.1.nonempty; Inseparable (lim f.1) (lim g.1) ↔ Inseparable f g :=
  inseparable_iff_of_le_nhds f.2.le_nhds_lim g.2.le_nhds_lim

end

theorem cauchyFilter_eq {α : Type*} [UniformSpace α] [CompleteSpace α] [T0Space α]
    {f g : CauchyFilter α} :
    haveI := f.2.1.nonempty; lim f.1 = lim g.1 ↔ Inseparable f g := by
  rw [← inseparable_iff_eq, inseparable_lim_iff]

set_option linter.uppercaseLean3 false in
#align Cauchy.Cauchy_eq CauchyFilter.cauchyFilter_eq

section

theorem separated_pureCauchy_injective {α : Type*} [UniformSpace α] [T0Space α] :
    Function.Injective fun a : α => SeparationQuotient.mk (pureCauchy a) := fun a b h ↦
  Inseparable.eq <| (inseparable_iff_of_le_nhds (pure_le_nhds a) (pure_le_nhds b)).2 <|
    SeparationQuotient.mk_eq_mk.1 h
set_option linter.uppercaseLean3 false in
#align Cauchy.separated_pure_cauchy_injective CauchyFilter.separated_pureCauchy_injective

end

end CauchyFilter

open CauchyFilter Set

namespace UniformSpace

variable (α : Type*) [UniformSpace α]
variable {β : Type*} [UniformSpace β]
variable {γ : Type*} [UniformSpace γ]

/-- Hausdorff completion of `α` -/
def Completion := SeparationQuotient (CauchyFilter α)
#align uniform_space.completion UniformSpace.Completion

namespace Completion

instance inhabited [Inhabited α] : Inhabited (Completion α) :=
  inferInstanceAs <| Inhabited (Quotient _)

instance uniformSpace : UniformSpace (Completion α) :=
  SeparationQuotient.instUniformSpace

instance completeSpace : CompleteSpace (Completion α) :=
  SeparationQuotient.instCompleteSpace

instance t0Space : T0Space (Completion α) := SeparationQuotient.instT0Space

/-- The map from a uniform space to its completion.

porting note: this was added to create a target for the `@[coe]` attribute. -/
@[coe] def coe' : α → Completion α := SeparationQuotient.mk ∘ pureCauchy

/-- Automatic coercion from `α` to its completion. Not always injective. -/
instance : Coe α (Completion α) :=
  ⟨coe' α⟩

-- note [use has_coe_t]
protected theorem coe_eq : ((↑) : α → Completion α) = SeparationQuotient.mk ∘ pureCauchy := rfl
#align uniform_space.completion.coe_eq UniformSpace.Completion.coe_eq

theorem uniformInducing_coe : UniformInducing ((↑) : α → Completion α) :=
  SeparationQuotient.uniformInducing_mk.comp uniformInducing_pureCauchy
#align uniform_space.completion.uniform_inducing_coe UniformSpace.Completion.uniformInducing_coe

theorem comap_coe_eq_uniformity :
    ((𝓤 _).comap fun p : α × α => ((p.1 : Completion α), (p.2 : Completion α))) = 𝓤 α :=
  (uniformInducing_coe _).1
#align uniform_space.completion.comap_coe_eq_uniformity UniformSpace.Completion.comap_coe_eq_uniformity

variable {α}

theorem denseRange_coe : DenseRange ((↑) : α → Completion α) :=
  SeparationQuotient.surjective_mk.denseRange.comp denseRange_pureCauchy
    SeparationQuotient.continuous_mk
#align uniform_space.completion.dense_range_coe UniformSpace.Completion.denseRange_coe

variable (α)

/-- The Haudorff completion as an abstract completion. -/
def cPkg {α : Type*} [UniformSpace α] : AbstractCompletion α where
  space := Completion α
  coe := (↑)
  uniformStruct := by infer_instance
  complete := by infer_instance
  separation := by infer_instance
  uniformInducing := Completion.uniformInducing_coe α
  dense := Completion.denseRange_coe
#align uniform_space.completion.cpkg UniformSpace.Completion.cPkg

instance AbstractCompletion.inhabited : Inhabited (AbstractCompletion α) :=
  ⟨cPkg⟩
#align uniform_space.completion.abstract_completion.inhabited UniformSpace.Completion.AbstractCompletion.inhabited

attribute [local instance]
  AbstractCompletion.uniformStruct AbstractCompletion.complete AbstractCompletion.separation

theorem nonempty_completion_iff : Nonempty (Completion α) ↔ Nonempty α :=
  cPkg.dense.nonempty_iff.symm
#align uniform_space.completion.nonempty_completion_iff UniformSpace.Completion.nonempty_completion_iff

theorem uniformContinuous_coe : UniformContinuous ((↑) : α → Completion α) :=
  cPkg.uniformContinuous_coe
#align uniform_space.completion.uniform_continuous_coe UniformSpace.Completion.uniformContinuous_coe

theorem continuous_coe : Continuous ((↑) : α → Completion α) :=
  cPkg.continuous_coe
#align uniform_space.completion.continuous_coe UniformSpace.Completion.continuous_coe

theorem uniformEmbedding_coe [T0Space α] : UniformEmbedding ((↑) : α → Completion α) :=
  { comap_uniformity := comap_coe_eq_uniformity α
    inj := separated_pureCauchy_injective }
#align uniform_space.completion.uniform_embedding_coe UniformSpace.Completion.uniformEmbedding_coe

theorem coe_injective [T0Space α] : Function.Injective ((↑) : α → Completion α) :=
  UniformEmbedding.inj (uniformEmbedding_coe _)
#align uniform_space.completion.coe_injective UniformSpace.Completion.coe_injective

variable {α}

theorem denseInducing_coe : DenseInducing ((↑) : α → Completion α) :=
  { (uniformInducing_coe α).inducing with dense := denseRange_coe }
#align uniform_space.completion.dense_inducing_coe UniformSpace.Completion.denseInducing_coe

/-- The uniform bijection between a complete space and its uniform completion. -/
def UniformCompletion.completeEquivSelf [CompleteSpace α] [T0Space α] : Completion α ≃ᵤ α :=
  AbstractCompletion.compareEquiv Completion.cPkg AbstractCompletion.ofComplete
#align uniform_space.completion.uniform_completion.complete_equiv_self UniformSpace.Completion.UniformCompletion.completeEquivSelf

open TopologicalSpace

instance separableSpace_completion [SeparableSpace α] : SeparableSpace (Completion α) :=
  Completion.denseInducing_coe.separableSpace
#align uniform_space.completion.separable_space_completion UniformSpace.Completion.separableSpace_completion

theorem denseEmbedding_coe [T0Space α] : DenseEmbedding ((↑) : α → Completion α) :=
  { denseInducing_coe with inj := separated_pureCauchy_injective }
#align uniform_space.completion.dense_embedding_coe UniformSpace.Completion.denseEmbedding_coe

theorem denseRange_coe₂ :
    DenseRange fun x : α × β => ((x.1 : Completion α), (x.2 : Completion β)) :=
  denseRange_coe.prod_map denseRange_coe
#align uniform_space.completion.dense_range_coe₂ UniformSpace.Completion.denseRange_coe₂

theorem denseRange_coe₃ :
    DenseRange fun x : α × β × γ =>
      ((x.1 : Completion α), ((x.2.1 : Completion β), (x.2.2 : Completion γ))) :=
  denseRange_coe.prod_map denseRange_coe₂
#align uniform_space.completion.dense_range_coe₃ UniformSpace.Completion.denseRange_coe₃

@[elab_as_elim]
theorem induction_on {p : Completion α → Prop} (a : Completion α) (hp : IsClosed { a | p a })
    (ih : ∀ a : α, p a) : p a :=
  isClosed_property denseRange_coe hp ih a
#align uniform_space.completion.induction_on UniformSpace.Completion.induction_on

@[elab_as_elim]
theorem induction_on₂ {p : Completion α → Completion β → Prop} (a : Completion α) (b : Completion β)
    (hp : IsClosed { x : Completion α × Completion β | p x.1 x.2 })
    (ih : ∀ (a : α) (b : β), p a b) : p a b :=
  have : ∀ x : Completion α × Completion β, p x.1 x.2 :=
    isClosed_property denseRange_coe₂ hp fun ⟨a, b⟩ => ih a b
  this (a, b)
#align uniform_space.completion.induction_on₂ UniformSpace.Completion.induction_on₂

@[elab_as_elim]
theorem induction_on₃ {p : Completion α → Completion β → Completion γ → Prop} (a : Completion α)
    (b : Completion β) (c : Completion γ)
    (hp : IsClosed { x : Completion α × Completion β × Completion γ | p x.1 x.2.1 x.2.2 })
    (ih : ∀ (a : α) (b : β) (c : γ), p a b c) : p a b c :=
  have : ∀ x : Completion α × Completion β × Completion γ, p x.1 x.2.1 x.2.2 :=
    isClosed_property denseRange_coe₃ hp fun ⟨a, b, c⟩ => ih a b c
  this (a, b, c)
#align uniform_space.completion.induction_on₃ UniformSpace.Completion.induction_on₃

theorem ext {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f g : Completion α → Y}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ a : α, f a = g a) : f = g :=
  cPkg.funext hf hg h
#align uniform_space.completion.ext UniformSpace.Completion.ext

theorem ext' {Y : Type*} [TopologicalSpace Y] [T2Space Y] {f g : Completion α → Y}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ a : α, f a = g a) (a : Completion α) :
    f a = g a :=
  congr_fun (ext hf hg h) a
#align uniform_space.completion.ext' UniformSpace.Completion.ext'

section Extension

variable {f : α → β}

/-- "Extension" to the completion. It is defined for any map `f` but
returns an arbitrary constant value if `f` is not uniformly continuous -/
protected def extension (f : α → β) : Completion α → β :=
  cPkg.extend f
#align uniform_space.completion.extension UniformSpace.Completion.extension

section CompleteSpace

variable [CompleteSpace β]

theorem uniformContinuous_extension : UniformContinuous (Completion.extension f) :=
  cPkg.uniformContinuous_extend
#align uniform_space.completion.uniform_continuous_extension UniformSpace.Completion.uniformContinuous_extension

@[continuity]
theorem continuous_extension : Continuous (Completion.extension f) :=
  cPkg.continuous_extend
#align uniform_space.completion.continuous_extension UniformSpace.Completion.continuous_extension

end CompleteSpace

/- porting note: removed `@[simp]` because this lemma doesn't even trigger on itself in Lean 3 or
Lean 4 unless the user manually supplies the `hf` argument, so it is useless as a `simp` lemma. -/
theorem extension_coe [T0Space β] (hf : UniformContinuous f) (a : α) :
    (Completion.extension f) a = f a :=
  cPkg.extend_coe hf a
#align uniform_space.completion.extension_coe UniformSpace.Completion.extension_coe

variable [T0Space β] [CompleteSpace β]

theorem extension_unique (hf : UniformContinuous f) {g : Completion α → β}
    (hg : UniformContinuous g) (h : ∀ a : α, f a = g (a : Completion α)) :
    Completion.extension f = g :=
  cPkg.extend_unique hf hg h
#align uniform_space.completion.extension_unique UniformSpace.Completion.extension_unique

@[simp]
theorem extension_comp_coe {f : Completion α → β} (hf : UniformContinuous f) :
    Completion.extension (f ∘ (↑)) = f :=
  cPkg.extend_comp_coe hf
#align uniform_space.completion.extension_comp_coe UniformSpace.Completion.extension_comp_coe

end Extension

section Map

variable {f : α → β}

/-- Completion functor acting on morphisms -/
protected def map (f : α → β) : Completion α → Completion β :=
  cPkg.map cPkg f
#align uniform_space.completion.map UniformSpace.Completion.map

theorem uniformContinuous_map : UniformContinuous (Completion.map f) :=
  cPkg.uniformContinuous_map cPkg f
#align uniform_space.completion.uniform_continuous_map UniformSpace.Completion.uniformContinuous_map

@[continuity]
theorem continuous_map : Continuous (Completion.map f) :=
  cPkg.continuous_map cPkg f
#align uniform_space.completion.continuous_map UniformSpace.Completion.continuous_map

/- porting note: removed `@[simp]` because this lemma doesn't even trigger on itself in Lean 3 or
Lean 4 unless the user manually supplies the `hf` argument, so it is useless as a `simp` lemma. -/
theorem map_coe (hf : UniformContinuous f) (a : α) : (Completion.map f) a = f a :=
  cPkg.map_coe cPkg hf a
#align uniform_space.completion.map_coe UniformSpace.Completion.map_coe

theorem map_unique {f : α → β} {g : Completion α → Completion β} (hg : UniformContinuous g)
    (h : ∀ a : α, ↑(f a) = g a) : Completion.map f = g :=
  cPkg.map_unique cPkg hg h
#align uniform_space.completion.map_unique UniformSpace.Completion.map_unique

@[simp]
theorem map_id : Completion.map (@id α) = id :=
  cPkg.map_id
#align uniform_space.completion.map_id UniformSpace.Completion.map_id

theorem extension_map [CompleteSpace γ] [T0Space γ] {f : β → γ} {g : α → β}
    (hf : UniformContinuous f) (hg : UniformContinuous g) :
    Completion.extension f ∘ Completion.map g = Completion.extension (f ∘ g) :=
  Completion.ext (continuous_extension.comp continuous_map) continuous_extension <| by
    intro a
    -- Porting note: this is not provable by simp [hf, hg, hf.comp hg, map_coe, extension_coe],
    -- but should be?
    rw [extension_coe (hf.comp hg), Function.comp_apply, map_coe hg, extension_coe hf,
      Function.comp_apply]
#align uniform_space.completion.extension_map UniformSpace.Completion.extension_map

theorem map_comp {g : β → γ} {f : α → β} (hg : UniformContinuous g) (hf : UniformContinuous f) :
    Completion.map g ∘ Completion.map f = Completion.map (g ∘ f) :=
  extension_map ((uniformContinuous_coe _).comp hg) hf
#align uniform_space.completion.map_comp UniformSpace.Completion.map_comp

end Map

/- In this section we construct isomorphisms between the completion of a uniform space and the
completion of its separation quotient -/
section SeparationQuotientCompletion

open SeparationQuotient in
/-- The isomorphism between the completion of a uniform space and the completion of its separation
quotient. -/
def completionSeparationQuotientEquiv (α : Type u) [UniformSpace α] :
    Completion (SeparationQuotient α) ≃ Completion α := by
  refine ⟨Completion.extension (lift' ((↑) : α → Completion α)),
    Completion.map SeparationQuotient.mk, fun a ↦ ?_, fun a ↦ ?_⟩
  · refine induction_on a (isClosed_eq (continuous_map.comp continuous_extension) continuous_id) ?_
    refine SeparationQuotient.surjective_mk.forall.2 fun a ↦ ?_
    rw [extension_coe (uniformContinuous_lift' _), lift'_mk (uniformContinuous_coe α),
      map_coe uniformContinuous_mk]
  · refine induction_on a
      (isClosed_eq (continuous_extension.comp continuous_map) continuous_id) fun a ↦ ?_
    rw [map_coe uniformContinuous_mk, extension_coe (uniformContinuous_lift' _),
      lift'_mk (uniformContinuous_coe _)]
#align uniform_space.completion.completion_separation_quotient_equiv UniformSpace.Completion.completionSeparationQuotientEquiv

theorem uniformContinuous_completionSeparationQuotientEquiv :
    UniformContinuous (completionSeparationQuotientEquiv α) :=
  uniformContinuous_extension
#align uniform_space.completion.uniform_continuous_completion_separation_quotient_equiv UniformSpace.Completion.uniformContinuous_completionSeparationQuotientEquiv

theorem uniformContinuous_completionSeparationQuotientEquiv_symm :
    UniformContinuous (completionSeparationQuotientEquiv α).symm :=
  uniformContinuous_map
#align uniform_space.completion.uniform_continuous_completion_separation_quotient_equiv_symm UniformSpace.Completion.uniformContinuous_completionSeparationQuotientEquiv_symm

end SeparationQuotientCompletion

section Extension₂

variable (f : α → β → γ)

open Function

/-- Extend a two variable map to the Hausdorff completions. -/
protected def extension₂ (f : α → β → γ) : Completion α → Completion β → γ :=
  cPkg.extend₂ cPkg f
#align uniform_space.completion.extension₂ UniformSpace.Completion.extension₂

section T0Space

variable [T0Space γ] {f}

/- porting note: removed `@[simp]` because this lemma doesn't even trigger on itself in Lean 3 or
Lean 4 unless the user manually supplies the `hf` argument, so it is useless as a `simp` lemma. -/
theorem extension₂_coe_coe (hf : UniformContinuous₂ f) (a : α) (b : β) :
    Completion.extension₂ f a b = f a b :=
  cPkg.extension₂_coe_coe cPkg hf a b
#align uniform_space.completion.extension₂_coe_coe UniformSpace.Completion.extension₂_coe_coe

end T0Space

variable [CompleteSpace γ]

theorem uniformContinuous_extension₂ : UniformContinuous₂ (Completion.extension₂ f) :=
  cPkg.uniformContinuous_extension₂ cPkg f
#align uniform_space.completion.uniform_continuous_extension₂ UniformSpace.Completion.uniformContinuous_extension₂

end Extension₂

section Map₂

open Function

/-- Lift a two variable map to the Hausdorff completions. -/
protected def map₂ (f : α → β → γ) : Completion α → Completion β → Completion γ :=
  cPkg.map₂ cPkg cPkg f
#align uniform_space.completion.map₂ UniformSpace.Completion.map₂

theorem uniformContinuous_map₂ (f : α → β → γ) : UniformContinuous₂ (Completion.map₂ f) :=
  cPkg.uniformContinuous_map₂ cPkg cPkg f
#align uniform_space.completion.uniform_continuous_map₂ UniformSpace.Completion.uniformContinuous_map₂

theorem continuous_map₂ {δ} [TopologicalSpace δ] {f : α → β → γ} {a : δ → Completion α}
    {b : δ → Completion β} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun d : δ => Completion.map₂ f (a d) (b d) :=
  cPkg.continuous_map₂ cPkg cPkg ha hb
#align uniform_space.completion.continuous_map₂ UniformSpace.Completion.continuous_map₂

theorem map₂_coe_coe (a : α) (b : β) (f : α → β → γ) (hf : UniformContinuous₂ f) :
    Completion.map₂ f (a : Completion α) (b : Completion β) = f a b :=
  cPkg.map₂_coe_coe cPkg cPkg a b f hf
#align uniform_space.completion.map₂_coe_coe UniformSpace.Completion.map₂_coe_coe

end Map₂

end Completion

end UniformSpace
