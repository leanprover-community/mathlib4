/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import Mathlib.Topology.ContinuousFunction.Basic

#align_import topology.compact_open from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# The compact-open topology

In this file, we define the compact-open topology on the set of continuous maps between two
topological spaces.

## Main definitions

* `CompactOpen` is the compact-open topology on `C(α, β)`. It is declared as an instance.
* `ContinuousMap.coev` is the coevaluation map `β → C(α, β × α)`. It is always continuous.
* `ContinuousMap.curry` is the currying map `C(α × β, γ) → C(α, C(β, γ))`. This map always exists
  and it is continuous as long as `α × β` is locally compact.
* `ContinuousMap.uncurry` is the uncurrying map `C(α, C(β, γ)) → C(α × β, γ)`. For this map to
  exist, we need `β` to be locally compact. If `α` is also locally compact, then this map is
  continuous.
* `Homeomorph.curry` combines the currying and uncurrying operations into a homeomorphism
  `C(α × β, γ) ≃ₜ C(α, C(β, γ))`. This homeomorphism exists if `α` and `β` are locally compact.


## Tags

compact-open, curry, function space
-/


open Set Filter TopologicalSpace
open scoped Topology

namespace ContinuousMap

section CompactOpen

variable {α : Type*} {β : Type*} {γ : Type*}

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-- A generating set for the compact-open topology (when `s` is compact and `u` is open). -/
def CompactOpen.gen (s : Set α) (u : Set β) : Set C(α, β) :=
  { f | f '' s ⊆ u }
#align continuous_map.compact_open.gen ContinuousMap.CompactOpen.gen

@[simp]
theorem gen_empty (u : Set β) : CompactOpen.gen (∅ : Set α) u = Set.univ :=
  Set.ext fun f => iff_true_intro ((congr_arg (· ⊆ u) (image_empty f)).mpr u.empty_subset)
#align continuous_map.gen_empty ContinuousMap.gen_empty

@[simp]
theorem gen_univ (s : Set α) : CompactOpen.gen s (Set.univ : Set β) = Set.univ :=
  Set.ext fun f => iff_true_intro (f '' s).subset_univ
#align continuous_map.gen_univ ContinuousMap.gen_univ

@[simp]
theorem gen_inter (s : Set α) (u v : Set β) :
    CompactOpen.gen s (u ∩ v) = CompactOpen.gen s u ∩ CompactOpen.gen s v :=
  Set.ext fun _ => subset_inter_iff
#align continuous_map.gen_inter ContinuousMap.gen_inter

@[simp]
theorem gen_union (s t : Set α) (u : Set β) :
    CompactOpen.gen (s ∪ t) u = CompactOpen.gen s u ∩ CompactOpen.gen t u :=
  Set.ext fun f => (iff_of_eq (congr_arg (· ⊆ u) (image_union f s t))).trans union_subset_iff
#align continuous_map.gen_union ContinuousMap.gen_union

theorem gen_empty_right {s : Set α} (h : s.Nonempty) : CompactOpen.gen s (∅ : Set β) = ∅ :=
  eq_empty_of_forall_not_mem fun _ => (h.image _).not_subset_empty
#align continuous_map.gen_empty_right ContinuousMap.gen_empty_right

-- The compact-open topology on the space of continuous maps α → β.
instance compactOpen : TopologicalSpace C(α, β) :=
  TopologicalSpace.generateFrom
    { m | ∃ (s : Set α) (_ : IsCompact s) (u : Set β) (_ : IsOpen u), m = CompactOpen.gen s u }
#align continuous_map.compact_open ContinuousMap.compactOpen

/-- Definition of `ContinuousMap.compactOpen` in terms of `Set.image2`. -/
theorem compactOpen_eq : @compactOpen α β _ _ =
    .generateFrom (Set.image2 CompactOpen.gen {s | IsCompact s} {t | IsOpen t}) :=
  congr_arg TopologicalSpace.generateFrom <| Set.ext fun _ ↦ by simp [eq_comm]

protected theorem isOpen_gen {s : Set α} (hs : IsCompact s) {u : Set β} (hu : IsOpen u) :
    IsOpen (CompactOpen.gen s u) :=
  TopologicalSpace.GenerateOpen.basic _ (by dsimp [mem_setOf_eq]; tauto)
#align continuous_map.is_open_gen ContinuousMap.isOpen_gen

lemma isOpen_setOf_mapsTo {K : Set α} (hK : IsCompact K) {U : Set β} (hU : IsOpen U) :
    IsOpen {f : C(α, β) | MapsTo f K U} := by
  simpa only [mapsTo'] using ContinuousMap.isOpen_gen hK hU

lemma eventually_mapsTo {f : C(α, β)} {K U} (hK : IsCompact K) (hU : IsOpen U) (h : MapsTo f K U) :
    ∀ᶠ g : C(α, β) in 𝓝 f, MapsTo g K U :=
  (isOpen_setOf_mapsTo hK hU).mem_nhds h

lemma tendsto_nhds_compactOpen {α : Type*} {l : Filter α} {f : α → C(β, γ)} {g : C(β, γ)} :
    Tendsto f l (𝓝 g) ↔
      ∀ K, IsCompact K → ∀ U, IsOpen U → MapsTo g K U → ∀ᶠ a in l, MapsTo (f a) K U := by
  simp_rw [compactOpen_eq, tendsto_nhds_generateFrom_iff, forall_image2_iff, mapsTo']; rfl

lemma continuous_compactOpen {f : α → C(β, γ)} :
    Continuous f ↔ ∀ K, IsCompact K → ∀ U, IsOpen U → IsOpen {x | MapsTo (f x) K U} := by
  simp_rw [compactOpen_eq, continuous_generateFrom_iff, forall_image2_iff, mapsTo']; rfl

section Functorial

variable (g : C(β, γ))

private theorem preimage_gen {s : Set α} {u : Set γ} :
    ContinuousMap.comp g ⁻¹' CompactOpen.gen s u = CompactOpen.gen s (g ⁻¹' u) := by
  ext ⟨f, _⟩
  change g ∘ f '' s ⊆ u ↔ f '' s ⊆ g ⁻¹' u
  rw [image_comp, image_subset_iff]

/-- C(α, -) is a functor. -/
theorem continuous_comp : Continuous (ContinuousMap.comp g : C(α, β) → C(α, γ)) :=
  continuous_generateFrom_iff.2 fun m ⟨s, hs, u, hu, hm⟩ => by
    rw [hm, preimage_gen g]; exact ContinuousMap.isOpen_gen hs (hu.preimage g.2)
#align continuous_map.continuous_comp ContinuousMap.continuous_comp

/-- If `g : C(β, γ)` is a topology inducing map, then the composition
`ContinuousMap.comp g : C(α, β) → C(α, γ)` is a topology inducing map too. -/
theorem inducing_comp (hg : Inducing g) : Inducing (g.comp : C(α, β) → C(α, γ)) where
  induced := by
    simp only [compactOpen_eq, induced_generateFrom_eq, image_image2, preimage_gen,
      hg.setOf_isOpen, image2_image_right]

/-- If `g : C(β, γ)` is a topological embedding, then the composition
`ContinuousMap.comp g : C(α, β) → C(α, γ)` is an embedding too. -/
theorem embedding_comp (hg : Embedding g) : Embedding (g.comp : C(α, β) → C(α, γ)) :=
  ⟨inducing_comp g hg.1, fun _ _ ↦ (cancel_left hg.2).1⟩

variable (f : C(α, β))

private theorem image_gen {s : Set α} (_ : IsCompact s) {u : Set γ} (_ : IsOpen u) :
    (fun g : C(β, γ) => g.comp f) ⁻¹' CompactOpen.gen s u = CompactOpen.gen (f '' s) u := by
  ext ⟨g, _⟩
  change g ∘ f '' s ⊆ u ↔ g '' (f '' s) ⊆ u
  rw [Set.image_comp]

/-- C(-, γ) is a functor. -/
theorem continuous_comp_left : Continuous (fun g => g.comp f : C(β, γ) → C(α, γ)) :=
  continuous_generateFrom_iff.2 fun m ⟨s, hs, u, hu, hm⟩ => by
    rw [hm, image_gen f hs hu]
    exact ContinuousMap.isOpen_gen (hs.image f.2) hu
#align continuous_map.continuous_comp_left ContinuousMap.continuous_comp_left

/-- Composition is a continuous map from `C(α, β) × C(β, γ)` to `C(α, γ)`, provided that `β` is
  locally compact. This is Prop. 9 of Chap. X, §3, №. 4 of Bourbaki's *Topologie Générale*. -/
theorem continuous_comp' [LocallyCompactPair β γ] :
    Continuous fun x : C(α, β) × C(β, γ) => x.2.comp x.1 := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, tendsto_nhds_compactOpen]
  intro ⟨f, g⟩ K hK U hU (hKU : MapsTo (g ∘ f) K U)
  obtain ⟨L, hKL, hLc, hLU⟩ : ∃ L ∈ 𝓝ˢ (f '' K), IsCompact L ∧ MapsTo g L U :=
    exists_mem_nhdsSet_isCompact_mapsTo g.continuous (hK.image f.continuous) hU
      (mapsTo_image_iff.2 hKU)
  rw [← subset_interior_iff_mem_nhdsSet, ← mapsTo'] at hKL
  exact ((eventually_mapsTo hK isOpen_interior hKL).prod_nhds
    (eventually_mapsTo hLc hU hLU)).mono fun ⟨f', g'⟩ ⟨hf', hg'⟩ ↦
      hg'.comp <| hf'.mono_right interior_subset
#align continuous_map.continuous_comp' ContinuousMap.continuous_comp'

theorem continuous.comp' {X : Type*} [TopologicalSpace X] [LocallyCompactPair β γ] {f : X → C(α, β)}
    {g : X → C(β, γ)} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => (g x).comp (f x) :=
  continuous_comp'.comp (hf.prod_mk hg : Continuous fun x => (f x, g x))
#align continuous_map.continuous.comp' ContinuousMap.continuous.comp'

end Functorial

section Ev

/-- The evaluation map `C(α, β) × α → β` is continuous
if `α, β` is a locally compact pair of spaces. -/
@[continuity]
theorem continuous_eval [LocallyCompactPair α β] : Continuous fun p : C(α, β) × α => p.1 p.2 := by
  simp_rw [continuous_iff_continuousAt, ContinuousAt, (nhds_basis_opens _).tendsto_right_iff]
  rintro ⟨f, x⟩ U ⟨hx : f x ∈ U, hU : IsOpen U⟩
  rcases exists_mem_nhds_isCompact_mapsTo f.continuous (hU.mem_nhds hx) with ⟨K, hxK, hK, hKU⟩
  filter_upwards [prod_mem_nhds (eventually_mapsTo hK hU hKU) hxK] using fun _ h ↦ h.1 h.2
#align continuous_map.continuous_eval' ContinuousMap.continuous_eval
#align continuous_map.continuous_eval ContinuousMap.continuous_eval

@[deprecated] alias continuous_eval' := continuous_eval

/-- Evaluation of a continuous map `f` at a point `a` is continuous in `f`.

Porting note: merged `continuous_eval_const` with `continuous_eval_const'` removing unneeded
assumptions. -/
@[continuity]
theorem continuous_eval_const (a : α) :
    Continuous fun f : C(α, β) => f a := by
  refine continuous_def.2 fun U hU ↦ ?_
  convert ContinuousMap.isOpen_gen (isCompact_singleton (x := a)) hU using 1
  ext; simp [CompactOpen.gen]
#align continuous_map.continuous_eval_const' ContinuousMap.continuous_eval_const
#align continuous_map.continuous_eval_const ContinuousMap.continuous_eval_const

/-- Coercion from `C(α, β)` with compact-open topology to `α → β` with pointwise convergence
topology is a continuous map.

Porting note: merged `continuous_coe` with `continuous_coe'` removing unneeded assumptions. -/
theorem continuous_coe : Continuous ((⇑) : C(α, β) → (α → β)) :=
  continuous_pi continuous_eval_const
#align continuous_map.continuous_coe' ContinuousMap.continuous_coe
#align continuous_map.continuous_coe ContinuousMap.continuous_coe

lemma isClosed_setOf_mapsTo {t : Set β} (ht : IsClosed t) (s : Set α) :
    IsClosed {f : C(α, β) | MapsTo f s t} :=
  ht.setOf_mapsTo fun _ _ ↦ continuous_eval_const _

lemma isClopen_setOf_mapsTo {K : Set α} (hK : IsCompact K) {U : Set β} (hU : IsClopen U) :
    IsClopen {f : C(α, β) | MapsTo f K U} :=
  ⟨isOpen_setOf_mapsTo hK hU.isOpen, isClosed_setOf_mapsTo hU.isClosed K⟩

instance [T0Space β] : T0Space C(α, β) :=
  t0Space_of_injective_of_continuous FunLike.coe_injective continuous_coe

instance [T1Space β] : T1Space C(α, β) :=
  t1Space_of_injective_of_continuous FunLike.coe_injective continuous_coe

instance [T2Space β] : T2Space C(α, β) :=
  .of_injective_continuous FunLike.coe_injective continuous_coe

end Ev

section InfInduced

theorem compactOpen_le_induced (s : Set α) :
    (ContinuousMap.compactOpen : TopologicalSpace C(α, β)) ≤
      TopologicalSpace.induced (ContinuousMap.restrict s) ContinuousMap.compactOpen := by
  simp only [induced_generateFrom_eq, ContinuousMap.compactOpen]
  apply TopologicalSpace.generateFrom_anti
  rintro b ⟨a, ⟨c, hc, u, hu, rfl⟩, rfl⟩
  refine' ⟨(↑) '' c, hc.image continuous_subtype_val, u, hu, _⟩
  ext f
  simp only [CompactOpen.gen, mem_setOf_eq, mem_preimage, ContinuousMap.coe_restrict]
  rw [image_comp f ((↑) : s → α)]
#align continuous_map.compact_open_le_induced ContinuousMap.compactOpen_le_induced

/-- The compact-open topology on `C(α, β)` is equal to the infimum of the compact-open topologies
on `C(s, β)` for `s` a compact subset of `α`.  The key point of the proof is that the union of the
compact subsets of `α` is equal to the union of compact subsets of the compact subsets of `α`. -/
theorem compactOpen_eq_sInf_induced :
    (ContinuousMap.compactOpen : TopologicalSpace C(α, β)) =
      ⨅ (s : Set α) (_ : IsCompact s),
        TopologicalSpace.induced (ContinuousMap.restrict s) ContinuousMap.compactOpen := by
  refine' le_antisymm _ _
  · refine' le_iInf₂ _
    exact fun s _ => compactOpen_le_induced s
  simp only [← generateFrom_iUnion, induced_generateFrom_eq, ContinuousMap.compactOpen]
  apply TopologicalSpace.generateFrom_anti
  rintro _ ⟨s, hs, u, hu, rfl⟩
  rw [mem_iUnion₂]
  refine' ⟨s, hs, _, ⟨univ, isCompact_iff_isCompact_univ.mp hs, u, hu, rfl⟩, _⟩
  ext f
  simp only [CompactOpen.gen, mem_setOf_eq, mem_preimage, ContinuousMap.coe_restrict]
  rw [image_comp f ((↑) : s → α)]
  simp
#align continuous_map.compact_open_eq_Inf_induced ContinuousMap.compactOpen_eq_sInf_induced

/-- For any subset `s` of `α`, the restriction of continuous functions to `s` is continuous as a
function from `C(α, β)` to `C(s, β)` with their respective compact-open topologies. -/
theorem continuous_restrict (s : Set α) : Continuous fun F : C(α, β) => F.restrict s := by
  rw [continuous_iff_le_induced]
  exact compactOpen_le_induced s
#align continuous_map.continuous_restrict ContinuousMap.continuous_restrict

theorem nhds_compactOpen_eq_sInf_nhds_induced (f : C(α, β)) :
    𝓝 f = ⨅ (s) (hs : IsCompact s), (𝓝 (f.restrict s)).comap (ContinuousMap.restrict s) := by
  rw [compactOpen_eq_sInf_induced]
  simp [nhds_iInf, nhds_induced]
#align continuous_map.nhds_compact_open_eq_Inf_nhds_induced ContinuousMap.nhds_compactOpen_eq_sInf_nhds_induced

theorem tendsto_compactOpen_restrict {ι : Type*} {l : Filter ι} {F : ι → C(α, β)} {f : C(α, β)}
    (hFf : Filter.Tendsto F l (𝓝 f)) (s : Set α) :
    Filter.Tendsto (fun i => (F i).restrict s) l (𝓝 (f.restrict s)) :=
  (continuous_restrict s).continuousAt.tendsto.comp hFf
#align continuous_map.tendsto_compact_open_restrict ContinuousMap.tendsto_compactOpen_restrict

theorem tendsto_compactOpen_iff_forall {ι : Type*} {l : Filter ι} (F : ι → C(α, β)) (f : C(α, β)) :
    Filter.Tendsto F l (𝓝 f) ↔
    ∀ (s) (hs : IsCompact s), Filter.Tendsto (fun i => (F i).restrict s) l (𝓝 (f.restrict s)) := by
    rw [compactOpen_eq_sInf_induced]
    simp [nhds_iInf, nhds_induced, Filter.tendsto_comap_iff, Function.comp]
#align continuous_map.tendsto_compact_open_iff_forall ContinuousMap.tendsto_compactOpen_iff_forall

/-- A family `F` of functions in `C(α, β)` converges in the compact-open topology, if and only if
it converges in the compact-open topology on each compact subset of `α`. -/
theorem exists_tendsto_compactOpen_iff_forall [WeaklyLocallyCompactSpace α] [T2Space β]
    {ι : Type*} {l : Filter ι} [Filter.NeBot l] (F : ι → C(α, β)) :
    (∃ f, Filter.Tendsto F l (𝓝 f)) ↔
    ∀ (s : Set α) (hs : IsCompact s), ∃ f, Filter.Tendsto (fun i => (F i).restrict s) l (𝓝 f) := by
  constructor
  · rintro ⟨f, hf⟩ s _
    exact ⟨f.restrict s, tendsto_compactOpen_restrict hf s⟩
  · intro h
    choose f hf using h
    -- By uniqueness of limits in a `T2Space`, since `fun i ↦ F i x` tends to both `f s₁ hs₁ x` and
    -- `f s₂ hs₂ x`, we have `f s₁ hs₁ x = f s₂ hs₂ x`
    have h :
      ∀ (s₁) (hs₁ : IsCompact s₁) (s₂) (hs₂ : IsCompact s₂) (x : α) (hxs₁ : x ∈ s₁) (hxs₂ : x ∈ s₂),
        f s₁ hs₁ ⟨x, hxs₁⟩ = f s₂ hs₂ ⟨x, hxs₂⟩ := by
      rintro s₁ hs₁ s₂ hs₂ x hxs₁ hxs₂
      haveI := isCompact_iff_compactSpace.mp hs₁
      haveI := isCompact_iff_compactSpace.mp hs₂
      have h₁ := (continuous_eval_const (⟨x, hxs₁⟩ : s₁)).continuousAt.tendsto.comp (hf s₁ hs₁)
      have h₂ := (continuous_eval_const (⟨x, hxs₂⟩ : s₂)).continuousAt.tendsto.comp (hf s₂ hs₂)
      exact tendsto_nhds_unique h₁ h₂
    -- So glue the `f s hs` together and prove that this glued function `f₀` is a limit on each
    -- compact set `s`
    refine ⟨liftCover' _ _ h exists_compact_mem_nhds, ?_⟩
    rw [tendsto_compactOpen_iff_forall]
    intro s hs
    rw [liftCover_restrict']
    exact hf s hs
#align continuous_map.exists_tendsto_compact_open_iff_forall ContinuousMap.exists_tendsto_compactOpen_iff_forall

end InfInduced

section Coev

variable (α β)

/-- The coevaluation map `β → C(α, β × α)` sending a point `x : β` to the continuous function
on `α` sending `y` to `(x, y)`. -/
def coev (b : β) : C(α, β × α) :=
  { toFun := Prod.mk b }
#align continuous_map.coev ContinuousMap.coev

variable {α β}

theorem image_coev {y : β} (s : Set α) : coev α β y '' s = ({y} : Set β) ×ˢ s := by
  aesop
#align continuous_map.image_coev ContinuousMap.image_coev

-- The coevaluation map β → C(α, β × α) is continuous (always).
theorem continuous_coev : Continuous (coev α β) :=
  continuous_generateFrom_iff.2 <| by
    rintro _ ⟨s, sc, u, uo, rfl⟩
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    have hy' : (↑(coev α β y) '' s ⊆ u) := hy
    -- porting notes: was below
    --change coev α β y '' s ⊆ u at hy
    rw [image_coev s] at hy'
    rcases generalized_tube_lemma isCompact_singleton sc uo hy' with ⟨v, w, vo, _, yv, sw, vwu⟩
    refine' ⟨v, _, vo, singleton_subset_iff.mp yv⟩
    intro y' hy'
    change coev α β y' '' s ⊆ u
    rw [image_coev s]
    exact (prod_mono (singleton_subset_iff.mpr hy') sw).trans vwu
#align continuous_map.continuous_coev ContinuousMap.continuous_coev

end Coev

section Curry

/-- Auxiliary definition, see `ContinuousMap.curry` and `Homeomorph.curry`. -/
def curry' (f : C(α × β, γ)) (a : α) : C(β, γ) :=
  ⟨Function.curry f a, Continuous.comp f.2 (continuous_const.prod_mk continuous_id)⟩
  -- Porting note: proof was `by continuity`
#align continuous_map.curry' ContinuousMap.curry'

/-- If a map `α × β → γ` is continuous, then its curried form `α → C(β, γ)` is continuous. -/
theorem continuous_curry' (f : C(α × β, γ)) : Continuous (curry' f) :=
  Continuous.comp (continuous_comp f) continuous_coev
#align continuous_map.continuous_curry' ContinuousMap.continuous_curry'

/-- To show continuity of a map `α → C(β, γ)`, it suffices to show that its uncurried form
    `α × β → γ` is continuous. -/
theorem continuous_of_continuous_uncurry (f : α → C(β, γ))
    (h : Continuous (Function.uncurry fun x y => f x y)) : Continuous f :=
  continuous_curry' ⟨_, h⟩
#align continuous_map.continuous_of_continuous_uncurry ContinuousMap.continuous_of_continuous_uncurry

/-- The curried form of a continuous map `α × β → γ` as a continuous map `α → C(β, γ)`.
    If `a × β` is locally compact, this is continuous. If `α` and `β` are both locally
    compact, then this is a homeomorphism, see `Homeomorph.curry`. -/
def curry (f : C(α × β, γ)) : C(α, C(β, γ)) :=
  ⟨_, continuous_curry' f⟩
#align continuous_map.curry ContinuousMap.curry

@[simp]
theorem curry_apply (f : C(α × β, γ)) (a : α) (b : β) : f.curry a b = f (a, b) :=
  rfl
#align continuous_map.curry_apply ContinuousMap.curry_apply

/-- The currying process is a continuous map between function spaces. -/
theorem continuous_curry [LocallyCompactSpace (α × β)] :
    Continuous (curry : C(α × β, γ) → C(α, C(β, γ))) := by
  apply continuous_of_continuous_uncurry
  apply continuous_of_continuous_uncurry
  rw [← (Homeomorph.prodAssoc _ _ _).symm.comp_continuous_iff']
  exact continuous_eval
#align continuous_map.continuous_curry ContinuousMap.continuous_curry

/-- The uncurried form of a continuous map `α → C(β, γ)` is a continuous map `α × β → γ`. -/
theorem continuous_uncurry_of_continuous [LocallyCompactSpace β] (f : C(α, C(β, γ))) :
    Continuous (Function.uncurry fun x y => f x y) :=
  continuous_eval.comp <| f.continuous.prod_map continuous_id
#align continuous_map.continuous_uncurry_of_continuous ContinuousMap.continuous_uncurry_of_continuous

/-- The uncurried form of a continuous map `α → C(β, γ)` as a continuous map `α × β → γ` (if `β` is
    locally compact). If `α` is also locally compact, then this is a homeomorphism between the two
    function spaces, see `Homeomorph.curry`. -/
@[simps]
def uncurry [LocallyCompactSpace β] (f : C(α, C(β, γ))) : C(α × β, γ) :=
  ⟨_, continuous_uncurry_of_continuous f⟩
#align continuous_map.uncurry ContinuousMap.uncurry

/-- The uncurrying process is a continuous map between function spaces. -/
theorem continuous_uncurry [LocallyCompactSpace α] [LocallyCompactSpace β] :
    Continuous (uncurry : C(α, C(β, γ)) → C(α × β, γ)) := by
  apply continuous_of_continuous_uncurry
  rw [← (Homeomorph.prodAssoc _ _ _).comp_continuous_iff']
  apply continuous_eval.comp (continuous_eval.prod_map continuous_id)
#align continuous_map.continuous_uncurry ContinuousMap.continuous_uncurry

/-- The family of constant maps: `β → C(α, β)` as a continuous map. -/
def const' : C(β, C(α, β)) :=
  curry ContinuousMap.fst
#align continuous_map.const' ContinuousMap.const'

@[simp]
theorem coe_const' : (const' : β → C(α, β)) = const α :=
  rfl
#align continuous_map.coe_const' ContinuousMap.coe_const'

theorem continuous_const' : Continuous (const α : β → C(α, β)) :=
  const'.continuous
#align continuous_map.continuous_const' ContinuousMap.continuous_const'

end Curry

end CompactOpen

end ContinuousMap

open ContinuousMap

namespace Homeomorph

variable {α : Type*} {β : Type*} {γ : Type*}

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-- Currying as a homeomorphism between the function spaces `C(α × β, γ)` and `C(α, C(β, γ))`. -/
def curry [LocallyCompactSpace α] [LocallyCompactSpace β] : C(α × β, γ) ≃ₜ C(α, C(β, γ)) :=
  ⟨⟨ContinuousMap.curry, uncurry, by intro; ext; rfl, by intro; ext; rfl⟩,
    continuous_curry, continuous_uncurry⟩
#align homeomorph.curry Homeomorph.curry

/-- If `α` has a single element, then `β` is homeomorphic to `C(α, β)`. -/
def continuousMapOfUnique [Unique α] : β ≃ₜ C(α, β) where
  toFun := const α
  invFun f := f default
  left_inv a := rfl
  right_inv f := by
    ext a
    rw [Unique.eq_default a]
    rfl
  continuous_toFun := continuous_const'
  continuous_invFun := continuous_eval_const _
#align homeomorph.continuous_map_of_unique Homeomorph.continuousMapOfUnique

@[simp]
theorem continuousMapOfUnique_apply [Unique α] (b : β) (a : α) : continuousMapOfUnique b a = b :=
  rfl
#align homeomorph.continuous_map_of_unique_apply Homeomorph.continuousMapOfUnique_apply

@[simp]
theorem continuousMapOfUnique_symm_apply [Unique α] (f : C(α, β)) :
    continuousMapOfUnique.symm f = f default :=
  rfl
#align homeomorph.continuous_map_of_unique_symm_apply Homeomorph.continuousMapOfUnique_symm_apply

end Homeomorph

section QuotientMap

variable {X₀ X Y Z : Type*} [TopologicalSpace X₀] [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [LocallyCompactSpace Y] {f : X₀ → X}

theorem QuotientMap.continuous_lift_prod_left (hf : QuotientMap f) {g : X × Y → Z}
    (hg : Continuous fun p : X₀ × Y => g (f p.1, p.2)) : Continuous g := by
  let Gf : C(X₀, C(Y, Z)) := ContinuousMap.curry ⟨_, hg⟩
  have h : ∀ x : X, Continuous fun y => g (x, y) := by
    intro x
    obtain ⟨x₀, rfl⟩ := hf.surjective x
    exact (Gf x₀).continuous
  let G : X → C(Y, Z) := fun x => ⟨_, h x⟩
  have : Continuous G := by
    rw [hf.continuous_iff]
    exact Gf.continuous
  exact ContinuousMap.continuous_uncurry_of_continuous ⟨G, this⟩
#align quotient_map.continuous_lift_prod_left QuotientMap.continuous_lift_prod_left

theorem QuotientMap.continuous_lift_prod_right (hf : QuotientMap f) {g : Y × X → Z}
    (hg : Continuous fun p : Y × X₀ => g (p.1, f p.2)) : Continuous g := by
  have : Continuous fun p : X₀ × Y => g ((Prod.swap p).1, f (Prod.swap p).2) :=
    hg.comp continuous_swap
  have : Continuous fun p : X₀ × Y => (g ∘ Prod.swap) (f p.1, p.2) := this
  exact (hf.continuous_lift_prod_left this).comp continuous_swap
#align quotient_map.continuous_lift_prod_right QuotientMap.continuous_lift_prod_right

end QuotientMap
