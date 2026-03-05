/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Stone-Čech compactification

Construction of the Stone-Čech compactification using ultrafilters.

For any topological space `α`, we build a compact Hausdorff space `StoneCech α` and a continuous
map `stoneCechUnit : α → StoneCech α` which is minimal in the sense of the following universal
property: for any compact Hausdorff space `β` and every map `f : α → β` such that
`hf : Continuous f`, there is a unique map `stoneCechExtend hf : StoneCech α → β` such that
`stoneCechExtend_extends : stoneCechExtend hf ∘ stoneCechUnit = f`.
Continuity of this extension is asserted by `continuous_stoneCechExtend` and uniqueness by
`stoneCech_hom_ext`.

Beware that the terminology “extend” is slightly misleading since `stoneCechUnit` is not always
injective, so one cannot always think of `α` as being “inside” its compactification `StoneCech α`.

## Implementation notes

Parts of the formalization are based on “Ultrafilters and Topology”
by Marius Stekelenburg, particularly section 5. However the construction in the general
case is different because the equivalence relation on spaces of ultrafilters described
by Stekelenburg causes issues with universes since it involves a condition
on all compact Hausdorff spaces. We replace it by a two steps construction.
The first step called `PreStoneCech` guarantees the expected universal property but
not the Hausdorff condition. We then define `StoneCech α` as `T2Quotient (PreStoneCech α)`.
-/

@[expose] public section


noncomputable section

open Filter Set

open Topology

universe u v

section Ultrafilter

/- The set of ultrafilters on α carries a natural topology which makes
  it the Stone-Čech compactification of α (viewed as a discrete space). -/
/-- Basis for the topology on `Ultrafilter α`. -/
def ultrafilterBasis (α : Type u) : Set (Set (Ultrafilter α)) :=
  range fun s : Set α ↦ { u | s ∈ u }

variable {α : Type u}

instance Ultrafilter.topologicalSpace : TopologicalSpace (Ultrafilter α) :=
  TopologicalSpace.generateFrom (ultrafilterBasis α)

theorem ultrafilterBasis_is_basis : TopologicalSpace.IsTopologicalBasis (ultrafilterBasis α) :=
  ⟨by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ u ⟨ua, ub⟩
    refine ⟨_, ⟨a ∩ b, rfl⟩, inter_mem ua ub, fun v hv ↦ ⟨?_, ?_⟩⟩ <;> apply mem_of_superset hv <;>
      simp [inter_subset_right],
    eq_univ_of_univ_subset <| subset_sUnion_of_mem <| ⟨univ, eq_univ_of_forall fun _ ↦ univ_mem⟩,
    rfl⟩

/-- The basic open sets for the topology on ultrafilters are open. -/
theorem ultrafilter_isOpen_basic (s : Set α) : IsOpen { u : Ultrafilter α | s ∈ u } :=
  ultrafilterBasis_is_basis.isOpen ⟨s, rfl⟩

/-- The basic open sets for the topology on ultrafilters are also closed. -/
theorem ultrafilter_isClosed_basic (s : Set α) : IsClosed { u : Ultrafilter α | s ∈ u } := by
  rw [← isOpen_compl_iff]
  convert ultrafilter_isOpen_basic sᶜ using 1
  ext u
  exact Ultrafilter.compl_mem_iff_notMem.symm

/-- Every ultrafilter `u` on `Ultrafilter α` converges to a unique
  point of `Ultrafilter α`, namely `joinM u`. -/
theorem ultrafilter_converges_iff {u : Ultrafilter (Ultrafilter α)} {x : Ultrafilter α} :
    ↑u ≤ 𝓝 x ↔ x = joinM u := by
  rw [eq_comm, ← Ultrafilter.coe_le_coe]
  change ↑u ≤ 𝓝 x ↔ ∀ s ∈ x, { v : Ultrafilter α | s ∈ v } ∈ u
  simp only [TopologicalSpace.nhds_generateFrom, le_iInf_iff, ultrafilterBasis, le_principal_iff,
    mem_setOf_eq]
  constructor
  · intro h a ha
    exact h _ ⟨ha, a, rfl⟩
  · rintro h a ⟨xi, a, rfl⟩
    exact h _ xi

instance ultrafilter_compact : CompactSpace (Ultrafilter α) :=
  ⟨isCompact_iff_ultrafilter_le_nhds.mpr fun f _ ↦
      ⟨joinM f, trivial, ultrafilter_converges_iff.mpr rfl⟩⟩

instance Ultrafilter.t2Space : T2Space (Ultrafilter α) :=
  t2_iff_ultrafilter.mpr fun {x y} f fx fy ↦
    have hx : x = joinM f := ultrafilter_converges_iff.mp fx
    have hy : y = joinM f := ultrafilter_converges_iff.mp fy
    hx.trans hy.symm

instance : TotallyDisconnectedSpace (Ultrafilter α) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  intro A
  simp only [Set.eq_singleton_iff_unique_mem, mem_connectedComponent, true_and]
  intro B hB
  rw [← Ultrafilter.coe_le_coe]
  intro s hs
  rw [connectedComponent_eq_iInter_isClopen, Set.mem_iInter] at hB
  let Z := { F : Ultrafilter α | s ∈ F }
  have hZ : IsClopen Z := ⟨ultrafilter_isClosed_basic s, ultrafilter_isOpen_basic s⟩
  exact hB ⟨Z, hZ, hs⟩

@[simp] theorem Ultrafilter.tendsto_pure_self (b : Ultrafilter α) : Tendsto pure b (𝓝 b) := by
  rw [Tendsto, ← coe_map, ultrafilter_converges_iff]
  ext s
  change s ∈ b ↔ {t | s ∈ t} ∈ map pure b
  simp_rw [mem_map, preimage_setOf_eq, mem_pure, setOf_mem_eq]

theorem ultrafilter_comap_pure_nhds (b : Ultrafilter α) : comap pure (𝓝 b) ≤ b := by
  rw [TopologicalSpace.nhds_generateFrom]
  simp only [comap_iInf, comap_principal]
  intro s hs
  rw [← le_principal_iff]
  refine iInf_le_of_le { u | s ∈ u } ?_
  refine iInf_le_of_le ⟨hs, ⟨s, rfl⟩⟩ ?_
  exact principal_mono.2 fun _ ↦ id

section Embedding

open TopologicalSpace

/-- The range of `pure : α → Ultrafilter α` is dense in `Ultrafilter α`. -/
theorem denseRange_pure : DenseRange (pure : α → Ultrafilter α) :=
  fun x ↦ mem_closure_iff_ultrafilter.mpr
    ⟨x.map pure, range_mem_map, ultrafilter_converges_iff.mpr (bind_pure x).symm⟩

/-- The map `pure : α → Ultrafilter α` induces on `α` the discrete topology. -/
theorem induced_topology_pure :
    TopologicalSpace.induced (pure : α → Ultrafilter α) Ultrafilter.topologicalSpace = ⊥ := by
  apply eq_bot_of_singletons_open
  intro x
  use { u : Ultrafilter α | {x} ∈ u }, ultrafilter_isOpen_basic _
  simp

/-- `pure : α → Ultrafilter α` defines a dense inducing of `α` in `Ultrafilter α`. -/
theorem isDenseInducing_pure : @IsDenseInducing _ _ ⊥ _ (pure : α → Ultrafilter α) :=
  letI : TopologicalSpace α := ⊥
  ⟨⟨induced_topology_pure.symm⟩, denseRange_pure⟩

-- The following refined version will never be used
/-- `pure : α → Ultrafilter α` defines a dense embedding of `α` in `Ultrafilter α`. -/
theorem isDenseEmbedding_pure : @IsDenseEmbedding _ _ ⊥ _ (pure : α → Ultrafilter α) :=
  letI : TopologicalSpace α := ⊥
  { isDenseInducing_pure with injective := Ultrafilter.pure_injective }

end Embedding

section Extension

/- Goal: Any function `α → γ` to a compact Hausdorff space `γ` has a
  unique extension to a continuous function `Ultrafilter α → γ`. We
  already know it must be unique because `α → Ultrafilter α` is a
  dense embedding and `γ` is Hausdorff. For existence, we will invoke
  `IsDenseInducing.continuous_extend`. -/
variable {γ : Type*} [TopologicalSpace γ]

/-- The extension of a function `α → γ` to a function `Ultrafilter α → γ`.
  When `γ` is a compact Hausdorff space it will be continuous. -/
def Ultrafilter.extend (f : α → γ) : Ultrafilter α → γ :=
  letI : TopologicalSpace α := ⊥
  isDenseInducing_pure.extend f

variable [T2Space γ]

@[simp]
lemma ultrafilter_extend_extends (f : α → γ) : Ultrafilter.extend f ∘ pure = f := by
  letI : TopologicalSpace α := ⊥
  haveI : DiscreteTopology α := ⟨rfl⟩
  exact funext (isDenseInducing_pure.extend_eq continuous_of_discreteTopology)

@[simp]
lemma ultrafilter_extend_pure (f : α → γ) (a : α) : Ultrafilter.extend f (pure a) = f a :=
  congr_fun (ultrafilter_extend_extends f) a

variable [CompactSpace γ]

theorem continuous_ultrafilter_extend (f : α → γ) : Continuous (Ultrafilter.extend f) := by
  have h (b : Ultrafilter α) : ∃ c, Tendsto f (comap pure (𝓝 b)) (𝓝 c) :=
    -- b.map f is an ultrafilter on γ, which is compact, so it converges to some c in γ.
    let ⟨c, _, h'⟩ :=
      isCompact_univ.ultrafilter_le_nhds (b.map f) (by rw [le_principal_iff]; exact univ_mem)
    ⟨c, le_trans (map_mono (ultrafilter_comap_pure_nhds _)) h'⟩
  let _ : TopologicalSpace α := ⊥
  exact isDenseInducing_pure.continuous_extend h

/-- The value of `Ultrafilter.extend f` on an ultrafilter `b` is the
  unique limit of the ultrafilter `b.map f` in `γ`. -/
theorem ultrafilter_extend_eq_iff {f : α → γ} {b : Ultrafilter α} {c : γ} :
    Ultrafilter.extend f b = c ↔ ↑(b.map f) ≤ 𝓝 c :=
  ⟨fun h ↦ by
     -- Write b as an ultrafilter limit of pure ultrafilters, and use
     -- the facts that ultrafilter.extend is a continuous extension of f.
     let b' : Ultrafilter (Ultrafilter α) := b.map pure
     have t : ↑b' ≤ 𝓝 b := ultrafilter_converges_iff.mpr (bind_pure _).symm
     rw [← h]
     have := (continuous_ultrafilter_extend f).tendsto b
     refine le_trans ?_ (le_trans (map_mono t) this)
     change _ ≤ map (Ultrafilter.extend f ∘ pure) ↑b
     rw [ultrafilter_extend_extends]
     exact le_rfl,
   fun h ↦
    let _ : TopologicalSpace α := ⊥
    isDenseInducing_pure.extend_eq_of_tendsto
      (le_trans (map_mono (ultrafilter_comap_pure_nhds _)) h)⟩

end Extension

end Ultrafilter

section PreStoneCech

variable (α : Type u) [TopologicalSpace α]

/-- Auxiliary construction towards the Stone-Čech compactification of a topological space.
It should not be used after the Stone-Čech compactification is constructed. -/
def PreStoneCech : Type u :=
  Quot fun F G : Ultrafilter α ↦ ∃ x, (F : Filter α) ≤ 𝓝 x ∧ (G : Filter α) ≤ 𝓝 x

variable {α}

instance : TopologicalSpace (PreStoneCech α) :=
  inferInstanceAs% (TopologicalSpace <| Quot _)

instance : CompactSpace (PreStoneCech α) :=
  Quot.compactSpace

instance [Inhabited α] : Inhabited (PreStoneCech α) :=
  inferInstanceAs% (Inhabited <| Quot _)

/-- The natural map from α to its pre-Stone-Čech compactification. -/
def preStoneCechUnit (x : α) : PreStoneCech α :=
  Quot.mk _ (pure x : Ultrafilter α)

theorem continuous_preStoneCechUnit : Continuous (preStoneCechUnit : α → PreStoneCech α) :=
  continuous_iff_ultrafilter.mpr fun x g gx ↦ by
    have : (g.map pure).toFilter ≤ 𝓝 g := by
      rw [ultrafilter_converges_iff, ← bind_pure g]
      rfl
    have : (map preStoneCechUnit g : Filter (PreStoneCech α)) ≤ 𝓝 (Quot.mk _ g) :=
      (map_mono this).trans (continuous_quot_mk.tendsto _)
    convert this
    exact Quot.sound ⟨x, pure_le_nhds x, gx⟩

theorem denseRange_preStoneCechUnit : DenseRange (preStoneCechUnit : α → PreStoneCech α) :=
  Quot.mk_surjective.denseRange.comp denseRange_pure continuous_coinduced_rng


section Extension
variable {β : Type v} [TopologicalSpace β] [T2Space β]

theorem preStoneCech_hom_ext {g₁ g₂ : PreStoneCech α → β} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (h : g₁ ∘ preStoneCechUnit = g₂ ∘ preStoneCechUnit) : g₁ = g₂ := by
  apply Continuous.ext_on denseRange_preStoneCechUnit h₁ h₂
  rintro x ⟨x, rfl⟩
  apply congr_fun h x

variable [CompactSpace β]
variable {g : α → β} (hg : Continuous g)
include hg

lemma preStoneCechCompat {F G : Ultrafilter α} {x : α} (hF : ↑F ≤ 𝓝 x) (hG : ↑G ≤ 𝓝 x) :
    Ultrafilter.extend g F = Ultrafilter.extend g G := by
  replace hF := (map_mono hF).trans hg.continuousAt
  replace hG := (map_mono hG).trans hg.continuousAt
  rwa [show Ultrafilter.extend g G = g x by rwa [ultrafilter_extend_eq_iff, G.coe_map],
       ultrafilter_extend_eq_iff, F.coe_map]

/-- The extension of a continuous function from `α` to a compact
  Hausdorff space `β` to the pre-Stone-Čech compactification of `α`. -/
def preStoneCechExtend : PreStoneCech α → β :=
  Quot.lift (Ultrafilter.extend g) fun _ _ ⟨_, hF, hG⟩ ↦ preStoneCechCompat hg hF hG

@[simp]
lemma preStoneCechExtend_extends : preStoneCechExtend hg ∘ preStoneCechUnit = g :=
  ultrafilter_extend_extends g

@[simp]
lemma preStoneCechExtend_preStoneCechUnit (a : α) :
    preStoneCechExtend hg (preStoneCechUnit a) = g a :=
  congr_fun (preStoneCechExtend_extends hg) a

set_option backward.isDefEq.respectTransparency false in
lemma eq_if_preStoneCechUnit_eq {a b : α} (h : preStoneCechUnit a = preStoneCechUnit b) :
    g a = g b := by
  have e := ultrafilter_extend_extends g
  rw [← congrFun e a, ← congrFun e b, Function.comp_apply, Function.comp_apply]
  rw [preStoneCechUnit, preStoneCechUnit, Quot.eq] at h
  generalize (pure a : Ultrafilter α) = F at h
  generalize (pure b : Ultrafilter α) = G at h
  induction h with
  | rel x y a => exact let ⟨a, hx, hy⟩ := a; preStoneCechCompat hg hx hy
  | refl x => rfl
  | symm x y _ h => rw [h]
  | trans x y z _ _ h h' => exact h.trans h'

theorem continuous_preStoneCechExtend : Continuous (preStoneCechExtend hg) :=
  continuous_quot_lift _ (continuous_ultrafilter_extend g)

end Extension

end PreStoneCech

section StoneCech

variable (α : Type u) [TopologicalSpace α]

/-- The Stone-Čech compactification of a topological space. -/
def StoneCech : Type u :=
  T2Quotient (PreStoneCech α)

variable {α}

instance : TopologicalSpace (StoneCech α) :=
  inferInstanceAs% (TopologicalSpace <| T2Quotient _)

instance : T2Space (StoneCech α) :=
  inferInstanceAs% (T2Space <| T2Quotient _)

instance : CompactSpace (StoneCech α) :=
  Quot.compactSpace

instance [Inhabited α] : Inhabited (StoneCech α) :=
  inferInstanceAs% (Inhabited <| Quotient _)

/-- The natural map from α to its Stone-Čech compactification. -/
def stoneCechUnit (x : α) : StoneCech α :=
  T2Quotient.mk (preStoneCechUnit x)

theorem continuous_stoneCechUnit : Continuous (stoneCechUnit : α → StoneCech α) :=
  (T2Quotient.continuous_mk _).comp continuous_preStoneCechUnit

/-- The image of `stoneCechUnit` is dense. (But `stoneCechUnit` need
  not be an embedding, for example if the original space is not Hausdorff.) -/
theorem denseRange_stoneCechUnit : DenseRange (stoneCechUnit : α → StoneCech α) := by
  unfold stoneCechUnit T2Quotient.mk
  have : Function.Surjective (T2Quotient.mk : PreStoneCech α → StoneCech α) := by
    exact Quot.mk_surjective
  exact this.denseRange.comp denseRange_preStoneCechUnit continuous_coinduced_rng

section Extension

variable {β : Type v} [TopologicalSpace β] [T2Space β]
variable {g : α → β} (hg : Continuous g)

theorem stoneCech_hom_ext {g₁ g₂ : StoneCech α → β} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (h : g₁ ∘ stoneCechUnit = g₂ ∘ stoneCechUnit) : g₁ = g₂ := by
  apply h₁.ext_on denseRange_stoneCechUnit h₂
  rintro _ ⟨x, rfl⟩
  exact congr_fun h x

variable [CompactSpace β]

/-- The extension of a continuous function from `α` to a compact
  Hausdorff space `β` to the Stone-Čech compactification of `α`.
  This extension implements the universal property of this compactification. -/
def stoneCechExtend : StoneCech α → β :=
  T2Quotient.lift (continuous_preStoneCechExtend hg)

@[simp]
lemma stoneCechExtend_extends : stoneCechExtend hg ∘ stoneCechUnit = g := by
  ext x
  rw [stoneCechExtend, Function.comp_apply, stoneCechUnit, T2Quotient.lift_mk]
  apply congrFun (preStoneCechExtend_extends hg)

@[simp]
lemma stoneCechExtend_stoneCechUnit (a : α) : stoneCechExtend hg (stoneCechUnit a) = g a :=
  congr_fun (stoneCechExtend_extends hg) a

theorem continuous_stoneCechExtend : Continuous (stoneCechExtend hg) :=
  continuous_coinduced_dom.mpr (continuous_preStoneCechExtend hg)

lemma eq_if_stoneCechUnit_eq {a b : α} {f : α → β} (hcf : Continuous f)
    (h : stoneCechUnit a = stoneCechUnit b) : f a = f b := by
  rw [← congrFun (stoneCechExtend_extends hcf), ← congrFun (stoneCechExtend_extends hcf)]
  exact congrArg (stoneCechExtend hcf) h

end Extension

end StoneCech
