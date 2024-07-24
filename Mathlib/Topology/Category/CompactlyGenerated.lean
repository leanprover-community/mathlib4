/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.CategoryTheory.Elementwise
/-!

# Compactly generated topological spaces

This file defines the category of compactly generated topological spaces. These are spaces `X` such
that a map `f : X → Y` is continuous whenever the composition `S → X → Y` is continuous for all
compact Hausdorff spaces `S` mapping continuously to `X`.

## TODO

* `CompactlyGenerated` is a reflective subcategory of `TopCat`.
* `CompactlyGenerated` is cartesian closed.
* Every first-countable space is `u`-compactly generated for every universe `u`.
-/

attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike

universe u w

open CategoryTheory Topology TopologicalSpace

/--
The compactly generated topology on a topological space `X`. This is the finest topology
which makes all maps from compact Hausdorff spaces to `X`, which are continuous for the original
topology, continuous.

Note: this definition should be used with an explicit universe parameter `u` for the size of the
compact Hausdorff spaces mapping to `X`.
-/
def TopologicalSpace.compactlyGenerated (X : Type w) [TopologicalSpace X] : TopologicalSpace X :=
  let f : (Σ (i : (S : CompHaus.{u}) × C(S, X)), i.fst) → X := fun ⟨⟨_, i⟩, s⟩ ↦ i s
  coinduced f inferInstance

lemma continuous_from_compactlyGenerated {X : Type w} [TopologicalSpace X]
    {Y : Type*} [t : TopologicalSpace Y] (f : X → Y)
      (h : ∀ (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) :
        Continuous[compactlyGenerated.{u} X, t] f := by
  rw [continuous_coinduced_dom]
  continuity

/--
A topological space `X` is compactly generated if its topology is finer than (and thus equal to)
the compactly generated topology, i.e. it is coinduced by the continuous maps from compact
Hausdorff spaces to `X`.
-/
class CompactlyGeneratedSpace (X : Type w) [t : TopologicalSpace X] : Prop where
  /-- The topology of `X` is finer than the compactly generated topology. -/
  le_compactlyGenerated : t ≤ compactlyGenerated.{u} X

lemma eq_compactlyGenerated {X : Type w} [t : TopologicalSpace X] [CompactlyGeneratedSpace.{u} X] :
    t = compactlyGenerated.{u} X := by
  apply le_antisymm
  · exact CompactlyGeneratedSpace.le_compactlyGenerated
  · simp only [compactlyGenerated, ← continuous_iff_coinduced_le, continuous_sigma_iff,
      Sigma.forall]
    exact fun S f ↦ f.2

instance (X : Type w) [t : TopologicalSpace X] [DiscreteTopology X] :
    CompactlyGeneratedSpace.{u} X where
  le_compactlyGenerated := by
    rw [DiscreteTopology.eq_bot (t := t)]
    exact bot_le

lemma continuous_from_compactlyGeneratedSpace {X : Type w} [TopologicalSpace X]
    [CompactlyGeneratedSpace.{u} X] {Y : Type*} [TopologicalSpace Y] (f : X → Y)
      (h : ∀ (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) : Continuous f := by
  apply continuous_le_dom CompactlyGeneratedSpace.le_compactlyGenerated
  exact continuous_from_compactlyGenerated f h

lemma compactlyGeneratedSpace_of_continuous_maps {X : Type w} [t : TopologicalSpace X]
    (h : ∀ {Y : Type w} [tY : TopologicalSpace Y] (f : X → Y),
      (∀ (S : CompHaus.{u}) (g : C(S, X)), Continuous (f ∘ g)) → Continuous f) :
        CompactlyGeneratedSpace.{u} X where
  le_compactlyGenerated := by
    suffices Continuous[t, compactlyGenerated.{u} X] (id : X → X) by
      rwa [← continuous_id_iff_le]
    apply h (tY := compactlyGenerated.{u} X)
    intro S g
    let f : (Σ (i : (T : CompHaus.{u}) × C(T, X)), i.fst) → X := fun ⟨⟨_, i⟩, s⟩ ↦ i s
    suffices ∀ (i : (T : CompHaus.{u}) × C(T, X)),
      Continuous[inferInstance, compactlyGenerated X] (fun (a : i.fst) ↦ f ⟨i, a⟩) from this ⟨S, g⟩
    rw [← @continuous_sigma_iff]
    apply continuous_coinduced_rng

theorem compactlyGeneratedSpace_iff {X : Type u} [TopologicalSpace X] :
    CompactlyGeneratedSpace.{u} X ↔
      (∀ s, IsClosed s ↔
        (∀ {K : Type u} [TopologicalSpace K], [CompactSpace K] → [T2Space K] →
          ∀ (f : K → X), Continuous f → IsClosed (f ⁻¹' s))) where
  mp := by
    refine fun _ s ↦ ⟨fun hs _ _ _ _ f hf ↦ hs.preimage hf, fun h ↦ ?_⟩
    rw [eq_compactlyGenerated (X := X), TopologicalSpace.compactlyGenerated, isClosed_coinduced,
      isClosed_sigma_iff]
    exact fun ⟨_, f⟩ ↦ h f f.continuous
  mpr := by
    refine fun h1 ↦ compactlyGeneratedSpace_of_continuous_maps fun f h2 ↦
      continuous_iff_isClosed.2 fun t ht ↦ (h1 _).2 ?_
    intro K _ _ _ g hg
    exact ht.preimage (h2 (CompHaus.of K) { toFun := g, continuous_toFun := hg })

theorem isOpenSingleton (n : ℕ) : @IsOpen ENat (Preorder.topology ENat) {↑n} := by
  let _ := Preorder.topology ENat
  have _ : OrderTopology ENat := OrderTopology.mk rfl
  cases n with
  | zero =>
    constructor
    refine ⟨1, Or.inr ?_⟩
    ext x
    simp only [CharP.cast_eq_zero, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact ENat.lt_one_iff_eq_zero.symm
  | succ k =>
    have : {@Nat.cast ENat _ (k + 1)} = (Set.Iio ↑(k + 2)) ∩ (Set.Ioi ↑k) := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi]
      rcases eq_or_ne x ⊤ with h | h
      · cases h
        simp only [not_top_lt, false_and, iff_false]
        exact ENat.top_ne_coe _
      · lift x to ℕ using h
        rw [Nat.cast_inj, Nat.cast_lt, Nat.cast_lt]
        omega
    rw [this]
    apply GenerateOpen.inter <;> constructor
    · exact ⟨@Nat.cast ENat _ (k + 2), Or.inr rfl⟩
    · exact ⟨k, Or.inl rfl⟩

theorem isOpen_top_not_mem (s : Set ENat) (h : ⊤ ∉ s) :
    @IsOpen ENat (Preorder.topology ENat) s := by
  let _ := Preorder.topology ENat
  rw [← Set.biUnion_of_singleton s]
  refine isOpen_biUnion fun x hx ↦ ?_
  lift x to ℕ using ne_of_mem_of_not_mem hx h
  exact isOpenSingleton x

theorem ENat.coe_max (a b : ℕ) : @Nat.cast ℕ∞ _ (max a b) = max ↑a ↑b := by
  apply eq_max <;> try rw [Nat.cast_le]
  · exact le_max_left _ _
  · exact le_max_right _ _
  · intro d h1 h2
    rcases max_choice a b with h | h <;> rwa [h]

theorem isOpen_iff_top_mem (s : Set ENat) (top_mem : ⊤ ∈ s) :
    @IsOpen ENat (Preorder.topology ENat) s ↔ ∃ x : ℕ, Set.Ioi ↑x ⊆ s where
  mp hs := by
    induction hs with
    | basic t ht =>
      rcases ht with ⟨a, rfl | rfl⟩
      · simp only [Set.mem_setOf_eq] at top_mem
        lift a to ℕ using top_mem.ne
        exact ⟨a, subset_refl _⟩
      · simp at top_mem
    | univ => exact ⟨0, Set.subset_univ _⟩
    | inter t u _ _ ht hu =>
      rcases ht (Set.mem_of_mem_inter_left top_mem) with ⟨a, ha⟩
      rcases hu (Set.mem_of_mem_inter_right top_mem) with ⟨b, hb⟩
      refine ⟨max a b, ?_⟩
      rw [ENat.coe_max]
      apply Set.subset_inter
      · exact subset_trans (Set.Ioi_subset_Ioi (le_max_left _ _)) ha
      · exact subset_trans (Set.Ioi_subset_Ioi (le_max_right _ _)) hb
    | sUnion S _ hS' =>
      rcases top_mem with ⟨t, ht1, ht2⟩
      rcases hS' t ht1 ht2 with ⟨a, ha⟩
      exact ⟨a, Set.subset_sUnion_of_subset _ _ ha ht1⟩
  mpr := by
    let _ := Preorder.topology ENat
    rintro ⟨a, ha⟩
    rw [← Set.inter_union_compl s (Set.Ioi a)]
    apply IsOpen.union
    · rw [Set.inter_eq_self_of_subset_right ha]
      constructor
      exact ⟨a, Or.inl rfl⟩
    · apply isOpen_top_not_mem
      simp [top_mem]

theorem ENat.tendsto_coe_atTop :
    Filter.Tendsto (@Nat.cast ENat _) Filter.atTop (@nhds _ (Preorder.topology ENat) ⊤) := by
  let _ := Preorder.topology ENat
  rw [tendsto_atTop_nhds]
  intro U mem_U hU
  rw [isOpen_iff_top_mem _ mem_U] at hU
  rcases hU with ⟨x, hU⟩
  refine ⟨x + 1, fun n hn ↦ hU ?_⟩
  simp only [Set.mem_Ioi, Nat.cast_lt]
  omega

def compSequence {X : Type*} [TopologicalSpace X]
    (f : ℕ → X) (x : X) : ENat → X := fun n ↦
  match n with
  | some k => f k
  | none => x

theorem continuous_compSequence {X : Type*} [TopologicalSpace X]
    (f : ℕ → X) (x : X) (h : Filter.Tendsto f Filter.atTop (𝓝 x)) :
    @Continuous _ _ (Preorder.topology ENat) _ (compSequence f x) := by
  let _ := Preorder.topology ENat
  constructor
  intro s hs
  by_cases htop : ⊤ ∈ (compSequence f x ⁻¹' s)
  · rw [isOpen_iff_top_mem _ htop]
    rcases tendsto_atTop_nhds.1 h s htop hs with ⟨N, hN⟩
    refine ⟨N, fun y hy ↦ ?_⟩
    rcases eq_or_ne y ⊤ with rfl | y_ne_top
    · exact htop
    · lift y to ℕ using y_ne_top
      exact hN _ (by simpa using hy : N < y).le
  exact isOpen_top_not_mem _ htop

instance {X : Type u} [TopologicalSpace X] [SequentialSpace X] : CompactlyGeneratedSpace.{w} X := by
  refine compactlyGeneratedSpace_of_continuous_maps fun f h ↦
    continuous_iff_isClosed.2 fun s hs ↦ SequentialSpace.isClosed_of_seq _ fun u p hu hup ↦ ?_
  let _ : TopologicalSpace ENat := Preorder.topology ENat
  have : OrderTopology ENat := OrderTopology.mk rfl
  let g : C(ULift.{w} ENat, X) :=
    { toFun := (compSequence u p) ∘ ULift.down,
      continuous_toFun := (continuous_compSequence u p hup).comp continuous_uLift_down }
  change ⊤ ∈ (f ∘ g) ⁻¹' s
  apply IsClosed.mem_of_tendsto _ ((continuous_uLift_up.tendsto ⊤).comp ENat.tendsto_coe_atTop)
  · simp only [Set.mem_preimage, Filter.eventually_atTop, ge_iff_le]
    exact ⟨0, fun b _ ↦ hu b⟩
  · have : CompactSpace (ULift.{w} ENat) := ULift.closedEmbedding_down.compactSpace
    exact hs.preimage <| h (CompHaus.of (ULift.{w} ENat)) g

theorem IsClosed.isClosedMap_subtype_val {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsClosed s) : IsClosedMap (@Subtype.val X s) :=
  hs.closedEmbedding_subtype_val.isClosedMap

theorem compactlyGeneratedSpace_iff_of_t2 {X : Type u} [TopologicalSpace X] [T2Space X] :
    CompactlyGeneratedSpace.{u} X ↔
      (∀ s, IsClosed s ↔ ∀ (K : Set X), IsCompact K → IsClosed (s ∩ K)) where
  mp _ s := by
    refine ⟨fun hs K hK ↦ hs.inter hK.isClosed, fun h ↦ ?_⟩
    rw [eq_compactlyGenerated (X := X), TopologicalSpace.compactlyGenerated, isClosed_coinduced,
      isClosed_sigma_iff]
    rintro ⟨K, f⟩
    change IsClosed (f ⁻¹' s)
    rw [← Set.preimage_inter_range]
    exact (h _ (isCompact_range f.continuous)).preimage f.continuous
  mpr h1 := by
    refine compactlyGeneratedSpace_of_continuous_maps fun f h2 ↦
      continuous_iff_isClosed.2 fun s hs ↦ (h1 _).2 fun K hK ↦ ?_
    rw [Set.inter_comm, ← Subtype.image_preimage_coe]
    apply hK.isClosed.isClosedMap_subtype_val
    rw [← Set.preimage_comp]
    apply hs.preimage
    have : CompactSpace ↑K := isCompact_iff_compactSpace.1 hK
    exact h2 (CompHaus.of ↑K) { toFun := Subtype.val, continuous_toFun := continuous_subtype_val }

instance {X : Type u} [TopologicalSpace X] [WeaklyLocallyCompactSpace X] [T2Space X] :
    CompactlyGeneratedSpace.{u} X := by
  refine compactlyGeneratedSpace_iff_of_t2.2 fun s ↦
    ⟨fun hs K hK ↦ hs.inter hK.isClosed, fun h ↦ ?_⟩
  rw [isClosed_iff_forall_filter]
  intro x ℱ hℱ₁ hℱ₂ hℱ₃
  rcases exists_compact_mem_nhds x with ⟨K, hK, K_mem⟩
  exact Set.mem_of_mem_inter_left <| isClosed_iff_forall_filter.1 (h _ hK) x ℱ hℱ₁
    (Filter.inf_principal ▸ le_inf hℱ₂ (le_trans hℱ₃ <| Filter.le_principal_iff.2 K_mem)) hℱ₃

/-- The type of `u`-compactly generated `w`-small topological spaces. -/
structure CompactlyGenerated where
  /-- The underlying topological space of an object of `CompactlyGenerated`. -/
  toTop : TopCat.{w}
  /-- The underlying topological space is compactly generated. -/
  [is_compactly_generated : CompactlyGeneratedSpace.{u} toTop]

namespace CompactlyGenerated

instance : Inhabited CompactlyGenerated.{u, w} :=
  ⟨{ toTop := { α := ULift (Fin 37) } }⟩

instance : CoeSort CompactlyGenerated Type* :=
  ⟨fun X => X.toTop⟩

attribute [instance] is_compactly_generated

instance : Category.{w, w+1} CompactlyGenerated.{u, w} :=
  InducedCategory.category toTop

instance : ConcreteCategory.{w} CompactlyGenerated.{u, w} :=
  InducedCategory.concreteCategory _

variable (X : Type w) [TopologicalSpace X] [CompactlyGeneratedSpace.{u} X]

/-- Constructor for objects of the category `CompactlyGenerated`. -/
def of : CompactlyGenerated.{u, w} where
  toTop := TopCat.of X
  is_compactly_generated := ‹_›

/-- The fully faithful embedding of `CompactlyGenerated` in `TopCat`. -/
@[simps!]
def compactlyGeneratedToTop : CompactlyGenerated.{u, w} ⥤ TopCat.{w} :=
  inducedFunctor _

/-- `compactlyGeneratedToTop` is fully faithful. -/
def fullyFaithfulCompactlyGeneratedToTop : compactlyGeneratedToTop.{u, w}.FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : compactlyGeneratedToTop.{u, w}.Full := fullyFaithfulCompactlyGeneratedToTop.full

instance : compactlyGeneratedToTop.{u, w}.Faithful := fullyFaithfulCompactlyGeneratedToTop.faithful

/-- Construct an isomorphism from a homeomorphism. -/
@[simps hom inv]
def isoOfHomeo {X Y : CompactlyGenerated.{u, w}} (f : X ≃ₜ Y) : X ≅ Y where
  hom := ⟨f, f.continuous⟩
  inv := ⟨f.symm, f.symm.continuous⟩
  hom_inv_id := by
    ext x
    exact f.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact f.apply_symm_apply x

/-- Construct a homeomorphism from an isomorphism. -/
@[simps]
def homeoOfIso {X Y : CompactlyGenerated.{u, w}} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := f.hom.continuous
  continuous_invFun := f.inv.continuous

/-- The equivalence between isomorphisms in `CompactlyGenerated` and homeomorphisms
of topological spaces. -/
@[simps]
def isoEquivHomeo {X Y : CompactlyGenerated.{u, w}} : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    rfl

end CompactlyGenerated
