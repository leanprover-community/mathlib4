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
    rw [isOpen_iff_generate_intervals]
    constructor
    use 1
    right
    ext x
    simp
    exact ENat.lt_one_iff_eq_zero.symm
  | succ k =>
    have : {@Nat.cast ENat _ (k + 1)} = (Set.Iio ↑(k + 2)) ∩ (Set.Ioi ↑k) := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi]
      rcases eq_or_ne x ⊤ with h | h
      · cases h
        simp only [not_top_lt, false_and, iff_false]
        apply ENat.top_ne_coe
      · lift x to ℕ using h
        rw [Nat.cast_inj, Nat.cast_lt, Nat.cast_lt]
        omega
    rw [isOpen_iff_generate_intervals, this]
    apply GenerateOpen.inter <;> constructor
    · exact ⟨@Nat.cast ENat _ (k + 2), Or.inr rfl⟩
    · exact ⟨k, Or.inl rfl⟩

theorem lol (s : Set ENat) (h : ⊤ ∉ s) : @IsOpen ENat (Preorder.topology ENat) s := by
  let _ := Preorder.topology ENat
  rw [← Set.biUnion_of_singleton s]
  apply isOpen_biUnion
  intro x hx
  have : x ≠ ⊤ := ne_of_mem_of_not_mem hx h
  lift x to ℕ using this
  exact isOpenSingleton x

theorem lol' (s : Set ENat) (h : ⊤ ∈ s) :
    @IsOpen ENat (Preorder.topology ENat) s ↔ ∃ x, x < ⊤ ∧ Set.Ioi x ⊆ s where
  mp hs := by
    induction hs with
    | basic t ht =>
      rcases ht with ⟨a, h' | h'⟩
      · use a
        rw [h']
        refine ⟨?_, subset_refl _⟩
        rw [h'] at h
        exact h
      · exfalso
        rw [h'] at h
        simp only [Set.mem_setOf_eq, not_top_lt] at h
    | univ => exact ⟨0, by norm_num, Set.subset_univ _⟩
    | inter t u ht hu ht' hu' =>
      rcases ht' (Set.mem_of_mem_inter_left h) with ⟨a, ha⟩
      rcases hu' (Set.mem_of_mem_inter_right h) with ⟨b, hb⟩
      refine ⟨max a b, ?_, ?_⟩
      · apply max_lt
        exact ha.1
        exact hb.1
      · apply Set.subset_inter
        · refine subset_trans ?_ ha.2
          exact Set.Ioi_subset_Ioi (le_max_left _ _)
        · refine subset_trans ?_ hb.2
          exact Set.Ioi_subset_Ioi (le_max_right _ _)
    | sUnion S hS hS' =>
      simp at h
      rcases h with ⟨t, ht1, ht2⟩
      rcases hS' t ht1 ht2 with ⟨a, ha⟩
      use a, ha.1
      apply Set.subset_sUnion_of_subset _ _ ha.2 ht1
  mpr := by
    let _ := Preorder.topology ENat
    have _ : OrderTopology ENat := OrderTopology.mk rfl
    rintro ⟨a, ha⟩
    rw [← Set.inter_union_compl s (Set.Ioi a)]
    apply IsOpen.union
    · rw [Set.inter_eq_self_of_subset_right ha.2, isOpen_iff_generate_intervals]
      constructor
      exact ⟨a, Or.inl rfl⟩
    · apply lol
      simp [h]
      exact ha.1.ne

instance {X : Type} [TopologicalSpace X] [SequentialSpace X] : CompactlyGeneratedSpace.{0} X := by
  rw [compactlyGeneratedSpace_iff]
  refine fun s ↦ ⟨fun hs _ _ _ _ f hf ↦ hs.preimage hf,
    fun h ↦ SequentialSpace.isClosed_of_seq _ fun u p hu hup ↦ ?_⟩
  let _ : TopologicalSpace ENat := Preorder.topology ENat
  have _ : OrderTopology ENat := OrderTopology.mk rfl
  let f : ENat → X := fun n ↦
    match n with
    | some k => u k
    | none => p
  have hf : Continuous f := by
    constructor
    intro s hs
    by_cases hmm : ⊤ ∈ (f ⁻¹' s)
    · rw [lol' _ hmm]
      have : Filter.Tendsto (fun n : ℕ ↦ f n) Filter.atTop (𝓝 p) := by
        simp_rw [f]
        exact hup
      have aux : p ∈ s := by
        rw [show p = f ⊤ by rfl]
        exact hmm
      rw [tendsto_atTop_nhds] at this
      rcases this s aux hs with ⟨N, hN⟩
      use N
      constructor
      · apply Ne.lt_top
        exact (ENat.top_ne_coe _).symm
      · intro x hx
        rcases eq_or_ne x ⊤ with y | z
        · rw [y]
          exact aux
        · lift x to ℕ using z
          apply hN
          simp at hx
          exact hx.le
    exact lol _ hmm
  have : Set.range f = insert p (Set.range u) := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      rcases eq_or_ne n ⊤ with hn | hn
      · rw [hn]
        exact Set.mem_insert _ _
      · lift n to ℕ using hn
        apply Set.mem_insert_of_mem
        use n
        rfl
    · intro h
      simp at h
      rcases h with rfl | h'
      · use ⊤
      · rcases h' with ⟨y, rfl⟩
        use y
        rfl
  rw [show p = f ⊤ by rfl]
  change ⊤ ∈ f ⁻¹' s
  have omg : Filter.Tendsto (fun n ↦ n : ℕ → ENat) Filter.atTop (𝓝 ⊤) := by
    rw [tendsto_atTop_nhds]
    intro U mem_U hU
    rw [lol' _ mem_U] at hU
    rcases hU with ⟨x, hx, hv⟩
    lift x to ℕ using hx.ne
    use x + 1
    intro n hn
    apply hv
    simp only [Set.mem_Ioi, Nat.cast_lt]
    omega
  apply IsClosed.mem_of_tendsto _ omg
  · simp
    use 0
    rintro b -
    exact hu b
  · apply h f hf

theorem IsClosed.isClosedMap_subtype_val {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsClosed s) :
    IsClosedMap (@Subtype.val X s) := hs.closedEmbedding_subtype_val.isClosedMap

theorem compactlyGeneratedSpace_iff_of_t2 {X : Type u} [TopologicalSpace X] [T2Space X] :
    CompactlyGeneratedSpace.{u} X ↔
      (∀ s, IsClosed s ↔ ∀ (K : Set X), IsCompact K → IsClosed (s ∩ K)) := by
  rw [compactlyGeneratedSpace_iff]
  congrm (∀ s, IsClosed s ↔ ?_)
  refine ⟨fun h K hK ↦ ?_, fun h K _ _ _ f hf ↦ ?_⟩
  · rw [Set.inter_comm, ← Subtype.image_preimage_coe]
    refine IsClosed.isClosedMap_subtype_val hK.isClosed _ ?_
    exact @h _ _ (isCompact_iff_compactSpace.1 hK) _ _ continuous_subtype_val
  · rw [← Set.preimage_inter_range]
    exact (h _ (isCompact_range hf)).preimage hf

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
