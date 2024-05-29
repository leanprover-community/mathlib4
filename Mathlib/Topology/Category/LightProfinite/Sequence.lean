import Mathlib.Topology.Compactification.OnePoint
import Mathlib.Topology.Category.LightProfinite.Basic
import Mathlib.Topology.Metrizable.Urysohn

open CategoryTheory Limits Opposite Option

namespace LightProfinite

instance (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    TotallySeparatedSpace (OnePoint X) where
  isTotallySeparated_univ x _ y _ hxy := by
    cases x with
    | none =>
      cases y with
      | none => tauto
      | some val =>
        refine ⟨{some val}ᶜ, {some val}, isOpen_compl_singleton, ?_, ?_, ?_, ?_, ?_⟩
        · refine (OnePoint.isOpen_iff_of_not_mem ?_).mpr (isOpen_discrete _)
          exact (some_ne_none val).symm
        all_goals simp [Set.union_comm]
    | some val =>
      cases y with
      | none =>
        refine ⟨{some val}, {some val}ᶜ, ?_, isOpen_compl_singleton, ?_, ?_, ?_, ?_⟩
        · refine (OnePoint.isOpen_iff_of_not_mem ?_).mpr (isOpen_discrete _)
          exact (some_ne_none val).symm
        all_goals simp
      | some val' =>
        refine ⟨{some val}, {some val}ᶜ, ?_, isOpen_compl_singleton, ?_, ?_, ?_, ?_⟩
        · refine (OnePoint.isOpen_iff_of_not_mem ?_).mpr (isOpen_discrete _)
          exact (some_ne_none val).symm
        all_goals aesop

open TopologicalSpace

instance (X : Type*) [TopologicalSpace X] [c : CompactSpace X] [MetrizableSpace X] :
    SecondCountableTopology X := by
  obtain ⟨_, h⟩ := MetrizableSpace.exists_metric (X := X)
  rw [← h] at c ⊢
  infer_instance

-- variable (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] [Countable X]

-- instance (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] [Countable X] :
--     FirstCountableTopology X := sorry

-- instance (X : Type*) [TopologicalSpace X] [Countable X] [FirstCountableTopology X] :
--     SecondCountableTopology X := by
--   let b : X → Set (Set X) := fun x ↦ (FirstCountableTopology.nhds_generated_countable x).out.choose
--   let B := ⋃ (x : X), b x
--   have hB : IsTopologicalBasis (⋃ (x : X), ((fun f ↦ ⋂₀ f) '' {f | f.Finite ∧ f ⊆ b x})) := by
--     apply IsTopologicalBasis.of_hasBasis_nhds
--     intro x
--     have : nhds x = Filter.generate (b x) :=
--       (FirstCountableTopology.nhds_generated_countable x).out.choose_spec.2
--     constructor
--     intro t
--     rw [this, Filter.mem_generate_iff]
--     constructor
--     · intro ⟨s, hs, hsf, hst⟩
--       refine ⟨⋂₀ s, ⟨?_, ?_⟩, hst⟩
--       · simp only [Set.mem_iUnion]
--         exact ⟨x, s, ⟨hsf, hs⟩, rfl⟩
--       · apply mem_of_mem_nhds
--         rw [this, Filter.sInter_mem hsf]
--         exact fun _ hU ↦ Filter.mem_generate_of_mem (hs hU)
--     · intro ⟨i, ⟨⟨s, hs, his⟩, hx⟩, hit⟩
--       sorry
--       -- intro ⟨i, ⟨⟨s, hs, his⟩, hx⟩, hit⟩
--       -- intro ⟨i, ⟨⟨s, ⟨x', hs⟩, his⟩, hx⟩, hit⟩
--       -- rw [← hs] at his
--       -- obtain ⟨t1, ht1⟩ := his
--       -- refine ⟨t1, ?_, ht1.1.1, ?_⟩
--       -- · sorry
--       -- · rw [← ht1.2] at hit
--       --   exact hit

--   -- refine IsTopologicalBasis.secondCountableTopology (isTopologicalBasis_of_subbasis (s := B) ?_) ?_
--   -- · sorry
--   -- · apply Set.Countable.image
--   --   exact Set.countable_setOf_finite_subset (Set.countable_iUnion fun x ↦
--   --     (FirstCountableTopology.nhds_generated_countable x).out.choose_spec.1)
--   -- have hB : IsTopologicalBasis B := by
--   --   apply IsTopologicalBasis.of_hasBasis_nhds
--   --   intro x
--   --   have : nhds x = Filter.generate (b x) :=
--   --     (FirstCountableTopology.nhds_generated_countable x).out.choose_spec.2
--   --   constructor
--   --   intro t
--   --   rw [this, Filter.mem_generate_iff]
--   --   constructor
--   --   · intro ⟨s, hs, hsf, hst⟩
--   --     refine ⟨⋂₀ s, ⟨?_, ?_⟩, hst⟩
--   --     · simp only [Set.mem_iUnion, B]
--   --       refine ⟨x, ?_⟩
--   --       sorry
--   --     · sorry
--   --   · intro ⟨i, _, _⟩
--   --     sorry
--   --   -- apply isTopologicalBasis_of_isOpen_of_nhds
--   --   -- · intro U ⟨_, ⟨x, rfl⟩, h⟩

--   --   --   sorry
--   --   -- · intro x U hx hU
--   --   --   sorry
--   refine hB.secondCountableTopology ?_
--   apply Set.countable_iUnion
--   intro x
--   apply Set.Countable.image
--   exact Set.countable_setOf_finite_subset
--     (FirstCountableTopology.nhds_generated_countable x).out.choose_spec.1
--   -- <| Set.countable_iUnion fun x ↦
--   --   (FirstCountableTopology.nhds_generated_countable x).out.choose_spec.1

-- example (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] [Countable X] :
--     SecondCountableTopology X := inferInstance

open OnePoint

lemma natUnionInfty_classifies_convergent_sequences {X : Type*} [TopologicalSpace X]
    (f : OnePoint ℕ → X) : Continuous f ↔
      sorry /- the restriction of `f` to `ℕ` is a convergent sequence -/ := sorry

noncomputable def natUnionInftyEmbedding : C(OnePoint ℕ, ℝ) where
  toFun
    | ∞ => 0
    | OnePoint.some n => 1 / (n+1 : ℝ)
  continuous_toFun := by
    rw [continuous_iff_continuousAt]
    rintro (_|n)
    · erw [OnePoint.continuousAt_infty]
      intro s (hs : s ∈ nhds 0)
      rw [Real.isTopologicalBasis_Ioo_rat.mem_nhds_iff] at hs
      obtain ⟨t, ht, zero_mem, hts⟩ := hs
      simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at ht
      obtain ⟨a, b, _, rfl⟩ := ht
      refine ⟨Finset.range (Nat.ceil (1/b)), isClosed_discrete _, ?_, ?_⟩
      · rw [isCompact_iff_finite]
        exact Finset.finite_toSet _
      · change Set.MapsTo (fun (n : ℕ) ↦ 1 / (n+1 : ℝ)) _ _
        intro n hn
        apply hts
        simp only [one_div, Set.mem_Ioo]
        simp only [Set.mem_Ioo] at zero_mem
        constructor
        · exact lt_trans zero_mem.1 Nat.inv_pos_of_nat
        · simp only [one_div, Finset.coe_range, Set.compl_Iio, Set.mem_Ici, Nat.ceil_le,
            ← Rat.cast_le (K := ℝ)] at hn
          rw [inv_lt (by positivity) zero_mem.2, ← Rat.cast_inv]
          exact lt_of_le_of_lt hn (lt_add_one _)
    · erw [continuousAt_coe]
      exact continuous_bot.continuousAt

lemma embedding_natUnionInftyEmbedding : ClosedEmbedding natUnionInftyEmbedding := by
  refine closedEmbedding_of_continuous_injective_closed
    natUnionInftyEmbedding.continuous_toFun ?_ ?_
  · rintro (_|n) (_|m) h
    · rfl
    · simp only [natUnionInftyEmbedding, one_div, ContinuousMap.coe_mk, zero_eq_inv] at h
      rw [eq_comm, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_eq_zero] at h
      simp at h
    · simp only [natUnionInftyEmbedding, one_div, ContinuousMap.coe_mk, inv_eq_zero] at h
      rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_eq_zero] at h
      simp at h
    · simp only [natUnionInftyEmbedding, one_div, ContinuousMap.coe_mk, inv_inj, add_left_inj,
        Nat.cast_inj] at h
      rw [h]
  · intro C hC
    sorry


instance : MetrizableSpace (OnePoint ℕ) := embedding_natUnionInftyEmbedding.metrizableSpace

def NatUnionInfty := of (OnePoint ℕ)

end LightProfinite
