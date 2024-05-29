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
