import Mathlib.Tactic.Linarith
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-- This file contains the definition of the Cantor ternary set
as well as some first properties, which will be updated later.


We give a definition by the iteration of to functions T_L and T_R.--/

noncomputable
def T_L (x : ℝ) : ℝ := x/3

noncomputable
def T_R (x : ℝ) : ℝ := (2+x)/3

def preCantorSet : ℕ → Set ℝ
  | 0 => Set.Icc 0 1
  | Nat.succ n => T_L '' preCantorSet n ∪ T_R '' preCantorSet n

def cantorSet := iInf preCantorSet


/--
         First steps towards an equivalence with an alternative definition
         -----------------------------------------------------------------
--/


/- Function which takes n and k as input and gives the union of two closed intervals as output-/

def prePreCantorSetIcc (n k : ℕ) : Set ℝ :=
  Set.Icc ((3*k)/3^n) ((3*k+1)/3^n) ∪ Set.Icc ((3*k+2)/3^n) ((3*k+3)/3^n)

def preCantorSetIcc (n : ℕ) := ⋃ (k : ℕ) (_ : k ≤ 3^(n-1)-1), prePreCantorSetIcc n k

def cantorSetIcc := ⋂ (i : ℕ) (_ : 1 ≤ i), preCantorSetIcc i

def h (n : ℕ) (i : ℕ) (_ : i ≤ n) : Set ℝ := preCantorSetIcc i


/--
         Simple exercises
         ----------------
--/

lemma quarters_in_preCantorSets (n : ℕ) : 1/4 ∈ preCantorSet n ∧ 3/4 ∈ preCantorSet n := by
  induction n with
  | zero =>
    simp only [preCantorSet, Set.mem_Icc, inv_nonneg, Nat.ofNat_nonneg, true_and]
    refine ⟨⟨?_, ?_ ⟩,?_,?_⟩ <;> linarith

  | succ n ih =>
    apply And.intro
    · -- goal: 1 / 4 ∈ preCantorSet n
      exact Or.inl ⟨3/4, ih.2, by unfold T_L; linarith ⟩

    · -- goal: 3 / 4 ∈ preCantorSet n
      exact Or.inr ⟨1/4, ih.1, by unfold T_R; linarith ⟩

lemma quarter_in_preCantorSets (n : ℕ) : 1/4 ∈ preCantorSet n := (quarters_in_preCantorSets n).1

theorem quarter_in_cantorSet : 1/4 ∈ cantorSet := by
  simp only [cantorSet,iInf, Set.sInf_eq_sInter, Set.sInter_range, Set.mem_iInter]
  exact quarter_in_preCantorSets

lemma zero_in_preCantorSets : ∀ n : ℕ, 0 ∈ preCantorSet n := by
  intro n
  induction n with
  | zero =>
    simp [preCantorSet]
  | succ n ih =>
    exact Or.inl ⟨0, ih, by unfold T_L; simp ⟩

theorem zero_in_cantorSet : 0 ∈ cantorSet := by
  simp only [cantorSet, iInf, Set.sInf_eq_sInter, Set.sInter_range, Set.mem_iInter]
  exact zero_in_preCantorSets


/--
         Standard topological facts
         --------------------------
--/

noncomputable def Homeomorph_T_L := Homeomorph.mulLeft₀ (1/3:ℝ) (by norm_num)

noncomputable def Homeomorph_T_R := (Homeomorph.addLeft (2:ℝ)).trans Homeomorph_T_L


--The tenary Cantor set is a subset of [0,1].

lemma cantorSet_subset_UnitInterval : cantorSet ⊆ Set.Icc 0 1 := by
  intro x hx
  simp only [cantorSet, Set.iInf_eq_iInter, Set.mem_iInter] at hx
  exact hx 0


/--The tenary Cantor set inherits the metric and in particular the topology from the reals.-/

instance cantorSet.metricSpace : MetricSpace cantorSet :=
  Subtype.metricSpace


/--The tenary Cantor set is closed -/

lemma cantorSet_IsClosed : IsClosed cantorSet  := by
  apply isClosed_iInter
  intro n
  induction n with
  | zero =>
    exact isClosed_Icc
  | succ n ih =>
    refine IsClosed.union ?_ ?_
    · refine (ClosedEmbedding.closed_iff_image_closed ?succ.refine_1.hf).mp ih
      convert Homeomorph_T_L.closedEmbedding
      ext x
      simp [T_L, Homeomorph_T_L, div_eq_inv_mul]
    · refine (ClosedEmbedding.closed_iff_image_closed ?succ.refine_2.hf).mp ih
      convert  Homeomorph_T_R.closedEmbedding
      ext x
      simp [T_R, Homeomorph_T_R, Homeomorph_T_L, div_eq_inv_mul]


/--The tenary Cantor set is compact.-/

lemma cantorSet_IsCompact : IsCompact cantorSet :=
  isCompact_Icc.of_isClosed_subset cantorSet_IsClosed cantorSet_subset_UnitInterval


/--The tenary Cantor set is a Hausorff space.-/

lemma cantorSet_IsT2 : T2Space cantorSet := by
  infer_instance

/-The tenary Cantor set is metrizble.-/
lemma cantorSet_IsMetrizable : TopologicalSpace.MetrizableSpace cantorSet := by
  infer_instance
