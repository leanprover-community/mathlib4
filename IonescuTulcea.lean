import Mathlib.KolmogorovExtension4.Transition
import Mathlib.KolmogorovExtension4.Boxes
import Mathlib.KolmogorovExtension4.Projective
import Mathlib.Probability.Kernel.MeasureCompProd

open MeasureTheory ProbabilityTheory Set

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
variable (κ : (k : ℕ) → kernel ((transitionGraph X).node k) ((transitionGraph X).path k (k + 1)))
variable [∀ k, IsMarkovKernel (κ k)]

noncomputable def family (μ : Measure ((transitionGraph X).node 0)) [IsProbabilityMeasure μ] :
  (S : Finset ℕ) → Measure ((k : S) → X k) := fun S ↦
  ((μ ⊗ₘ (MeasurableSpaceGraph.transition κ).ker 0 (S.sup id + 1)).map
  ((transitionGraph X).el 0 (S.sup id + 1) (Nat.succ_pos _))).map
  (fun x (i : S) ↦ x ⟨i.1, mem_Iic.2 (le_trans (Finset.le_sup (f := id) i.2) (Nat.le_succ _))⟩)

variable (μ : Measure ((transitionGraph X).node 0)) [IsProbabilityMeasure μ]

theorem map_compProd {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (κ : kernel X Y) {f : Y → Z} (mf : Measurable f) :
    (μ ⊗ₘ κ).map (Prod.map id f) = μ ⊗ₘ (kernel.map κ f mf) := by sorry

theorem proj_family : IsProjectiveMeasureFamily (family κ μ) := by
  intro S T hTS
  have aux : Ioc 0 (T.sup id + 1) ⊆ Ioc 0 (S.sup id + 1) := by
    intro i
    simp only [mem_Ioc, and_imp]
    refine fun h1 h2 ↦ ⟨h1, ?_⟩
    linarith [Finset.sup_mono (f := id) hTS]
  simp only [family]
  let M := transitionGraph X
  have : M.el 0 (S.sup id + 1) (Nat.succ_pos _) =
      (M.el 0 (T.sup id + 1) (Nat.succ_pos _)) ∘
      (Prod.map id (fun (x : M.path 0 (S.sup id + 1)) i ↦ x ⟨i.1, aux i.2⟩)) := by sorry
  rw [Measure.map_map, Measure]

theorem test
    (μ : Measure ((transitionGraph X).node 0)) [IsProbabilityMeasure μ] :
    ∃ ν : Measure ((k : ℕ) → X k), ∀ k : ℕ, (hk : 0 < k) →
    ν.map (fun x (i : Iic k) ↦ x i) =
    (μ ⊗ₘ (MeasurableSpaceGraph.transition κ).ker 0 k).map ((transitionGraph X).el 0 k hk) := by sorry

theorem test' :
    ∃ ν : kernel ((transitionGraph X).node 0) ((k : Ioi 0) → X k), ∀ k : ℕ, (hk : 0 < k) →
    kernel.map ν
      (fun x (i : Ioc 0 k) ↦ x ⟨i.1, Ioc_subset_Ioi_self i.2⟩
        : ((k : Ioi 0) → X k) → (transitionGraph X).path 0 k)
      (measurable_proj₂ _ _ Ioc_subset_Ioi_self) =
    (MeasurableSpaceGraph.transition κ).ker 0 k := by sorry
