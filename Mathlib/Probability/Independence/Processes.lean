/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Probability.Independence.Basic

/-!
# Independence of stochastic processes

Two stochastic processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ are independent if
for all $s_1, ..., s_p \in S$ and $t_1, ..., t_q \in T$ the two families
$(X_{s_1}, ..., X_{s_p})$ and $(Y_{t_1}, ..., Y_{t_q})$ are independent. We prove an analogous
condition for a family of stochastic processes.

## Tags

independence, stochastic processes
-/

open MeasureTheory MeasurableSpace

namespace ProbabilityTheory

variable {S Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α Ω} {P : Measure α}

/-- Two stochastic processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ are independent if
for all $s_1, ..., s_p \in S$ and $t_1, ..., t_q \in T$ the two families
$(X_{s_1}, ..., X_{s_p})$ and $(Y_{t_1}, ..., Y_{t_q})$ are independent. -/
lemma IndepFun.indepFun_processes {T : Type*} {𝓧 : S → Type*} {𝓨 : T → Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [∀ j, MeasurableSpace (𝓨 j)] {X : (i : S) → Ω → 𝓧 i}
    {Y : (j : T) → Ω → 𝓨 j} (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (h : ∀ (I : Finset S) (J : Finset T),
      IndepFun (fun ω (i : I) ↦ X i ω) (fun ω (j : J) ↦ Y j ω) κ P) [IsZeroOrMarkovKernel κ] :
    IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) κ P := by
  -- The π-system obtained by pulling back the π-system of square cylinders by `X`.
  let πX := {s : Set Ω | ∃ t ∈ squareCylinders (fun i ↦ {s : Set (𝓧 i) | MeasurableSet s}),
      (fun ω i ↦ X i ω) ⁻¹' t = s}
  have πX_pi : IsPiSystem πX :=
    IsPiSystem.comap (isPiSystem_squareCylinders (fun _ ↦ isPiSystem_measurableSet) (by simp)) _
  have πX_gen : (MeasurableSpace.pi.comap fun ω i ↦ X i ω) = generateFrom πX := by
    rw [generateFrom_squareCylinders.symm, MeasurableSpace.comap_generateFrom]
    rfl
  -- The π-system obtained by pulling back the π-system of square cylinders by `Y`.
  let πY := {s : Set Ω | ∃ t ∈ squareCylinders (fun j ↦ {s : Set (𝓨 j) | MeasurableSet s}),
      (fun ω j ↦ Y j ω) ⁻¹' t = s}
  have πY_pi : IsPiSystem πY :=
    IsPiSystem.comap (isPiSystem_squareCylinders (fun _ ↦ isPiSystem_measurableSet) (by simp)) _
  have πY_gen : (MeasurableSpace.pi.comap fun ω j ↦ Y j ω) = generateFrom πY := by
    rw [generateFrom_squareCylinders.symm, MeasurableSpace.comap_generateFrom]
    rfl
  -- To prove independence, we prove independence of the generating π-systems.
  refine IndepSets.indep (measurable_pi_iff.2 hX).comap_le (measurable_pi_iff.2 hY).comap_le
     πX_pi πY_pi πX_gen πY_gen ?_
  rintro - - ⟨-, ⟨I, s, hs, rfl⟩, rfl⟩ ⟨-, ⟨J, t, ht, rfl⟩, rfl⟩
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, forall_const] at hs ht
  have : (fun ω i ↦ X i ω) ⁻¹' .pi I s ∩ (fun ω j ↦ Y j ω) ⁻¹' .pi J t =
      (fun ω (i : I) ↦ X i ω) ⁻¹' .pi (SetLike.coe Finset.univ) (fun i ↦ s i) ∩
      (fun ω (j : J) ↦ Y j ω) ⁻¹' .pi (SetLike.coe Finset.univ) (fun j ↦ t j) := by
    ext; simp
  have h1 : MeasurableSet <| .pi (SetLike.coe Finset.univ) (fun (i : I) ↦ s i) :=
    .pi (Finset.countable_toSet _) (fun _ _ ↦ hs _)
  have h2 : MeasurableSet <| .pi (SetLike.coe Finset.univ) (fun (j : J) ↦ t j) :=
    .pi (Finset.countable_toSet _) (fun _ _ ↦ ht _)
  filter_upwards [(h I J).measure_inter_preimage_eq_mul _ _ h1 h2] with ω hω
  rw [this, hω]
  congr 2 <;> ext <;> simp

/-- Stochastic processes $((X^s_t)_{t \in T_s})_{s \in S}$ are mutually independent if
for all $s_1, ..., s_n$ and all $t^{s_i}_1, ..., t^{s_i}_{p_i}^ the families
$(X^{s_1}_{t^{s_1}_1}, ..., X^{s_1}_{t^{s_1}_{p_1}}), ...,
(X^{s_n}_{t^{s_n}_1}, ..., X^{s_n}_{t^{s_n}_{p_n}})$ are mutually independent. -/
lemma iIndepFun.iIndepFun_processes {T : S → Type*} {𝓧 : (i : S) → (j : T i) → Type*}
    [∀ i j, MeasurableSpace (𝓧 i j)] {X : (i : S) → (j : T i) → Ω → 𝓧 i j}
    (hX : ∀ i j, Measurable (X i j))
    (h : ∀ (I : Finset S) (J : (i : I) → Finset (T i)),
      iIndepFun (fun i ω (j : J i) ↦ X i j ω) κ P) :
    iIndepFun (fun i ω j ↦ X i j ω) κ P := by
  obtain rfl | hμ := eq_or_ne P 0
  · simp
  obtain ⟨η, η_eq, hη⟩ : ∃ (η : Kernel α Ω), κ =ᵐ[P] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel (h ∅ fun _ ↦ ∅).ae_isProbabilityMeasure hμ
  apply iIndepFun.congr (Filter.EventuallyEq.symm η_eq)
  let π i := {s : Set Ω | ∃ t ∈ squareCylinders (fun j ↦ {s : Set (𝓧 i j) | MeasurableSet s}),
    (fun ω j ↦ X i j ω) ⁻¹' t = s}
  have π_pi i : IsPiSystem (π i) :=
    (isPiSystem_squareCylinders (fun _ ↦ isPiSystem_measurableSet) (by simp)).comap _
  have π_gen i : (MeasurableSpace.pi.comap fun ω j ↦ X i j ω) = generateFrom (π i) := by
    rw [generateFrom_squareCylinders.symm, MeasurableSpace.comap_generateFrom]
    rfl
  refine iIndepSets.iIndep _ (fun i ↦ (measurable_pi_iff.2 (hX i)).comap_le) π π_pi π_gen
    fun I s hs ↦ ?_
  simp only [squareCylinders, Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, forall_const,
    ↓existsAndEq, and_true, π] at hs
  choose! J t ht hs using hs
  simp_rw [Set.iInter₂_congr (fun i hi ↦ (hs i hi).symm),
    I.prod_congr rfl (fun i hi ↦ congrArg _ (hs i hi).symm)]
  have : (⋂ i ∈ I, (fun ω j ↦ X i j ω) ⁻¹' .pi (J i) (t i)) =
      (⋂ i ∈ (.univ : Finset I), (fun ω (j : J i) ↦ X i j ω) ⁻¹'
        .pi (SetLike.coe Finset.univ) (fun j ↦ t i j)) := by
    ext; simp
  have h' (i : I) (hi : i ∈ Finset.univ) :
      MeasurableSet <| (SetLike.coe Finset.univ).pi fun (j : J i) ↦ t i j :=
    .pi (Finset.countable_toSet _) (fun _ _ ↦ ht _ i.2 _)
  filter_upwards [(h I (fun i ↦ J i)).measure_inter_preimage_eq_mul _ _ .univ h',
    η_eq] with ω hω hη
  rw [this, ← hη, hω, ← I.prod_coe_sort]
  congrm ∏ _, κ ω ?_
  ext; simp

end Kernel

variable {P : Measure Ω}

/-- Two stochastic processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ are independent if
for all $s_1, ..., s_p \in S$ and $t_1, ..., t_q \in T$ the two families
$(X_{s_1}, ..., X_{s_p})$ and $(Y_{t_1}, ..., Y_{t_q})$ are independent. -/
lemma IndepFun.indepFun_processes {T : Type*} {𝓧 : S → Type*} {𝓨 : T → Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [∀ j, MeasurableSpace (𝓨 j)] {X : (i : S) → Ω → 𝓧 i}
    {Y : (j : T) → Ω → 𝓨 j} (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (h : ∀ (I : Finset S) (J : Finset T),
      IndepFun (fun ω (i : I) ↦ X i ω) (fun ω (j : J) ↦ Y j ω) P) [IsProbabilityMeasure P] :
    IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P :=
  Kernel.IndepFun.indepFun_processes hX hY h

/-- Stochastic processes $((X^s_t)_{t \in T_s})_{s \in S}$ are mutually independent if
for all $s_1, ..., s_n$ and all $t^{s_i}_1, ..., t^{s_i}_{p_i}^ the families
$(X^{s_1}_{t^{s_1}_1}, ..., X^{s_1}_{t^{s_1}_{p_1}}), ...,
(X^{s_n}_{t^{s_n}_1}, ..., X^{s_n}_{t^{s_n}_{p_n}})$ are mutually independent. -/
lemma iIndepFun.iIndepFun_processes {T : S → Type*} {𝓧 : (i : S) → (j : T i) → Type*}
    [∀ i j, MeasurableSpace (𝓧 i j)] {X : (i : S) → (j : T i) → Ω → 𝓧 i j}
    (hX : ∀ i j, Measurable (X i j))
    (h : ∀ (I : Finset S) (J : (i : I) → Finset (T i)),
      iIndepFun (fun i ω (j : J i) ↦ X i j ω) P) :
    iIndepFun (fun i ω j ↦ X i j ω) P :=
  Kernel.iIndepFun.iIndepFun_processes hX h

end ProbabilityTheory
