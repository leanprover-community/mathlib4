/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.Probability.Independence.Basic

/-!
# Independence of stochastic processes

We prove that a stochastic process $(X_s)_{s \in S}$ is independent from a random variable $Y$ if
for all $s_1, ..., s_p \in S$ the family $(X_{s_1}, ..., X_{s_p})$ is independent from $Y$.

We prove that two stochastic processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ are independent if
for all $s_1, ..., s_p \in S$ and $t_1, ..., t_q \in T$ the two families
$(X_{s_1}, ..., X_{s_p})$ and $(Y_{t_1}, ..., Y_{t_q})$ are independent.
We prove an analogous condition for a family of stochastic processes.

## Tags

independence, stochastic processes
-/

public section

open MeasureTheory MeasurableSpace Set

namespace ProbabilityTheory

variable {S Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α Ω} {P : Measure α}

/-- If `X` is a process independent from `Y` and for all `i`, `X' i` is almost everywhere equal
to `X i`, then `X'` is also independent from `Y`. This implies that independence results about
measurable processes should generally also hold
for processes whose marginals are only aemeasurable. -/
lemma IndepFun.process_congr {𝓧 : S → Type*} {𝓨 : Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X X' : (i : S) → Ω → 𝓧 i}
    {Y : Ω → 𝓨} (h1 : IndepFun (fun ω i ↦ X i ω) Y κ P) (h2 : ∀ i, ∀ᵐ a ∂P, X i =ᵐ[κ a] X' i) :
    IndepFun (fun ω i ↦ X' i ω) Y κ P := by
  rintro - - ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  have := h1 ((fun ω i ↦ X i ω) ⁻¹' s) (Y ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  obtain ⟨I, u, hI, rfl⟩ := hs.eq_preimage_restrict_countable
  have aux (f : (i : S) → Ω → 𝓧 i) : (fun ω i ↦ f i ω) ⁻¹' (I.restrict ⁻¹' u) =
      (fun ω (i : I) ↦ f i ω) ⁻¹' u := rfl
  simp_rw [aux] at *
  have _ : Countable I := hI.to_subtype
  have h : ∀ᵐ a ∂P, (fun ω (i : I) ↦ X i ω) =ᵐ[κ a] (fun ω (i : I) ↦ X' i ω) := by
    filter_upwards [ae_all_iff.2 fun (i : I) ↦ h2 i] with
      a (ha : ∀ (i : I), ∀ᵐ ω ∂κ a, X i ω = X' i ω)
    filter_upwards [ae_all_iff.2 ha] with ω hω using by simp [hω]
  filter_upwards [this, h] with a ha1 ha2
  refine .trans (measure_congr (ae_eq_set_inter (ha2.symm.preimage _) .rfl)) (ha1.trans ?_)
  congr 1
  exact measure_congr (ha2.preimage _)


/-- A stochastic process $(X_s)_{s \in S}$ is independent from a random variable $Y$ if
for all $s_1, ..., s_p \in S$ the family $(X_{s_1}, ..., X_{s_p})$ is independent from $Y$. -/
lemma IndepFun.process_indepFun {𝓧 : S → Type*} {𝓨 : Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X : (i : S) → Ω → 𝓧 i}
    {Y : Ω → 𝓨} (hX : ∀ i, Measurable (X i)) (hY : Measurable Y)
    (h : ∀ (I : Finset S),
      IndepFun (fun ω (i : I) ↦ X i ω) Y κ P) [IsZeroOrMarkovKernel κ] :
    IndepFun (fun ω i ↦ X i ω) Y κ P := by
  -- The π-system obtained by pulling back the π-system of square cylinders by `X`.
  let πX := {s : Set Ω | ∃ t ∈ squareCylinders (fun i ↦ {s : Set (𝓧 i) | MeasurableSet s}),
      (fun ω i ↦ X i ω) ⁻¹' t = s}
  have πX_pi : IsPiSystem πX :=
    IsPiSystem.comap (isPiSystem_squareCylinders (fun _ ↦ isPiSystem_measurableSet) (by simp)) _
  have πX_gen : (MeasurableSpace.pi.comap fun ω i ↦ X i ω) = generateFrom πX := by
    rw [generateFrom_squareCylinders.symm, MeasurableSpace.comap_generateFrom]
    rfl
  -- To prove independence, we prove independence of the generating π-system with the `σ`-alebra.
  refine IndepSets.indep (measurable_pi_iff.2 hX).comap_le hY.comap_le
    πX_pi (@isPiSystem_measurableSet Ω (.comap Y inferInstance)) πX_gen
    (@generateFrom_measurableSet Ω (.comap Y inferInstance)).symm ?_
  rintro - - ⟨-, ⟨I, s, hs, rfl⟩, rfl⟩ ⟨t, ht, rfl⟩
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, forall_const] at hs
  have : (fun ω i ↦ X i ω) ⁻¹' .pi I s =
      (fun ω (i : I) ↦ X i ω) ⁻¹' .pi (SetLike.coe Finset.univ) (fun i ↦ s i)
       := by
    ext; simp
  have h1 : MeasurableSet <| .pi (SetLike.coe Finset.univ) (fun (i : I) ↦ s i) :=
    .pi (Finset.countable_toSet _) (fun _ _ ↦ hs _)
  filter_upwards [(h I).measure_inter_preimage_eq_mul _ _ h1 ht] with ω hω
  rw [this, hω]

/-- A stochastic process $(X_s)_{s \in S}$ is independent from a random variable $Y$ if
for all $s_1, ..., s_p \in S$ the family $(X_{s_1}, ..., X_{s_p})$ is independent from $Y$. -/
lemma IndepFun.process_indepFun₀ {𝓧 : S → Type*} {𝓨 : Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X : (i : S) → Ω → 𝓧 i}
    {Y : Ω → 𝓨} (hX : ∀ i, AEMeasurable (X i) (κ ∘ₘ P)) (hY : ∀ᵐ a ∂P, AEMeasurable Y (κ a))
    (h : ∀ (I : Finset S), IndepFun (fun ω (i : I) ↦ X i ω) Y κ P) [IsZeroOrMarkovKernel κ] :
    IndepFun (fun ω i ↦ X i ω) Y κ P := by
  refine .congr' ?_ .rfl (by filter_upwards [hY] with a ha; exact ha.ae_eq_mk.symm)
  apply process_congr (X := fun i ↦ (hX i).mk (X i))
  · refine IndepFun.process_indepFun (fun i ↦ (hX i).measurable_mk) hY
      fun I ↦ process_congr (X := fun (i : I) ↦ X i) (h I) (fun i ↦ ?_)
    exact Measure.ae_ae_of_ae_comp (hX i).ae_eq_mk
  exact fun i ↦ Measure.ae_ae_of_ae_comp (hX i).ae_eq_mk.symm

/-- A random variable $X$ is independent from a stochastic process $(Y_s)_{s \in S}$  if
for all $s_1, ..., s_p \in S$ the variable $Y$ is independent from the family
$(X_{s_1}, ..., X_{s_p})$. -/
lemma IndepFun.indepFun_process {𝓧 : Type*} {𝓨 : S → Type*}
    [MeasurableSpace 𝓧] [∀ i, MeasurableSpace (𝓨 i)] {X : Ω → 𝓧}
    {Y : (i : S) → Ω → 𝓨 i} (hX : Measurable X) (hY : ∀ i, Measurable (Y i))
    (h : ∀ (I : Finset S),
      IndepFun X (fun ω (i : I) ↦ Y i ω) κ P) [IsZeroOrMarkovKernel κ] :
    IndepFun X (fun ω i ↦ Y i ω) κ P :=
  (IndepFun.process_indepFun hY hX (fun I ↦ (h I).symm)).symm

/-- Two stochastic processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ are independent if
for all $s_1, ..., s_p \in S$ and $t_1, ..., t_q \in T$ the two families
$(X_{s_1}, ..., X_{s_p})$ and $(Y_{t_1}, ..., Y_{t_q})$ are independent. -/
lemma IndepFun.process_indepFun_process {T : Type*} {𝓧 : S → Type*} {𝓨 : T → Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [∀ j, MeasurableSpace (𝓨 j)] {X : (i : S) → Ω → 𝓧 i}
    {Y : (j : T) → Ω → 𝓨 j} (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (h : ∀ (I : Finset S) (J : Finset T),
      IndepFun (fun ω (i : I) ↦ X i ω) (fun ω (j : J) ↦ Y j ω) κ P) [IsZeroOrMarkovKernel κ] :
    IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) κ P := by
  refine IndepFun.process_indepFun hX (measurable_pi_lambda _ hY) fun I ↦ ?_
  exact IndepFun.indepFun_process (measurable_pi_lambda _ fun _ ↦ hX _) hY fun J ↦ h I J

/-- Stochastic processes $((X^s_t)_{t \in T_s})_{s \in S}$ are mutually independent if
for all $s_1, ..., s_n$ and all $t^{s_i}_1, ..., t^{s_i}_{p_i}$ the families
$(X^{s_1}_{t^{s_1}_1}, ..., X^{s_1}_{t^{s_1}_{p_1}}), ...,
(X^{s_n}_{t^{s_n}_1}, ..., X^{s_n}_{t^{s_n}_{p_n}})$ are mutually independent. -/
lemma iIndepFun.iIndepFun_process {T : S → Type*} {𝓧 : (i : S) → (j : T i) → Type*}
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


lemma lol' {𝓧 : S → Type*} {𝓨 : Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X X' : (i : S) → Ω → 𝓧 i}
    {Y : Ω → 𝓨} (h1 : (fun ω i ↦ X i ω) ⟂ᵢ[P] Y) (h2 : ∀ i, X i =ᵐ[P] X' i) :
    (fun ω i ↦ X' i ω) ⟂ᵢ[P] Y := by
  apply Kernel.lol h1
  simpa

/-- A stochastic process $(X_s)_{s \in S}$ is independent from a random variable $Y$ if
for all $s_1, ..., s_p \in S$ the family $(X_{s_1}, ..., X_{s_p})$ is independent from $Y$. -/
lemma IndepFun.process_indepFun {𝓧 : S → Type*} {𝓨 : Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X : (i : S) → Ω → 𝓧 i}
    {Y : Ω → 𝓨} (hX : ∀ i, Measurable (X i)) (hY : AEMeasurable Y P)
    (h : ∀ (I : Finset S),
      IndepFun (fun ω (i : I) ↦ X i ω) Y P) [IsZeroOrProbabilityMeasure P] :
    IndepFun (fun ω i ↦ X i ω) Y P := by
  suffices (fun ω i ↦ X i ω) ⟂ᵢ[P] (hY.mk Y) from
    this.congr .rfl hY.ae_eq_mk.symm
  exact Kernel.IndepFun.process_indepFun hX hY.measurable_mk (fun I ↦ (h I).congr .rfl hY.ae_eq_mk)

/-- A stochastic process $(X_s)_{s \in S}$ is independent from a random variable $Y$ if
for all $s_1, ..., s_p \in S$ the family $(X_{s_1}, ..., X_{s_p})$ is independent from $Y$. -/
lemma IndepFun.process_indepFun₀ {𝓧 : S → Type*} {𝓨 : Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X : (i : S) → Ω → 𝓧 i}
    {Y : Ω → 𝓨} (hX : ∀ i, AEMeasurable (X i) P) (hY : AEMeasurable Y P)
    (h : ∀ (I : Finset S),
      IndepFun (fun ω (i : I) ↦ X i ω) Y P) [IsZeroOrProbabilityMeasure P] :
    IndepFun (fun ω i ↦ X i ω) Y P := by
  suffices (fun ω i ↦ (hX i).mk (X i) ω) ⟂ᵢ[P] (hY.mk Y) by
    apply lol' (X := fun i ↦ (hX i).mk (X i))
    · exact this.congr .rfl hY.ae_eq_mk.symm
    · exact fun i ↦ (hX i).ae_eq_mk.symm
  have (I : Finset S) : (fun ω (i : I) ↦ (hX i).mk (X i) ω) ⟂ᵢ[P] (hY.mk Y) := by
    apply lol' (X := fun (i : I) ↦ X i)
    · exact (h I).congr .rfl hY.ae_eq_mk
    · exact fun i ↦ (hX i).ae_eq_mk
  exact Kernel.IndepFun.process_indepFun (fun i ↦ (hX i).measurable_mk) hY.measurable_mk this

/-- A random variable $X$ is independent from a stochastic process $(Y_s)_{s \in S}$  if
for all $s_1, ..., s_p \in S$ the variable $Y$ is independent from the family
$(X_{s_1}, ..., X_{s_p})$. -/
lemma IndepFun.indepFun_process {𝓧 : Type*} {𝓨 : S → Type*}
    [MeasurableSpace 𝓧] [∀ i, MeasurableSpace (𝓨 i)] {X : Ω → 𝓧}
    {Y : (i : S) → Ω → 𝓨 i} (hX : AEMeasurable X P) (hY : ∀ i, Measurable (Y i))
    (h : ∀ (I : Finset S),
      IndepFun X (fun ω (i : I) ↦ Y i ω) P) [IsZeroOrProbabilityMeasure P] :
    IndepFun X (fun ω i ↦ Y i ω) P := by
  suffices (hX.mk X) ⟂ᵢ[P] (fun ω i ↦ Y i ω) from
    this.congr hX.ae_eq_mk.symm .rfl
  exact Kernel.IndepFun.indepFun_process hX.measurable_mk hY (fun I ↦ (h I).congr hX.ae_eq_mk .rfl)

/-- Two stochastic processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ are independent if
for all $s_1, ..., s_p \in S$ and $t_1, ..., t_q \in T$ the two families
$(X_{s_1}, ..., X_{s_p})$ and $(Y_{t_1}, ..., Y_{t_q})$ are independent. -/
lemma IndepFun.process_indepFun_process {T : Type*} {𝓧 : S → Type*} {𝓨 : T → Type*}
    [∀ i, MeasurableSpace (𝓧 i)] [∀ j, MeasurableSpace (𝓨 j)] {X : (i : S) → Ω → 𝓧 i}
    {Y : (j : T) → Ω → 𝓨 j} (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (h : ∀ (I : Finset S) (J : Finset T),
      IndepFun (fun ω (i : I) ↦ X i ω) (fun ω (j : J) ↦ Y j ω) P) [IsZeroOrProbabilityMeasure P] :
    IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P :=
  Kernel.IndepFun.process_indepFun_process hX hY h

/-- Stochastic processes $((X^s_t)_{t \in T_s})_{s \in S}$ are mutually independent if
for all $s_1, ..., s_n$ and all $t^{s_i}_1, ..., t^{s_i}_{p_i}$ the families
$(X^{s_1}_{t^{s_1}_1}, ..., X^{s_1}_{t^{s_1}_{p_1}}), ...,
(X^{s_n}_{t^{s_n}_1}, ..., X^{s_n}_{t^{s_n}_{p_n}})$ are mutually independent. -/
lemma iIndepFun.iIndepFun_process {T : S → Type*} {𝓧 : (i : S) → (j : T i) → Type*}
    [∀ i j, MeasurableSpace (𝓧 i j)] {X : (i : S) → (j : T i) → Ω → 𝓧 i j}
    (hX : ∀ i j, Measurable (X i j))
    (h : ∀ (I : Finset S) (J : (i : I) → Finset (T i)), iIndepFun (fun i ω (j : J i) ↦ X i j ω) P) :
    iIndepFun (fun i ω j ↦ X i j ω) P :=
  Kernel.iIndepFun.iIndepFun_process hX h

end ProbabilityTheory
