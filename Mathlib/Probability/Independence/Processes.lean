/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Probability.Independence.Kernel

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {S Ω α : Type*} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} {κ : Kernel α Ω}
  {P : Measure α}

lemma test {T : Type*} {𝓧 : S → Type*} {𝓨 : T → Type*} [∀ i, MeasurableSpace (𝓧 i)]
    [∀ j, MeasurableSpace (𝓨 j)] {X : (i : S) → Ω → 𝓧 i} {Y : (j : T) → Ω → 𝓨 j}
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (h : ∀ (I : Finset S) (J : Finset T),
      IndepFun (fun ω (i : I) ↦ X i ω) (fun ω (j : J) ↦ Y j ω) κ P) [IsZeroOrMarkovKernel κ] :
    IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) κ P := by
  let πSβ := MeasureTheory.squareCylinders (fun i ↦ {s : Set (𝓧 i) | MeasurableSet s})
  let πS := { s : Set Ω | ∃ t ∈ πSβ, (fun ω i => X i ω) ⁻¹' t = s }
  have hπS_pi : IsPiSystem πS := by
    refine IsPiSystem.comap (isPiSystem_squareCylinders ?_ ?_) _
    · exact fun i ↦ MeasurableSpace.isPiSystem_measurableSet
    · simp
  have hπS_gen : (MeasurableSpace.pi.comap fun a i => X i a) = .generateFrom πS := by
    rw [generateFrom_squareCylinders.symm, MeasurableSpace.comap_generateFrom]
    congr
  let πTβ := squareCylinders (fun j ↦ {s : Set (𝓨 j) | MeasurableSet s})
  let πT := { s : Set Ω | ∃ t ∈ πTβ, (fun a j => Y j a) ⁻¹' t = s }
  have hπT_pi : IsPiSystem πT := by
    refine IsPiSystem.comap (isPiSystem_squareCylinders ?_ ?_) _
    · exact fun i ↦ MeasurableSpace.isPiSystem_measurableSet
    · simp
  have hπT_gen : (MeasurableSpace.pi.comap fun a j => Y j a) = .generateFrom πT := by
    rw [generateFrom_squareCylinders.symm, MeasurableSpace.comap_generateFrom]
    congr
  -- To prove independence, we prove independence of the generating π-systems.
  refine IndepSets.indep (Measurable.comap_le (measurable_pi_iff.mpr fun i => hX i))
    (Measurable.comap_le (measurable_pi_iff.mpr fun i => hY i)) hπS_pi hπT_pi hπS_gen hπT_gen
    ?_
  rintro - - ⟨s, ⟨sets_s, hs1, hs2, rfl⟩, rfl⟩ ⟨t, ⟨sets_t, ht1, ht2, rfl⟩, rfl⟩
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, forall_const] at hs2 ht2
  have : (fun ω i ↦ X i ω) ⁻¹' .pi sets_s hs1 ∩ (fun a j ↦ Y j a) ⁻¹' .pi sets_t ht1 =
      (fun ω (i : sets_s) ↦ X i ω) ⁻¹' .pi (SetLike.coe Finset.univ) (fun i ↦ hs1 i) ∩
      (fun a (j : sets_t) ↦ Y j a) ⁻¹' .pi (SetLike.coe Finset.univ) (fun j ↦ ht1 j) := by
    ext; simp
  have h1 : MeasurableSet[MeasurableSpace.comap (fun ω (i : sets_s) ↦ X i ω) .pi]
      ((fun ω (i : sets_s) ↦ X i ω) ⁻¹' .pi (SetLike.coe Finset.univ) (fun i ↦ hs1 i)) := by
    apply MeasurableSet.preimage
    · exact MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ ↦ hs2 _)
    · exact comap_measurable _
  have h2 : MeasurableSet[MeasurableSpace.comap (fun ω (j : sets_t) ↦ Y j ω) .pi]
      ((fun ω (j : sets_t) ↦ Y j ω) ⁻¹' .pi (SetLike.coe Finset.univ) (fun j ↦ ht1 j)) := by
    apply MeasurableSet.preimage
    · exact MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ ↦ ht2 _)
    · exact comap_measurable _
  filter_upwards [(h sets_s sets_t).meas_inter h1 h2] with ω hω
  rw [this, hω]
  congr 2
  · ext; simp
  · ext; simp

lemma test' {ι : Type*} {κ : ι → Type*} {𝓧 : (i : ι) → (j : κ i) → Type*}
    [∀ i j, MeasurableSpace (𝓧 i j)] {X : (i : ι) → (j : κ i) → Ω → 𝓧 i j}
    (hX : ∀ i j, Measurable (X i j))
    (h : ∀ (S : Finset ι) (T : (i : S) → Finset (κ i)),
      iIndepFun (fun i ω (j : T i) ↦ X i j ω) P) [IsProbabilityMeasure P] :
    iIndepFun (fun i ω j ↦ X i j ω) P := by
  let πsys (i : ι) := squareCylinders (fun j ↦ {s : Set (𝓧 i j) | MeasurableSet s})
  let πsys' i := {s : Set Ω | ∃ t ∈ πsys i, (fun ω j ↦ X i j ω) ⁻¹' t = s}
  have πsys'_pi i : IsPiSystem (πsys' i) := by
    refine IsPiSystem.comap (isPiSystem_squareCylinders ?_ ?_) _
    · exact fun i ↦ MeasurableSpace.isPiSystem_measurableSet
    · simp
  have πsys'_gen i : (MeasurableSpace.pi.comap fun ω j ↦ X i j ω) = .generateFrom (πsys' i) := by
    rw [generateFrom_squareCylinders.symm, MeasurableSpace.comap_generateFrom]
    congr
  refine iIndepSets.iIndep (fun i ↦ (Measurable.comap_le (measurable_pi_iff.mpr fun j => hX i j)))
    πsys' πsys'_pi πsys'_gen ((iIndepSets_iff _ _).2 ?_)
  intro S f hf
  simp only [squareCylinders, Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, forall_const,
    ↓existsAndEq, and_true, πsys', πsys] at hf
  choose! T s hs hf using hf
  rw [Set.iInter₂_congr (fun i hi ↦ (hf i hi).symm),
    S.prod_congr rfl (fun i hi ↦ congrArg P (hf i hi).symm)]
  have : (⋂ i ∈ S, (fun ω j ↦ X i j ω) ⁻¹' (T i).toSet.pi (s i)) =
      (⋂ i ∈ (univ : Finset S), (fun ω (j : T i) ↦ X i j ω) ⁻¹' univ.toSet.pi (fun j ↦ s i j)) := by
    ext; simp
  rw [this, (h S (fun i ↦ T i)).measure_inter_preimage_eq_mul, ← S.prod_coe_sort]
  · congrm ∏ _, P ?_
    ext; simp
  · exact fun i _ ↦ .pi (Finset.countable_toSet _) (fun _ _ ↦ hs _ i.2 _)
