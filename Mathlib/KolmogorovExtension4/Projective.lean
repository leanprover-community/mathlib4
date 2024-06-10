import Mathlib.KolmogorovExtension4.Boxes

open Set

namespace MeasureTheory

variable {ι : Type _} {α : ι → Type _}

def IsProjective [Preorder ι] (P : ∀ j : ι, α j) (π : ∀ {i j : ι}, j ≤ i → α i → α j) : Prop :=
  ∀ (i j) (hji : j ≤ i), P j = π hji (P i)

def IsProjectiveMeasureFamily [∀ i, MeasurableSpace (α i)]
    (P : ∀ J : Finset ι, Measure (∀ j : J, α j)) : Prop :=
  IsProjective P
    (fun I _ hJI μ ↦ μ.map fun x : ∀ i : I, α i ↦ fun j ↦ x ⟨j, hJI j.2⟩ :
      ∀ (I J : Finset ι) (_ : J ⊆ I), Measure (∀ i : I, α i) → Measure (∀ j : J, α j))

def IsProjectiveLimit [∀ i, MeasurableSpace (α i)] (μ : Measure (∀ i, α i))
    (P : ∀ J : Finset ι, Measure (∀ j : J, α j)) : Prop :=
  ∀ I : Finset ι, (μ.map fun x : ∀ i, α i ↦ fun i : I ↦ x i) = P I

variable [∀ i, MeasurableSpace (α i)] {P : ∀ J : Finset ι, Measure (∀ j : J, α j)}

theorem IsProjectiveMeasureFamily.empty (hP : IsProjectiveMeasureFamily P) (i : ι)
    [hi : IsEmpty (α i)] {I J : Finset ι} (hIJ : I ⊆ J) (i_mem : i ∈ J) : P I = 0 := by
  ext S mS
  rw [hP J I hIJ]
  simp only
  rw [Measure.map_apply (measurable_proj₂' J I hIJ) mS]
  have : IsEmpty ((j : J) → α j) := by
    rw [← not_nonempty_iff, Classical.nonempty_pi]
    push_neg
    simp_rw [not_nonempty_iff]
    exact ⟨⟨i, i_mem⟩, hi⟩
  have : P J = 0 := (P J).eq_zero_of_isEmpty
  simp [this]

theorem IsProjectiveMeasureFamily.empty' (hP : IsProjectiveMeasureFamily P) (i : ι)
    [hi : IsEmpty (α i)] (I : Finset ι) : P I = 0 := by
  classical
  exact hP.empty i (I.subset_insert i) (I.mem_insert_self i)

theorem IsProjectiveMeasureFamily.congr_cylinder_aux
    (hP : IsProjectiveMeasureFamily P) {I J : Finset ι} {S : Set (∀ i : I, α i)}
    {T : Set (∀ i : J, α i)} (hT : MeasurableSet T) (h_eq : cylinder I S = cylinder J T)
    (hJI : J ⊆ I) :
    P I S = P J T := by
  classical
  by_cases h : Nonempty ((i : ι) → α i)
  · have : S = (fun f : ∀ i : I, α i ↦ fun j : J ↦ f ⟨j, hJI j.prop⟩) ⁻¹' T :=
      eq_of_cylinder_eq_of_subset h_eq hJI
    rw [hP I J hJI, Measure.map_apply _ hT, this]
    rw [measurable_pi_iff]
    intro i
    apply measurable_pi_apply
  · rw [Classical.nonempty_pi] at h
    push_neg at h
    rcases h with ⟨i, hi⟩
    rw [not_nonempty_iff] at hi
    simp [hP.empty' i I, hP.empty' i J]

theorem IsProjectiveMeasureFamily.congr_cylinder
    (hP : IsProjectiveMeasureFamily P) {I J : Finset ι} {S : Set (∀ i : I, α i)}
    {T : Set (∀ i : J, α i)} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (h_eq : cylinder I S = cylinder J T) :
    P I S = P J T := by
  classical
  let U :=
    (fun f : ∀ i : (I ∪ J : Finset ι), α i
        ↦ fun j : I ↦ f ⟨j, Finset.mem_union_left J j.prop⟩) ⁻¹' S ∩
      (fun f ↦ fun j : J ↦ f ⟨j, Finset.mem_union_right I j.prop⟩) ⁻¹' T
  suffices P (I ∪ J) U = P I S ∧ P (I ∪ J) U = P J T from this.1.symm.trans this.2
  constructor
  · have h_eq_union : cylinder I S = cylinder (I ∪ J) U := by
      rw [← inter_cylinder, h_eq, inter_self]
    exact hP.congr_cylinder_aux hS h_eq_union.symm Finset.subset_union_left
  · have h_eq_union : cylinder J T = cylinder (I ∪ J) U := by
      rw [← inter_cylinder, h_eq, inter_self]
    exact hP.congr_cylinder_aux hT h_eq_union.symm Finset.subset_union_right

theorem IsProjectiveMeasureFamily.measure_univ_eq_of_subset (hP : IsProjectiveMeasureFamily P)
    (I J : Finset ι) (hJI : J ⊆ I) : P I univ = P J univ := by
  classical
  have : (univ : Set (∀ i : I, α i)) =
      (fun x : ∀ i : I, α i ↦ fun i : J ↦ x ⟨i, hJI i.2⟩) ⁻¹' (univ : Set (∀ i : J, α i)) :=
    by rw [preimage_univ]
  rw [this, ← Measure.map_apply _ MeasurableSet.univ]
  · rw [hP I J hJI]
  · exact measurable_proj₂' I J hJI

theorem IsProjectiveMeasureFamily.measure_univ_eq (hP : IsProjectiveMeasureFamily P)
    (I J : Finset ι) : P I univ = P J univ := by
  classical rw [← hP.measure_univ_eq_of_subset (I ∪ J) I Finset.subset_union_left, ←
    hP.measure_univ_eq_of_subset (I ∪ J) J Finset.subset_union_right]

theorem IsProjectiveLimit.measure_cylinder {μ : Measure (∀ i, α i)} (h : IsProjectiveLimit μ P)
    (I : Finset ι) {s : Set (∀ i : I, α i)} (hs : MeasurableSet s) : μ (cylinder I s) = P I s := by
  rw [cylinder, ← Measure.map_apply _ hs, h I]
  apply measurable_proj

theorem IsProjectiveLimit.measure_univ_eq {μ : Measure (∀ i, α i)} (hμ : IsProjectiveLimit μ P)
    (I : Finset ι) : μ univ = P I univ := by
  rw [← cylinder_univ I, hμ.measure_cylinder _ MeasurableSet.univ]

theorem IsProjectiveLimit.measure_univ_unique [hι : Nonempty ι] {μ ν : Measure (∀ i, α i)}
    (hμ : IsProjectiveLimit μ P) (hν : IsProjectiveLimit ν P) : μ univ = ν univ := by
  rw [hμ.measure_univ_eq ({hι.some} : Finset ι), hν.measure_univ_eq ({hι.some} : Finset ι)]

theorem isFiniteMeasure_of_isProjectiveLimit [hι : Nonempty ι] {μ : Measure (∀ i, α i)}
    [∀ i, IsFiniteMeasure (P i)] (hμ : IsProjectiveLimit μ P) : IsFiniteMeasure μ := by
  constructor
  rw [hμ.measure_univ_eq ({hι.some} : Finset ι)]
  exact measure_lt_top _ _

theorem isProjectiveLimit_unique [hι : Nonempty ι] {μ ν : Measure (∀ i, α i)}
    [∀ i, IsFiniteMeasure (P i)] (hμ : IsProjectiveLimit μ P) (hν : IsProjectiveLimit ν P) :
    μ = ν := by
  haveI : IsFiniteMeasure μ := isFiniteMeasure_of_isProjectiveLimit hμ
  refine ext_of_generate_finite (cylinders α) generateFrom_cylinders.symm isPiSystem_cylinders
    (fun s hs ↦ ?_) (hμ.measure_univ_unique hν)
  obtain ⟨I, S, hS, rfl⟩ := (mem_cylinders _).mp hs
  rw [hμ.measure_cylinder _ hS, hν.measure_cylinder _ hS]

end MeasureTheory
