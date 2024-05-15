import KolmogorovExtension4.KolmogorovExtension

open Set

open scoped ENNReal BigOperators

lemma Finset.prod_mem_not_mem_of_eq_one_if_not_mem {α β : Type*} [CommMonoid β]
    {f g : α → β} {I J : Finset α} (hJI : J ⊆ I)
    (h1 : ∀ (x : α) (_ : x ∈ J), f x = g x) (h2 : ∀ (x : α) (_ : x ∉ J), f x = 1) :
    (∏ i : { x // x ∈ I }, f i) = ∏ i : { x // x ∈ J }, g i := by
  simp only [univ_eq_attach, Finset.prod_attach]
  classical
  refine (Finset.prod_subset_one_on_sdiff hJI ?_ ?_).symm
  · simp only [mem_sdiff, and_imp]
    exact fun x _ hx ↦ h2 x hx
  · exact fun x hx ↦ (h1 x hx).symm

variable {ι : Type*} {α : ι → Type*}

section Projections

namespace Function

variable (α)
/-- projection to an index set I -/
def projI (I : Set ι) : ((i : ι) → α i) → ((i : I) → α i) :=
  fun (f : (i : ι) → α i) (i : I) ↦ f i

variable {α}

end Function


namespace Set

def boxI (I : Set ι) (t : (i : ι) → Set (α i)) : Set ((i : I) → α i) :=
  (univ : Set I).pi (fun (i : I) ↦ t i)

@[simp]
lemma mem_boxI {I : Set ι} (t : (i : ι) → Set (α i)) (x : (i : I) → α i) :
    x ∈ boxI I t ↔ ∀ (i) (hi : i ∈ I), x ⟨i, hi⟩ ∈ t i := by
  simp only [boxI, mem_pi, mem_univ, forall_true_left, Subtype.forall]

@[simp]
lemma mem_boxI' {I : Finset ι} (t : (i : ι) → Set (α i)) (x : (i : I) → α i) :
    x ∈ boxI I t ↔ ∀ (i) (hi : i ∈ I), x ⟨i, hi⟩ ∈ t i := by
  simp only [boxI, mem_pi, mem_univ, forall_true_left, Subtype.forall]

lemma boxI_univ (I : Set ι) :
    (univ : Set ((i : I) → α i)) = boxI I (fun (i : ι) ↦ (univ : Set (α i))) := by
  simp only [boxI, pi_univ]

lemma projI_mem_boxI {I : Set ι} (t : (i : ι) → Set (α i)) (x : (i : ι) → α i) :
    Function.projI α I x ∈ boxI I t ↔ ∀ i ∈ I, x i ∈ t i := by
  simp only [Function.projI, boxI, mem_pi, mem_univ, forall_true_left, Subtype.forall]

def boxesI (I : Set ι) (C : (i : ι) → Set (Set (α i))) : Set (Set ((i : I) → α i)) :=
  univ.pi '' univ.pi fun i ↦ C i

@[simp]
theorem mem_boxesI {I : Set ι} (s : Set ((i : I) → α i)) (C : (i : ι) → Set (Set (α i)))
    (hC : ∀ i : ι, univ ∈ C i) :
    s ∈ boxesI I C ↔ ∃ (t : (i : ι) → Set (α i)), s = boxI I t ∧ ∀ i, t i ∈ C i := by
  rw [boxesI]
  simp only [mem_image, mem_pi, mem_univ, forall_true_left, Subtype.forall]
  constructor
  · rintro ⟨t', hx1, rfl⟩
    classical
    use fun (i : ι) ↦ if h : i ∈ I then t' ⟨i, h⟩ else (univ : Set (α i))
    simp only [boxI, Subtype.coe_prop, dite_true, true_and]
    intro i
    by_cases hi : i ∈ I
    · simp only [hi, dite_true, hx1]
    · simp only [hi, dite_false, hC i]
  · rintro ⟨t, ⟨ht1, ht2⟩⟩
    rw [ht1, boxI]
    exact ⟨fun (i : I) ↦ t i, fun a _ ↦ ht2 a, rfl⟩

lemma preimage_boxI {I : Set ι} (t : (i : ι) → Set (α i)) :
    (fun (f : (i : ι) → α i) (i : I) ↦ f i)⁻¹' (boxI I t) = pi I t := by
  ext x
  simp only [mem_preimage, mem_boxI, mem_pi]

lemma preimage_boxI' [DecidableEq ι] {J I : Finset ι} (hJI : J ⊆ I)
    (t : (i : ι) → Set (α i)) :
    (fun (f : (i : I) → α i) (i : J) ↦ f ⟨i, hJI i.prop⟩)⁻¹' (boxI J t)
      = boxI I (fun (i : ι) ↦ if i ∈ J then t i else (univ : Set (α i))) := by
  ext y
  simp only [mem_preimage, mem_boxI', mem_ite_univ_right]
  exact ⟨fun h i _ hiJ ↦ h i hiJ, fun h i hiJ ↦ h i (hJI hiJ) hiJ⟩

end Set

end Projections


section IsPiSystem

theorem isPiSystem_boxesI (I : Set ι) (C : (i : ι) → Set (Set (α i)))
    (hC1 : ∀ i, IsPiSystem (C i)) :
    IsPiSystem (boxesI I C) :=
  IsPiSystem.pi (fun (i : I) ↦ hC1 i)

theorem isPiSystem_boxesI_of_measurable [∀ i, MeasurableSpace (α i)] (I : Set ι) :
    IsPiSystem (boxesI I (fun (i : ι) ↦ {s : Set (α i) | MeasurableSet s})) :=
  IsPiSystem.pi (fun _ ↦ MeasurableSpace.isPiSystem_measurableSet)

end IsPiSystem


section IndependentFamily

variable [∀ i, MeasurableSpace (α i)]

namespace MeasureTheory

theorem generateFrom_boxesI (I : Finset ι) :
  (@MeasurableSpace.pi I (fun (i : I) ↦ α i) _)
    = MeasurableSpace.generateFrom
      (boxesI I (fun (i : ι) ↦ {s : Set (α i) | MeasurableSet s})) :=
  generateFrom_pi.symm

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

/-- Product measure on a finite subset of indices. -/
noncomputable def Measure.subset_pi (P : ∀ i, Measure (α i)) (I : Finset ι) :
    Measure ((i : I) → α i) :=
  Measure.pi (fun (i : I) ↦ P i)

theorem Measure.subset_pi_eval (I : Finset ι) (P : ∀ i : ι, Measure (α i))
    [∀ i : ι, IsProbabilityMeasure (P i)] (A : (i : ι) → Set (α i)) :
    Measure.subset_pi P I (univ.pi (fun i : I ↦ A i)) = ∏ i : I, P i (A i) := by
  simp only [subset_pi, Measure.pi_pi, Finset.univ_eq_attach]

theorem Measure.subset_pi_eval_boxI (I : Finset ι) (P : ∀ i : ι, Measure (α i))
    [∀ i : ι, IsProbabilityMeasure (P i)] (t : (i : ι) → Set (α i)) :
    Measure.subset_pi P I (boxI I t) = ∏ i : I, P i (t i) := by
  simp only [subset_pi, boxI._eq_1, Finset.coe_sort_coe, Measure.pi_pi, Finset.univ_eq_attach]

theorem Measure.subset_pi_eval_boxI' [DecidableEq ι] (I J : Finset ι) (hJI : J ⊆ I)
    (P : ∀ i, Measure (α i)) [∀ i : ι, IsProbabilityMeasure (P i)] (t : (i : ι) → Set (α i)) :
    Measure.subset_pi P I
        (boxI I (fun (i : ι) ↦ if i ∈ J then t i else (univ : Set (α i))))
      = ∏ i : J, P i (t i) := by
  rw [Measure.subset_pi_eval_boxI]
  let g := fun i ↦ P i (t i)
  let f := fun i ↦ P i (if i ∈ J then t i else (univ : Set (α i)))
  have h1 : ∀ (x : ι), x ∈ J → f x = g x := by
    intros x hx
    simp only [f, dite_eq_ite, hx, ite_true]
  have h2 : ∀ (x : ι), ¬x ∈ J → f x = 1 := by
    intros x hx
    simp only [f, dite_eq_ite, hx, ite_false, measure_univ]
  exact Finset.prod_mem_not_mem_of_eq_one_if_not_mem hJI h1 h2

/-- A product of probability measures is a probability measure -/
instance Measure.subset_pi_of_ProbabilityMeasure (P : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (P i)] (I : Finset ι) :
    IsProbabilityMeasure (Measure.subset_pi P I) := by
  constructor
  rw [← Set.pi_univ, Measure.subset_pi_eval I P (fun i : ι ↦ univ)]
  simp only [Finset.univ_eq_attach, measure_univ, Finset.prod_const_one]

lemma box_measurable (I : Finset ι) {s : Set ((i : I) → α i)}
    (hs : s ∈ boxesI I (fun (i : ι) ↦ {s : Set (α i) | MeasurableSet s})) :
    MeasurableSet s := by
  rcases hs with ⟨t, ⟨h1, rfl⟩⟩
  have ht : ∀ i, MeasurableSet (t i) := by
    simpa only [Finset.coe_sort_coe, pi, mem_univ, mem_setOf_eq, forall_true_left, Subtype.forall]
      using h1
  exact MeasurableSet.pi countable_univ (fun i _ ↦ ht i)

theorem proj' (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)]
    (J I : Finset ι) (hJI : J ⊆ I) :
    Measure.subset_pi P J
      = Measure.map ((fun (f : (i : I) → α i) (i : J) ↦ f ⟨i, hJI i.prop⟩))
        (Measure.subset_pi P I) := by
  let C := (fun (i : ι) ↦ {s : Set (α i) | MeasurableSet s})
  have hu : ∀ i, univ ∈ C i := by
    simp only [C, mem_setOf_eq, MeasurableSet.univ, implies_true]
  apply MeasureTheory.ext_of_generate_finite _ (generateFrom_boxesI J)
  · exact @isPiSystem_boxesI_of_measurable ι α _ J
  · intros s hs
    rcases (mem_boxesI s C hu).1 hs with ⟨t, ⟨rfl, _⟩⟩
    rw [Measure.map_apply (measurable_proj₂' I J hJI) (box_measurable J hs)]
    classical
    change Measure.subset_pi P J (boxI J t) = Measure.subset_pi P I
      ((fun f (i : J) ↦ f ⟨i, hJI i.prop⟩) ⁻¹' boxI J t)
    rw [Measure.subset_pi_eval_boxI, preimage_boxI', Measure.subset_pi_eval_boxI' _ _ hJI]
  · rw [Measure.map_apply (measurable_proj₂' I J hJI) (box_measurable J _)]
    simp only [measure_univ, preimage_univ]
    change univ ∈ boxesI J C
    rw [mem_boxesI univ C hu]
    use fun (i : ι) ↦ (univ : Set (α i)), boxI_univ (J : Set ι)

theorem product_isProjective (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] :
    IsProjectiveMeasureFamily (Measure.subset_pi P) :=
  fun I J ↦ proj' P J I

noncomputable def independentFamily [∀ i, PseudoEMetricSpace (α i)]
    [∀ i, BorelSpace (α i)] [∀ i, SecondCountableTopology (α i)]
    [∀ i, CompleteSpace (α i)] [∀ i, Nonempty (α i)]
    (P : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)] :
    Measure (∀ i, α i) :=
  projectiveLimitWithWeakestHypotheses (Measure.subset_pi P) (product_isProjective P)

end MeasureTheory

end IndependentFamily
