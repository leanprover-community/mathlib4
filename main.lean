import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.KolmogorovExtension4.Projective

open Set MeasureTheory

theorem preimage_proj {ι : Type*} {X : ι → Type*} (I J : Finset ι) [∀ j : J, Decidable (j.1 ∈ I)]
    (hIJ : I ⊆ J) (s : ∀ i : I, Set (X i)) :
    (fun t : (∀ j : J, X j) ↦ fun i : I ↦ t ⟨i, hIJ i.2⟩) ⁻¹' (univ.pi s) =
    (@univ J).pi (fun j ↦ if h : j.1 ∈ I then s ⟨j.1, h⟩ else univ) := by
  ext x; simp
  refine ⟨fun h i hi ↦ ?_, fun h i i_mem ↦ by simpa [i_mem] using h i (hIJ i_mem)⟩
  by_cases i_mem : i ∈ I
  · simp [i_mem, h i i_mem]
  · simp [i_mem]

variable (X : ℕ → Type*) [∀ n, MeasurableSpace (X n)]
variable (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]

theorem isProjectiveMeasureFamily_prod :
    IsProjectiveMeasureFamily (fun S : Finset ℕ ↦ (Measure.pi (fun n : S ↦ μ n))) := by
  intro T S hST
  -- simp only
  refine Measure.pi_eq (fun s ms ↦ ?_)
  rw [Measure.map_apply (measurable_proj₂' (α := X) T S hST) (MeasurableSet.univ_pi ms),
    preimage_proj S T hST, Measure.pi_pi]
  let e : S ≃ {a : T | a.1 ∈ S} :=
    {
      toFun := fun a ↦ ⟨⟨a.1, hST a.2⟩, a.2⟩,
      invFun := fun a ↦ ⟨a.1.1, a.2⟩,
      left_inv := by simp [Function.LeftInverse]
      right_inv := by simp [Function.RightInverse, Function.LeftInverse]
    }
  conv_rhs =>
    change Finset.univ.prod (fun i ↦ ((fun i : S ↦ (μ i) (s i)) ∘ e.invFun) (e i))
    rw [e.prod_comp]
  have : (fun i ↦ (((fun j : S ↦ (μ j) (s j)) ∘ e.invFun) i)) =
      fun i : {a : T | a.1 ∈ S} ↦
      (fun i : T ↦ (μ i) (if h : i.1 ∈ S then s ⟨i, h⟩ else univ)) i := by
    ext i
    have : i.1.1 ∈ S := i.2
    simp [this]
  rw [this, Finset.prod_set_coe (f := fun i : T ↦ (μ i) (if h : i.1 ∈ S then s ⟨i, h⟩ else univ))]
  refine (Finset.prod_subset (Finset.subset_univ _) (fun x _ hx ↦ ?_)).symm
  simp only [mem_setOf_eq, toFinset_setOf, Finset.univ_eq_attach, Finset.mem_filter,
    Finset.mem_attach, true_and] at hx
  simp [hx]


theorem cylinders_nat : cylinders X =
    ⋃ (N) (S) (_ : MeasurableSet S), {cylinder (Finset.range N) S} := by
  ext s; simp
  constructor
  rintro ⟨t, S, mS, rfl⟩
  · use (t.sup id).succ
    use (fun f : ∀ n : Finset.range (t.sup id).succ,
      X n ↦ fun k : t ↦ f ⟨k, t.subset_range_sup_succ k.2⟩) ⁻¹' S
    constructor
    · apply mS.preimage
      apply measurable_proj₂
    · dsimp only [cylinder]
      rw [← preimage_comp]
      rfl
  · rintro ⟨N, S, mS, rfl⟩
    exact ⟨Finset.range N, S, mS, rfl⟩

lemma useful (s : Set (∀ n, X n)) (s_mem : s ∈ cylinders X) :
    ∃ N S, MeasurableSet S ∧ s = cylinder (Finset.range N) S := by
  simpa [cylinders_nat] using s_mem


theorem test (A : ℕ → Set (∀ n, X n)) (A_mem : ∀ n, A n ∈ cylinders X) (A_anti : Antitone A)
    (A_inter : ⋂ n, A n = ∅) :
