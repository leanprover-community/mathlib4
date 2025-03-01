import Mathlib


variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {ι : Type*} (b : Basis ι K V)
variable (μ : ι → K) (f : Module.End K V) (H : ∀ i, f.HasEigenvector (μ i) (b i))

include H in
lemma Module.End.eigenspace_eq_comap_repr (l : K) : f.eigenspace l =
    (Finsupp.supported K _ { j | μ j = l }).comap b.repr := by
  classical
  let W := (Finsupp.supported K _ { j | μ j ≠ l }).comap b.repr
  have := (f.eigenspaces_iSupIndep l).mono_right (b := W) ?_
  · apply le_antisymm
    · intro v hv
      let p : V →ₗ[K] W := b.constr K fun i ↦ if h : μ i = l then 0 else ⟨b i, by
          simp [W, Finsupp.mem_supported, Finsupp.support_single_ne_zero, h]⟩
      have hp₁ (j) (h : μ j = l) : p (b j) = 0 := by simp [-Basis.constr_apply_fintype, p, h]
      have hp₂ (j) (h : μ j ≠ l) : (p (b j)).1 = b j := by simp [-Basis.constr_apply_fintype, p, h]
      have hp : ⊤ ≤ (f.eigenspace l).comap (1 - W.subtype.comp p) := by
        rw [← b.span_eq, Submodule.span_le, Set.range_subset_iff]
        intro i
        by_cases hi : μ i = l
        · simp [(H _).apply_eq_smul, hp₁ _ hi, hi]
        · simp [(H _).apply_eq_smul, hp₂ _ hi]
      have : (p v).1 = 0 :=
        Submodule.disjoint_def.mp this _ (by simpa using sub_mem hv (@hp v trivial)) (p v).2
      have hp : ⊤ ≤ ((Finsupp.supported K _ { j | μ j = l }).comap b.repr).comap
          (1 - W.subtype.comp p) := by
        rw [← b.span_eq, Submodule.span_le, Set.range_subset_iff]
        intro i j
        by_cases hi : μ i = l
        · simp +contextual [(H _).apply_eq_smul, hp₁ _ hi, ← hi, Finsupp.single_apply]
        · simp [(H _).apply_eq_smul, hp₂ _ hi]
      simpa [this] using @hp v trivial
    · have : (Finsupp.supported K _ { j | μ j = l }).comap b.repr =
        Submodule.span K (b '' { j | μ j = l }) := Submodule.ext fun _ ↦ b.mem_span_image.symm
      rw [this, Submodule.span_le, Set.image_subset_iff]
      rintro i rfl
      simpa using (H i).1
  · have : W = .span K (b '' { j | μ j ≠ l }) := Submodule.ext fun _ ↦ b.mem_span_image.symm
    rw [this, Submodule.span_le, Set.image_subset_iff]
    rintro j hj
    exact Submodule.mem_iSup_of_mem (μ j) (Submodule.mem_iSup_of_mem hj (H j).1)

include H in
lemma Module.End.eigenspace_eq_span_singleton (i : ι) (hμ : Function.Injective μ) :
    f.eigenspace (μ i) = Submodule.span K {b i} := by
  simp_rw [f.eigenspace_eq_comap_repr b μ H, hμ.eq_iff, Set.setOf_eq_eq_singleton]
  ext x
  rw [← Set.image_singleton, b.mem_span_image]
  rfl
