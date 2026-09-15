import Mathlib

open MeasureTheory

section

variable {α β ε : Type*} [ENorm ε]

@[fun_prop]
def HasBoundedENorm (f : α → ε) : Prop := ⨆ x : α, ‖f x‖ₑ < ⊤

lemma hasBoundedENorm_def (f : α → ε) : HasBoundedENorm f ↔ ⨆ x : α, ‖f x‖ₑ < ⊤ := by
  simp [HasBoundedENorm]

lemma hasBoundedENorm_const' {c : ε} (hc : ‖c‖ₑ ≠ ⊤) : HasBoundedENorm (fun _ : α ↦ c) := by
  by_cases! hα : Nonempty α
  · grw [hasBoundedENorm_def, iSup_const]; exact lt_top_iff_ne_top.mpr hc
  · grw [hasBoundedENorm_def, iSup_of_empty]; simp

@[fun_prop]
lemma hasBoundedENorm_comp (f : β → ε) (g : α → β) (hf : HasBoundedENorm f) :
    HasBoundedENorm (fun x ↦ f (g x)) := by
  refine lt_of_le_of_lt ?_ hf
  exact iSup_le (fun i ↦ le_iSup (f := fun x ↦ ‖f x‖ₑ) (i := g i))

variable {E 𝕜 : Type*} [TopologicalSpace E] [ESeminormedAddCommMonoid E]

@[fun_prop]
lemma hasBoundedENorm_const (c : E) : HasBoundedENorm (fun _ : α ↦ c) := by
  simp [hasBoundedENorm_const']

variable {E' : Type*} [ESeminormedCommMonoid E'] [NormedSpace 𝕜 E']

@[fun_prop]
lemma HasBoundedENorm_fst (f : α → E × E') (hf : HasBoundedENorm f) :
    HasBoundedENorm (fun x ↦ (f x).fst) := by
  refine lt_of_le_of_lt ?_ hf
  exact (iSup_mono fun x ↦ by simp [enorm_le_iff_norm_le, norm_fst_le])

@[fun_prop]
lemma HasBoundedENorm_snd (f : α → E × E') (hf : HasBoundedENorm f) :
    HasBoundedENorm (fun x ↦ (f x).snd) := by
  refine lt_of_le_of_lt ?_ hf
  exact (iSup_mono fun x ↦ by simp [enorm_le_iff_norm_le, norm_snd_le])

@[fun_prop]
lemma HasBoundedENorm_prod_mk (f : α → E) (g : α → E')
    (hf : HasBoundedENorm f) (hg : HasBoundedENorm g) :
    HasBoundedENorm (fun x ↦ Prod.mk (f x) (g x)) := by
  refine lt_of_le_of_lt ?_ (max_lt hf hg)
  calc ⨆ x, ‖(f x, g x)‖ₑ
    _ = ⨆ x, max ‖f x‖ₑ ‖g x‖ₑ := by congr
    _ ≤ max (⨆ x, ‖f x‖ₑ) (⨆ x, ‖g x‖ₑ) := by
      apply iSup_le (fun i ↦ ?_)
      exact max_le_max (le_iSup (fun x ↦ ‖f x‖ₑ) _) (le_iSup (fun x ↦ ‖g x‖ₑ) _)

@[fun_prop]
lemma HasBoundedENorm_add
    (f g : α → E) (hf : HasBoundedENorm f) (hg : HasBoundedENorm g) :
    HasBoundedENorm (fun x ↦ f x + g x) := by
  refine lt_of_le_of_lt ?_ (ENNReal.add_lt_top.mpr ⟨hf, hg⟩)
  · refine iSup_le (fun x ↦ ?_)
    calc ‖f x + g x‖ₑ
      ≤ ‖f x‖ₑ + ‖g x‖ₑ := by sorry
      _ ≤ (⨆ x, ‖f x‖ₑ) + ⨆ x, ‖g x‖ₑ :=
        add_le_add (le_iSup (fun x ↦ ‖f x‖ₑ) _) (le_iSup (fun x ↦ ‖g x‖ₑ) _)

@[fun_prop]
lemma HasBoundedENorm_neg
    (f : α → E) (hf : HasBoundedENorm f) :
    HasBoundedENorm (fun x ↦ -f x) := by
  simp_rw [hasBoundedENorm_def, enorm_neg]
  exact hf

@[fun_prop]
lemma HasBoundedENorm_sub
    (f g : α → E) (hf : HasBoundedENorm f) (hg : HasBoundedENorm g) :
    HasBoundedENorm (fun x ↦ f x - g x) := by
  simp_rw [sub_eq_add_neg]; fun_prop

variable {α E E' 𝕜 : Type*}

variable [NormedField 𝕜] [NonUnitalSeminormedRing E] [NormedSpace 𝕜 E]

@[fun_prop]
lemma HasBoundedENorm_mul
    (f g : α → E) (hf : HasBoundedENorm f) (hg : HasBoundedENorm g) :
    HasBoundedENorm (fun x ↦ f x * g x) := by
  refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top hf hg)
  refine iSup_le (fun x ↦ ?_)
  calc ‖f x * g x‖ₑ
      ≤ ‖f x‖ₑ * ‖g x‖ₑ := by sorry
      _ ≤ (⨆ x, ‖f x‖ₑ) * ⨆ x, ‖g x‖ₑ := by
        exact mul_le_mul' (le_iSup (fun x ↦ ‖f x‖ₑ) _) (le_iSup (fun x ↦ ‖g x‖ₑ) _)

end

section Integrable

variable {α ε E 𝕜 : Type*} [MeasurableSpace α] [TopologicalSpace ε] [ContinuousENorm ε]

@[fun_prop]
lemma HasBoundedENorm.integrable {f : α → ε} {μ : Measure α} [IsFiniteMeasure μ]
    (hf : HasBoundedENorm f) (hf_meas : AEStronglyMeasurable f μ) :
    Integrable f μ := by
  refine ⟨hf_meas, ?_⟩
  apply HasFiniteIntegral.of_bounded_enorm (C := ⨆ x : α, ‖f x‖ₑ)
  filter_upwards with _
  exact le_iSup (f := fun x ↦ ‖f x‖ₑ) _

variable {R : Type*} [NormedRing R]

@[fun_prop]
lemma Integrable.mul_hasBoundedENorm {f g : α → R} {μ : Measure α}
    (hf : Integrable f μ) (hg : HasBoundedENorm g)
    (hg_meas : AEStronglyMeasurable g μ) :
    Integrable (fun x ↦ f x * g x) μ := by
  apply MeasureTheory.Integrable.mul_bdd (c := (⨆ x : α, ‖g x‖ₑ).toReal) hf hg_meas
  filter_upwards with x
  rw [← toReal_enorm, ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  exact le_iSup (f := fun x ↦ ‖g x‖ₑ) _

@[fun_prop]
lemma Integrable.hasBoundedENorm_mul {f g : α → R} {μ : Measure α}
    (hf : HasBoundedENorm f) (hg : Integrable g μ)
    (hf_meas : AEStronglyMeasurable f μ) :
    Integrable (fun x ↦ f x * g x) μ := by
  apply MeasureTheory.Integrable.bdd_mul (c := (⨆ x : α, ‖f x‖ₑ).toReal) hg hf_meas
  filter_upwards with x
  rw [← toReal_enorm, ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  exact le_iSup (f := fun x ↦ ‖f x‖ₑ) _

end Integrable
