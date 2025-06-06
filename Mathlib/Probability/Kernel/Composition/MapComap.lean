/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Basic

/-!
# Map of a kernel by a measurable function

We define the map and comap of a kernel along a measurable function, as well as some often useful
particular cases.

## Main definitions

Kernels built from other kernels:
* `map (κ : Kernel α β) (f : β → γ) : Kernel α γ`
  `∫⁻ c, g c ∂(map κ f a) = ∫⁻ b, g (f b) ∂(κ a)`
* `comap (κ : Kernel α β) (f : γ → α) (hf : Measurable f) : Kernel γ β`
  `∫⁻ b, g b ∂(comap κ f hf c) = ∫⁻ b, g b ∂(κ (f c))`

## Main statements

* `lintegral_map`, `lintegral_comap`: Lebesgue integral of a function against the map or comap of
  a kernel.

-/


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

section MapComap

/-! ### map, comap -/


variable {γ δ : Type*} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} {f : β → γ} {g : γ → α}

/-- The pushforward of a kernel along a measurable function. This is an implementation detail,
use `map κ f` instead. -/
noncomputable def mapOfMeasurable (κ : Kernel α β) (f : β → γ) (hf : Measurable f) :
    Kernel α γ where
  toFun a := (κ a).map f
  measurable' := by fun_prop

open Classical in
/-- The pushforward of a kernel along a function.
If the function is not measurable, we use zero instead. This choice of junk
value ensures that typeclass inference can infer that the `map` of a kernel
satisfying `IsZeroOrMarkovKernel` again satisfies this property. -/
noncomputable def map [MeasurableSpace γ] (κ : Kernel α β) (f : β → γ) : Kernel α γ :=
  if hf : Measurable f then mapOfMeasurable κ f hf else 0

theorem map_of_not_measurable (κ : Kernel α β) {f : β → γ} (hf : ¬(Measurable f)) :
    map κ f = 0 := by
  simp [map, hf]

@[simp] theorem mapOfMeasurable_eq_map (κ : Kernel α β) {f : β → γ} (hf : Measurable f) :
    mapOfMeasurable κ f hf = map κ f := by
  simp [map, hf]

theorem map_apply (κ : Kernel α β) (hf : Measurable f) (a : α) : map κ f a = (κ a).map f := by
  simp only [map, hf, ↓reduceDIte, mapOfMeasurable, coe_mk]

theorem map_apply' (κ : Kernel α β) (hf : Measurable f) (a : α) {s : Set γ} (hs : MeasurableSet s) :
    map κ f a s = κ a (f ⁻¹' s) := by rw [map_apply _ hf, Measure.map_apply hf hs]

lemma map_comp_right (κ : Kernel α β) {f : β → γ} (hf : Measurable f) {g : γ → δ}
    (hg : Measurable g) : κ.map (g ∘ f) = (κ.map f).map g := by
  ext1 x
  rw [map_apply _ hg, map_apply _ hf, Measure.map_map hg hf, ← map_apply _ (hg.comp hf)]

@[simp]
lemma map_zero : Kernel.map (0 : Kernel α β) f = 0 := by
  ext
  by_cases hf : Measurable f
  · simp [map_apply, hf]
  · simp [map_of_not_measurable _ hf, map_apply]

@[simp]
lemma map_id (κ : Kernel α β) : map κ id = κ := by
  ext a
  simp [map_apply, measurable_id]

@[simp]
lemma map_id' (κ : Kernel α β) : map κ (fun a ↦ a) = κ := map_id κ

nonrec theorem lintegral_map (κ : Kernel α β) (hf : Measurable f) (a : α) {g' : γ → ℝ≥0∞}
    (hg : Measurable g') : ∫⁻ b, g' b ∂map κ f a = ∫⁻ a, g' (f a) ∂κ a := by
  rw [map_apply _ hf, lintegral_map hg hf]

lemma map_apply_eq_iff_map_symm_apply_eq (κ : Kernel α β) {f : β ≃ᵐ γ} (η : Kernel α γ) :
    κ.map f = η ↔ κ = η.map f.symm := by
  simp_rw [Kernel.ext_iff, map_apply _ f.measurable, map_apply _ f.symm.measurable,
    f.map_apply_eq_iff_map_symm_apply_eq]

theorem sum_map_seq (κ : Kernel α β) [IsSFiniteKernel κ] (f : β → γ) :
    (Kernel.sum fun n => map (seq κ n) f) = map κ f := by
  by_cases hf : Measurable f
  · ext a s hs
    rw [Kernel.sum_apply, map_apply' κ hf a hs, Measure.sum_apply _ hs, ← measure_sum_seq κ,
      Measure.sum_apply _ (hf hs)]
    simp_rw [map_apply' _ hf _ hs]
  · simp [map_of_not_measurable _ hf]

lemma IsMarkovKernel.map (κ : Kernel α β) [IsMarkovKernel κ] (hf : Measurable f) :
    IsMarkovKernel (map κ f) :=
  ⟨fun a => ⟨by rw [map_apply' κ hf a MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩⟩

instance IsZeroOrMarkovKernel.map (κ : Kernel α β) [IsZeroOrMarkovKernel κ] (f : β → γ) :
    IsZeroOrMarkovKernel (map κ f) := by
  by_cases hf : Measurable f
  · rcases eq_zero_or_isMarkovKernel κ with rfl | h
    · simp only [map_zero]; infer_instance
    · have := IsMarkovKernel.map κ hf; infer_instance
  · simp only [map_of_not_measurable _ hf]; infer_instance

instance IsFiniteKernel.map (κ : Kernel α β) [IsFiniteKernel κ] (f : β → γ) :
    IsFiniteKernel (map κ f) := by
  refine ⟨⟨IsFiniteKernel.bound κ, IsFiniteKernel.bound_lt_top κ, fun a => ?_⟩⟩
  by_cases hf : Measurable f
  · rw [map_apply' κ hf a MeasurableSet.univ]
    exact measure_le_bound κ a _
  · simp [map_of_not_measurable _ hf]

instance IsSFiniteKernel.map (κ : Kernel α β) [IsSFiniteKernel κ] (f : β → γ) :
    IsSFiniteKernel (map κ f) :=
  ⟨⟨fun n => Kernel.map (seq κ n) f, inferInstance, (sum_map_seq κ f).symm⟩⟩

@[simp]
lemma map_const (μ : Measure α) {f : α → β} (hf : Measurable f) :
    map (const γ μ) f = const γ (μ.map f) := by
  ext x s hs
  rw [map_apply' _ hf _ hs, const_apply, const_apply, Measure.map_apply hf hs]

/-- Pullback of a kernel, such that for each set s `comap κ g hg c s = κ (g c) s`.
We include measurability in the assumptions instead of using junk values
to make sure that typeclass inference can infer that the `comap` of a Markov kernel
is again a Markov kernel. -/
def comap (κ : Kernel α β) (g : γ → α) (hg : Measurable g) : Kernel γ β where
  toFun a := κ (g a)
  measurable' := κ.measurable.comp hg

@[simp, norm_cast]
lemma coe_comap (κ : Kernel α β) (g : γ → α) (hg : Measurable g) : κ.comap g hg = κ ∘ g := rfl

theorem comap_apply (κ : Kernel α β) (hg : Measurable g) (c : γ) : comap κ g hg c = κ (g c) :=
  rfl

theorem comap_apply' (κ : Kernel α β) (hg : Measurable g) (c : γ) (s : Set β) :
    comap κ g hg c s = κ (g c) s :=
  rfl

@[simp]
lemma comap_zero (hg : Measurable g) : Kernel.comap (0 : Kernel α β) g hg = 0 := by
  ext; rw [Kernel.comap_apply]; simp

@[simp]
lemma comap_id (κ : Kernel α β) : comap κ id measurable_id = κ := by ext a; rw [comap_apply]; simp

@[simp]
lemma comap_id' (κ : Kernel α β) : comap κ (fun a ↦ a) measurable_id = κ := comap_id κ

theorem lintegral_comap (κ : Kernel α β) (hg : Measurable g) (c : γ) (g' : β → ℝ≥0∞) :
    ∫⁻ b, g' b ∂comap κ g hg c = ∫⁻ b, g' b ∂κ (g c) :=
  rfl

theorem sum_comap_seq (κ : Kernel α β) [IsSFiniteKernel κ] (hg : Measurable g) :
    (Kernel.sum fun n => comap (seq κ n) g hg) = comap κ g hg := by
  ext a s hs
  rw [Kernel.sum_apply, comap_apply' κ hg a s, Measure.sum_apply _ hs, ← measure_sum_seq κ,
    Measure.sum_apply _ hs]
  simp_rw [comap_apply' _ hg _ s]

instance IsMarkovKernel.comap (κ : Kernel α β) [IsMarkovKernel κ] (hg : Measurable g) :
    IsMarkovKernel (comap κ g hg) :=
  ⟨fun a => ⟨by rw [comap_apply' κ hg a Set.univ, measure_univ]⟩⟩

instance IsZeroOrMarkovKernel.comap (κ : Kernel α β) [IsZeroOrMarkovKernel κ] (hg : Measurable g) :
    IsZeroOrMarkovKernel (comap κ g hg) := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | h
  · simp only [comap_zero]; infer_instance
  · have := IsMarkovKernel.comap κ hg; infer_instance

instance IsFiniteKernel.comap (κ : Kernel α β) [IsFiniteKernel κ] (hg : Measurable g) :
    IsFiniteKernel (comap κ g hg) := by
  refine ⟨⟨IsFiniteKernel.bound κ, IsFiniteKernel.bound_lt_top κ, fun a => ?_⟩⟩
  rw [comap_apply' κ hg a Set.univ]
  exact measure_le_bound κ _ _

instance IsSFiniteKernel.comap (κ : Kernel α β) [IsSFiniteKernel κ] (hg : Measurable g) :
    IsSFiniteKernel (comap κ g hg) :=
  ⟨⟨fun n => Kernel.comap (seq κ n) g hg, inferInstance, (sum_comap_seq κ hg).symm⟩⟩

lemma comap_map_comm (κ : Kernel β γ) {f : α → β} {g : γ → δ}
    (hf : Measurable f) (hg : Measurable g) :
    comap (map κ g) f hf = map (comap κ f hf) g := by
  ext x s _
  rw [comap_apply, map_apply _ hg, map_apply _ hg, comap_apply]

end MapComap

@[simp]
lemma id_map {f : α → β} (hf : Measurable f) : Kernel.id.map f = deterministic f hf := by
  ext
  rw [Kernel.map_apply _ hf, Kernel.deterministic_apply, Kernel.id_apply, Measure.map_dirac hf]

@[simp]
lemma id_comap {f : α → β} (hf : Measurable f) : Kernel.id.comap f hf = deterministic f hf := by
  ext
  rw [Kernel.comap_apply _ hf, Kernel.deterministic_apply, Kernel.id_apply]

lemma deterministic_map {f : α → β} (hf : Measurable f) {g : β → γ} (hg : Measurable g) :
    (deterministic f hf).map g = deterministic (g ∘ f) (hg.comp hf) := by
  rw [← id_map, ← map_comp_right _ hf hg, id_map]

section FstSnd

variable {δ : Type*} {mδ : MeasurableSpace δ}

/-- Define a `Kernel (γ × α) β` from a `Kernel α β` by taking the comap of the projection. -/
def prodMkLeft (γ : Type*) [MeasurableSpace γ] (κ : Kernel α β) : Kernel (γ × α) β :=
  comap κ Prod.snd measurable_snd

/-- Define a `Kernel (α × γ) β` from a `Kernel α β` by taking the comap of the projection. -/
def prodMkRight (γ : Type*) [MeasurableSpace γ] (κ : Kernel α β) : Kernel (α × γ) β :=
  comap κ Prod.fst measurable_fst

@[simp]
theorem prodMkLeft_apply (κ : Kernel α β) (ca : γ × α) : prodMkLeft γ κ ca = κ ca.snd :=
  rfl

@[simp]
theorem prodMkRight_apply (κ : Kernel α β) (ca : α × γ) : prodMkRight γ κ ca = κ ca.fst := rfl

theorem prodMkLeft_apply' (κ : Kernel α β) (ca : γ × α) (s : Set β) :
    prodMkLeft γ κ ca s = κ ca.snd s :=
  rfl

theorem prodMkRight_apply' (κ : Kernel α β) (ca : α × γ) (s : Set β) :
    prodMkRight γ κ ca s = κ ca.fst s := rfl

@[simp]
lemma prodMkLeft_zero : Kernel.prodMkLeft α (0 : Kernel β γ) = 0 := by
  ext x s _; simp

@[simp]
lemma prodMkRight_zero : Kernel.prodMkRight α (0 : Kernel β γ) = 0 := by
  ext x s _; simp

@[simp]
lemma prodMkLeft_add (κ η : Kernel α β) :
    prodMkLeft γ (κ + η) = prodMkLeft γ κ + prodMkLeft γ η := by ext; simp

@[simp]
lemma prodMkRight_add (κ η : Kernel α β) :
    prodMkRight γ (κ + η) = prodMkRight γ κ + prodMkRight γ η := by ext; simp

lemma sum_prodMkLeft {ι : Type*} [Countable ι] {κ : ι → Kernel α β} :
    Kernel.sum (fun i ↦ Kernel.prodMkLeft γ (κ i)) = Kernel.prodMkLeft γ (Kernel.sum κ) := by
  ext
  simp_rw [sum_apply, prodMkLeft_apply, sum_apply]

lemma sum_prodMkRight {ι : Type*} [Countable ι] {κ : ι → Kernel α β} :
    Kernel.sum (fun i ↦ Kernel.prodMkRight γ (κ i)) = Kernel.prodMkRight γ (Kernel.sum κ) := by
  ext
  simp_rw [sum_apply, prodMkRight_apply, sum_apply]

theorem lintegral_prodMkLeft (κ : Kernel α β) (ca : γ × α) (g : β → ℝ≥0∞) :
    ∫⁻ b, g b ∂prodMkLeft γ κ ca = ∫⁻ b, g b ∂κ ca.snd := rfl

theorem lintegral_prodMkRight (κ : Kernel α β) (ca : α × γ) (g : β → ℝ≥0∞) :
    ∫⁻ b, g b ∂prodMkRight γ κ ca = ∫⁻ b, g b ∂κ ca.fst := rfl

instance IsMarkovKernel.prodMkLeft (κ : Kernel α β) [IsMarkovKernel κ] :
    IsMarkovKernel (prodMkLeft γ κ) := by rw [Kernel.prodMkLeft]; infer_instance

instance IsMarkovKernel.prodMkRight (κ : Kernel α β) [IsMarkovKernel κ] :
    IsMarkovKernel (prodMkRight γ κ) := by rw [Kernel.prodMkRight]; infer_instance

instance IsZeroOrMarkovKernel.prodMkLeft (κ : Kernel α β) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (prodMkLeft γ κ) := by rw [Kernel.prodMkLeft]; infer_instance

instance IsZeroOrMarkovKernel.prodMkRight (κ : Kernel α β) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (prodMkRight γ κ) := by rw [Kernel.prodMkRight]; infer_instance

instance IsFiniteKernel.prodMkLeft (κ : Kernel α β) [IsFiniteKernel κ] :
    IsFiniteKernel (prodMkLeft γ κ) := by rw [Kernel.prodMkLeft]; infer_instance

instance IsFiniteKernel.prodMkRight (κ : Kernel α β) [IsFiniteKernel κ] :
    IsFiniteKernel (prodMkRight γ κ) := by rw [Kernel.prodMkRight]; infer_instance

instance IsSFiniteKernel.prodMkLeft (κ : Kernel α β) [IsSFiniteKernel κ] :
    IsSFiniteKernel (prodMkLeft γ κ) := by rw [Kernel.prodMkLeft]; infer_instance

instance IsSFiniteKernel.prodMkRight (κ : Kernel α β) [IsSFiniteKernel κ] :
    IsSFiniteKernel (prodMkRight γ κ) := by rw [Kernel.prodMkRight]; infer_instance

lemma isSFiniteKernel_prodMkLeft_unit {κ : Kernel α β} :
    IsSFiniteKernel (prodMkLeft Unit κ) ↔ IsSFiniteKernel κ := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  change IsSFiniteKernel ((prodMkLeft Unit κ).comap (fun a ↦ ((), a)) (by fun_prop))
  infer_instance

lemma isSFiniteKernel_prodMkRight_unit {κ : Kernel α β} :
    IsSFiniteKernel (prodMkRight Unit κ) ↔ IsSFiniteKernel κ := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  change IsSFiniteKernel ((prodMkRight Unit κ).comap (fun a ↦ (a, ())) (by fun_prop))
  infer_instance

lemma map_prodMkLeft (γ : Type*) [MeasurableSpace γ] (κ : Kernel α β) (f : β → δ) :
    map (prodMkLeft γ κ) f = prodMkLeft γ (map κ f) := by
  by_cases hf : Measurable f
  · simp only [map, hf, ↓reduceDIte]
    rfl
  · simp [map_of_not_measurable _ hf]

lemma map_prodMkRight (κ : Kernel α β) (γ : Type*) {mγ : MeasurableSpace γ} (f : β → δ) :
    map (prodMkRight γ κ) f = prodMkRight γ (map κ f) := by
  by_cases hf : Measurable f
  · simp only [map, hf, ↓reduceDIte]
    rfl
  · simp [map_of_not_measurable _ hf]

/-- Define a `Kernel (β × α) γ` from a `Kernel (α × β) γ` by taking the comap of `Prod.swap`. -/
def swapLeft (κ : Kernel (α × β) γ) : Kernel (β × α) γ :=
  comap κ Prod.swap measurable_swap

@[simp]
lemma swapLeft_zero : swapLeft (0 : Kernel (α × β) γ) = 0 := by simp [swapLeft]

@[simp]
theorem swapLeft_apply (κ : Kernel (α × β) γ) (a : β × α) : swapLeft κ a = κ a.swap := rfl

theorem swapLeft_apply' (κ : Kernel (α × β) γ) (a : β × α) (s : Set γ) :
    swapLeft κ a s = κ a.swap s := rfl

theorem lintegral_swapLeft (κ : Kernel (α × β) γ) (a : β × α) (g : γ → ℝ≥0∞) :
    ∫⁻ c, g c ∂swapLeft κ a = ∫⁻ c, g c ∂κ a.swap := by
  rw [swapLeft_apply]

instance IsMarkovKernel.swapLeft (κ : Kernel (α × β) γ) [IsMarkovKernel κ] :
    IsMarkovKernel (swapLeft κ) := by rw [Kernel.swapLeft]; infer_instance

instance IsFiniteKernel.swapLeft (κ : Kernel (α × β) γ) [IsFiniteKernel κ] :
    IsFiniteKernel (swapLeft κ) := by rw [Kernel.swapLeft]; infer_instance

instance IsSFiniteKernel.swapLeft (κ : Kernel (α × β) γ) [IsSFiniteKernel κ] :
    IsSFiniteKernel (swapLeft κ) := by rw [Kernel.swapLeft]; infer_instance

@[simp] lemma swapLeft_prodMkLeft (κ : Kernel α β) (γ : Type*) {_ : MeasurableSpace γ} :
    swapLeft (prodMkLeft γ κ) = prodMkRight γ κ := rfl

@[simp] lemma swapLeft_prodMkRight (κ : Kernel α β) (γ : Type*) {_ : MeasurableSpace γ} :
    swapLeft (prodMkRight γ κ) = prodMkLeft γ κ := rfl

/-- Define a `Kernel α (γ × β)` from a `Kernel α (β × γ)` by taking the map of `Prod.swap`.
We use `mapOfMeasurable` in the definition for better defeqs. -/
noncomputable def swapRight (κ : Kernel α (β × γ)) : Kernel α (γ × β) :=
  mapOfMeasurable κ Prod.swap measurable_swap

lemma swapRight_eq (κ : Kernel α (β × γ)) : swapRight κ = map κ Prod.swap := by
  simp [swapRight]

@[simp]
lemma swapRight_zero : swapRight (0 : Kernel α (β × γ)) = 0 := by simp [swapRight]

theorem swapRight_apply (κ : Kernel α (β × γ)) (a : α) : swapRight κ a = (κ a).map Prod.swap :=
  rfl

theorem swapRight_apply' (κ : Kernel α (β × γ)) (a : α) {s : Set (γ × β)} (hs : MeasurableSet s) :
    swapRight κ a s = κ a {p | p.swap ∈ s} := by
  rw [swapRight_apply, Measure.map_apply measurable_swap hs]; rfl

theorem lintegral_swapRight (κ : Kernel α (β × γ)) (a : α) {g : γ × β → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂swapRight κ a = ∫⁻ bc : β × γ, g bc.swap ∂κ a := by
  rw [swapRight_eq, lintegral_map _ measurable_swap a hg]

instance IsMarkovKernel.swapRight (κ : Kernel α (β × γ)) [IsMarkovKernel κ] :
    IsMarkovKernel (swapRight κ) := by
  rw [Kernel.swapRight_eq]; exact IsMarkovKernel.map _ measurable_swap

instance IsZeroOrMarkovKernel.swapRight (κ : Kernel α (β × γ)) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (swapRight κ) := by rw [Kernel.swapRight_eq]; infer_instance

instance IsFiniteKernel.swapRight (κ : Kernel α (β × γ)) [IsFiniteKernel κ] :
    IsFiniteKernel (swapRight κ) := by rw [Kernel.swapRight_eq]; infer_instance

instance IsSFiniteKernel.swapRight (κ : Kernel α (β × γ)) [IsSFiniteKernel κ] :
    IsSFiniteKernel (swapRight κ) := by rw [Kernel.swapRight_eq]; infer_instance

/-- Define a `Kernel α β` from a `Kernel α (β × γ)` by taking the map of the first projection.
We use `mapOfMeasurable` for better defeqs. -/
noncomputable def fst (κ : Kernel α (β × γ)) : Kernel α β :=
  mapOfMeasurable κ Prod.fst measurable_fst

theorem fst_eq (κ : Kernel α (β × γ)) : fst κ = map κ Prod.fst := by simp [fst]

theorem fst_apply (κ : Kernel α (β × γ)) (a : α) : fst κ a = (κ a).map Prod.fst :=
  rfl

theorem fst_apply' (κ : Kernel α (β × γ)) (a : α) {s : Set β} (hs : MeasurableSet s) :
    fst κ a s = κ a {p | p.1 ∈ s} := by rw [fst_apply, Measure.map_apply measurable_fst hs]; rfl

theorem fst_real_apply (κ : Kernel α (β × γ)) (a : α) {s : Set β} (hs : MeasurableSet s) :
    (fst κ a).real s = (κ a).real {p | p.1 ∈ s} := by
  simp [fst_apply', hs, measureReal_def]

@[simp]
lemma fst_zero : fst (0 : Kernel α (β × γ)) = 0 := by simp [fst]

theorem lintegral_fst (κ : Kernel α (β × γ)) (a : α) {g : β → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂fst κ a = ∫⁻ bc : β × γ, g bc.fst ∂κ a := by
  rw [fst_eq, lintegral_map _ measurable_fst a hg]

instance IsMarkovKernel.fst (κ : Kernel α (β × γ)) [IsMarkovKernel κ] : IsMarkovKernel (fst κ) := by
  rw [Kernel.fst_eq]; exact IsMarkovKernel.map _ measurable_fst

instance IsZeroOrMarkovKernel.fst (κ : Kernel α (β × γ)) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (fst κ) := by
  rw [Kernel.fst_eq]; infer_instance

instance IsFiniteKernel.fst (κ : Kernel α (β × γ)) [IsFiniteKernel κ] : IsFiniteKernel (fst κ) := by
  rw [Kernel.fst_eq]; infer_instance

instance IsSFiniteKernel.fst (κ : Kernel α (β × γ)) [IsSFiniteKernel κ] :
    IsSFiniteKernel (fst κ) := by rw [Kernel.fst_eq]; infer_instance

instance (priority := 100) isFiniteKernel_of_isFiniteKernel_fst {κ : Kernel α (β × γ)}
    [h : IsFiniteKernel (fst κ)] :
    IsFiniteKernel κ := by
  refine ⟨h.bound, h.bound_lt_top, fun a ↦ le_trans ?_ (measure_le_bound (fst κ) a Set.univ)⟩
  rw [fst_apply' _ _ MeasurableSet.univ]
  simp

lemma fst_map_prod (κ : Kernel α β) {f : β → γ} {g : β → δ} (hg : Measurable g) :
    fst (map κ (fun x ↦ (f x, g x))) = map κ f := by
  by_cases hf : Measurable f
  · ext x s hs
    rw [fst_apply' _ _ hs, map_apply' _ (hf.prod hg) _, map_apply' _ hf _ hs]
    · simp only [Set.preimage, Set.mem_setOf]
    · exact measurable_fst hs
  · have : ¬ Measurable (fun x ↦ (f x, g x)) := by
      contrapose! hf; exact hf.fst
    simp [map_of_not_measurable _ hf, map_of_not_measurable _ this]

lemma fst_map_id_prod (κ : Kernel α β) {f : β → γ} (hf : Measurable f) :
    fst (map κ (fun a ↦ (a, f a))) = κ := by
  rw [fst_map_prod _ hf, Kernel.map_id']

lemma fst_prodMkLeft (δ : Type*) [MeasurableSpace δ] (κ : Kernel α (β × γ)) :
    fst (prodMkLeft δ κ) = prodMkLeft δ (fst κ) := rfl

lemma fst_prodMkRight (κ : Kernel α (β × γ)) (δ : Type*) [MeasurableSpace δ] :
    fst (prodMkRight δ κ) = prodMkRight δ (fst κ) := rfl

/-- Define a `Kernel α γ` from a `Kernel α (β × γ)` by taking the map of the second projection.
We use `mapOfMeasurable` for better defeqs. -/
noncomputable def snd (κ : Kernel α (β × γ)) : Kernel α γ :=
  mapOfMeasurable κ Prod.snd measurable_snd

theorem snd_eq (κ : Kernel α (β × γ)) : snd κ = map κ Prod.snd := by simp [snd]

theorem snd_apply (κ : Kernel α (β × γ)) (a : α) : snd κ a = (κ a).map Prod.snd :=
  rfl

theorem snd_apply' (κ : Kernel α (β × γ)) (a : α) {s : Set γ} (hs : MeasurableSet s) :
    snd κ a s = κ a (Prod.snd ⁻¹' s) := by rw [snd_apply, Measure.map_apply measurable_snd hs]

@[simp]
lemma snd_zero : snd (0 : Kernel α (β × γ)) = 0 := by simp [snd]

theorem lintegral_snd (κ : Kernel α (β × γ)) (a : α) {g : γ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂snd κ a = ∫⁻ bc : β × γ, g bc.snd ∂κ a := by
  rw [snd_eq, lintegral_map _ measurable_snd a hg]

instance IsMarkovKernel.snd (κ : Kernel α (β × γ)) [IsMarkovKernel κ] : IsMarkovKernel (snd κ) := by
  rw [Kernel.snd_eq]; exact IsMarkovKernel.map _ measurable_snd

instance IsZeroOrMarkovKernel.snd (κ : Kernel α (β × γ)) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (snd κ) := by
  rw [Kernel.snd_eq]; infer_instance

instance IsFiniteKernel.snd (κ : Kernel α (β × γ)) [IsFiniteKernel κ] : IsFiniteKernel (snd κ) := by
  rw [Kernel.snd_eq]; infer_instance

instance IsSFiniteKernel.snd (κ : Kernel α (β × γ)) [IsSFiniteKernel κ] :
    IsSFiniteKernel (snd κ) := by rw [Kernel.snd_eq]; infer_instance

instance (priority := 100) isFiniteKernel_of_isFiniteKernel_snd {κ : Kernel α (β × γ)}
    [h : IsFiniteKernel (snd κ)] :
    IsFiniteKernel κ := by
  refine ⟨h.bound, h.bound_lt_top, fun a ↦ le_trans ?_ (measure_le_bound (snd κ) a Set.univ)⟩
  rw [snd_apply' _ _ MeasurableSet.univ]
  simp

lemma snd_map_prod (κ : Kernel α β) {f : β → γ} {g : β → δ} (hf : Measurable f) :
    snd (map κ (fun x ↦ (f x, g x))) = map κ g := by
  by_cases hg : Measurable g
  · ext x s hs
    rw [snd_apply' _ _ hs, map_apply' _ (hf.prod hg), map_apply' _ hg _ hs]
    · simp only [Set.preimage, Set.mem_setOf]
    · exact measurable_snd hs
  · have : ¬ Measurable (fun x ↦ (f x, g x)) := by
      contrapose! hg; exact hg.snd
    simp [map_of_not_measurable _ hg, map_of_not_measurable _ this]

lemma snd_map_prod_id (κ : Kernel α β) {f : β → γ} (hf : Measurable f) :
    snd (map κ (fun a ↦ (f a, a))) = κ := by
  rw [snd_map_prod _ hf, Kernel.map_id']

lemma snd_prodMkLeft (δ : Type*) [MeasurableSpace δ] (κ : Kernel α (β × γ)) :
    snd (prodMkLeft δ κ) = prodMkLeft δ (snd κ) := rfl

lemma snd_prodMkRight (κ : Kernel α (β × γ)) (δ : Type*) [MeasurableSpace δ] :
    snd (prodMkRight δ κ) = prodMkRight δ (snd κ) := rfl

@[simp]
lemma fst_swapRight (κ : Kernel α (β × γ)) : fst (swapRight κ) = snd κ := by
  ext a s hs
  rw [fst_apply' _ _ hs, swapRight_apply', snd_apply' _ _ hs]
  · rfl
  · exact measurable_fst hs

@[simp]
lemma snd_swapRight (κ : Kernel α (β × γ)) : snd (swapRight κ) = fst κ := by
  ext a s hs
  rw [snd_apply' _ _ hs, swapRight_apply', fst_apply' _ _ hs]
  · rfl
  · exact measurable_snd hs

end FstSnd

section sectLsectR

variable {γ δ : Type*} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

/-- Define a `Kernel α γ` from a `Kernel (α × β) γ` by taking the comap of `fun a ↦ (a, b)` for
a given `b : β`. -/
noncomputable def sectL (κ : Kernel (α × β) γ) (b : β) : Kernel α γ :=
  comap κ (fun a ↦ (a, b)) (measurable_id.prodMk measurable_const)

@[simp] theorem sectL_apply (κ : Kernel (α × β) γ) (b : β) (a : α) : sectL κ b a = κ (a, b) := rfl

@[simp] lemma sectL_zero (b : β) : sectL (0 : Kernel (α × β) γ) b = 0 := by simp [sectL]

instance (κ : Kernel (α × β) γ) (b : β) [IsMarkovKernel κ] : IsMarkovKernel (sectL κ b) := by
  rw [sectL]; infer_instance

instance (κ : Kernel (α × β) γ) (b : β) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (sectL κ b) := by
  rw [sectL]; infer_instance

instance (κ : Kernel (α × β) γ) (b : β) [IsFiniteKernel κ] : IsFiniteKernel (sectL κ b) := by
  rw [sectL]; infer_instance

instance (κ : Kernel (α × β) γ) (b : β) [IsSFiniteKernel κ] : IsSFiniteKernel (sectL κ b) := by
  rw [sectL]; infer_instance

instance (κ : Kernel (α × β) γ) (a : α) (b : β) [NeZero (κ (a, b))] : NeZero ((sectL κ b) a) := by
  rw [sectL_apply]; infer_instance

instance (priority := 100) {κ : Kernel (α × β) γ} [∀ b, IsMarkovKernel (sectL κ b)] :
    IsMarkovKernel κ := by
  refine ⟨fun _ ↦ ⟨?_⟩⟩
  rw [← sectL_apply, measure_univ]

--I'm not sure this lemma is actually useful
lemma comap_sectL (κ : Kernel (α × β) γ) (b : β) {f : δ → α} (hf : Measurable f) :
    comap (sectL κ b) f hf = comap κ (fun d ↦ (f d, b)) (hf.prodMk measurable_const) := by
  ext d s
  rw [comap_apply, sectL_apply, comap_apply]

@[simp]
lemma sectL_prodMkLeft (α : Type*) [MeasurableSpace α] (κ : Kernel β γ) (a : α) {b : β} :
    sectL (prodMkLeft α κ) b a = κ b := rfl

@[simp]
lemma sectL_prodMkRight (β : Type*) [MeasurableSpace β] (κ : Kernel α γ) (b : β) :
    sectL (prodMkRight β κ) b = κ := rfl

/-- Define a `Kernel β γ` from a `Kernel (α × β) γ` by taking the comap of `fun b ↦ (a, b)` for
a given `a : α`. -/
noncomputable def sectR (κ : Kernel (α × β) γ) (a : α) : Kernel β γ :=
  comap κ (fun b ↦ (a, b)) (measurable_const.prodMk measurable_id)

@[simp] theorem sectR_apply (κ : Kernel (α × β) γ) (b : β) (a : α) : sectR κ a b = κ (a, b) := rfl

@[simp] lemma sectR_zero (a : α) : sectR (0 : Kernel (α × β) γ) a = 0 := by simp [sectR]

instance (κ : Kernel (α × β) γ) (a : α) [IsMarkovKernel κ] : IsMarkovKernel (sectR κ a) := by
  rw [sectR]; infer_instance

instance (κ : Kernel (α × β) γ) (a : α) [IsZeroOrMarkovKernel κ] :
    IsZeroOrMarkovKernel (sectR κ a) := by
  rw [sectR]; infer_instance

instance (κ : Kernel (α × β) γ) (a : α) [IsFiniteKernel κ] : IsFiniteKernel (sectR κ a) := by
  rw [sectR]; infer_instance

instance (κ : Kernel (α × β) γ) (a : α) [IsSFiniteKernel κ] : IsSFiniteKernel (sectR κ a) := by
  rw [sectR]; infer_instance

instance (κ : Kernel (α × β) γ) (a : α) (b : β) [NeZero (κ (a, b))] : NeZero ((sectR κ a) b) := by
  rw [sectR_apply]; infer_instance

instance (priority := 100) {κ : Kernel (α × β) γ} [∀ b, IsMarkovKernel (sectR κ b)] :
    IsMarkovKernel κ := by
  refine ⟨fun _ ↦ ⟨?_⟩⟩
  rw [← sectR_apply, measure_univ]

--I'm not sure this lemma is actually useful
lemma comap_sectR (κ : Kernel (α × β) γ) (a : α) {f : δ → β} (hf : Measurable f) :
    comap (sectR κ a) f hf = comap κ (fun d ↦ (a, f d)) (measurable_const.prodMk hf) := by
  ext d s
  rw [comap_apply, sectR_apply, comap_apply]

@[simp]
lemma sectR_prodMkLeft (α : Type*) [MeasurableSpace α] (κ : Kernel β γ) (a : α) :
    sectR (prodMkLeft α κ) a = κ := rfl

@[simp]
lemma sectR_prodMkRight (β : Type*) [MeasurableSpace β] (κ : Kernel α γ) (b : β) {a : α} :
    sectR (prodMkRight β κ) a b = κ a := rfl

@[simp] lemma sectL_swapRight (κ : Kernel (α × β) γ) : sectL (swapLeft κ) = sectR κ := rfl

@[simp] lemma sectR_swapRight (κ : Kernel (α × β) γ) : sectR (swapLeft κ) = sectL κ := rfl

end sectLsectR

lemma isSFiniteKernel_prodMkLeft_iff [Nonempty γ] {κ : Kernel α β} :
    IsSFiniteKernel (prodMkLeft γ κ) ↔ IsSFiniteKernel κ := by
  inhabit γ
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  rw [← sectR_prodMkLeft γ κ default]
  infer_instance

lemma isSFiniteKernel_prodMkRight_iff [Nonempty γ] {κ : Kernel α β} :
    IsSFiniteKernel (prodMkRight γ κ) ↔ IsSFiniteKernel κ := by
  inhabit γ
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  rw [← sectL_prodMkRight γ κ default]
  infer_instance

end Kernel
end ProbabilityTheory
