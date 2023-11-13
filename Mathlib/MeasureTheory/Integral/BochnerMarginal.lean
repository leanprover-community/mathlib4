import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Integral.Marginal

/-!
# Marginals of Banach valued functions
-/

open scoped Classical ENNReal
open Set Function Equiv Finset

noncomputable section

namespace MeasureTheory

section Marginal

variable {δ δ' : Type*} {π : δ → Type*} [∀ x, MeasurableSpace (π x)]
variable {μ : ∀ i, Measure (π i)} [∀ i, SigmaFinite (μ i)] [DecidableEq δ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {s t : Finset δ} {f g : (∀ i, π i) → E} {x y : ∀ i, π i} {i : δ}

variable {α β} [MeasurableSpace α] {μ : Measure α} in
protected theorem MeasurePreserving.integral_map_equiv [MeasurableSpace β] {ν : Measure β}
    (f : β → E) (g : α ≃ᵐ β) (hg : MeasurePreserving g μ ν) :
    ∫ a, f a ∂ν = ∫ a, f (g a) ∂μ := by
  rw [← MeasureTheory.integral_map_equiv g f, hg.map_eq]

variable {α β} [MeasurableSpace α] [NormedAddCommGroup β] [MeasurableSpace β] [BorelSpace β]
  [MeasurableSpace δ] {μ : Measure α} in
theorem Integrable.comp_measurePreserving {ν : Measure δ} {g : δ → β} {f : α → δ}
    (hg : Integrable g ν) (hf : MeasurePreserving f μ ν) : Integrable (g ∘ f) μ :=
  hf.integrable_comp hg.aestronglyMeasurable |>.mpr hg


-- note: Measurable.integral_prod_right inconsistent with Integral.integral_prod_right

-- inconsistent:
-- #check Subsingleton.stronglyMeasurable
-- #check Subsingleton.measurable

-- variable order inconsistent
-- #check MeasureTheory.integral_map_equiv
-- #check MeasureTheory.lintegral_map_equiv

variable (μ f s x) in
/-- Integrate `f(x₁,…,xₙ)` over all variables `xᵢ` where `i ∈ s`. Return a function in the
  remaining variables (it will be constant in the `xᵢ` for `i ∈ s`).
  This is the marginal distribution of all variables not in `s`. -/
def marginal : E :=
  ∫ y : ∀ i : s, π i, f (updateFinset x s y) ∂Measure.pi fun i : s ↦ μ i

-- Note: this notation is not a binder. This is more convenient since it returns a function.
notation "∫⋯∫_" s ", " f " ∂" μ:70 => marginal μ s f

notation "∫⋯∫_" s ", " f => marginal (fun _ ↦ volume) s f


variable (μ) [CompleteSpace E] in
@[simp] theorem marginal_empty (f : (∀ i, π i) → E) : ∫⋯∫_∅, f ∂μ = f := by
  ext1 x
  simp_rw [marginal, Measure.pi_of_empty fun i : (∅ : Finset δ) ↦ μ i]
  apply integral_dirac'
  convert Subsingleton.stronglyMeasurable' _
  -- doesn't work?
  -- convert Subsingleton.stronglyMeasurable' (α := ((∅ : Finset δ) → π i)) _
  infer_instance

variable (μ) in
/-- The marginal distribution is independent of the variables in `s`. -/
theorem marginal_congr {x y : ∀ i, π i} (f : (∀ i, π i) → E)
    (h : ∀ i ∉ s, x i = y i) :
    (∫⋯∫_s, f ∂μ) x = (∫⋯∫_s, f ∂μ) y := by
  dsimp [marginal, updateFinset]; rcongr; exact h _ ‹_›

variable (μ) in
theorem marginal_update_of_mem {i : δ} (hi : i ∈ s)
    (f : (∀ i, π i) → E) (x : ∀ i, π i) (y : π i) :
    (∫⋯∫_s, f ∂μ) (Function.update x i y) = (∫⋯∫_s, f ∂μ) x := by
  apply marginal_congr
  intro j hj
  have : j ≠ i := by rintro rfl; exact hj hi
  apply update_noteq this

variable  [Fintype δ] [MeasurableSpace E]

-- move
theorem Integrable.comp_updateFinset (hf : Integrable f (.pi μ)) :
    Integrable (uncurry fun x y ↦ f (updateFinset x s y)) (.prod (.pi μ) (.pi (fun i ↦ μ i))) := by
  sorry

theorem Integrable.comp_updateFinset_right (hf : Integrable f (.pi μ)) (x : ∀ i, π i) :
    Integrable (fun y ↦ f (updateFinset x s y)) (.pi (fun i ↦ μ i)) := by
  sorry


theorem Integrable.marginal (hf : Integrable f (.pi μ)) : Integrable (∫⋯∫_s, f ∂μ) (.pi μ) :=
  hf.comp_updateFinset.integral_prod_left

theorem marginal_union (f : (∀ i, π i) → E) (hf : Integrable f (.pi μ))
    (hst : Disjoint s t) : ∫⋯∫_s ∪ t, f ∂μ = ∫⋯∫_s, ∫⋯∫_t, f ∂μ ∂μ := by
  ext1 x
  let e := MeasurableEquiv.piFinsetUnion π hst
  calc (∫⋯∫_s ∪ t, f ∂μ) x
      = ∫ (y : (i : ↥(s ∪ t)) → π i), f (updateFinset x (s ∪ t) y)
          ∂.pi fun i' : ↥(s ∪ t) ↦ μ i' := rfl
    _ = ∫ (y : ((i : s) → π i) × ((j : t) → π j)), f (updateFinset x (s ∪ t) _)
          ∂(Measure.pi fun i : s ↦ μ i).prod (.pi fun j : t ↦ μ j) := by
        rw [measurePreserving_piFinsetUnion hst μ |>.integral_map_equiv]
    _ = ∫ (y : (i : s) → π i), ∫ (z : (j : t) → π j), f (updateFinset x (s ∪ t) (e (y, z)))
          ∂.pi fun j : t ↦ μ j ∂.pi fun i : s ↦ μ i := by
        apply integral_prod
        exact hf.comp_updateFinset_right x |>.comp_measurePreserving <|
          measurePreserving_piFinsetUnion hst μ
    _ = (∫⋯∫_s, ∫⋯∫_t, f ∂μ ∂μ) x := by
        simp_rw [marginal, updateFinset_updateFinset hst]
        rfl

theorem marginal_union' (f : (∀ i, π i) → E) (hf : Integrable f (.pi μ)) {s t : Finset δ}
    (hst : Disjoint s t) : ∫⋯∫_s ∪ t, f ∂μ = ∫⋯∫_t, ∫⋯∫_s, f ∂μ ∂μ := by
  rw [Finset.union_comm, marginal_union f hf hst.symm]

theorem marginal_singleton (f : (∀ i, π i) → E) (i : δ) :
    ∫⋯∫_{i}, f ∂μ = fun x ↦ ∫ xᵢ, f (Function.update x i xᵢ) ∂μ i := by
  let α : Type _ := ({i} : Finset δ)
  let e := (MeasurableEquiv.piUnique fun j : α ↦ π j).symm
  ext1 x
  calc (∫⋯∫_{i}, f ∂μ) x
      = ∫ (y : π (default : α)), f (updateFinset x {i} (e y)) ∂μ (default : α) := by
        simp_rw [marginal, measurePreserving_piUnique (fun j : ({i} : Finset δ) ↦ μ j) |>.symm _
          |>.integral_map_equiv]
    _ = ∫ xᵢ, f (Function.update x i xᵢ) ∂μ i := by simp [update_eq_updateFinset]; rfl

/-- Peel off a single integral from a `marginal` integral at the beginning (compare with
`marginal_insert'`, which peels off an integral at the end). -/
theorem marginal_insert (f : (∀ i, π i) → E) (hf : Integrable f (.pi μ)) {i : δ}
    (hi : i ∉ s) (x : ∀ i, π i) :
    (∫⋯∫_insert i s, f ∂μ) x = ∫ xᵢ, (∫⋯∫_s, f ∂μ) (Function.update x i xᵢ) ∂μ i := by
  rw [Finset.insert_eq, marginal_union f hf (Finset.disjoint_singleton_left.mpr hi),
    marginal_singleton]

/-- Peel off a single integral from a `marginal` integral at the beginning (compare with
`marginal_erase'`, which peels off an integral at the end). -/
theorem marginal_erase (f : (∀ i, π i) → E) (hf : Integrable f (.pi μ)) {i : δ}
    (hi : i ∈ s) (x : ∀ i, π i) :
    (∫⋯∫_s, f ∂μ) x = ∫ xᵢ, (∫⋯∫_(erase s i), f ∂μ) (Function.update x i xᵢ) ∂μ i := by
  simpa [insert_erase hi] using marginal_insert _ hf (not_mem_erase i s) x

/-- Peel off a single integral from a `marginal` integral at the end (compare with
`marginal_insert`, which peels off an integral at the beginning). -/
theorem marginal_insert' (f : (∀ i, π i) → E) (hf : Integrable f (.pi μ)) {i : δ}
    (hi : i ∉ s) :
    ∫⋯∫_insert i s, f ∂μ = ∫⋯∫_s, (fun x ↦ ∫ xᵢ, f (Function.update x i xᵢ) ∂μ i) ∂μ := by
  rw [Finset.insert_eq, Finset.union_comm,
    marginal_union (s := s) f hf (Finset.disjoint_singleton_right.mpr hi), marginal_singleton]

/-- Peel off a single integral from a `marginal` integral at the end (compare with
`marginal_erase`, which peels off an integral at the beginning). -/
theorem marginal_erase' (f : (∀ i, π i) → E) (hf : Integrable f (.pi μ)) {i : δ}
    (hi : i ∈ s) :
    ∫⋯∫_s, f ∂μ = ∫⋯∫_(erase s i), (fun x ↦ ∫ xᵢ, f (Function.update x i xᵢ) ∂μ i) ∂μ := by
  simpa [insert_erase hi] using marginal_insert' _ hf (not_mem_erase i s)

open Filter

@[gcongr]
theorem marginal_mono {f g : (∀ i, π i) → ℝ} (hf : Integrable f (.pi μ)) (hg : Integrable g (.pi μ))
    (hfg : f ≤ g) : ∫⋯∫_s, f ∂μ ≤ ∫⋯∫_s, g ∂μ :=
  fun x ↦ integral_mono (hf.comp_updateFinset_right x) (hg.comp_updateFinset_right x)
    fun _ ↦ hfg _

@[simp] theorem marginal_univ {f : (∀ i, π i) → E} :
    ∫⋯∫_univ, f ∂μ = fun _ ↦ ∫ x, f x ∂Measure.pi μ := by
  let e : { j // j ∈ Finset.univ } ≃ δ := Equiv.subtypeUnivEquiv mem_univ
  ext1 x
  simp_rw [marginal, measurePreserving_piCongrLeft μ e |>.integral_map_equiv, updateFinset]
  simp
  rfl

theorem integral_eq_marginal_univ {f : (∀ i, π i) → E} (x : ∀ i, π i) :
    ∫ x, f x ∂Measure.pi μ = (∫⋯∫_univ, f ∂μ) x := by simp

theorem marginal_image [DecidableEq δ'] {e : δ' → δ} (he : Injective e) (s : Finset δ')
    {f : (∀ i, π (e i)) → E} (hf : Integrable f (.pi μ)) (x : ∀ i, π i) :
      (∫⋯∫_s.image e, f ∘ (· ∘' e) ∂μ) x = (∫⋯∫_s, f ∂μ ∘' e) (x ∘' e) := by
  have h : Measurable ((· ∘' e) : (∀ i, π i) → _) :=
    measurable_pi_iff.mpr <| λ i ↦ measurable_pi_apply (e i)
  induction s using Finset.induction generalizing x
  case empty => simp
  case insert i s hi ih =>
    rw [image_insert, marginal_insert _ (hf.comp h) (he.mem_finset_image.not.mpr hi),
      marginal_insert _ hf hi]
    simp_rw [ih, ← update_comp_eq_of_injective' x he]

theorem marginal_update_of_not_mem {i : δ}
    {f : (∀ i, π i) → E} (hf : Integrable f (.pi μ)) (hi : i ∉ s) (x : ∀ i, π i) (y : π i) :
    (∫⋯∫_s, f ∂μ) (Function.update x i y) = (∫⋯∫_s, f ∘ (Function.update · i y) ∂μ) x := by
  induction s using Finset.induction generalizing x
  case empty => simp
  case insert i' s hi' ih =>
    rw [marginal_insert _ hf hi', marginal_insert _ (hf.comp measurable_update_left) hi']
    have hii' : i ≠ i' := mt (by rintro rfl; exact mem_insert_self i s) hi
    simp_rw [update_comm hii', ih (mt Finset.mem_insert_of_mem hi)]

theorem marginal_eq_of_subset {f g : (∀ i, π i) → E} (hst : s ⊆ t)
    (hf : Integrable f (.pi μ)) (hg : Measurable g) (hfg : ∫⋯∫_s, f ∂μ = ∫⋯∫_s, g ∂μ) :
    ∫⋯∫_t, f ∂μ = ∫⋯∫_t, g ∂μ := by
  rw [← union_sdiff_of_subset hst, marginal_union' μ f hf disjoint_sdiff,
    marginal_union' μ g hg disjoint_sdiff, hfg]

theorem marginal_le_of_subset {f g : (∀ i, π i) → E} (hst : s ⊆ t)
    (hf : Integrable f (.pi μ)) (hg : Measurable g) (hfg : ∫⋯∫_s, f ∂μ ≤ ∫⋯∫_s, g ∂μ) :
    ∫⋯∫_t, f ∂μ ≤ ∫⋯∫_t, g ∂μ := by
  rw [← union_sdiff_of_subset hst, marginal_union' μ f hf disjoint_sdiff,
    marginal_union' μ g hg disjoint_sdiff]
  exact marginal_mono hfg

theorem integral_eq_of_marginal_eq [Fintype δ] (s : Finset δ) {f g : (∀ i, π i) → E}
    (hf : Integrable f (.pi μ)) (hg : Measurable g) (hfg : ∫⋯∫_s, f ∂μ = ∫⋯∫_s, g ∂μ) :
    ∫ x, f x ∂Measure.pi μ = ∫ x, g x ∂Measure.pi μ := by
  rcases isEmpty_or_nonempty (∀ i, π i) with h|⟨⟨x⟩⟩
  · simp_rw [integral_of_isEmpty]
  simp_rw [integral_eq_marginal_univ x, marginal_eq_of_subset (Finset.subset_univ s) hf hg hfg]

theorem integral_le_of_marginal_le [Fintype δ] (s : Finset δ) {f g : (∀ i, π i) → E}
    (hf : Integrable f (.pi μ)) (hg : Measurable g) (hfg : ∫⋯∫_s, f ∂μ ≤ ∫⋯∫_s, g ∂μ) :
    ∫ x, f x ∂Measure.pi μ ≤ ∫ x, g x ∂Measure.pi μ := by
  rcases isEmpty_or_nonempty (∀ i, π i) with h|⟨⟨x⟩⟩
  · simp_rw [integral_of_isEmpty, le_rfl]
  simp_rw [integral_eq_marginal_univ x, marginal_le_of_subset (Finset.subset_univ s) hf hg hfg x]

end Marginal

end MeasureTheory
