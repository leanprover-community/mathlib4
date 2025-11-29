import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Order.CompletePartialOrder

/-!
# A function with vanishing lower Lebesgue integral which is not a.e. zero

This counterexample shows that the a.e. measurability hypothesis in
`MeasureTheory.lintegral_eq_zero_iff'` cannot be removed: the indicator function of the Vitali set
is a counterexample.

-/

open scoped ENNReal Real
open Function MeasureTheory Set

noncomputable section

def VitaliSet : Set (Icc (0 : ℝ) 1) := sorry -- defined in PR #20722

local notation "I" => Icc (0 : ℝ) 1

-- TODO: not quite the right definition yet, but this is the idea
def shift (t : Icc (0 : ℚ) 1) : I → I := fun x ↦
  if h : x + (t : ℝ) < 1 then ⟨x + t, sorry, h.le⟩ else ⟨x + t - 1, by linarith, sorry⟩

/-- Any two translates of the Vitali set by distinct amounts are disjoint. -/
lemma vitaliSet_disjoint_trans {s t : Icc (0 : ℚ) 1} (hst : s ≠ t) :
    Disjoint (shift s '' VitaliSet) (shift t '' VitaliSet) :=
  -- This holds by construction of the Vitali set:
  -- pick only one representative from each equivalence class.
  sorry

/-- The Vitali set does not contain any measurable subset of positive measure. -/
lemma not_vitaliSet_subset_measure_pos :
    ¬ (∃ s : Set I, s ⊆ VitaliSet ∧ Measurable s ∧ 0 < (volume.restrict I) s) := by
  by_contra h
  choose T hTV hTMeasurable hTvolume using h
  -- XXX: does measurability of T follow from some junk value?

  -- Lebesgue measure is translation-invariant...
  have hmtrans (t : Icc (0 : ℚ) 1) : MeasurableSet (shift t '' T) := sorry

  -- All shifts of T are disjoint: otherwise, shifts of VitaliSet were not disjoint, contradiction.
  have hdisjoint : ∀ s t : Icc (0 : ℚ) 1, s ≠ t → Disjoint (shift s '' T) (shift t '' T) := by
    by_contra! h
    choose s t hst h using h
    have : ¬(Disjoint (shift s '' VitaliSet) (shift t '' VitaliSet)) :=
      fun h' ↦ h (h'.mono (image_mono hTV) (image_mono hTV))
    exact this (vitaliSet_disjoint_trans hst)
  -- The union of all of these is measurable, a subset of Ioo 0 1 (thus has measure at most 1),
  -- but their measure is infinite by countable additivity.
  let A : Set I := ⋃ t : Icc (0 : ℚ) 1, (shift t '' T)
  -- Do we need this? I think we don't... but need the individual pieces.
  -- have : MeasurableSet A := MeasurableSet.iUnion (fun b ↦ hmtrans b)
  have h : volume A ≤ 1 := by
    have : volume (univ : Set I) = 1 := measure_univ
    rw [← this]
    gcongr
    exact subset_univ _

  have h' : volume A = ⊤ := by
    -- enumerate all the rationals in the interval: should be easy
    let enum : ℕ → Icc (0 : ℚ) 1 := sorry
    have hinj : Injective enum := sorry
    have hsurj : Surjective enum := sorry
    calc volume A
      _ = volume.toOuterMeasure A := rfl
      _ = volume.toOuterMeasure (⋃ (i : ℕ), (shift (enum i) '' T)) := by
        unfold A
        congr
        -- use hsurj
        sorry
      _ = ∑' (i : ℕ), volume.toOuterMeasure (shift ↑↑(enum i) '' T) := by
        apply volume.m_iUnion (f := fun n ↦ shift (enum n) '' T)
        · exact fun i ↦ hmtrans (enum i)
        · exact fun s t hst ↦ hdisjoint _ _ (hinj.ne hst)
      _ = ∑' (i : ℕ), (volume.restrict I) T := by
        congr
        ext i
        -- volume is translation-invariant; possibly some casting
        sorry
      _ = ⊤ := by
        rw [ENNReal.tsum_const]
        refine ((fun {a b} ↦ ENNReal.mul_eq_top.mpr) ?_)
        right
        exact ⟨by simp, hTvolume.ne'⟩
  simp_all only [measurableSet_Icc, Measure.restrict_apply', image_val_inter_self_left_eq_coe,
    Subtype.forall, mem_Icc, and_imp, ne_eq, Subtype.mk.injEq, top_le_iff, ENNReal.one_ne_top]

/-- There exists a non-negative function `I → ℝ` with vanishing lower Lebesgue integral
which is not zero a.e. -/
theorem exists_non_ae_zero_lintegral_zero :
    ∃ f : I → ℝ≥0∞, ¬(f =ᶠ[ae volume] 0) ∧ ∫⁻ a, f a ∂volume= 0 := by
  use indicator VitaliSet (fun _ ↦ 1)
  constructor
  · by_contra h
    rw [indicator_ae_eq_zero, support_const zero_ne_one.symm, inter_univ] at h
    sorry -- VitaliSet is not a zero set

  -- By definition, its lower Lebesgue integral is sup g ∫ g ( x ) d x,
  -- where the supremum runs over all non-negative measurable functions g : I → \R with g ≤ f .
  -- For each non-negative measurable function g with g\leq f, observe g\leq 1_{x : 0 < g x},
  -- thus \int g \leq \mu(x : 0 < g x) and we may restrict to indicator functions g.
  -- If g=1_A is an indicator function, we have A ⊆ S since g ≤ 1_S=f.
  -- On the other hand, \int g dx = volume A;
  -- this must be zero since S contains no subset of positive measure.
  sorry

end
