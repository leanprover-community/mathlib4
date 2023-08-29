/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.MeasureTheory.Integral.Lebesgue

#align_import measure_theory.measure.giry_monad from "leanprover-community/mathlib"@"56f4cd1ef396e9fd389b5d8371ee9ad91d163625"

/-!
# The Giry monad

Let X be a measurable space. The collection of all measures on X again
forms a measurable space. This construction forms a monad on
measurable spaces and measurable functions, called the Giry monad.

Note that most sources use the term "Giry monad" for the restriction
to *probability* measures. Here we include all measures on X.

See also `MeasureTheory/Category/MeasCat.lean`, containing an upgrade of the type-level
monad to an honest monad of the functor `measure : MeasCat ⥤ MeasCat`.

## References

* <https://ncatlab.org/nlab/show/Giry+monad>

## Tags

giry monad
-/


noncomputable section

open Classical BigOperators ENNReal

open Classical Set Filter

variable {α β : Type*}

namespace MeasureTheory

namespace Measure

variable [MeasurableSpace α] [MeasurableSpace β]

/-- Measurability structure on `Measure`: Measures are measurable w.r.t. all projections -/
instance instMeasurableSpace : MeasurableSpace (Measure α) :=
  ⨆ (s : Set α) (_ : MeasurableSet s), (borel ℝ≥0∞).comap fun μ => μ s
#align measure_theory.measure.measurable_space MeasureTheory.Measure.instMeasurableSpace

theorem measurable_coe {s : Set α} (hs : MeasurableSet s) : Measurable fun μ : Measure α => μ s :=
  Measurable.of_comap_le <| le_iSup_of_le s <| le_iSup_of_le hs <| le_rfl
#align measure_theory.measure.measurable_coe MeasureTheory.Measure.measurable_coe

theorem measurable_of_measurable_coe (f : β → Measure α)
    (h : ∀ (s : Set α), MeasurableSet s → Measurable fun b => f b s) : Measurable f :=
  Measurable.of_le_map <|
    iSup₂_le fun s hs =>
      MeasurableSpace.comap_le_iff_le_map.2 <| by rw [MeasurableSpace.map_comp]; exact h s hs
                                                  -- ⊢ borel ℝ≥0∞ ≤ MeasurableSpace.map ((fun μ => ↑↑μ s) ∘ f) inst✝
                                                                                 -- 🎉 no goals
#align measure_theory.measure.measurable_of_measurable_coe MeasureTheory.Measure.measurable_of_measurable_coe

instance instMeasurableAdd₂ {α : Type*} {m : MeasurableSpace α} : MeasurableAdd₂ (Measure α) := by
  refine' ⟨Measure.measurable_of_measurable_coe _ fun s hs => _⟩
  -- ⊢ Measurable fun b => ↑↑(b.fst + b.snd) s
  simp_rw [Measure.coe_add, Pi.add_apply]
  -- ⊢ Measurable fun b => ↑↑b.fst s + ↑↑b.snd s
  refine' Measurable.add _ _
  -- ⊢ Measurable fun b => ↑↑b.fst s
  · exact (Measure.measurable_coe hs).comp measurable_fst
    -- 🎉 no goals
  · exact (Measure.measurable_coe hs).comp measurable_snd
    -- 🎉 no goals
#align measure_theory.measure.has_measurable_add₂ MeasureTheory.Measure.instMeasurableAdd₂

theorem measurable_measure {μ : α → Measure β} :
    Measurable μ ↔ ∀ (s : Set β), MeasurableSet s → Measurable fun b => μ b s :=
  ⟨fun hμ _s hs => (measurable_coe hs).comp hμ, measurable_of_measurable_coe μ⟩
#align measure_theory.measure.measurable_measure MeasureTheory.Measure.measurable_measure

theorem measurable_map (f : α → β) (hf : Measurable f) :
    Measurable fun μ : Measure α => map f μ := by
  refine' measurable_of_measurable_coe _ fun s hs => _
  -- ⊢ Measurable fun b => ↑↑(map f b) s
  simp_rw [map_apply hf hs]
  -- ⊢ Measurable fun b => ↑↑b (f ⁻¹' s)
  exact measurable_coe (hf hs)
  -- 🎉 no goals
#align measure_theory.measure.measurable_map MeasureTheory.Measure.measurable_map

theorem measurable_dirac : Measurable (Measure.dirac : α → Measure α) := by
  refine' measurable_of_measurable_coe _ fun s hs => _
  -- ⊢ Measurable fun b => ↑↑(dirac b) s
  simp_rw [dirac_apply' _ hs]
  -- ⊢ Measurable fun b => indicator s 1 b
  exact measurable_one.indicator hs
  -- 🎉 no goals
#align measure_theory.measure.measurable_dirac MeasureTheory.Measure.measurable_dirac

theorem measurable_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun μ : Measure α => ∫⁻ x, f x ∂μ := by
  simp only [lintegral_eq_iSup_eapprox_lintegral, hf, SimpleFunc.lintegral]
  -- ⊢ Measurable fun μ => ⨆ (n : ℕ), ∑ x in SimpleFunc.range (SimpleFunc.eapprox ( …
  refine' measurable_iSup fun n => Finset.measurable_sum _ fun i _ => _
  -- ⊢ Measurable fun μ => i * ↑↑μ (↑(SimpleFunc.eapprox (fun x => f x) n) ⁻¹' {i})
  refine' Measurable.const_mul _ _
  -- ⊢ Measurable fun μ => ↑↑μ (↑(SimpleFunc.eapprox (fun x => f x) n) ⁻¹' {i})
  exact measurable_coe ((SimpleFunc.eapprox f n).measurableSet_preimage _)
  -- 🎉 no goals
#align measure_theory.measure.measurable_lintegral MeasureTheory.Measure.measurable_lintegral

/-- Monadic join on `Measure` in the category of measurable spaces and measurable
functions. -/
def join (m : Measure (Measure α)) : Measure α :=
  Measure.ofMeasurable (fun s _ => ∫⁻ μ, μ s ∂m)
    (by simp only [measure_empty, lintegral_const, zero_mul])
        -- 🎉 no goals
    (by
      intro f hf h
      -- ⊢ (fun s x => ∫⁻ (μ : Measure α), ↑↑μ s ∂m) (⋃ (i : ℕ), f i) (_ : MeasurableSe …
      simp_rw [measure_iUnion h hf]
      -- ⊢ ∫⁻ (μ : Measure α), ∑' (i : ℕ), ↑↑μ (f i) ∂m = ∑' (i : ℕ), ∫⁻ (μ : Measure α …
      apply lintegral_tsum
      -- ⊢ ∀ (i : ℕ), AEMeasurable fun a => ↑↑a (f i)
      intro i; exact (measurable_coe (hf i)).aemeasurable)
      -- ⊢ AEMeasurable fun a => ↑↑a (f i)
               -- 🎉 no goals
#align measure_theory.measure.join MeasureTheory.Measure.join

@[simp]
theorem join_apply {m : Measure (Measure α)} {s : Set α} (hs : MeasurableSet s) :
    join m s = ∫⁻ μ, μ s ∂m :=
  Measure.ofMeasurable_apply s hs
#align measure_theory.measure.join_apply MeasureTheory.Measure.join_apply

@[simp]
theorem join_zero : (0 : Measure (Measure α)).join = 0 := by
  ext1 s hs
  -- ⊢ ↑↑(join 0) s = ↑↑0 s
  simp only [hs, join_apply, lintegral_zero_measure, coe_zero, Pi.zero_apply]
  -- 🎉 no goals
#align measure_theory.measure.join_zero MeasureTheory.Measure.join_zero

theorem measurable_join : Measurable (join : Measure (Measure α) → Measure α) :=
  measurable_of_measurable_coe _ fun s hs => by
    simp only [join_apply hs]; exact measurable_lintegral (measurable_coe hs)
    -- ⊢ Measurable fun b => ∫⁻ (μ : Measure α), ↑↑μ s ∂b
                               -- 🎉 no goals
#align measure_theory.measure.measurable_join MeasureTheory.Measure.measurable_join

theorem lintegral_join {m : Measure (Measure α)} {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂join m = ∫⁻ μ, ∫⁻ x, f x ∂μ ∂m := by
  simp_rw [lintegral_eq_iSup_eapprox_lintegral hf, SimpleFunc.lintegral,
    join_apply (SimpleFunc.measurableSet_preimage _ _)]
  suffices
    ∀ (s : ℕ → Finset ℝ≥0∞) (f : ℕ → ℝ≥0∞ → Measure α → ℝ≥0∞), (∀ n r, Measurable (f n r)) →
      Monotone (fun n μ => ∑ r in s n, r * f n r μ) →
      ⨆ n, ∑ r in s n, r * ∫⁻ μ, f n r μ ∂m = ∫⁻ μ, ⨆ n, ∑ r in s n, r * f n r μ ∂m by
    refine'
      this (fun n => SimpleFunc.range (SimpleFunc.eapprox f n))
        (fun n r μ => μ (SimpleFunc.eapprox f n ⁻¹' {r})) _ _
    · exact fun n r => measurable_coe (SimpleFunc.measurableSet_preimage _ _)
    · exact fun n m h μ => SimpleFunc.lintegral_mono (SimpleFunc.monotone_eapprox _ h) le_rfl
  intro s f hf hm
  -- ⊢ ⨆ (n : ℕ), ∑ r in s n, r * ∫⁻ (μ : Measure α), f n r μ ∂m = ∫⁻ (μ : Measure  …
  rw [lintegral_iSup _ hm]
  -- ⊢ ⨆ (n : ℕ), ∑ r in s n, r * ∫⁻ (μ : Measure α), f n r μ ∂m = ⨆ (n : ℕ), ∫⁻ (a …
  swap
  -- ⊢ ∀ (n : ℕ), Measurable fun μ => ∑ r in s n, r * f n r μ
  · exact fun n => Finset.measurable_sum _ fun r _ => (hf _ _).const_mul _
    -- 🎉 no goals
  congr
  -- ⊢ (fun n => ∑ r in s n, r * ∫⁻ (μ : Measure α), f n r μ ∂m) = fun n => ∫⁻ (a : …
  funext n
  -- ⊢ ∑ r in s n, r * ∫⁻ (μ : Measure α), f n r μ ∂m = ∫⁻ (a : Measure α), ∑ r in  …
  rw [lintegral_finset_sum (s n)]
  -- ⊢ ∑ r in s n, r * ∫⁻ (μ : Measure α), f n r μ ∂m = ∑ b in s n, ∫⁻ (a : Measure …
  · simp_rw [lintegral_const_mul _ (hf _ _)]
    -- 🎉 no goals
  · exact fun r _ => (hf _ _).const_mul _
    -- 🎉 no goals
#align measure_theory.measure.lintegral_join MeasureTheory.Measure.lintegral_join

/-- Monadic bind on `Measure`, only works in the category of measurable spaces and measurable
functions. When the function `f` is not measurable the result is not well defined. -/
def bind (m : Measure α) (f : α → Measure β) : Measure β :=
  join (map f m)
#align measure_theory.measure.bind MeasureTheory.Measure.bind

@[simp]
theorem bind_zero_left (f : α → Measure β) : bind 0 f = 0 := by simp [bind]
                                                                -- 🎉 no goals
#align measure_theory.measure.bind_zero_left MeasureTheory.Measure.bind_zero_left

@[simp]
theorem bind_zero_right (m : Measure α) : bind m (0 : α → Measure β) = 0 := by
  ext1 s hs
  -- ⊢ ↑↑(bind m 0) s = ↑↑0 s
  simp only [bind, hs, join_apply, coe_zero, Pi.zero_apply]
  -- ⊢ ∫⁻ (μ : Measure β), ↑↑μ s ∂map 0 m = 0
  rw [lintegral_map (measurable_coe hs) measurable_zero]
  -- ⊢ ∫⁻ (a : α), ↑↑(OfNat.ofNat 0 a) s ∂m = 0
  simp only [Pi.zero_apply, coe_zero, lintegral_const, zero_mul]
  -- 🎉 no goals
#align measure_theory.measure.bind_zero_right MeasureTheory.Measure.bind_zero_right

@[simp]
theorem bind_zero_right' (m : Measure α) : bind m (fun _ => 0 : α → Measure β) = 0 :=
  bind_zero_right m
#align measure_theory.measure.bind_zero_right' MeasureTheory.Measure.bind_zero_right'

@[simp]
theorem bind_apply {m : Measure α} {f : α → Measure β} {s : Set β} (hs : MeasurableSet s)
    (hf : Measurable f) : bind m f s = ∫⁻ a, f a s ∂m := by
  rw [bind, join_apply hs, lintegral_map (measurable_coe hs) hf]
  -- 🎉 no goals
#align measure_theory.measure.bind_apply MeasureTheory.Measure.bind_apply

theorem measurable_bind' {g : α → Measure β} (hg : Measurable g) : Measurable fun m => bind m g :=
  measurable_join.comp (measurable_map _ hg)
#align measure_theory.measure.measurable_bind' MeasureTheory.Measure.measurable_bind'

theorem lintegral_bind {m : Measure α} {μ : α → Measure β} {f : β → ℝ≥0∞} (hμ : Measurable μ)
    (hf : Measurable f) : ∫⁻ x, f x ∂bind m μ = ∫⁻ a, ∫⁻ x, f x ∂μ a ∂m :=
  (lintegral_join hf).trans (lintegral_map (measurable_lintegral hf) hμ)
#align measure_theory.measure.lintegral_bind MeasureTheory.Measure.lintegral_bind

theorem bind_bind {γ} [MeasurableSpace γ] {m : Measure α} {f : α → Measure β} {g : β → Measure γ}
    (hf : Measurable f) (hg : Measurable g) : bind (bind m f) g = bind m fun a => bind (f a) g := by
  ext1 s hs
  -- ⊢ ↑↑(bind (bind m f) g) s = ↑↑(bind m fun a => bind (f a) g) s
  erw [bind_apply hs hg, bind_apply hs ((measurable_bind' hg).comp hf),
    lintegral_bind hf ((measurable_coe hs).comp hg)]
  conv_rhs => enter [2, a]; erw [bind_apply hs hg]
  -- 🎉 no goals
#align measure_theory.measure.bind_bind MeasureTheory.Measure.bind_bind

theorem bind_dirac {f : α → Measure β} (hf : Measurable f) (a : α) : bind (dirac a) f = f a := by
  ext1 s hs
  -- ⊢ ↑↑(bind (dirac a) f) s = ↑↑(f a) s
  erw [bind_apply hs hf, lintegral_dirac' a ((measurable_coe hs).comp hf)]
  -- ⊢ ((fun μ => ↑↑μ s) ∘ f) a = ↑↑(f a) s
  rfl
  -- 🎉 no goals
#align measure_theory.measure.bind_dirac MeasureTheory.Measure.bind_dirac

theorem dirac_bind {m : Measure α} : bind m dirac = m := by
  ext1 s hs
  -- ⊢ ↑↑(bind m dirac) s = ↑↑m s
  simp only [bind_apply hs measurable_dirac, dirac_apply' _ hs, lintegral_indicator 1 hs,
    Pi.one_apply, lintegral_one, restrict_apply, MeasurableSet.univ, univ_inter]
#align measure_theory.measure.dirac_bind MeasureTheory.Measure.dirac_bind

theorem join_eq_bind (μ : Measure (Measure α)) : join μ = bind μ id := by rw [bind, map_id]
                                                                          -- 🎉 no goals
#align measure_theory.measure.join_eq_bind MeasureTheory.Measure.join_eq_bind

theorem join_map_map {f : α → β} (hf : Measurable f) (μ : Measure (Measure α)) :
    join (map (map f) μ) = map f (join μ) := by
  ext1 s hs
  -- ⊢ ↑↑(join (map (map f) μ)) s = ↑↑(map f (join μ)) s
  rw [join_apply hs, map_apply hf hs, join_apply (hf hs),
    lintegral_map (measurable_coe hs) (measurable_map f hf)]
  simp_rw [map_apply hf hs]
  -- 🎉 no goals
#align measure_theory.measure.join_map_map MeasureTheory.Measure.join_map_map

theorem join_map_join (μ : Measure (Measure (Measure α))) : join (map join μ) = join (join μ) := by
  show bind μ join = join (join μ)
  -- ⊢ bind μ join = join (join μ)
  rw [join_eq_bind, join_eq_bind, bind_bind measurable_id measurable_id]
  -- ⊢ bind μ join = bind μ fun a => bind (id a) id
  apply congr_arg (bind μ)
  -- ⊢ join = fun a => bind (id a) id
  funext ν
  -- ⊢ join ν = bind (id ν) id
  exact join_eq_bind ν
  -- 🎉 no goals
#align measure_theory.measure.join_map_join MeasureTheory.Measure.join_map_join

theorem join_map_dirac (μ : Measure α) : join (map dirac μ) = μ :=
  dirac_bind
#align measure_theory.measure.join_map_dirac MeasureTheory.Measure.join_map_dirac

theorem join_dirac (μ : Measure α) : join (dirac μ) = μ :=
  (join_eq_bind (dirac μ)).trans (bind_dirac measurable_id _)
#align measure_theory.measure.join_dirac MeasureTheory.Measure.join_dirac

end Measure

end MeasureTheory
