/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Floor
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Order.Filter.Map
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# The Giry monad

Let X be a measurable space. The collection of all measures on X again
forms a measurable space. This construction forms a monad on
measurable spaces and measurable functions, called the Giry monad.

Note that most sources use the term "Giry monad" for the restriction
to *probability* measures. Here we include all measures on X.

See also `Mathlib/MeasureTheory/Category/MeasCat.lean`, containing an upgrade of the type-level
monad to an honest monad of the functor `measure : MeasCat ⥤ MeasCat`.

## References

* <https://ncatlab.org/nlab/show/Giry+monad>

## Tags

giry monad
-/

@[expose] public section


noncomputable section

open ENNReal Set Filter

variable {α β : Type*}

namespace MeasureTheory

namespace Measure

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- Measurability structure on `Measure`: Measures are measurable w.r.t. all projections -/
instance instMeasurableSpace : MeasurableSpace (Measure α) :=
  ⨆ (s : Set α) (_ : MeasurableSet s), (borel ℝ≥0∞).comap fun μ => μ s

theorem measurable_coe {s : Set α} (hs : MeasurableSet s) : Measurable fun μ : Measure α => μ s :=
  Measurable.of_comap_le <| le_iSup_of_le s <| le_iSup_of_le hs <| le_rfl

theorem measurable_of_measurable_coe (f : β → Measure α)
    (h : ∀ (s : Set α), MeasurableSet s → Measurable fun b => f b s) : Measurable f :=
  Measurable.of_le_map <|
    iSup₂_le fun s hs =>
      MeasurableSpace.comap_le_iff_le_map.2 <| by rw [MeasurableSpace.map_comp]; exact h s hs

instance instMeasurableAdd₂ {α : Type*} {m : MeasurableSpace α} : MeasurableAdd₂ (Measure α) := by
  refine ⟨Measure.measurable_of_measurable_coe _ fun s hs => ?_⟩
  simp_rw [Measure.coe_add, Pi.add_apply]
  refine Measurable.add ?_ ?_
  · exact (Measure.measurable_coe hs).comp measurable_fst
  · exact (Measure.measurable_coe hs).comp measurable_snd

-- There is no typeclass for measurability of `SMul` only on that side, otherwise we could
-- turn that into an instance.
@[fun_prop]
lemma _root_.Measurable.smul_measure {f : α → ℝ≥0∞} (hf : Measurable f) (μ : Measure β) :
    Measurable (fun x ↦ f x • μ) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  fun_prop

theorem measurable_measure {μ : α → Measure β} :
    Measurable μ ↔ ∀ (s : Set β), MeasurableSet s → Measurable fun b => μ b s :=
  ⟨fun hμ _s hs => (measurable_coe hs).comp hμ, measurable_of_measurable_coe μ⟩

theorem _root_.Measurable.measure_of_isPiSystem {μ : α → Measure β} [∀ a, IsFiniteMeasure (μ a)]
    {S : Set (Set β)} (hgen : ‹MeasurableSpace β› = .generateFrom S) (hpi : IsPiSystem S)
    (h_basic : ∀ s ∈ S, Measurable fun a ↦ μ a s) (h_univ : Measurable fun a ↦ μ a univ) :
    Measurable μ := by
  rw [measurable_measure]
  intro s hs
  induction s, hs using MeasurableSpace.induction_on_inter hgen hpi with
  | empty => simp
  | basic s hs => exact h_basic s hs
  | compl s hsm ihs =>
    simp only [measure_compl hsm (measure_ne_top _ _)]
    exact h_univ.sub ihs
  | iUnion f hfd hfm ihf =>
    simpa only [measure_iUnion hfd hfm] using .tsum ihf

theorem _root_.Measurable.measure_of_isPiSystem_of_isProbabilityMeasure {μ : α → Measure β}
    [∀ a, IsProbabilityMeasure (μ a)]
    {S : Set (Set β)} (hgen : ‹MeasurableSpace β› = .generateFrom S) (hpi : IsPiSystem S)
    (h_basic : ∀ s ∈ S, Measurable fun a ↦ μ a s) : Measurable μ :=
  .measure_of_isPiSystem hgen hpi h_basic <| by simp

@[fun_prop]
theorem measurable_map (f : α → β) (hf : Measurable f) :
    Measurable fun μ : Measure α => map f μ := by
  refine measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [map_apply hf hs]
  exact measurable_coe (hf hs)

@[fun_prop]
theorem measurable_dirac : Measurable (Measure.dirac : α → Measure α) := by
  refine measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [dirac_apply' _ hs]
  exact measurable_one.indicator hs

@[fun_prop]
theorem measurable_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun μ : Measure α => ∫⁻ x, f x ∂μ := by
  simp only [lintegral_eq_iSup_eapprox_lintegral, hf, SimpleFunc.lintegral]
  refine .iSup fun n => Finset.measurable_fun_sum _ fun i _ => ?_
  refine Measurable.const_mul ?_ _
  exact measurable_coe ((SimpleFunc.eapprox f n).measurableSet_preimage _)

/-- Monadic join on `Measure` in the category of measurable spaces and measurable
functions. -/
def join (m : Measure (Measure α)) : Measure α :=
  Measure.ofMeasurable (fun s _ => ∫⁻ μ, μ s ∂m)
    (by simp only [measure_empty, lintegral_const, zero_mul])
    (by
      intro f hf h
      simp_rw [measure_iUnion h hf]
      apply lintegral_tsum
      intro i; exact (measurable_coe (hf i)).aemeasurable)

@[simp]
theorem join_apply {m : Measure (Measure α)} {s : Set α} (hs : MeasurableSet s) :
    join m s = ∫⁻ μ, μ s ∂m :=
  Measure.ofMeasurable_apply s hs

theorem le_join_apply (m : Measure (Measure α)) (s : Set α) : ∫⁻ μ, μ s ∂m ≤ join m s := by
  rw [measure_eq_iInf]
  exact le_iInf₂ fun t hst ↦ le_iInf fun htm ↦ join_apply htm ▸ by gcongr

@[simp]
theorem join_smul {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R)
    (m : Measure (Measure α)) : (c • m).join = c • m.join := by
  ext s hs
  simp [hs]

lemma join_sum {ι : Type*} (m : ι → Measure (Measure α)) :
    (sum m).join = sum fun (i : ι) ↦ (m i).join := by
  ext s hs
  simp_rw [sum_apply _ hs, join_apply hs, lintegral_sum_measure]

@[simp]
theorem join_dirac (μ : Measure α) : join (dirac μ) = μ := by
  ext s hs
  simp [hs, lintegral_dirac', measurable_coe]

theorem le_ae_join (m : Measure (Measure α)) : (ae m).bind ae ≤ ae m.join := by
  intro s hs
  rcases exists_measurable_superset_of_null hs with ⟨t, hst, htm, ht⟩
  rw [join_apply htm, lintegral_eq_zero_iff (measurable_coe htm)] at ht
  rw [mem_bind']
  exact ht.mono fun _ ↦ measure_mono_null hst

theorem ae_ae_of_ae_join {m : Measure (Measure α)} {p : α → Prop} (h : ∀ᵐ a ∂m.join, p a) :
    ∀ᵐ μ ∂m, ∀ᵐ a ∂μ, p a :=
  le_ae_join m h

theorem _root_.AEMeasurable.ae_of_join {m : Measure (Measure α)} {f : α → β}
    (h : AEMeasurable f m.join) : ∀ᵐ μ ∂m, AEMeasurable f μ :=
  let ⟨g, hgm, hg⟩ := h; (ae_ae_of_ae_join hg).mono fun _μ hμ ↦ ⟨g, hgm, hμ⟩

theorem aemeasurable_lintegral {m : Measure (Measure α)} {f : α → ℝ≥0∞}
    (h : AEMeasurable f m.join) : AEMeasurable (fun μ ↦ ∫⁻ a, f a ∂μ) m :=
  let ⟨g, hgm, hfg⟩ := h
  ⟨fun μ ↦ ∫⁻ a, g a ∂μ, measurable_lintegral hgm,
    (ae_ae_of_ae_join hfg).mono fun _ ↦ lintegral_congr_ae⟩

@[simp]
theorem join_zero : (0 : Measure (Measure α)).join = 0 := by
  ext1 s hs
  simp [hs]

@[fun_prop]
theorem measurable_join : Measurable (join : Measure (Measure α) → Measure α) :=
  measurable_of_measurable_coe _ fun s hs => by
    simp only [join_apply hs, measurable_lintegral (measurable_coe hs)]

theorem lintegral_join {m : Measure (Measure α)} {f : α → ℝ≥0∞} (hf : AEMeasurable f (join m)) :
    ∫⁻ x, f x ∂join m = ∫⁻ μ, ∫⁻ x, f x ∂μ ∂m := by
  wlog hfm : Measurable f generalizing f
  · rcases hf with ⟨g, hgm, hfg⟩
    rw [lintegral_congr_ae hfg, this hgm.aemeasurable hgm]
    exact lintegral_congr_ae <| (ae_ae_of_ae_join hfg).mono fun μ hμ ↦
      .symm <| lintegral_congr_ae hμ
  simp_rw [lintegral_eq_iSup_eapprox_lintegral hfm, SimpleFunc.lintegral,
    join_apply (SimpleFunc.measurableSet_preimage _ _)]
  clear hf
  suffices
    ∀ (s : ℕ → Finset ℝ≥0∞) (f : ℕ → ℝ≥0∞ → Measure α → ℝ≥0∞), (∀ n r, Measurable (f n r)) →
      Monotone (fun n μ => ∑ r ∈ s n, r * f n r μ) →
      ⨆ n, ∑ r ∈ s n, r * ∫⁻ μ, f n r μ ∂m = ∫⁻ μ, ⨆ n, ∑ r ∈ s n, r * f n r μ ∂m by
    refine
      this (fun n => SimpleFunc.range (SimpleFunc.eapprox f n))
        (fun n r μ => μ (SimpleFunc.eapprox f n ⁻¹' {r})) ?_ ?_
    · exact fun n r => measurable_coe (SimpleFunc.measurableSet_preimage _ _)
    · exact fun n m h μ => SimpleFunc.lintegral_mono (SimpleFunc.monotone_eapprox _ h) le_rfl
  intro s f hf hm
  rw [lintegral_iSup _ hm]
  swap
  · fun_prop
  congr
  funext n
  rw [lintegral_finsetSum (s n)]
  · simp_rw [lintegral_const_mul _ (hf _ _)]
  · exact fun r _ => (hf _ _).const_mul _

theorem lintegral_join_le (f : α → ℝ≥0∞) (m : Measure (Measure α)) :
    ∫⁻ x, f x ∂join m ≤ ∫⁻ μ, ∫⁻ x, f x ∂μ ∂m := by
  rcases exists_measurable_le_lintegral_eq (join m) f with ⟨g, hgm, hgf, hfg_int⟩
  rw [hfg_int, lintegral_join hgm.aemeasurable]
  gcongr
  apply hgf

/-- Monadic bind on `Measure`, only works in the category of measurable spaces and measurable
functions. When the function `f` is not measurable the result is not well defined. -/
def bind (m : Measure α) (f : α → Measure β) : Measure β :=
  join (map f m)

@[simp]
theorem bind_zero_left (f : α → Measure β) : bind (0 : Measure α) f = 0 := by simp [bind]

@[simp]
theorem bind_apply {m : Measure α} {f : α → Measure β} {s : Set β} (hs : MeasurableSet s)
    (hf : AEMeasurable f m) : bind m f s = ∫⁻ a, f a s ∂m := by
  rw [bind, join_apply hs, lintegral_map' (measurable_coe hs).aemeasurable hf]

theorem bind_apply_le {m : Measure α} (f : α → Measure β) {s : Set β} (hs : MeasurableSet s) :
    bind m f s ≤ ∫⁻ a, f a s ∂m := by
  rw [bind, join_apply hs]
  apply lintegral_map_le

theorem ae_ae_of_ae_bind {m : Measure α} {f : α → Measure β} {p : β → Prop} (hf : AEMeasurable f m)
    (h : ∀ᵐ b ∂m.bind f, p b) : ∀ᵐ a ∂m, ∀ᵐ b ∂f a, p b :=
  ae_of_ae_map hf <| ae_ae_of_ae_join h

theorem _root_.AEMeasurable.ae_of_bind {γ : Type*} {_ : MeasurableSpace γ} {m : Measure α}
    {f : α → Measure β} {g : β → γ} (hf : AEMeasurable f m) (hg : AEMeasurable g (m.bind f)) :
    ∀ᵐ a ∂m, AEMeasurable g (f a) :=
  ae_of_ae_map hf hg.ae_of_join

theorem bind_congr_right {μ : Measure α} {f g : α → Measure β} (h : f =ᵐ[μ] g) :
    μ.bind f = μ.bind g :=
  congrArg join <| map_congr h

@[simp]
lemma bind_const {m : Measure α} {ν : Measure β} : m.bind (fun _ ↦ ν) = m Set.univ • ν := by
  simp [bind]

theorem bind_zero_right' (m : Measure α) : bind m (fun _ => 0 : α → Measure β) = 0 := by simp

@[simp]
theorem bind_zero_right (m : Measure α) : bind m (0 : α → Measure β) = 0 := bind_zero_right' m

@[fun_prop]
theorem measurable_bind' {g : α → Measure β} (hg : Measurable g) :
    Measurable fun m : Measure α => bind m g :=
  measurable_join.comp (measurable_map _ hg)

theorem aemeasurable_bind {g : α → Measure β} {m : Measure (Measure α)}
    (hg : AEMeasurable g m.join) : AEMeasurable (bind · g) m :=
  let ⟨f, hfm, hf⟩ := hg
  ⟨(bind · f), measurable_bind' hfm, (ae_ae_of_ae_join hf).mono fun _ ↦ bind_congr_right⟩

theorem bind_sum {ι : Type*} (m : ι → Measure α) (f : α → Measure β)
    (h : AEMeasurable f (sum fun i => m i)) :
    (sum fun (i : ι) ↦ m i).bind f = sum fun (i : ι) ↦ (m i).bind f := by
  simp_rw [bind, map_sum h, join_sum]

lemma bind_smul {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R) (m : Measure α)
    (f : α → Measure β) : (c • m).bind f = c • (m.bind f) := by
  simp_rw [bind, Measure.map_smul, join_smul]

theorem lintegral_bind {m : Measure α} {μ : α → Measure β} {f : β → ℝ≥0∞} (hμ : AEMeasurable μ m)
    (hf : AEMeasurable f (bind m μ)) : ∫⁻ x, f x ∂bind m μ = ∫⁻ a, ∫⁻ x, f x ∂μ a ∂m :=
  (lintegral_join hf).trans (lintegral_map' (aemeasurable_lintegral hf) hμ)

theorem lintegral_bind_le (f : β → ℝ≥0∞) (m : Measure α) (μ : α → Measure β) :
    ∫⁻ x, f x ∂bind m μ ≤ ∫⁻ a, ∫⁻ x, f x ∂μ a ∂m :=
  (lintegral_join_le _ _).trans (lintegral_map_le _ _)

theorem bind_bind {γ} [MeasurableSpace γ] {m : Measure α} {f : α → Measure β} {g : β → Measure γ}
    (hf : AEMeasurable f m) (hg : AEMeasurable g (m.bind f)) :
    bind (bind m f) g = bind m fun a => bind (f a) g := by
  ext1 s hs
  rw [bind_apply hs hg, lintegral_bind hf, bind_apply hs]
  · exact lintegral_congr_ae <| (hf.ae_of_bind hg).mono fun a ha ↦ .symm <| bind_apply hs ha
  · exact (aemeasurable_bind hg).comp_aemeasurable hf
  · exact (measurable_coe hs).comp_aemeasurable hg

@[simp]
theorem dirac_bind {f : α → Measure β} (hf : Measurable f) (a : α) : bind (dirac a) f = f a := by
  simp [bind, map_dirac' hf]

@[simp]
theorem bind_dirac {m : Measure α} : bind m dirac = m := by
  ext1 s hs
  simp only [bind_apply hs measurable_dirac.aemeasurable, dirac_apply' _ hs, lintegral_indicator hs,
    Pi.one_apply, lintegral_one, restrict_apply, MeasurableSet.univ, univ_inter]

@[simp]
lemma bind_dirac_eq_map (m : Measure α) {f : α → β} (hf : Measurable f) :
    m.bind (fun x ↦ Measure.dirac (f x)) = m.map f := by
  rw [← bind_dirac (m := m.map f), bind, bind, map_map, Function.comp_def]
  exacts [measurable_dirac, hf]

theorem join_eq_bind (μ : Measure (Measure α)) : join μ = bind μ id := by rw [bind, map_id]

theorem join_map_map {f : α → β} (hf : Measurable f) (μ : Measure (Measure α)) :
    join (map (map f) μ) = map f (join μ) := by
  ext1 s hs
  rw [join_apply hs, map_apply hf hs, join_apply (hf hs),
    lintegral_map (measurable_coe hs) (measurable_map f hf)]
  simp_rw [map_apply hf hs]

theorem join_map_join (μ : Measure (Measure (Measure α))) : join (map join μ) = join (join μ) := by
  change bind μ join = join (join μ)
  rw [join_eq_bind, join_eq_bind, bind_bind aemeasurable_id aemeasurable_id]
  apply congr_arg (bind μ)
  funext ν
  exact join_eq_bind ν

theorem join_map_dirac (μ : Measure α) : join (map dirac μ) = μ := bind_dirac

end Measure

end MeasureTheory
