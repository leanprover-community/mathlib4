/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Quasi-Measure-Preserving Functions

A map `f : α → β` is said to be *quasi-measure-preserving* (a.k.a. non-singular) w.r.t. measures
`μa` and `μb` if it is measurable and `μb s = 0` implies `μa (f ⁻¹' s) = 0`.
That last condition can also be written `μa.map f ≪ μb` (the map of `μa` by `f` is
absolutely continuous with respect to `μb`).

## Main definitions

* `MeasureTheory.Measure.QuasiMeasurePreserving f μa μb`: `f` is quasi-measure-preserving with
  respect to `μa` and `μb`.

-/

variable {α β γ δ : Type*}

namespace MeasureTheory

open Set Function ENNReal
open Filter hiding map

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {s : Set α}

namespace Measure

/-- A map `f : α → β` is said to be *quasi-measure-preserving* (a.k.a. non-singular) w.r.t. measures
`μa` and `μb` if it is measurable and `μb s = 0` implies `μa (f ⁻¹' s) = 0`. -/
@[fun_prop]
structure QuasiMeasurePreserving {m0 : MeasurableSpace α} (f : α → β)
  (μa : Measure α := by volume_tac)
  (μb : Measure β := by volume_tac) : Prop where
  protected measurable : Measurable f
  protected absolutelyContinuous : μa.map f ≪ μb

attribute [fun_prop] QuasiMeasurePreserving.measurable

namespace QuasiMeasurePreserving

@[fun_prop]
protected theorem id {_m0 : MeasurableSpace α} (μ : Measure α) : QuasiMeasurePreserving id μ μ :=
  ⟨measurable_id, map_id.absolutelyContinuous⟩

variable {μa μa' : Measure α} {μb μb' : Measure β} {μc : Measure γ} {f : α → β}

protected theorem _root_.Measurable.quasiMeasurePreserving
    {_m0 : MeasurableSpace α} (hf : Measurable f) (μ : Measure α) :
    QuasiMeasurePreserving f μ (μ.map f) :=
  ⟨hf, AbsolutelyContinuous.rfl⟩

theorem mono_left (h : QuasiMeasurePreserving f μa μb) (ha : μa' ≪ μa) :
    QuasiMeasurePreserving f μa' μb :=
  ⟨h.1, (ha.map h.1).trans h.2⟩

theorem mono_right (h : QuasiMeasurePreserving f μa μb) (ha : μb ≪ μb') :
    QuasiMeasurePreserving f μa μb' :=
  ⟨h.1, h.2.trans ha⟩

@[mono]
theorem mono (ha : μa' ≪ μa) (hb : μb ≪ μb') (h : QuasiMeasurePreserving f μa μb) :
    QuasiMeasurePreserving f μa' μb' :=
  (h.mono_left ha).mono_right hb

@[fun_prop]
protected theorem comp {g : β → γ} {f : α → β} (hg : QuasiMeasurePreserving g μb μc)
    (hf : QuasiMeasurePreserving f μa μb) : QuasiMeasurePreserving (g ∘ f) μa μc :=
  ⟨hg.measurable.comp hf.measurable, by
    rw [← map_map hg.1 hf.1]
    exact (hf.2.map hg.1).trans hg.2⟩

protected theorem iterate {f : α → α} (hf : QuasiMeasurePreserving f μa μa) :
    ∀ n, QuasiMeasurePreserving f^[n] μa μa
  | 0 => QuasiMeasurePreserving.id μa
  | n + 1 => (hf.iterate n).comp hf

protected theorem aemeasurable (hf : QuasiMeasurePreserving f μa μb) : AEMeasurable f μa :=
  hf.1.aemeasurable

theorem smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (hf : QuasiMeasurePreserving f μa μb) (c : R) : QuasiMeasurePreserving f (c • μa) (c • μb) :=
  ⟨hf.1, by rw [Measure.map_smul]; exact hf.2.smul c⟩

theorem ae_map_le (h : QuasiMeasurePreserving f μa μb) : ae (μa.map f) ≤ ae μb :=
  h.2.ae_le

theorem tendsto_ae (h : QuasiMeasurePreserving f μa μb) : Tendsto f (ae μa) (ae μb) :=
  (tendsto_ae_map h.aemeasurable).mono_right h.ae_map_le

theorem ae (h : QuasiMeasurePreserving f μa μb) {p : β → Prop} (hg : ∀ᵐ x ∂μb, p x) :
    ∀ᵐ x ∂μa, p (f x) :=
  h.tendsto_ae hg

theorem ae_eq (h : QuasiMeasurePreserving f μa μb) {g₁ g₂ : β → δ} (hg : g₁ =ᵐ[μb] g₂) :
    g₁ ∘ f =ᵐ[μa] g₂ ∘ f :=
  h.ae hg

theorem preimage_null (h : QuasiMeasurePreserving f μa μb) {s : Set β} (hs : μb s = 0) :
    μa (f ⁻¹' s) = 0 :=
  preimage_null_of_map_null h.aemeasurable (h.2 hs)

theorem preimage_mono_ae {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s ≤ᵐ[μb] t) :
    f ⁻¹' s ≤ᵐ[μa] f ⁻¹' t :=
  eventually_map.mp <|
    Eventually.filter_mono (tendsto_ae_map hf.aemeasurable) (Eventually.filter_mono hf.ae_map_le h)

theorem preimage_ae_eq {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s =ᵐ[μb] t) :
    f ⁻¹' s =ᵐ[μa] f ⁻¹' t :=
  EventuallyLE.antisymm (hf.preimage_mono_ae h.le) (hf.preimage_mono_ae h.symm.le)

/-- The preimage of a null measurable set under a (quasi-)measure-preserving map is a null
measurable set. -/
theorem _root_.MeasureTheory.NullMeasurableSet.preimage {s : Set β} (hs : NullMeasurableSet s μb)
    (hf : QuasiMeasurePreserving f μa μb) : NullMeasurableSet (f ⁻¹' s) μa :=
  let ⟨t, htm, hst⟩ := hs
  ⟨f ⁻¹' t, hf.measurable htm, hf.preimage_ae_eq hst⟩

theorem preimage_iterate_ae_eq {s : Set α} {f : α → α} (hf : QuasiMeasurePreserving f μ μ) (k : ℕ)
    (hs : f ⁻¹' s =ᵐ[μ] s) : f^[k] ⁻¹' s =ᵐ[μ] s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ, preimage_comp]
    exact EventuallyEq.trans (hf.preimage_ae_eq ih) hs

theorem image_zpow_ae_eq {s : Set α} {e : α ≃ α} (he : QuasiMeasurePreserving e μ μ)
    (he' : QuasiMeasurePreserving e.symm μ μ) (k : ℤ) (hs : e '' s =ᵐ[μ] s) :
    (⇑(e ^ k)) '' s =ᵐ[μ] s := by
  rw [Equiv.image_eq_preimage]
  obtain ⟨k, rfl | rfl⟩ := k.eq_nat_or_neg
  · replace hs : (⇑e⁻¹) ⁻¹' s =ᵐ[μ] s := by rwa [Equiv.image_eq_preimage] at hs
    replace he' : (⇑e⁻¹)^[k] ⁻¹' s =ᵐ[μ] s := he'.preimage_iterate_ae_eq k hs
    rwa [Equiv.Perm.iterate_eq_pow e⁻¹ k, inv_pow e k] at he'
  · rw [zpow_neg, zpow_natCast]
    replace hs : e ⁻¹' s =ᵐ[μ] s := by
      convert he.preimage_ae_eq hs.symm
      rw [Equiv.preimage_image]
    replace he : (⇑e)^[k] ⁻¹' s =ᵐ[μ] s := he.preimage_iterate_ae_eq k hs
    rwa [Equiv.Perm.iterate_eq_pow e k] at he

-- Need to specify `α := Set α` below because of diamond; see https://github.com/leanprover-community/mathlib4/issues/10941
theorem limsup_preimage_iterate_ae_eq {f : α → α} (hf : QuasiMeasurePreserving f μ μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) : limsup (α := Set α) (fun n => (preimage f)^[n] s) atTop =ᵐ[μ] s :=
  limsup_ae_eq_of_forall_ae_eq (fun n => (preimage f)^[n] s) fun n ↦ by
    simpa only [Set.preimage_iterate_eq] using hf.preimage_iterate_ae_eq n hs

-- Need to specify `α := Set α` below because of diamond; see https://github.com/leanprover-community/mathlib4/issues/10941
theorem liminf_preimage_iterate_ae_eq {f : α → α} (hf : QuasiMeasurePreserving f μ μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) : liminf (α := Set α) (fun n => (preimage f)^[n] s) atTop =ᵐ[μ] s :=
  liminf_ae_eq_of_forall_ae_eq (fun n => (preimage f)^[n] s) fun n ↦ by
    simpa only [Set.preimage_iterate_eq] using hf.preimage_iterate_ae_eq n hs

/-- For a quasi-measure-preserving self-map `f`, if a null measurable set `s` is a.e. invariant,
then it is a.e. equal to a measurable invariant set.
-/
theorem exists_preimage_eq_of_preimage_ae {f : α → α} (h : QuasiMeasurePreserving f μ μ)
    (hs : NullMeasurableSet s μ) (hs' : f ⁻¹' s =ᵐ[μ] s) :
    ∃ t : Set α, MeasurableSet t ∧ t =ᵐ[μ] s ∧ f ⁻¹' t = t := by
  obtain ⟨t, htm, ht⟩ := hs
  refine ⟨limsup (f^[·] ⁻¹' t) atTop, ?_, ?_, ?_⟩
  · exact .measurableSet_limsup fun n ↦ h.measurable.iterate n htm
  · have : f ⁻¹' t =ᵐ[μ] t := (h.preimage_ae_eq ht.symm).trans (hs'.trans ht)
    exact limsup_ae_eq_of_forall_ae_eq _ fun n ↦ .trans (h.preimage_iterate_ae_eq _ this) ht.symm
  · simp only [Set.preimage_iterate_eq]
    exact CompleteLatticeHom.apply_limsup_iterate (CompleteLatticeHom.setPreimage f) t

open Pointwise

@[to_additive]
theorem smul_ae_eq_of_ae_eq {G α : Type*} [Group G] [MulAction G α] {_ : MeasurableSpace α}
    {s t : Set α} {μ : Measure α} (g : G)
    (h_qmp : QuasiMeasurePreserving (g⁻¹ • · : α → α) μ μ)
    (h_ae_eq : s =ᵐ[μ] t) : (g • s : Set α) =ᵐ[μ] (g • t : Set α) := by
  simpa only [← preimage_smul_inv] using h_qmp.ae_eq h_ae_eq

end QuasiMeasurePreserving

section Pointwise

open Pointwise

@[to_additive]
theorem pairwise_aedisjoint_of_aedisjoint_forall_ne_one {G α : Type*} [Group G] [MulAction G α]
    {_ : MeasurableSpace α} {μ : Measure α} {s : Set α}
    (h_ae_disjoint : ∀ g ≠ (1 : G), AEDisjoint μ (g • s) s)
    (h_qmp : ∀ g : G, QuasiMeasurePreserving (g • ·) μ μ) :
    Pairwise (AEDisjoint μ on fun g : G => g • s) := by
  intro g₁ g₂ hg
  let g := g₂⁻¹ * g₁
  replace hg : g ≠ 1 := by
    rw [Ne, inv_mul_eq_one]
    exact hg.symm
  have : (g₂⁻¹ • ·) ⁻¹' (g • s ∩ s) = g₁ • s ∩ g₂ • s := by
    rw [preimage_eq_iff_eq_image (MulAction.bijective g₂⁻¹), image_smul, smul_set_inter, smul_smul,
      smul_smul, inv_mul_cancel, one_smul]
  change μ (g₁ • s ∩ g₂ • s) = 0
  exact this ▸ (h_qmp g₂⁻¹).preimage_null (h_ae_disjoint g hg)

end Pointwise

end Measure

open Measure

theorem NullMeasurable.comp_quasiMeasurePreserving {ν : Measure β}
    {f : α → β} {g : β → γ} (hg : NullMeasurable g ν) (hf : QuasiMeasurePreserving f μ ν) :
    NullMeasurable (g ∘ f) μ := fun _s hs ↦ (hg hs).preimage hf

theorem NullMeasurableSet.mono_ac (h : NullMeasurableSet s μ) (hle : ν ≪ μ) :
    NullMeasurableSet s ν :=
  h.preimage <| (QuasiMeasurePreserving.id μ).mono_left hle

theorem NullMeasurableSet.mono (h : NullMeasurableSet s μ) (hle : ν ≤ μ) : NullMeasurableSet s ν :=
  h.mono_ac hle.absolutelyContinuous

lemma NullMeasurableSet.smul_measure (h : NullMeasurableSet s μ) (c : ℝ≥0∞) :
    NullMeasurableSet s (c • μ) :=
  h.mono_ac (Measure.AbsolutelyContinuous.rfl.smul_left c)

lemma nullMeasurableSet_smul_measure_iff {c : ℝ≥0∞} (hc : c ≠ 0) :
    NullMeasurableSet s (c • μ) ↔ NullMeasurableSet s μ :=
  ⟨fun h ↦ h.mono_ac (Measure.absolutelyContinuous_smul hc), fun h ↦ h.smul_measure c⟩

theorem AEDisjoint.preimage {ν : Measure β} {f : α → β} {s t : Set β} (ht : AEDisjoint ν s t)
    (hf : QuasiMeasurePreserving f μ ν) : AEDisjoint μ (f ⁻¹' s) (f ⁻¹' t) :=
  hf.preimage_null ht

end MeasureTheory

open MeasureTheory

namespace MeasurableEquiv

variable {_ : MeasurableSpace α} [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

theorem quasiMeasurePreserving_symm (μ : Measure α) (e : α ≃ᵐ β) :
    Measure.QuasiMeasurePreserving e.symm (μ.map e) μ :=
  ⟨e.symm.measurable, by rw [Measure.map_map, e.symm_comp_self, Measure.map_id] <;> measurability⟩

end MeasurableEquiv
