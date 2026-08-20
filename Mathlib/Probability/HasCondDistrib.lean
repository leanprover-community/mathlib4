/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber, Bo Cowgill
-/

module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# A predicate for having a specified conditional distribution

We introduce a predicate `HasCondDistrib Y X κ P` stating that the conditional distribution of `Y`
given `X` under the measure `P` is equal to the kernel `κ`.
The statement uses `HasLaw` to express that the law of the pair `(X, Y)` under `P` is equal to
`(P.map X) ⊗ₘ κ`, the product of the law of `X` under `P` and the kernel `κ`.
The use of `HasLaw` also implies that `Y` and `X` are a.e. measurable.
When a regular conditional distribution exists, we show that `condDistrib Y X P` satisfies this
predicate and characterize all finite kernels satisfying it. We also characterize independence in
terms of constant conditional distributions.

## Main definitions

* `HasCondDistrib Y X κ P` : predicate stating that the conditional distribution of `Y` given `X`
  under the measure `P` is equal to the kernel `κ`.

## Main results

* `hasCondDistrib_condDistrib`: the regular conditional distribution is a conditional distribution.
* `hasCondDistrib_iff_condDistrib_ae_eq`: a finite kernel is a conditional distribution if and only
  if it is almost everywhere equal to the regular conditional distribution.
* `indepFun_iff_hasCondDistrib_const`: independence is equivalent to the constant marginal kernel
  being a conditional distribution.
* `indepFun_iff_condDistrib_ae_eq_const`: independence is equivalent to the regular conditional
  distribution being almost everywhere equal to the constant marginal kernel.

-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω 𝓧 𝓨 𝓩 : Type*} {mΩ : MeasurableSpace Ω}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : MeasurableSpace 𝓩}
  {P : Measure Ω} {X : Ω → 𝓧} {Y : Ω → 𝓨} {κ : Kernel 𝓧 𝓨}

/-- Predicate stating that the conditional distribution of `Y` given `X` under the measure `P`
is equal to the kernel `κ`. -/
def HasCondDistrib (Y : Ω → 𝓨) (X : Ω → 𝓧) (κ : Kernel 𝓧 𝓨) (P : Measure Ω) : Prop :=
  HasLaw (fun ω ↦ (X ω, Y ω)) ((P.map X) ⊗ₘ κ) P

@[fun_prop]
lemma HasCondDistrib.aemeasurable_fst (h : HasCondDistrib Y X κ P) :
    AEMeasurable X P := h.aemeasurable.fst

@[fun_prop]
lemma HasCondDistrib.aemeasurable_snd (h : HasCondDistrib Y X κ P) :
    AEMeasurable Y P := h.aemeasurable.snd

lemma HasLaw.prodMk_of_hasCondDistrib {Q : Measure 𝓧}
    (h1 : HasLaw X Q P) (h2 : HasCondDistrib Y X κ P) :
    HasLaw (fun ω ↦ (X ω, Y ω)) (Q ⊗ₘ κ) P := by rwa [← h1.map_eq]

lemma HasCondDistrib.hasLaw_of_const [IsProbabilityMeasure P] {Q : Measure 𝓨} [SFinite Q]
    (h : HasCondDistrib Y X (Kernel.const 𝓧 Q) P) :
    HasLaw Y Q P where
  map_eq := by
    have h_snd : (P.map (fun ω ↦ (X ω, Y ω))).snd = Q := by
      rw [h.map_eq, Measure.snd_compProd]
      simp [Measure.map_apply_of_aemeasurable h.aemeasurable_fst]
    rwa [Measure.snd_map_prodMk₀ h.aemeasurable_fst] at h_snd

/-- Two random variables with specified laws are independent if and only if the conditional
distribution of the second given the first is the constant kernel at its law. -/
theorem indepFun_iff_hasCondDistrib_const_of_hasLaw [IsFiniteMeasure P]
    {μ : Measure 𝓧} {ν : Measure 𝓨} (hX : HasLaw X μ P) (hY : HasLaw Y ν P) :
    X ⟂ᵢ[P] Y ↔ HasCondDistrib Y X (Kernel.const 𝓧 ν) P := by
  simp [indepFun_iff_hasLaw_prodMk_prod hX hY, HasCondDistrib, ← hX.map_eq, ← hY.map_eq,
    Measure.compProd_const]

/-- Two a.e.-measurable random variables are independent if and only if the conditional
distribution of the second given the first is the constant kernel at its marginal distribution. -/
theorem indepFun_iff_hasCondDistrib_const [IsFiniteMeasure P]
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    X ⟂ᵢ[P] Y ↔ HasCondDistrib Y X (Kernel.const 𝓧 (P.map Y)) P :=
  indepFun_iff_hasCondDistrib_const_of_hasLaw ⟨hX, rfl⟩ ⟨hY, rfl⟩

alias ⟨IndepFun.hasCondDistrib_const, HasCondDistrib.indepFun_of_const⟩ :=
  indepFun_iff_hasCondDistrib_const

section CondDistrib

variable [StandardBorelSpace 𝓨] [Nonempty 𝓨] [IsFiniteMeasure P]

/-- The regular conditional distribution of `Y` given `X` is a conditional distribution. -/
lemma hasCondDistrib_condDistrib (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    HasCondDistrib Y X (condDistrib Y X P) P where
  aemeasurable := hX.prodMk hY
  map_eq := (compProd_map_condDistrib hY).symm

/-- A finite kernel is a conditional distribution of `Y` given `X` if and only if it is almost
everywhere equal to the regular conditional distribution. -/
theorem hasCondDistrib_iff_condDistrib_ae_eq [IsFiniteKernel κ]
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    HasCondDistrib Y X κ P ↔ condDistrib Y X P =ᵐ[P.map X] κ := by
  constructor
  · intro h
    exact condDistrib_ae_eq_of_measure_eq_compProd X hY h.map_eq
  · intro h
    exact ⟨hX.prodMk hY,
      (hasCondDistrib_condDistrib hX hY).map_eq.trans (Measure.compProd_congr h)⟩

/-- Two random variables with specified laws are independent if and only if the conditional
distribution of the second given the first is almost everywhere the constant kernel at its law. -/
theorem indepFun_iff_condDistrib_ae_eq_const_of_hasLaw {μ : Measure 𝓧} {ν : Measure 𝓨}
    (hX : HasLaw X μ P) (hY : HasLaw Y ν P) :
    X ⟂ᵢ[P] Y ↔ condDistrib Y X P =ᵐ[μ] Kernel.const 𝓧 ν := by
  let _ : IsFiniteMeasure ν := hY.isFiniteMeasure_iff.mp inferInstance
  rw [← hX.map_eq, indepFun_iff_hasCondDistrib_const_of_hasLaw hX hY,
    hasCondDistrib_iff_condDistrib_ae_eq hX.aemeasurable hY.aemeasurable]

/-- Two a.e.-measurable random variables are independent if and only if the conditional
distribution of the second given the first is almost everywhere its marginal distribution. -/
theorem indepFun_iff_condDistrib_ae_eq_const
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    X ⟂ᵢ[P] Y ↔ condDistrib Y X P =ᵐ[P.map X] Kernel.const 𝓧 (P.map Y) :=
  indepFun_iff_condDistrib_ae_eq_const_of_hasLaw ⟨hX, rfl⟩ ⟨hY, rfl⟩

end CondDistrib

variable [SFinite P] [IsSFiniteKernel κ]

lemma HasCondDistrib.comp_left (h : HasCondDistrib Y X κ P) {f : 𝓨 → 𝓩} (hf : Measurable f) :
    HasCondDistrib (f ∘ Y) X (κ.map f) P where
  map_eq := calc
    P.map (fun ω ↦ (X ω, f (Y ω)))
    _ = (P.map (fun ω ↦ (X ω, Y ω))).map (Prod.map id f) := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
      congr
    _ = (P.map X ⊗ₘ κ).map (Prod.map id f) := by rw [h.map_eq]
    _ = P.map X ⊗ₘ κ.map f := by rw [Measure.compProd_map hf]

lemma HasCondDistrib.fst {Y : Ω → 𝓨 × 𝓩} {κ : Kernel 𝓧 (𝓨 × 𝓩)} [IsSFiniteKernel κ]
    (h : HasCondDistrib Y X κ P) :
    HasCondDistrib (fun ω ↦ (Y ω).1) X κ.fst P := by
  rw [Kernel.fst_eq]
  exact h.comp_left measurable_fst

lemma HasCondDistrib.snd {Y : Ω → 𝓨 × 𝓩} {κ : Kernel 𝓧 (𝓨 × 𝓩)} [IsSFiniteKernel κ]
    (h : HasCondDistrib Y X κ P) :
    HasCondDistrib (fun ω ↦ (Y ω).2) X κ.snd P := by
  rw [Kernel.snd_eq]
  exact h.comp_left measurable_snd

lemma HasCondDistrib.comp_right {f : 𝓩 → 𝓧}
    {hf : Measurable f} {Z : Ω → 𝓩} (h : HasCondDistrib Y Z (κ.comap f hf) P) :
    HasCondDistrib Y (f ∘ Z) κ P where
  map_eq := calc
    P.map (fun a ↦ ((f ∘ Z) a, Y a))
    _ = (P.map (fun a ↦ (Z a, Y a))).map (Prod.map f id) := by
        rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
        rfl
    _ = (P.map Z ⊗ₘ κ.comap f hf).map (Prod.map f id) := by rw [h.map_eq]
    _ = (P.map Z).map f ⊗ₘ κ := by
        ext s hs
        rw [Measure.map_apply (by fun_prop) hs, Measure.compProd_apply (by measurability),
          Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
        rfl
    _ = P.map (f ∘ Z) ⊗ₘ κ := by
        rw [AEMeasurable.map_map_of_aemeasurable hf.aemeasurable (by fun_prop)]

lemma HasCondDistrib.measurableEquiv_comp_right (h : HasCondDistrib Y X κ P) (f : 𝓧 ≃ᵐ 𝓩) :
    HasCondDistrib Y (f ∘ X) (κ.comap f.symm f.symm.measurable) P := by
  apply HasCondDistrib.comp_right (hf := f.measurable)
  simpa [← Kernel.comap_comp_right]

lemma HasCondDistrib.of_compProd {Z : Ω → 𝓩} {η : Kernel (𝓧 × 𝓨) 𝓩} [IsMarkovKernel η]
    (h : HasCondDistrib (fun a ↦ (Y a, Z a)) X (κ ⊗ₖ η) P) :
    HasCondDistrib Z (fun a ↦ (X a, Y a)) η P := by
  have hZ : AEMeasurable Z P := h.aemeasurable_snd.snd
  have hY : AEMeasurable Y P := h.aemeasurable_snd.fst
  refine ⟨by fun_prop, ?_⟩
  calc P.map (fun a ↦ ((X a, Y a), Z a))
  _ = (P.map X ⊗ₘ (κ ⊗ₖ η)).map MeasurableEquiv.prodAssoc.symm := by
      rw [← h.map_eq, AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
      rfl
  _ = P.map X ⊗ₘ κ ⊗ₘ η := Measure.compProd_assoc
  _ = P.map (fun a ↦ (X a, Y a)) ⊗ₘ η := by simp [h.fst.map_eq]

end ProbabilityTheory
