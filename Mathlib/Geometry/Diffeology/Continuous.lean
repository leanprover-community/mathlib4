/-
Copyright (c) 2024 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Geometry.Diffeology.Basic
import Mathlib.Topology.Compactness.DeltaGeneratedSpace

/-!
# Continuous diffeology

The continuous diffeology on a topological space is the diffeology consisting of all continuous
plots. On the level of categories, this defines a right adjoint of the D-topology functor; on the
level of individual types, this means that it forms a Galois connection with
`@DTop X : DiffeologicalSpace X → TopologicalSpace X`. We introduce the continuous diffeology as
as well as this Galois connection and use it to show a few more properties of the D-topology.

See https://ncatlab.org/nlab/show/adjunction+between+topological+spaces+and+diffeological+spaces.
-/

universe u

open scoped Topology

/-- The continuous diffeology on a topological space `X`, consisting of all continuous plots. -/
def continuousDiffeology (X : Type u) [TopologicalSpace X] : DiffeologicalSpace X :=
  DiffeologicalSpace.ofCorePlotsOn {
    isPlotOn := fun {_ u} _ p ↦ ContinuousOn p u
    isPlotOn_congr := fun _ _ _ h ↦ continuousOn_congr h
    isPlot := fun p ↦ Continuous p
    isPlotOn_univ := continuousOn_univ
    isPlot_const := fun _ ↦ continuous_const
    isPlotOn_reparam := fun _ _ _ h hp hf ↦ hp.comp hf.continuousOn h.subset_preimage
    locality := fun _ _ h ↦ fun x hxu ↦ by
      let ⟨v, hv, hxv, hv'⟩ := h x hxu
      exact ((hv' x hxv).continuousAt (hv.mem_nhds hxv)).continuousWithinAt
    dTopology := .deltaGenerated X
    isOpen_iff_preimages_plots := isOpen_deltaGenerated_iff.trans <|
      forall_congr' fun n ↦ ⟨fun h p hp ↦ h ⟨p, hp⟩, fun h p ↦ h p p.2⟩ }

/-- The D-topology of the continuous diffeology is the coarsest delta-generated topology containing
the original topology. -/
lemma dTop_continuousDiffeology {X : Type u} [TopologicalSpace X] :
    DTop[continuousDiffeology X] = .deltaGenerated X :=
  rfl

/-- For delta-generated spaces, the D-topology of the continuous diffeology is the
topology itself. -/
lemma dTop_continuousDiffeology_eq_self {X : Type u} [t : TopologicalSpace X]
    [DeltaGeneratedSpace X] : DTop[continuousDiffeology X] = t :=
  dTop_continuousDiffeology.trans eq_deltaGenerated.symm

/-- Type synonym to get equipped with the continuous diffeology. -/
def WithContinuousDiffeology (X : Type u) := X

instance (X : Type u) [TopologicalSpace X] : DiffeologicalSpace (WithContinuousDiffeology X) :=
  continuousDiffeology X

/-- Every continuous map is smooth with respect to the continuous diffeologies. -/
lemma Continuous.dsmooth {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) : DSmooth[continuousDiffeology X, continuousDiffeology Y] f :=
  fun _ _ hp ↦ hf.comp hp

/-- Every continuous map into a space carrying the continuous diffeology is smooth. -/
lemma Continuous.dsmooth' {X Y : Type u} {dX : DiffeologicalSpace X} {tY : TopologicalSpace Y}
    {f : X → Y} (hf : Continuous[DTop, _] f) : DSmooth[_, continuousDiffeology Y] f := by
  let _ : TopologicalSpace X := DTop; exact fun n p hp ↦ hf.comp hp.continuous

lemma dTop_le_iff_le_continuousDiffeology {X : Type u} {d : DiffeologicalSpace X}
    {t : TopologicalSpace X} : DTop[d] ≤ t ↔ d ≤ @continuousDiffeology X t :=
  ⟨fun h ↦ DiffeologicalSpace.le_iff'.2 fun _ _ hp ↦ continuous_le_rng h hp.continuous,
    fun h ↦ TopologicalSpace.le_def.2 fun _ hu ↦ isOpen_iff_preimages_plots.2 fun _ _ hp ↦
      hu.preimage <| DiffeologicalSpace.le_iff'.1 h _ _ hp⟩

/-- The D-topology and continuous diffeology form a Galois connection between diffeologies
and topologies on `X`. -/
theorem gc_dTop (X : Type*) : GaloisConnection (@DTop X) (@continuousDiffeology X) :=
  @dTop_le_iff_le_continuousDiffeology X

lemma dTop_mono {X : Type*} {d₁ d₂ : DiffeologicalSpace X} (h : d₁ ≤ d₂) :
    DTop[d₁] ≤ DTop[d₂] :=
  (gc_dTop X).monotone_l h

lemma continuousDiffeology_mono {X : Type*} {t₁ t₂ : TopologicalSpace X} (h : t₁ ≤ t₂) :
    @continuousDiffeology X t₁ ≤ @continuousDiffeology X t₂ :=
  (gc_dTop X).monotone_u h

lemma dTop_continuousDiffeology_le {X : Type u} {t : TopologicalSpace X} :
    DTop[@continuousDiffeology X t] ≤ t :=
  (gc_dTop X).l_u_le t

lemma le_continuousDiffeology_dTop {X : Type u} {d : DiffeologicalSpace X} :
    d ≤ @continuousDiffeology X DTop[d] :=
  (gc_dTop X).le_u_l d

lemma dTop_sup {X : Type u} (d₁ d₂ : DiffeologicalSpace X) :
    DTop[d₁ ⊔ d₂] = DTop[d₁] ⊔ DTop[d₂] :=
  (gc_dTop X).l_sup (a₁ := d₁)

lemma dTop_iSup {X : Type u} {ι : Type*} {D : ι → DiffeologicalSpace X} :
    DTop[⨆ i, D i] = ⨆ i, DTop[D i] :=
  (gc_dTop X).l_iSup

lemma dTop_sSup {X : Type u} {D : Set (DiffeologicalSpace X)} :
    DTop[sSup D] = ⨆ d ∈ D, DTop[d] :=
  (gc_dTop X).l_sSup

lemma continuousDiffeology_inf {X : Type u} (t₁ t₂ : TopologicalSpace X) :
    @continuousDiffeology X (t₁ ⊓ t₂) =
    @continuousDiffeology X t₁ ⊓ @continuousDiffeology X t₂ :=
  (gc_dTop X).u_inf (b₁ := t₁)

lemma continuousDiffeology_iInf {X : Type u} {ι : Type*} {T : ι → TopologicalSpace X} :
    @continuousDiffeology X (⨅ i, T i) = ⨅ i, @continuousDiffeology X (T i) :=
  (gc_dTop X).u_iInf

lemma continuousDiffeology_sInf {X : Type u} {T : Set (TopologicalSpace X)} :
    @continuousDiffeology X (sInf T) = ⨅ t ∈ T, @continuousDiffeology X t :=
  (gc_dTop X).u_sInf

open DiffeologicalSpace in
/-- The D-topology of the diffeology generated by `g` is coinduced by all plots in `g`. -/
lemma dTop_generateFrom_eq_iSup {X : Type*} {g : Set ((n : ℕ) × (Eucl n → X))} :
    DTop[generateFrom g] = ⨆ p ∈ g, .coinduced p.2 inferInstance := by
  let _ := generateFrom g
  refine le_antisymm ((dTop_mono ?_).trans dTop_continuousDiffeology_le) <|
    iSup₂_le fun p hp ↦ (isPlot_generatedFrom_of_mem hp).continuous.coinduced_le
  exact generateFrom_le_iff.2 fun n p hp ↦
    continuous_le_rng (le_iSup₂ _ hp) continuous_coinduced_rng

/-- A version of `dTop_generateFrom_eq_iSup` stated in terms of individual open sets. -/
lemma isOpen_dTop_generateFrom {X : Type*} {g : Set ((n : ℕ) × (Eucl n → X))} {u : Set X} :
    @IsOpen X DTop[DiffeologicalSpace.generateFrom g] u ↔
    ∀ n p, ⟨n, p⟩ ∈ g → IsOpen (p ⁻¹' u) := by
  simp_rw [dTop_generateFrom_eq_iSup, isOpen_iSup_iff, isOpen_coinduced]
  exact ⟨fun h _ _ hp ↦ h _ hp, fun h _ hp ↦ h _ _ hp⟩
