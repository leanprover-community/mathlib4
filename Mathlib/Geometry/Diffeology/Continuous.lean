/-
Copyright (c) 2024 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.Geometry.Diffeology.Basic
public import Mathlib.Topology.Compactness.DeltaGeneratedSpace

/-!
# Continuous diffeology

The continuous diffeology on a topological space is the diffeology consisting of all continuous
plots. On the level of categories, this defines a right adjoint of the D-topology functor; on the
level of individual types, this means that it forms a Galois connection with
`@dTopology X : DiffeologicalSpace X → TopologicalSpace X`. We introduce the continuous diffeology
as well as this Galois connection and use it to show a few more properties of the D-topology.

See https://ncatlab.org/nlab/show/adjunction+between+topological+spaces+and+diffeological+spaces.
-/

universe u

@[expose] public section

open scoped Topology

namespace Diffeology

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
    isOpen_iff_preimages_plots := isOpen_deltaGenerated_iff.trans <| forall_congr' fun n ↦ by
      refine ⟨fun h p hp ↦ ?_, fun h p ↦ ?_⟩
      · rw [← (HomeomorphClass.toHomeomorph (EuclideanSpace.equiv (Fin n) ℝ).symm).isOpen_preimage]
        exact h ⟨_, hp.comp (EuclideanSpace.equiv _ _).symm.continuous⟩
      · rw [← (HomeomorphClass.toHomeomorph (EuclideanSpace.equiv (Fin n) ℝ)).isOpen_preimage]
        exact h _ (p.2.comp (EuclideanSpace.equiv (Fin n) ℝ).continuous) }

/-- The D-topology of the continuous diffeology is the coarsest delta-generated topology containing
the original topology. -/
lemma dTopology_continuousDiffeology {X : Type u} [TopologicalSpace X] :
    (continuousDiffeology X).dTopology = .deltaGenerated X :=
  rfl

/-- For delta-generated spaces, the D-topology of the continuous diffeology is the
topology itself. -/
lemma dTopopology_continuousDiffeology_eq_self {X : Type u} [t : TopologicalSpace X]
    [DeltaGeneratedSpace X] : (continuousDiffeology X).dTopology = t :=
  dTopology_continuousDiffeology.trans eq_deltaGenerated.symm

/-- Type synonym to get equipped with the continuous diffeology. -/
def WithContinuousDiffeology (X : Type u) := X

instance (X : Type u) [TopologicalSpace X] : DiffeologicalSpace (WithContinuousDiffeology X) :=
  continuousDiffeology X

/-- Every continuous map is smooth with respect to the continuous diffeologies. -/
lemma _root_.Continuous.dsmooth {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) : @DSmooth _ _ (continuousDiffeology X) (continuousDiffeology Y) f :=
  fun _ _ hp ↦ hf.comp hp

/-- Every continuous map into a space carrying the continuous diffeology is smooth. -/
lemma _root_.Continuous.dsmooth' {X Y : Type u} {dX : DiffeologicalSpace X}
    {tY : TopologicalSpace Y} {f : X → Y} (hf : Continuous[dTopology, _] f) :
    @DSmooth _ _ _ (continuousDiffeology Y) f := by
  let _ : TopologicalSpace X := dTopology; exact fun n p hp ↦ hf.comp hp.continuous

lemma dTopology_le_iff_le_continuousDiffeology {X : Type u} {d : DiffeologicalSpace X}
    {t : TopologicalSpace X} : d.dTopology ≤ t ↔ d ≤ @continuousDiffeology X t :=
  ⟨fun h ↦ DiffeologicalSpace.le_iff'.2 fun _ _ hp ↦ continuous_le_rng h hp.continuous,
    fun h ↦ TopologicalSpace.le_def.2 fun _ hu ↦ isOpen_iff_preimages_plots.2 fun _ _ hp ↦
      hu.preimage <| DiffeologicalSpace.le_iff'.1 h _ _ hp⟩

/-- The D-topology and continuous diffeology form a Galois connection between diffeologies
and topologies on `X`. -/
theorem gc_dTopology (X : Type*) : GaloisConnection (@dTopology X) (@continuousDiffeology X) :=
  @dTopology_le_iff_le_continuousDiffeology X

lemma dTopology_mono {X : Type*} {d₁ d₂ : DiffeologicalSpace X} (h : d₁ ≤ d₂) :
    d₁.dTopology ≤ d₂.dTopology :=
  (gc_dTopology X).monotone_l h

lemma continuousDiffeology_mono {X : Type*} {t₁ t₂ : TopologicalSpace X} (h : t₁ ≤ t₂) :
    @continuousDiffeology X t₁ ≤ @continuousDiffeology X t₂ :=
  (gc_dTopology X).monotone_u h

lemma dTopology_continuousDiffeology_le {X : Type u} {t : TopologicalSpace X} :
    (@continuousDiffeology X t).dTopology ≤ t :=
  (gc_dTopology X).l_u_le t

lemma le_continuousDiffeology_dTopology {X : Type u} {d : DiffeologicalSpace X} :
    d ≤ @continuousDiffeology X d.dTopology :=
  (gc_dTopology X).le_u_l d

lemma dTopology_sup {X : Type u} (d₁ d₂ : DiffeologicalSpace X) :
    (d₁ ⊔ d₂).dTopology = d₁.dTopology ⊔ d₂.dTopology :=
  (gc_dTopology X).l_sup (a₁ := d₁)

lemma dTopology_iSup {X : Type u} {ι : Type*} {D : ι → DiffeologicalSpace X} :
    (⨆ i, D i).dTopology = ⨆ i, (D i).dTopology :=
  (gc_dTopology X).l_iSup

lemma dTopology_sSup {X : Type u} {D : Set (DiffeologicalSpace X)} :
    (sSup D).dTopology = ⨆ d ∈ D, d.dTopology :=
  (gc_dTopology X).l_sSup

lemma continuousDiffeology_inf {X : Type u} (t₁ t₂ : TopologicalSpace X) :
    @continuousDiffeology X (t₁ ⊓ t₂) =
    @continuousDiffeology X t₁ ⊓ @continuousDiffeology X t₂ :=
  (gc_dTopology X).u_inf (b₁ := t₁)

lemma continuousDiffeology_iInf {X : Type u} {ι : Type*} {T : ι → TopologicalSpace X} :
    @continuousDiffeology X (⨅ i, T i) = ⨅ i, @continuousDiffeology X (T i) :=
  (gc_dTopology X).u_iInf

lemma continuousDiffeology_sInf {X : Type u} {T : Set (TopologicalSpace X)} :
    @continuousDiffeology X (sInf T) = ⨅ t ∈ T, @continuousDiffeology X t :=
  (gc_dTopology X).u_sInf

open DiffeologicalSpace in
/-- The D-topology of the diffeology generated by `g` is coinduced by all plots in `g`. -/
lemma dTopology_generateFrom_eq_iSup {X : Type*}
    {g : Set ((n : ℕ) × (EuclideanSpace ℝ (Fin n) → X))} :
    (generateFrom g).dTopology = ⨆ p ∈ g, .coinduced p.2 inferInstance := by
  let _ := generateFrom g
  refine le_antisymm ((dTopology_mono ?_).trans dTopology_continuousDiffeology_le) <|
    iSup₂_le fun p hp ↦ (isPlot_generatedFrom_of_mem hp).continuous.coinduced_le
  exact generateFrom_le_iff.2 fun n p hp ↦
    continuous_le_rng (le_iSup₂ _ hp) continuous_coinduced_rng

/-- A version of `dTopology_generateFrom_eq_iSup` stated in terms of individual open sets. -/
lemma isOpen_dTopology_generateFrom {X : Type*}
    {g : Set ((n : ℕ) × (EuclideanSpace ℝ (Fin n) → X))} {u : Set X} :
    @IsOpen X (DiffeologicalSpace.generateFrom g).dTopology u ↔
    ∀ n p, ⟨n, p⟩ ∈ g → IsOpen (p ⁻¹' u) := by
  rw [dTopology_generateFrom_eq_iSup]
  simp_rw [isOpen_iSup_iff, isOpen_coinduced]
  exact ⟨fun h _ _ hp ↦ h _ hp, fun h _ hp ↦ h _ _ hp⟩

end Diffeology
