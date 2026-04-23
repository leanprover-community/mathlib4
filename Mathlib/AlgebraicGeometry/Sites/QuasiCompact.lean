/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.ZeroFamily
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Sheaves.Init

/-!
# Quasi-compact precoverage

In this file we define the quasi-compact precoverage. A cover is covering in the quasi-compact
precoverage if it is a quasi-compact cover, i.e., if every affine open of the base can be covered
by a finite union of images of quasi-compact opens of the components.

The fpqc precoverage is the precoverage by flat covers that are quasi-compact in this sense.
-/

@[expose] public section

universe w' w v u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

@[simp]
lemma quasiCompactCover_shrink_iff (E : PreZeroHypercover.{w} S) :
    QuasiCompactCover E.shrink ↔ QuasiCompactCover E :=
  ⟨fun _ ↦ .of_hom E.fromShrink, fun _ ↦ .of_hom E.toShrink⟩

/-- The pre-`0`-hypercover family on the category of schemes underlying the fpqc precoverage. -/
@[simps]
def qcCoverFamily : PreZeroHypercoverFamily Scheme.{u} where
  property X := X.quasiCompactCover
  iff_shrink {_} E := (quasiCompactCover_shrink_iff E).symm

/--
The quasi-compact precoverage on the category of schemes is the precoverage
given by quasi-compact covers. The intersection of this precoverage
with the precoverage defined by jointly surjective families of flat morphisms is
the fpqc-precoverage.
-/
def qcPrecoverage : Precoverage Scheme.{u} :=
  qcCoverFamily.precoverage

@[simp]
lemma presieve₀_mem_qcPrecoverage_iff {E : PreZeroHypercover.{w} S} :
    E.presieve₀ ∈ Scheme.qcPrecoverage S ↔ QuasiCompactCover E := by
  rw [← PreZeroHypercover.presieve₀_shrink, Scheme.qcPrecoverage,
    E.shrink.presieve₀_mem_precoverage_iff]
  simp

instance : qcPrecoverage.HasIsos := .of_preZeroHypercoverFamily fun X Y f hf ↦ by
  rw [qcCoverFamily_property, Scheme.quasiCompactCover_iff]
  infer_instance

instance : qcPrecoverage.IsStableUnderBaseChange := by
  refine .of_preZeroHypercoverFamily_of_isClosedUnderIsomorphisms ?_ ?_
  · intro X
    exact X.isClosedUnderIsomorphisms_quasiCompactCover
  · intro X Y f E h hE
    simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE ⊢
    infer_instance

instance : qcPrecoverage.IsStableUnderComposition := by
  refine .of_preZeroHypercoverFamily fun {X} E F hE hF ↦ ?_
  simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE hF ⊢
  infer_instance

instance : qcPrecoverage.IsStableUnderSup := by
  refine .of_preZeroHypercoverFamily fun {X} E F hE hF ↦ ?_
  simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE hF ⊢
  infer_instance

lemma bot_mem_qcPrecoverage (X : Scheme.{u}) [IsEmpty X] : ⊥ ∈ qcPrecoverage X := by
  rw [← PreZeroHypercover.presieve₀_empty.{0}, presieve₀_mem_qcPrecoverage_iff]
  infer_instance

/-- If `P` implies being an open map, the by `P` induced precoverage is coarser
than the quasi-compact precoverage. -/
lemma precoverage_le_qcPrecoverage_of_isOpenMap {P : MorphismProperty Scheme.{u}}
    (hP : P ≤ fun _ _ f ↦ IsOpenMap f.base) :
    precoverage P ≤ qcPrecoverage := by
  refine Precoverage.le_of_zeroHypercover fun X E ↦ ?_
  rw [presieve₀_mem_qcPrecoverage_iff]
  exact .of_isOpenMap fun i ↦ hP _ (Scheme.Cover.map_prop E i)

lemma zariskiPrecoverage_le_qcPrecoverage :
    zariskiPrecoverage ≤ qcPrecoverage :=
  precoverage_le_qcPrecoverage_of_isOpenMap fun _ _ f _ ↦ f.isOpenEmbedding.isOpenMap

lemma Hom.singleton_mem_qcPrecoverage {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    [QuasiCompact f] : Presieve.singleton f ∈ qcPrecoverage Y := by
  let E : Cover.{u} _ _ := f.cover (P := ⊤) trivial
  rw [qcPrecoverage, PreZeroHypercoverFamily.mem_precoverage_iff]
  refine ⟨(f.cover (P := ⊤) trivial).toPreZeroHypercover, ?_, by simp⟩
  simp only [qcCoverFamily_property, quasiCompactCover_iff]
  infer_instance

section Property

variable {P : MorphismProperty Scheme.{u}}

/-- The `qc`-precoverage of a scheme wrt. to a morphism property `P` is the precoverage
given by quasi-compact covers satisfying `P`. -/
abbrev propQCPrecoverage (P : MorphismProperty Scheme.{u}) : Precoverage Scheme.{u} :=
  qcPrecoverage ⊓ Scheme.precoverage P

@[grind .]
lemma propQCPrecoverage_le_precoverage : propQCPrecoverage P ≤ precoverage P :=
  inf_le_right

lemma propQCPrecoverage_monotone : Monotone propQCPrecoverage := by
  intro P Q h
  rw [propQCPrecoverage, propQCPrecoverage]
  gcongr
  exact precoverage_mono h

lemma zariskiPrecoverage_le_propQCPrecoverage [P.ContainsIdentities] [IsZariskiLocalAtSource P] :
    zariskiPrecoverage ≤ propQCPrecoverage P := by
  rw [propQCPrecoverage, le_inf_iff]
  refine ⟨zariskiPrecoverage_le_qcPrecoverage, precoverage_mono fun X Y f hf ↦ ?_⟩
  apply IsZariskiLocalAtSource.of_isOpenImmersion

instance {S : Scheme.{u}} (𝒰 : Scheme.Cover (propQCPrecoverage P) S) :
    QuasiCompactCover 𝒰.toPreZeroHypercover := by
  rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
  exact 𝒰.mem₀.1

lemma bot_mem_propQCPrecoverage (X : Scheme.{u}) [IsEmpty X] : ⊥ ∈ propQCPrecoverage P X :=
  ⟨bot_mem_qcPrecoverage _, bot_mem_precoverage _ _⟩

/-- Forget being quasi-compact. -/
@[simps toPreZeroHypercover]
abbrev Cover.forgetQc {S : Scheme.{u}} (𝒰 : Scheme.Cover (propQCPrecoverage P) S) :
    S.Cover (precoverage P) where
  __ := 𝒰.toPreZeroHypercover
  mem₀ := 𝒰.mem₀.2

instance {S : Scheme.{u}} (𝒰 : Scheme.Cover (propQCPrecoverage P) S) :
    QuasiCompactCover 𝒰.forgetQc.toPreZeroHypercover := by
  dsimp; infer_instance

/-- Construct a cover in the `P`-qc topology from a quasi-compact cover in the `P`-topology. -/
@[simps toPreZeroHypercover]
def Cover.ofQuasiCompactCover {S : Scheme.{u}} (𝒰 : Scheme.Cover (precoverage P) S)
    [qc : QuasiCompactCover 𝒰.1] :
    Scheme.Cover (propQCPrecoverage P) S where
  __ := 𝒰.toPreZeroHypercover
  mem₀ := ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr ‹_›, 𝒰.mem₀⟩

/-- Lift a quasi-compact `P`-cover of a `u`-scheme in an arbitrary universe to universe `u`.
This is again quasi-compact. -/
noncomputable def Cover.qculift {S : Scheme.{u}} (𝒰 : Cover.{w} (precoverage P) S)
    [QuasiCompactCover 𝒰.1] : Scheme.Cover.{u} (precoverage P) S where
  __ := 𝒰.ulift.toPreZeroHypercover.sum (QuasiCompactCover.ulift 𝒰.1)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ⟨.inl x, 𝒰.covers _⟩, fun i ↦ ?_⟩
    induction i <;> exact 𝒰.map_prop _

instance {S : Scheme.{u}} (𝒰 : S.Cover (precoverage P)) [QuasiCompactCover 𝒰.1] :
    QuasiCompactCover (Scheme.Cover.qculift 𝒰).1 :=
  .of_hom (PreZeroHypercover.sumInr _ _)

instance : Precoverage.Small.{u} (propQCPrecoverage P) where
  zeroHypercoverSmall {S} (𝒰 : S.Cover _) := by
    refine ⟨𝒰.forgetQc.qculift.I₀, Sum.elim 𝒰.forgetQc.idx (QuasiCompactCover.uliftHom _).s₀,
      ⟨?_, ?_⟩⟩
    · rw [Scheme.presieve₀_mem_qcPrecoverage_iff]
      exact .of_hom (𝒱 := QuasiCompactCover.ulift 𝒰.1) ⟨Sum.inr, fun i ↦ 𝟙 _, by cat_disch⟩
    · rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x ↦ ⟨Sum.inl x, 𝒰.forgetQc.covers _⟩, fun i ↦ 𝒰.forgetQc.map_prop _⟩

lemma mem_propQCPrecoverage_iff_exists_quasiCompactCover {S : Scheme.{u}} {R : Presieve S} :
    R ∈ propQCPrecoverage P S ↔ ∃ (𝒰 : Scheme.Cover.{u + 1} (precoverage P) S),
      QuasiCompactCover 𝒰.toPreZeroHypercover ∧ R = 𝒰.presieve₀ := by
  rw [Precoverage.mem_iff_exists_zeroHypercover]
  refine ⟨fun ⟨𝒰, h⟩ ↦ ⟨𝒰.weaken propQCPrecoverage_le_precoverage, ?_, h⟩,
    fun ⟨𝒰, _, h⟩ ↦ ⟨⟨𝒰.1, ⟨by simpa, 𝒰.mem₀⟩⟩, h⟩⟩
  rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
  exact 𝒰.mem₀.1

@[grind .]
lemma Hom.singleton_mem_propQCPrecoverage {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : P f) [Surjective f]
    [QuasiCompact f] : Presieve.singleton f ∈ propQCPrecoverage P Y := by
  refine ⟨f.singleton_mem_qcPrecoverage, ?_⟩
  grind [singleton_mem_precoverage_iff]

/-- The `P`-`qc`-topology on the category of schemes wrt. to a morphism property `P` is the
topology generated by quasi-compact covers satisfying `P`. -/
abbrev propQCTopology (P : MorphismProperty Scheme.{u}) : GrothendieckTopology Scheme.{u} :=
  (propQCPrecoverage P).toGrothendieck

lemma bot_mem_propQCTopology (X : Scheme.{u}) [IsEmpty X] : ⊥ ∈ propQCTopology P X := by
  rw [← Sieve.generate_bot]
  exact Precoverage.generate_mem_toGrothendieck (bot_mem_propQCPrecoverage X)

@[grind .]
lemma Hom.generate_singleton_mem_propQCTopology {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : P f)
    [Surjective f] [QuasiCompact f] :
    .generate (.singleton f) ∈ propQCTopology P Y := by
  apply Precoverage.generate_mem_toGrothendieck
  exact f.singleton_mem_propQCPrecoverage hf

@[simp, grind .]
lemma Cover.mem_propQCTopology {S : Scheme.{u}} (𝒰 : Cover.{u} (precoverage P) S)
    [QuasiCompactCover 𝒰.1] :
    .ofArrows 𝒰.X 𝒰.f ∈ propQCTopology P S := by
  refine Precoverage.generate_mem_toGrothendieck ⟨?_, 𝒰.mem₀⟩
  rwa [presieve₀_mem_qcPrecoverage_iff]

lemma zariskiTopology_le_propQCTopology [P.IsMultiplicative] [IsZariskiLocalAtSource P] :
    zariskiTopology ≤ propQCTopology P :=
  Precoverage.toGrothendieck_mono zariskiPrecoverage_le_propQCPrecoverage

end Property

end AlgebraicGeometry.Scheme
