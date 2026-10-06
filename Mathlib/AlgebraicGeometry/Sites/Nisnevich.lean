/-
Authors: Filippo Belfiori, Aristotele.
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Small
import Mathlib.CategoryTheory.Limits.Elements
import Mathlib.CategoryTheory.Sites.Point.Basic

/-!

# The Nisnevich site

In this file we define the big Nisnevich site, i.e. the Nisnevich topology as a Grothendieck topology
on the category of schemes.

-/

universe v u

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry.Scheme

def NisnevichCondition (X Y : Scheme) (f : Y ⟶ X) (x : X) : Prop :=
  ∃ (y : Y), (f y = x ∧ IsIso (Hom.residueFieldMap f y))


def IsNisnevichCovering (X : Scheme) (S : Presieve X) : Prop :=
  (∀ ⦃Y⦄ (f : Y ⟶ X), S f → Etale f) ∧
  (∀ (x : X), ∃ Y, ∃ (f : Y ⟶ X), S f ∧ NisnevichCondition X Y f x)


/-- The Nisnevich condition at `x` holds iff the canonical morphism `Spec κ(x) ⟶ X`
lifts along `f`. -/

lemma NisnevichCondition_iff_exists_lift {X Y : Scheme.{u}} (f : Y ⟶ X) (x : X) :
    NisnevichCondition X Y f x ↔
      ∃ h : Spec (X.residueField x) ⟶ Y, h ≫ f = X.fromSpecResidueField x := by
  constructor
  · rintro ⟨y, rfl, hy⟩
    refine ⟨Spec.map (inv (f.residueFieldMap y)) ≫ Y.fromSpecResidueField y, ?_⟩
    rw [Category.assoc, ← Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Spec.map_comp_assoc, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  · rintro ⟨h, hh⟩
    obtain ⟨⟨y, ψ⟩, rfl⟩ := (SpecToEquivOfField (X.residueField x) Y).symm.surjective h
    have key : (SpecToEquivOfField (X.residueField x) X).symm ⟨f y, f.residueFieldMap y ≫ ψ⟩ =
        (SpecToEquivOfField (X.residueField x) X).symm ⟨x, 𝟙 _⟩ := by
      simp only [SpecToEquivOfField, Equiv.coe_fn_symm_mk] at hh ⊢
      rw [Spec.map_comp, Category.assoc, Hom.SpecMap_residueFieldMap_fromSpecResidueField,
        ← Category.assoc, hh, Spec.map_id]
      exact (Category.id_comp _).symm
    obtain ⟨e, he⟩ := SpecToEquivOfField_eq_iff.1 ((Equiv.injective _) key)
    refine ⟨y, e, ?_⟩
    have h1 : IsIso (f.residueFieldMap y ≫ ψ) := by
      simp only at he
      rw [he]
      infer_instance
    have h2 : IsIso ψ := by
      have hb : Function.Bijective ψ.hom := by
        refine ⟨ψ.hom.injective, fun z ↦ ?_⟩
        obtain ⟨w, hw⟩ := (ConcreteCategory.bijective_of_isIso
          (f.residueFieldMap y ≫ ψ)).2 z
        exact ⟨_, hw⟩
      exact (RingEquiv.ofBijective ψ.hom hb).toCommRingCatIso.isIso_hom
    exact IsIso.of_isIso_comp_right _ ψ

/-- Big Nisnevich site: the étale precoverage on the category of schemes. -/

def NisnevichPrecoverage : Precoverage Scheme.{u} where
  coverings X := {S | IsNisnevichCovering X S}

instance : NisnevichPrecoverage.HasIsos where
  mem_coverings_of_isIso {Y X} f hf := by
    refine ⟨fun Z g hg ↦ ?_, fun x ↦ ⟨Y, f, ⟨⟩, inv f x, ?_, inferInstance⟩⟩
    · cases hg
      infer_instance
    · simp [← Scheme.Hom.comp_apply]

instance : NisnevichPrecoverage.IsStableUnderComposition where
  comp_mem_coverings {ι} S X f hf σ Y g hg := by
    refine ⟨fun Z u hu ↦ ?_, fun s ↦ ?_⟩
    · obtain ⟨⟨i, j⟩⟩ := hu
      have := hf.1 _ ⟨i⟩
      have := (hg i).1 _ ⟨j⟩
      infer_instance
    · obtain ⟨_, _, ⟨i⟩, x, rfl, hx⟩ := hf.2 s
      obtain ⟨_, _, ⟨j⟩, y, rfl, hy⟩ := (hg i).2 x
      refine ⟨_, _, ⟨⟨i, j⟩⟩, y, rfl, ?_⟩
      rw [Scheme.residueFieldMap_comp]
      exact IsIso.comp_isIso' hx hy

instance : NisnevichPrecoverage.IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} S X f hR T g P p₁ p₂ h := by
    refine ⟨fun Z u hu ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨i⟩ := hu
      have := hR.1 _ ⟨i⟩
      exact MorphismProperty.of_isPullback (P := @Etale) (h i).flip this
    · obtain ⟨_, _, ⟨i⟩, hs⟩ := hR.2 (g y)
      obtain ⟨k, hk⟩ := (NisnevichCondition_iff_exists_lift _ _).1 hs
      refine ⟨_, _, ⟨i⟩, (NisnevichCondition_iff_exists_lift _ _).2
        ⟨(h i).lift (T.fromSpecResidueField y) (Spec.map (g.residueFieldMap y) ≫ k) ?_, ?_⟩⟩
      · simp [hk]
      · simp

def NisnevichPretopology : Pretopology Scheme.{u} := NisnevichPrecoverage.toPretopology

def NisnevichTopology : GrothendieckTopology Scheme.{u} :=
  NisnevichPretopology.toGrothendieck

lemma NisnevichTopology_mem : NisnevichTopology = NisnevichPrecoverage.toGrothendieck := by
  exact Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck


/- Nisnevich topology and Zariski topology -/

lemma ZariskiPrecoverage_le_NisnevichPrecoverage : zariskiPrecoverage ≤ NisnevichPrecoverage := by
  intro X S
  rw [zariskiPrecoverage]
  rw [NisnevichPrecoverage]
  intro hS
  simp
  rw [IsNisnevichCovering]
  constructor
  · intro Y f
    refine fun a ↦ ?_
    have : IsOpenImmersion f := hS.2 a
    infer_instance
  · intro x
    obtain ⟨_, _, ⟨hf⟩, y, rfl⟩ := hS.1 x
    have := hS.2 hf
    exact ⟨_, _, hf, y, rfl, inferInstance⟩

lemma ZariskiPretopology_le_NisnevichPretopology : zariskiPretopology ≤ NisnevichPretopology := by
  intro X S hS
  exact ZariskiPrecoverage_le_NisnevichPrecoverage X hS

lemma ZariskiTopology_le_NisnevichTopology : zariskiTopology ≤ NisnevichTopology := by
  intro X S hS
  rw [NisnevichTopology]
  rw [zariskiTopology_eq] at hS
  obtain ⟨R, hR, hRS⟩ := (Pretopology.mem_toGrothendieck _ X S).1 hS
  exact (Pretopology.mem_toGrothendieck _ X S).2
    ⟨R, ZariskiPretopology_le_NisnevichPretopology X hR, hRS⟩


/- Nisnevich topology and etale topology -/

lemma NisnevichPrecoverage_le_etalePrecoverage : NisnevichPrecoverage ≤ etalePrecoverage := by
  intro X S
  rw [NisnevichPrecoverage]
  rw [etalePrecoverage]
  intro hS
  simp at hS
  refine ⟨fun x ↦ ?_, fun Y f hf ↦ hS.1 f hf⟩
  obtain ⟨_, f, hf, y, rfl, -⟩ := hS.2 x
  exact ⟨_, _, Presieve.map.of hf, y, rfl⟩

lemma NisnevichPretopology_le_EtalePretopology : NisnevichPretopology ≤ etalePretopology := by
  intro X S hS
  exact NisnevichPrecoverage_le_etalePrecoverage X hS

lemma NisnevichTopology_le_etaleTopology : NisnevichTopology ≤ etaleTopology := by
  intro X S hS
  obtain ⟨R, hR, hRS⟩ := (Pretopology.mem_toGrothendieck _ X S).1 hS
  have hR' : R ∈ etalePrecoverage X := NisnevichPrecoverage_le_etalePrecoverage X hR
  apply etaleTopology.superset_covering ((Sieve.giGenerate.gc R S).2 hRS)
  exact Precoverage.generate_mem_toGrothendieck hR'


end AlgebraicGeometry.Scheme
