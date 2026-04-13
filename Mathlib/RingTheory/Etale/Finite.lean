/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib

public section

open CategoryTheory

universe u

variable (R : Type*) [CommRing R]
variable (k : Type u) [Field k]

variable {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)]

lemma PrimeSpectrum.sigmaToPi_apply (i : ι) (p : PrimeSpectrum (R i)) :
    sigmaToPi R ⟨i, p⟩ = comap (Pi.evalRingHom R i) p :=
  rfl

lemma PrimeSpectrum.comap_evalRingHom_basicOpen [DecidableEq ι] (i : ι) (f : R i) :
    comap (Pi.evalRingHom R i) '' basicOpen f = basicOpen (Pi.single i f) := by
  ext p
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp, rfl⟩
    simpa
  · intro hp
    have : p ∈ Set.range (PrimeSpectrum.comap (Pi.evalRingHom R i)) := by
      rw [range_comap_of_surjective _ _ (RingHom.surjective _), mem_zeroLocus,
        SetLike.coe_subset_coe]
      intro x hx
      rw [RingHom.mem_ker, Pi.evalRingHom_apply] at hx
      have : Pi.single i f * x = 0 := by
        ext j
        by_cases h : i = j
        · subst h
          simp [hx]
        · simp [h]
      obtain (h | h) := Ideal.IsPrime.mem_or_mem_of_mul_eq_zero p.isPrime this <;> tauto
    obtain ⟨q, rfl⟩ := this
    exact ⟨q, by simpa using hp, by ext; simp⟩

lemma PrimeSpectrum.sigmaToPi_mk_basicOpen [DecidableEq ι] (i : ι) (f : R i) :
    sigmaToPi R '' (Sigma.mk i '' basicOpen f) = basicOpen (Pi.single i f) := by
  simp only [Set.image_image, sigmaToPi_apply]
  exact PrimeSpectrum.comap_evalRingHom_basicOpen _ _

lemma PrimeSpectrum.isEmbedding_sigmaToPi {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)] :
    Topology.IsOpenEmbedding (sigmaToPi R) := by
  classical
  refine .of_continuous_injective_isOpenMap ?_ ?_ ?_
  · rw [continuous_sigma_iff]
    intro i
    exact continuous_comap (Pi.evalRingHom R i)
  · exact sigmaToPi_injective R
  · rw [isOpenMap_sigma]
    intro i
    simp only [sigmaToPi_apply, PrimeSpectrum.isTopologicalBasis_basic_opens.isOpenMap_iff]
    rintro - ⟨f, rfl⟩
    rw [PrimeSpectrum.comap_evalRingHom_basicOpen]
    exact isOpen_basicOpen

@[expose]
noncomputable
def PrimeSpectrum.sigmaHomeoPi {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)] [Finite ι] :
    (Σ i, PrimeSpectrum (R i)) ≃ₜ PrimeSpectrum (Π i, R i) :=
  (isEmbedding_sigmaToPi R).toHomeomorphOfSurjective (sigmaToPi_bijective R).surjective

lemma PrimeSpectrum.sigmaHomeoPi_apply {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)] [Finite ι]
    (p : Σ i, PrimeSpectrum (R i)) :
    sigmaHomeoPi R p = sigmaToPi R p :=
  rfl

namespace CommAlgCat

section

variable (R : Type*) [CommRing R]

abbrev finite (R : Type*) [CommRing R] : ObjectProperty (CommAlgCat R) :=
  fun S ↦ Module.Finite R S

abbrev etale (R : Type*) [CommRing R] : ObjectProperty (CommAlgCat R) :=
  fun S ↦ Algebra.Etale R S

abbrev finiteEtale (R : Type*) [CommRing R] : ObjectProperty (CommAlgCat R) :=
  finite R ⊓ etale R

abbrev FiniteEtale (R : Type*) [CommRing R] : Type _ :=
  (finiteEtale R).FullSubcategory

abbrev FiniteEtale.of (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.Etale R S] :
    FiniteEtale R where
  obj := .of R S
  property := ⟨‹_›, ‹_›⟩

variable {R}

@[simps]
abbrev FiniteEtale.ofHom {S T : Type u} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Module.Finite R S] [Algebra.Etale R S] [Module.Finite R T]
    [Algebra.Etale R T] (f : S →ₐ[R] T) :
    FiniteEtale.of R S ⟶ FiniteEtale.of R T where
  hom := CommAlgCat.ofHom f

end

instance (R : FiniteEtale k) : Finite (PrimeSpectrum R.obj) :=
  sorry

@[expose] def toFintypeCat : (FiniteEtale k)ᵒᵖ ⥤ FintypeCat where
  obj R := .of (PrimeSpectrum R.unop.obj)
  map f := { hom := PrimeSpectrum.comap f.unop.hom.hom }

@[expose] def ofFintypeCat : FintypeCat ⥤ (FiniteEtale k)ᵒᵖ where
  obj X := .op (.of _ (X → k))
  map {X Y} f := .op (FiniteEtale.ofHom <| Pi.algHom _ _ fun i ↦ Pi.evalAlgHom _ _ (f i))

def equiv [IsSepClosed k] : (FiniteEtale k)ᵒᵖ ≌ FintypeCat where
  functor := toFintypeCat k
  inverse := ofFintypeCat k
  unitIso :=
    sorry
  counitIso := NatIso.ofComponents
    (fun X ↦ FintypeCat.equivEquivIso sorry) sorry
  functor_unitIso_comp := sorry

end CommAlgCat

namespace CommRingCat

abbrev finiteEtale : MorphismProperty CommRingCat.{u} :=
  RingHom.toMorphismProperty fun f ↦ f.Finite ∧ f.Etale

lemma finiteEtale_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    finiteEtale f ↔ f.hom.Finite ∧ f.hom.Etale :=
  .rfl

end CommRingCat
