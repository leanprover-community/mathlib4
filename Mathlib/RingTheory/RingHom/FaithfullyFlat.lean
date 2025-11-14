/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/
import Mathlib.RingTheory.RingHom.Flat

/-!
# Faithfully flat ring maps

A ring map `f : R →+* S` is faithfully flat if `S` is faithfully flat as an `R`-algebra. This is
the same as being flat and a surjection on prime spectra.
-/

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}

/-- A ring map `f : R →+* S` is faithfully flat if `S` is faithfully flat as an `R`-algebra. -/
@[stacks 00HB "Part (4)", algebraize Module.FaithfullyFlat]
def FaithfullyFlat {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Module.FaithfullyFlat R S

lemma faithfullyFlat_algebraMap_iff [Algebra R S] :
    (algebraMap R S).FaithfullyFlat ↔ Module.FaithfullyFlat R S := by
  simp only [FaithfullyFlat]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

namespace FaithfullyFlat

lemma flat (hf : f.FaithfullyFlat) : f.Flat := by
  algebraize [f]
  exact inferInstanceAs <| Module.Flat R S

lemma iff_flat_and_comap_surjective :
    f.FaithfullyFlat ↔ f.Flat ∧ Function.Surjective f.specComap := by
  algebraize [f]
  rw [← algebraMap_toAlgebra f, faithfullyFlat_algebraMap_iff, flat_algebraMap_iff]
  exact ⟨fun h ↦ ⟨inferInstance, PrimeSpectrum.specComap_surjective_of_faithfullyFlat⟩,
    fun ⟨h, hf⟩ ↦ .of_specComap_surjective hf⟩

lemma eq_and : FaithfullyFlat =
      fun (f : R →+* S) ↦ f.Flat ∧ Function.Surjective f.specComap := by
  ext
  rw [iff_flat_and_comap_surjective]

lemma stableUnderComposition : StableUnderComposition FaithfullyFlat := by
  introv R hf hg
  algebraize [f, g, g.comp f]
  rw [← algebraMap_toAlgebra (g.comp f), faithfullyFlat_algebraMap_iff]
  exact .trans R S T

lemma of_bijective (hf : Function.Bijective f) : f.FaithfullyFlat := by
  rw [iff_flat_and_comap_surjective]
  refine ⟨.of_bijective hf, fun p ↦ ?_⟩
  use ((RingEquiv.ofBijective f hf).symm : _ →+* _).specComap p
  have : ((RingEquiv.ofBijective f hf).symm : _ →+* _).comp f = id R := by
    ext
    exact (RingEquiv.ofBijective f hf).injective (by simp)
  rw [← PrimeSpectrum.specComap_comp_apply, this, PrimeSpectrum.specComap_id]

lemma injective (hf : f.FaithfullyFlat) : Function.Injective ⇑f := by
  algebraize [f]
  exact FaithfulSMul.algebraMap_injective R S

lemma respectsIso : RespectsIso FaithfullyFlat :=
  stableUnderComposition.respectsIso (fun e ↦ .of_bijective e.bijective)

lemma isStableUnderBaseChange : IsStableUnderBaseChange FaithfullyFlat := by
  refine .mk respectsIso (fun R S T _ _ _ _ _ _ ↦ show (algebraMap _ _).FaithfullyFlat from ?_)
  rw [faithfullyFlat_algebraMap_iff] at *
  infer_instance

end RingHom.FaithfullyFlat
