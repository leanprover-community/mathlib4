/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Injective
import Mathlib.RingTheory.RingHom.Surjective

/-!
# Properties satisfying faithfully flat descent for rings

We show the following properties of ring homomorphisms descend under faithfully flat ring maps:

- injective
- surjective
- bijective
-/

open TensorProduct

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {T : Type*} [CommRing T] [Algebra R T]

lemma Module.FaithfullyFlat.injective_of_tensorProduct [Module.FaithfullyFlat R S]
    (H : Function.Injective (algebraMap S (S ⊗[R] T))) :
    Function.Injective (algebraMap R T) := by
  have : LinearMap.lTensor S (Algebra.linearMap R T) =
      Algebra.linearMap S (S ⊗[R] T) ∘ₗ (AlgebraTensorModule.rid R S S).toLinearMap := by
    ext; simp
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective R S (Algebra.linearMap R T)).mp
  simpa [this] using H

lemma Module.FaithfullyFlat.surjective_of_tensorProduct [Module.FaithfullyFlat R S]
    (H : Function.Surjective (algebraMap S (S ⊗[R] T))) :
    Function.Surjective (algebraMap R T) := by
  have : LinearMap.lTensor S (Algebra.linearMap R T) =
      Algebra.linearMap S (S ⊗[R] T) ∘ₗ (AlgebraTensorModule.rid R S S).toLinearMap := by
    ext; simp
  apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S (Algebra.linearMap R T)).mp
  simpa [this] using H

lemma Module.FaithfullyFlat.bijective_of_tensorProduct [Module.FaithfullyFlat R S]
    (H : Function.Bijective (algebraMap S (S ⊗[R] T))) :
    Function.Bijective (algebraMap R T) :=
  ⟨injective_of_tensorProduct H.1, surjective_of_tensorProduct H.2⟩

end

lemma RingHom.FaithfullyFlat.codescendsAlong_injective :
    CodescendsAlong (fun f ↦ Function.Injective f) FaithfullyFlat := by
  apply CodescendsAlong.mk _ injective_respectsIso
  introv h H
  rw [faithfullyFlat_algebraMap_iff] at h
  exact h.injective_of_tensorProduct H

lemma RingHom.FaithfullyFlat.codescendsAlong_surjective :
    CodescendsAlong (fun f ↦ Function.Surjective f) FaithfullyFlat := by
  apply CodescendsAlong.mk _ surjective_respectsIso
  introv h H
  rw [faithfullyFlat_algebraMap_iff] at h
  exact h.surjective_of_tensorProduct H

lemma RingHom.FaithfullyFlat.codescendsAlong_bijective :
    CodescendsAlong (fun f ↦ Function.Bijective f) FaithfullyFlat :=
  .and codescendsAlong_injective codescendsAlong_surjective
