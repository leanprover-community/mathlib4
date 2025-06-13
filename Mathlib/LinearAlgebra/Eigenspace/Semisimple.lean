/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Semisimple

/-!
# Eigenspaces of semisimple linear endomorphisms

This file contains basic results relevant to the study of eigenspaces of semisimple linear
endomorphisms.

## Main definitions / results

* `Module.End.IsSemisimple.genEigenspace_eq_eigenspace`: for a semisimple endomorphism,
  a generalized eigenspace is an eigenspace.

-/

open Function Set

namespace Module.End

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {f g : End R M}

lemma apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
    {μ : R} {k : ℕ∞} {m : M} (hm : m ∈ f.genEigenspace μ k)
    (hfg : Commute f g) (hss : g.IsFinitelySemisimple) (hnil : IsNilpotent (f - g)) :
    g m = μ • m := by
  rw [f.mem_genEigenspace] at hm
  obtain ⟨l, -, hm⟩ := hm
  rw [← f.mem_genEigenspace_nat] at hm
  set p := f.genEigenspace μ l
  have h₁ : MapsTo g p p := mapsTo_genEigenspace_of_comm hfg μ l
  have h₂ : MapsTo (g - algebraMap R (End R M) μ) p p :=
    mapsTo_genEigenspace_of_comm (hfg.sub_right <| Algebra.commute_algebraMap_right μ f) μ l
  have h₃ : MapsTo (f - g) p p :=
    mapsTo_genEigenspace_of_comm (Commute.sub_right rfl hfg) μ l
  have h₄ : MapsTo (f - algebraMap R (End R M) μ) p p :=
    mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ l
  replace hfg : Commute (f - algebraMap R (End R M) μ) (f - g) :=
    (Commute.sub_right rfl hfg).sub_left <| Algebra.commute_algebraMap_left μ (f - g)
  suffices IsNilpotent ((g - algebraMap R (End R M) μ).restrict h₂) by
    replace this : g.restrict h₁ - algebraMap R (End R p) μ = 0 :=
      eq_zero_of_isNilpotent_of_isFinitelySemisimple this (by simpa using hss.restrict _)
    simpa [LinearMap.restrict_apply, sub_eq_zero] using LinearMap.congr_fun this ⟨m, hm⟩
  simpa [LinearMap.restrict_sub h₄ h₃] using (LinearMap.restrict_commute hfg h₄ h₃).isNilpotent_sub
    (f.isNilpotent_restrict_sub_algebraMap μ l) (Module.End.isNilpotent.restrict h₃ hnil)

lemma IsFinitelySemisimple.genEigenspace_eq_eigenspace
    (hf : f.IsFinitelySemisimple) (μ : R) {k : ℕ∞} (hk : 0 < k) :
    f.genEigenspace μ k = f.eigenspace μ := by
  refine le_antisymm (fun m hm ↦ mem_eigenspace_iff.mpr ?_) (f.genEigenspace μ |>.mono ?_)
  · apply apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil hm rfl hf
    simp
  · exact Order.one_le_iff_pos.mpr hk

lemma IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
    (hf : f.IsFinitelySemisimple) (μ : R) :
    f.maxGenEigenspace μ = f.eigenspace μ :=
  hf.genEigenspace_eq_eigenspace μ ENat.top_pos

end Module.End
