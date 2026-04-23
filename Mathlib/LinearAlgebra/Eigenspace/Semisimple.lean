/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas
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

/-!
# Eigenspaces of semisimple linear endomorphisms

This file contains basic results relevant to the study of eigenspaces of semisimple linear
endomorphisms.

## Main definitions / results

* `Module.End.IsFinitelySemisimple.genEigenspace_eq_eigenspace`: for a semisimple endomorphism,
  a generalized eigenspace is an eigenspace.
* `Module.End.IsSemisimple.iSup_eigenspace_eq_top`: over an algebraically closed field,
  the eigenspaces of a semisimple endomorphism span the whole space.
* `Module.End.IsSemisimple.eq_zero_iff_forall_eigenvalue`: a semisimple endomorphism over
  an algebraically closed field is zero iff all eigenvalues are zero.

-/

public section

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

section AlgClosed

variable {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {f : End K V}

lemma IsSemisimple.iSup_eigenspace_eq_top (hf : f.IsSemisimple) :
    ⨆ μ : K, f.eigenspace μ = ⊤ := by
  simpa only [(isFinitelySemisimple_iff_isSemisimple.mpr hf).maxGenEigenspace_eq_eigenspace] using
    iSup_maxGenEigenspace_eq_top f

lemma IsSemisimple.eq_zero_iff_forall_eigenvalue (hf : f.IsSemisimple) :
    f = 0 ↔ ∀ μ : K, f.HasEigenvalue μ → μ = 0 := by
  constructor
  · rintro rfl μ hμ
    by_contra hμ0
    obtain ⟨x, hx, hx_ne⟩ := (Submodule.ne_bot_iff _).mp hμ
    rw [mem_eigenspace_iff] at hx
    exact hx_ne ((smul_eq_zero.mp hx.symm).resolve_left hμ0)
  · intro h
    suffices f.eigenspace 0 = ⊤ by rwa [eigenspace_zero, LinearMap.ker_eq_top] at this
    rw [← hf.iSup_eigenspace_eq_top]
    refine le_antisymm (le_iSup _ 0) (iSup_le fun μ ↦ ?_)
    rcases eq_or_ne μ 0 with rfl | hμ
    · exact le_refl _
    · have : f.eigenspace μ = ⊥ := not_not.mp (hasEigenvalue_iff.not.mp fun he ↦ hμ (h μ he))
      simp [this]

end AlgClosed

end Module.End
