/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Support
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
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

/-!

# Subsets of prime spectra related to modules

## Main results

- `LocalizedModule.subsingleton_iff_disjoint` : `M[1/f] = 0 ↔ D(f) ∩ Supp M = 0`.
- `Module.isClosed_support` : If `M` is a finite `R`-module, then `Supp M` is closed.

## TODO
- If `M` is finitely presented, the complement of `Supp M` is quasi-compact. (stacks#051B)

-/

public section

variable {R A M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [CommRing A] [Algebra R A] [Module A M]

variable (R M) in
lemma IsLocalRing.closedPoint_mem_support [IsLocalRing R] [Nontrivial M] :
    IsLocalRing.closedPoint R ∈ Module.support R M := by
  obtain ⟨p, hp⟩ := (Module.nonempty_support_iff (R := R)).mpr ‹_›
  exact Module.mem_support_mono le_top hp

/-- `M[1/f] = 0` if and only if `D(f) ∩ Supp M = 0`. -/
lemma LocalizedModule.subsingleton_iff_disjoint {f : R} :
    Subsingleton (LocalizedModule (.powers f) M) ↔
      Disjoint ↑(PrimeSpectrum.basicOpen f) (Module.support R M) := by
  rw [subsingleton_iff_support_subset, PrimeSpectrum.basicOpen_eq_zeroLocus_compl,
    disjoint_compl_left_iff, Set.le_iff_subset]

lemma Module.stableUnderSpecialization_support : StableUnderSpecialization (Module.support R M) :=
  fun x y e ↦ mem_support_mono <| (PrimeSpectrum.le_iff_specializes x y).mpr e

lemma Module.isClosed_support [Module.Finite R M] :
    IsClosed (Module.support R M) := by
  rw [support_eq_zeroLocus]
  apply PrimeSpectrum.isClosed_zeroLocus

lemma Module.support_subset_preimage_comap [IsScalarTower R A M] :
    Module.support A M ⊆ PrimeSpectrum.comap (algebraMap R A) ⁻¹' Module.support R M := by
  intro x hx
  simp only [Set.mem_preimage, mem_support_iff', PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
    ne_eq, not_imp_not] at hx ⊢
  obtain ⟨m, hm⟩ := hx
  exact ⟨m, fun r e ↦ hm _ (by simpa)⟩
