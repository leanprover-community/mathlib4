/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.BigOperators


/-!
# Lemmas about ideals of `MvPowerSeries`

## Main results

* `MvPowerSeries.mem_map_C_iff_of_FG`
* `MvPowerSeries.ker_map`
* `MvPowerSeries.ker_mapAlgHom`
-/


@[expose] public section

namespace MvPowerSeries

variable {R S σ : Type*} [CommRing R] [CommRing S]

section

open Ideal

variable {S₁ S₂ : Type*} [CommRing S₁] [CommRing S₂] [Algebra R S₁] [Algebra R S₂]
  {I : Ideal R} {f : MvPowerSeries σ R}

theorem mem_map_C_imp (h : f ∈ I.map C) : ∀ m : σ →₀ ℕ, f.coeff m ∈ I := by
  classical
  refine Submodule.span_induction ?_ ?_ ?_ ?_ h
  · intro f hf n
    obtain ⟨x, hx⟩ := (Set.mem_image _ _ _).mp hf
    rw [← hx.right, coeff_C]
    by_cases h : n = 0
    · simpa [h] using hx.left
    · simp [if_neg h]
  · simp
  · exact fun f g _ _ hf hg n => by simp [I.add_mem (hf n) (hg n)]
  · refine fun f g _ hg n => ?_
    rw [smul_eq_mul, coeff_mul]
    exact I.sum_mem fun c _ => I.mul_mem_left (f.coeff c.fst) (hg c.snd)

/-- If every coefficient of `f` lies in `I`, and `I` is finitely generated,
then `f ∈ I.map C`. -/
theorem mem_map_C_of_forall_coeff_mem (hI : I.FG) (hf : ∀ m : σ →₀ ℕ, f.coeff m ∈ I) :
    f ∈ I.map C := by
  obtain ⟨S, hS⟩ := hI
  have (m : σ →₀ ℕ) : ∃ r : S → R, (coeff m) f = ∑ a ∈ S.attach, r a * a := by
    have h_mem : (coeff m) f ∈ Submodule.span R (Set.range (fun a : S => a.val)) := by
      convert hf m using 1
      simp [hS]
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h_mem
    exact ⟨c, by simp_all [Finsupp.sum_fintype]⟩
  obtain ⟨g, hg⟩ : ∃ g : S → MvPowerSeries σ R,
      ∀ m, (coeff m) f = ∑ a ∈ S.attach, (coeff m) (g a) * a.val := by
    choose r hr using this
    exact ⟨fun a m => r m a, hr⟩
  have h_sum : f = ∑ a ∈ S.attach, g a * MvPowerSeries.C a.val := by
    simp [MvPowerSeries.ext_iff, hg]
  rw [← hS, h_sum]
  exact sum_mem _ fun a _ => mul_mem_left _ _ (mem_map_of_mem _ (subset_span a.2))

/-- Suppose that `I` is finitely generated, then the push-forward of an ideal `I` of `R` to
`MvPowerSeries σ R` via inclusion is exactly the set of power series whose
coefficients are in `I`. -/
theorem mem_map_C_iff_of_FG (hI : I.FG) :
    f ∈ I.map C ↔ ∀ m, f.coeff m ∈ I :=
  ⟨mem_map_C_imp, mem_map_C_of_forall_coeff_mem hI⟩

theorem ker_map_of_FG (f : R →+* S) (hf : (RingHom.ker f).FG) :
    RingHom.ker (map f (σ := σ)) = Ideal.map C (RingHom.ker f) := by
  ext
  rw [mem_map_C_iff_of_FG hf, RingHom.mem_ker, MvPowerSeries.ext_iff]
  simp_rw [coeff_map, coeff_zero, RingHom.mem_ker]

lemma ker_mapAlgHom_of_FG (f : S₁ →ₐ[R] S₂) (hf : (RingHom.ker f).FG) :
    RingHom.ker (mapAlgHom (σ := σ) f) = Ideal.map C (RingHom.ker f) :=
  ker_map_of_FG f.toRingHom hf

end

end MvPowerSeries
