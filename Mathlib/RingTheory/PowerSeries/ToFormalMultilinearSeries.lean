/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Xavier Genereux
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Data.List.ToFinsupp
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Power series as formal multilinear series

This file defines the map from formal power series `R⟦X⟧` to formal multilinear series
`FormalMultilinearSeries R A A`, and proves key properties including injectivity and
compatibility with composition.

## Main definitions

* `PowerSeries.toFormalMultilinearSeries`: maps `f : R⟦X⟧` to the formal multilinear series
  whose `n`-th term is `(coeff n f) • ContinuousMultilinearMap.mkPiAlgebraFin R n A`.

## Main results

* `PowerSeries.toFormalMultilinearSeries_inj`: the map is injective.
* `PowerSeries.toFormalMultilinearSeries_comp`: the map is compatible with composition
  of power series.

-/

@[expose] public section

variable {R : Type*} [Field R]
variable {A : Type*} [CommRing A]

variable [Algebra R A]

@[simp]
theorem List.prod_ofFn_smul {m : ℕ} (g : Fin m → R) (f : Fin m → A) :
    (List.ofFn (fun i ↦ g i • f i)).prod = (List.ofFn g).prod • (List.ofFn f).prod := by
  simp [Algebra.smul_def, List.prod_ofFn, Finset.prod_mul_distrib, map_prod]

@[simp]
theorem ofFn_prod_one {n : ℕ} : (List.ofFn (1 : Fin n → A)).prod = 1 := by
  induction n <;> simp

variable [TopologicalSpace A] [IsTopologicalRing A]

theorem mkPiAlgebraFin_ne_zero [Nontrivial A] (n : ℕ) :
    ContinuousMultilinearMap.mkPiAlgebraFin R n A ≠ 0 := by
  intro h
  simpa using congr($h 1)

open PowerSeries
open Nat hiding pow_zero pow_succ
open Set Fin Topology
open Finset

variable (A) in
/-- The formal multilinear series associated to a power series `f : R⟦X⟧`, given by
`n ↦ (coeff n f) • ContinuousMultilinearMap.mkPiAlgebraFin R n A`. -/
noncomputable def PowerSeries.toFormalMultilinearSeries (f : R⟦X⟧) :
    FormalMultilinearSeries R A A := fun n ↦
  (coeff n f) • (ContinuousMultilinearMap.mkPiAlgebraFin R n A)

omit [TopologicalSpace A] [IsTopologicalRing A] in
private lemma prod_univ_embedding {n : ℕ} (a : Fin n → A) (x : Composition n) :
    ∏ i, ∏ j, a ((x.embedding i) j) = ∏ i, a i := by
  simpa [Finset.prod_sigma', Finset.univ_sigma_univ] using x.blocksFinEquiv.prod_comp a

variable (f g : R⟦X⟧)

@[simp]
theorem List.filter_nezero_sum (l : List ℕ) : (List.filter (· ≠ 0) l).sum = l.sum := by
  induction l <;> grind

def Composition.ofFinsuppAntidiag (n : ℕ) (c : ℕ →₀ ℕ)
    (hc : c ∈ Finset.finsuppAntidiag (Finset.range n) n) : Composition n where
  blocks := (List.ofFn (fun n : Fin n ↦ c n)).filter (· ≠ 0)
  blocks_pos := by grind
  blocks_sum := by
    grind [mem_finsuppAntidiag, List.filter_nezero_sum, sum_ofFn, sum_univ_eq_sum_range]

abbrev posAntidiagonals (n : ℕ) : Finset ((_ : ℕ) × (ℕ →₀ ℕ)) := (Finset.range (n + 1)).sigma
  fun d ↦ {c ∈ (Finset.range d).finsuppAntidiag n | ∀ i ∈ Finset.range d, 0 < c i}

def Composition.asFinsuppAntidiag (n : ℕ) : Composition n ≃ posAntidiagonals n where
  toFun c := {
    val := ⟨c.length, c.blocks.toFinsupp⟩
    property := by
      rw [mem_sigma, mem_filter, mem_finsuppAntidiag]
      constructor
      · grind [Composition.length_le]
      · simp_all [Composition.length, Finset.sum_range, List.toFinsupp_support]
  }
  invFun s := ⟨(List.range s.1.1).map s.1.2, by aesop, by aesop⟩
  left_inv x := by simp_all [Composition.ext_iff, List.ext_get_iff]
  right_inv f := by
    obtain ⟨⟨c, f⟩, hf⟩ := f
    simp_rw [length, List.length_map, List.length_range, Subtype.mk.injEq, Sigma.mk.injEq,
      heq_eq_eq, true_and]
    ext a
    by_cases ha : a ∈ f.support <;> grind [List.toFinsupp_apply, mem_finsuppAntidiag]

lemma Finset.sigma_filter {ι : Type*} (α : ι → Type*) (s : Finset ι)
    (t : (i : ι) → Finset (α i)) (p : {i : ι} → α i → Prop)
    [∀ i, DecidablePred (p (i := i))] :
    (s.sigma t).filter (fun x ↦ p x.snd) = (s.sigma fun i ↦ ((t i).filter p)) := by
  ext ⟨i, a⟩
  simp [Finset.mem_filter, Finset.mem_sigma, and_assoc]

variable {g} in
private lemma apply_pos_of_prod_ne_zero (hassump : constantCoeff g = 0) (x : Nat) (y : ℕ →₀ ℕ) :
    coeff x f * ∏ i ∈ Finset.range x, (coeff (y i)) g ≠ 0 → ∀ i ∈ Finset.range x, 0 < y i := by
  contrapose!
  rintro ⟨i, hi, h0⟩
  apply mul_eq_zero_of_right _ (Finset.prod_eq_zero hi ?_)
  rwa [Nat.le_zero.mp h0, PowerSeries.coeff_zero_eq_constantCoeff]

variable {f g} in
private theorem sum_sigma_range_eq_sum_posAntidiagonals (c : ℕ) :
    ∑ x ∈ (Finset.range (c + 1)).sigma fun i ↦ (Finset.range i).finsuppAntidiag c with
      ∀ i ∈ Finset.range x.fst, 0 < x.snd i,
      (coeff x.fst) f * ∏ i ∈ Finset.range x.fst, (coeff (x.snd i)) g =
    ∑ x ∈ posAntidiagonals c, (coeff x.fst) f * ∏ i ∈ Finset.range x.fst, (coeff (x.snd i)) g := by
  apply Finset.sum_congr _ (by simp)
  rw [posAntidiagonals, ← Finset.sigma_filter]

variable {g} in
theorem coeff_subst_comp (hassump : constantCoeff g = 0) (f : R⟦X⟧) (c : ℕ) :
    coeff c (f.subst g) = ∑ C : Composition c, coeff (C.length) f *
      (C.blocks.map fun i ↦ coeff i g).prod := by
  simp_rw [PowerSeries.coeff_subst' (.of_constantCoeff_zero' hassump), smul_eq_mul,
    coeff_pow, Finset.mul_sum]
  rw [finsum_eq_finsetSum_of_support_subset (s := Finset.range (c + 1))]
  · have (x) (hx : x ∈ (Finset.range (c + 1)).sigma fun i ↦ (Finset.range i).finsuppAntidiag c) :=
      apply_pos_of_prod_ne_zero f hassump x.fst x.snd
    rw [Finset.sum_sigma', ←sum_filter_of_ne this, sum_sigma_range_eq_sum_posAntidiagonals,
      ←sum_coe_sort, sum_equiv (Composition.asFinsuppAntidiag c)]
      <;> simp [Composition.asFinsuppAntidiag, ←prod_univ_fun_getElem, prod_range]
  · intro a ha
    contrapose ha
    rw [Function.mem_support, not_ne_iff, Finset.sum_eq_zero]
    intro x hx
    apply mul_eq_zero_of_right
    obtain ⟨i, hi, hi'⟩ : ∃ i ∈ Finset.range a, x i = 0 := by
      by_contra!
      suffices a ≤ (Finset.range a).sum x by grind [Finset.mem_finsuppAntidiag]
      calc a = (Finset.range a).sum 1 := by simp
        _ ≤ (Finset.range a).sum x :=
          Finset.sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.mpr (this i hi)
    apply Finset.prod_eq_zero hi <| by rwa [hi', PowerSeries.coeff_zero_eq_constantCoeff]

theorem toFormalMultilinearSeries_inj [Nontrivial A] :
    Function.Injective (toFormalMultilinearSeries (R := R) A) := by
  intro f g h
  ext n
  exact smul_left_injective R (mkPiAlgebraFin_ne_zero n) (funext_iff.mp h n)

@[simp]
theorem FormalMultilinearSeries.applyComposition_apply_prod {𝕜 : Type*} {E : Type*} {F : Type*}
    [CommRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [CommRing F] [Algebra 𝕜 F] [TopologicalSpace E]
    [TopologicalSpace F]
    [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E] [IsTopologicalRing F]
    [ContinuousConstSMul 𝕜 F]
    (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (c : Composition n) (v : Fin n → E) :
    ∏ i, p.applyComposition c v i = ∏ i, p (c.blocksFun i) (v ∘ c.embedding i) := by
  rfl

theorem toFormalMultilinearSeries_comp (f g : R⟦X⟧) (hfg : constantCoeff g = 0) :
    PowerSeries.toFormalMultilinearSeries A (f.subst g) =
      (f.toFormalMultilinearSeries A).comp (g.toFormalMultilinearSeries A) := by
  ext n : 1
  rw [toFormalMultilinearSeries, coeff_subst_comp hfg, FormalMultilinearSeries.comp, sum_smul,
    sum_congr rfl]
  intro x _
  ext a
  simp [← Composition.ofFn_blocksFun, toFormalMultilinearSeries, List.prod_ofFn, mul_smul,
    prod_smul, prod_univ_embedding]
