/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Construction of L-functions

This file constructs L-functions as formal Dirichlet series.

## Main definitions

* `ArithmeticFunction.eulerProduct f`: the Euler product of a family `f i` of Dirichlet series.

## TODO
* If each `f i` is multiplicative, then `ArithmeticFunction.eulerProduct f` is multiplicative.
-/

@[expose] public section

namespace ArithmeticFunction

section EulerProduct

open Filter

variable {ι R : Type*} [CommSemiring R]

/-- A private uniform space instance on `ArithmeticFunction R` in order to define `eulerProduct` as
a `tprod`. If `R` is viewed as having the discrete topology, then the resulting topology on
`ArithmeticFunction R` is the topology of pointwise convergence (see `tendsto_iff`).

See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
local instance uniformSpace : UniformSpace (ArithmeticFunction R) :=
  letI : UniformSpace R := ⊥
  .comap ((↑) : ArithmeticFunction R → (ℕ → R)) inferInstance

/-- A family `f i : ArithmeticFunction R` tends to `g` if and only if for each `n`, the `n`th
coefficient of `f i` is eventually equal to the `n`th coefficient of `g`. If `R` is viewed as
having the discrete topology, then this is the topology of pointwise convergence.

See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
private theorem tendsto_iff
    {f : ι → ArithmeticFunction R} {F : Filter ι} {g : ArithmeticFunction R} :
    Tendsto f F (nhds g) ↔ ∀ n, ∀ᶠ i in F, f i n = g n := by
  let : UniformSpace R := ⊥
  have : Topology.IsInducing ((↑) : ArithmeticFunction R → (ℕ → R)) := ⟨rfl⟩
  simp [this.tendsto_nhds_iff, tendsto_pi_nhds]

/-- The uniform space structure on arithmetic functions is complete.
See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
local instance : CompleteSpace (ArithmeticFunction R) := by
  let : UniformSpace R := ⊥
  apply IsUniformInducing.completeSpace ⟨rfl⟩
  apply IsClosed.isComplete
  have : Set.range ((↑) : ArithmeticFunction R → (ℕ → R)) = {f | Function.eval 0 f = 0} := by
    ext f
    exact ⟨by rintro ⟨f, rfl⟩; simp, fun hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩
  rw [this]
  apply isClosed_setOf_map_zero

/-- The Euler product of a family of arithmetic functions. Defined as a `tprod`, but see
`tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
noncomputable def eulerProduct (f : ι → ArithmeticFunction R) : ArithmeticFunction R :=
  ∏' i, f i

/-- If arithmetic functions `f i` converges to `1` pointwise, then the partial products
`∏ i ∈ s, f i` converge to `eulerProduct f` pointwise. -/
theorem tendsTo_eulerProduct_of_tendsTo (f : ι → ArithmeticFunction R)
    (hf : ∀ n, ∀ᶠ i in cofinite, f i n = (1 : ArithmeticFunction R) n) :
    ∀ n, ∀ᶠ s in atTop, (∏ i ∈ s, f i) n = eulerProduct f n := by
  let : UniformSpace R := ⊥
  have : IsUniformInducing ((↑) : ArithmeticFunction R → (ℕ → R)) := ⟨rfl⟩
  classical
  suffices Multipliable f from tendsto_iff.mp this.hasProd
  simp_rw [multipliable_iff_cauchySeq_finset, CauchySeq, ← this.cauchy_map_iff,
    Filter.map_map, cauchy_map_iff', Pi.uniformity, DiscreteUniformity.eq_principal_setRelId,
    tendsto_iInf, tendsto_comap_iff, tendsto_principal, Function.comp_apply, prod_atTop_atTop_eq,
    eventually_atTop_prod_self, SetRel.mem_id]
  intro n
  replace hf : ∀ k ∈ Set.Iic n, ∀ᶠ (x : ι) in cofinite, (f x) k = (1 : ArithmeticFunction R) k :=
    fun k hk ↦ hf k
  rw [← eventually_all_finite (Set.finite_Iic n), eventually_iff_exists_mem] at hf
  obtain ⟨s, hs, hs'⟩ := hf
  let t := (mem_cofinite.mp hs).toFinset
  refine ⟨t, fun u v hu hv ↦ ?_⟩
  rw [← Finset.prod_sdiff hu, ← Finset.prod_sdiff hv]
  replace hu : ∀ i ∈ u \ t, i ∈ s := by
    intro i hi
    rw [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.notMem_compl_iff] at hi
    exact hi.2
  replace hv : ∀ i ∈ v \ t, i ∈ s := by
    intro i hi
    rw [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.notMem_compl_iff] at hi
    exact hi.2
  suffices ∀ k ≤ n, (∏ x ∈ u \ t, f x) k = (∏ x ∈ v \ t, f x) k by
    rw [mul_apply, mul_apply]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [this k.1 (Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hk))]
  suffices ∀ w, (∀ i ∈ w, i ∈ s) → ∀ k ≤ n, (∏ x ∈ w, f x) k = (1 : ArithmeticFunction R) k by
    intro k hk
    rw [this (u \ t) hu k hk, this (v \ t) hv k hk]
  intro w hw
  induction w using Finset.induction_on
  case empty => simp
  case insert i w hi hw' =>
    intro k hk
    rw [← one_mul (1 : ArithmeticFunction R), Finset.prod_insert hi, mul_apply, mul_apply]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have h1 := hs' i (hw i (Finset.mem_insert_self i w)) j.1
      ((Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hj)).trans hk)
    have h2 := hw' (fun i hi ↦ hw i (Finset.mem_insert_of_mem hi)) j.2
      ((Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hj)).trans hk)
    rw [h1, h2]

end EulerProduct

end ArithmeticFunction
