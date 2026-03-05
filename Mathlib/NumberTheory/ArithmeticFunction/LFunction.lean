/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs
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

section EulerProduct -- Euler product of Arithmetic Functions

open Filter

variable {ι R : Type*} [CommSemiring R]

/-- A private uniform space instance on `ArithmeticFunction` in order to define `eulerProduct` as a
`tprod`. See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
local instance uniformSpace : UniformSpace (ArithmeticFunction R) :=
  .comap ((↑) : ArithmeticFunction R → (ℕ → R)) <| .ofCore <|
    .mk (⨅ s : Finset ℕ, 𝓟 {(f, g) | Set.EqOn f g s})
      (by simp [Set.subset_def, Set.eqOn_refl])
      (tendsto_iInf_iInf fun _ ↦ tendsto_principal_principal.mpr fun _ ↦ Set.EqOn.symm)
      (le_iInf fun s ↦ lift'_le (le_principal_iff.mp (iInf_le _ s))
        (by grind [principal_mono, SetRel.comp, Set.EqOn]))

/-- The uniformity on `ArithmeticFunction` required in order to define `eulerProduct` as a `tprod`.
See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
private theorem uniformity_eq : uniformity (ArithmeticFunction R) =
    comap (fun i ↦ (i.1, i.2)) (⨅ s : Finset ℕ, 𝓟 {((f : ℕ → R), g) | Set.EqOn f g s}) :=
  rfl

/-- The topology on `ArithmeticFunction` is the topology of pointwise convergence.
See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
private theorem tendsto_iff
    {f : ι → ArithmeticFunction R} {F : Filter ι} {g : ArithmeticFunction R} :
    Tendsto f F (nhds g) ↔ ∀ n, Filter.Tendsto (fun i ↦ f i n) F (pure (g n)) := by
  simp_rw [nhds_eq_comap_uniformity,
    uniformity_eq, tendsto_comap_iff, tendsto_iInf, tendsto_principal, Function.comp_apply,
    tendsto_pure, Set.EqOn, Finset.mem_coe, Set.mem_setOf_eq, eventually_all_finset, eq_comm]
  exact ⟨fun h n ↦ by simpa using h { n }, fun h s k hk ↦ h k⟩

/-- The uniform space structure on arithmetic functions is complete.
See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
local instance : CompleteSpace (ArithmeticFunction R) where
  complete {f} hf := by
    simp_rw [Cauchy, nhds_eq_comap_uniformity, uniformity_eq, comap_iInf, comap_principal,
      le_iInf_iff, le_principal_iff, Set.preimage_setOf_eq] at hf ⊢
    obtain ⟨hf0, hf⟩ := hf
    replace hf' : ∀ i, ∃ x : R, {a | x = a i} ∈ f := by
      intro i
      specialize hf {i}
      simp_rw [Finset.coe_singleton, Set.eqOn_singleton, mem_prod_self_iff] at hf
      obtain ⟨t, htf, ht⟩ := hf
      obtain ⟨g₁, hg₁⟩ := hf0.nonempty_of_mem htf
      exact ⟨g₁ i, Filter.mem_of_superset htf fun g₂ hg₂ ↦ @ht (g₁, g₂) ⟨hg₁, hg₂⟩⟩
    choose g hg using hf'
    refine ⟨⟨g, ?_⟩, fun s ↦ ?_⟩
    · specialize hg 0
      contrapose! hg
      simp [hg]
    · simp_rw [coe_mk, Set.EqOn, Finset.mem_coe, Set.setOf_forall, biInter_finset_mem]
      exact fun i hi ↦ hg i

/-- The Euler product of a family of arithmetic functions. Defined as a `tprod`, but see
`tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
noncomputable def eulerProduct (f : ι → ArithmeticFunction R) : ArithmeticFunction R :=
  ∏' i, f i

set_option backward.isDefEq.respectTransparency false in
/-- If arithmetic functions `f i` converges to `1` pointwise, then the partial products
`∏ i ∈ s, f i` converge to `eulerProduct f` pointwise. -/
theorem tendsTo_eulerProduct_of_tendsTo (f : ι → ArithmeticFunction R)
    (hf : ∀ n, Tendsto (fun i ↦ f i n) cofinite (pure ((1 : ArithmeticFunction R) n))) :
    ∀ n, Tendsto (fun s : Finset ι ↦ (∏ i ∈ s, f i) n) atTop (pure (eulerProduct f n)) := by
  classical
  suffices Multipliable f from tendsto_iff.mp this.hasProd
  simp_rw [multipliable_iff_cauchySeq_finset, CauchySeq, cauchy_map_iff',
    uniformity_eq, tendsto_comap_iff, tendsto_iInf, tendsto_principal, Function.comp_apply,
    Set.EqOn, Finset.mem_coe, Set.mem_setOf_eq, eventually_all_finset]
  intro s n hn
  rw [prod_atTop_atTop_eq, eventually_atTop_prod_self]
  replace hf : ∀ k ∈ Set.Iic n, ∀ᶠ (x : ι) in cofinite, (f x) k = (1 : ArithmeticFunction R) k :=
    fun k hk ↦ tendsto_pure.mp (hf k)
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
