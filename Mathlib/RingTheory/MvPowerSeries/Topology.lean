/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/

import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.UniformGroup
import Mathlib.Topology.UniformSpace.Pi

/-! # Topology on power series

Let `α` be with Semiring α` and `TopologicalSpace α`
In this file we the topology on `MvPowerSeries σ α`
that corresponds to the simple convergence on its coefficients.
It is the coarsest topology for which all coefficients maps are continuous.

When `α` has `UniformSpace α`, we define the corresponding uniform structure.

When the type of coefficients has the discrete topology,
it corresponds to the topology defined by [bourbaki1981], chapter 4, §4, n°2

It is *not* the adic topology in general.

- `tendsto_pow_zero_of_constantCoeff_zero` : if the constant coefficient of `f`
is nilpotent, then the powers of `f` converge to zero

- `tendsto_pow_of_constantCoeff_nilpotent_iff` : the powers of `f` converge to zero iff
the constant coefficient of `f` is nilpotent

- `hasSum_of_monomials_self` : viewed as an infinite sum, a power series coverges to itself

TODO: add the similar result for the series of homogeneous components

## Instances

- If `α` is a topological (semi)ring, then so is `MvPowerSeries σ α`

- If the topology of `α` is T2, then so is that of `MvPowerSeries σ α``

- If `α` is a `uniformAddGroup`, then so is `MvPowerSeries σ α``

- If `α` is complete, then so is `MvPowerSeries σ α`

-/


theorem Finset.prod_one_add {ι α : Type _} [DecidableEq ι] [CommRing α] {f : ι → α} (s : Finset ι) :
    (s.prod fun i => 1 + f i) = s.powerset.sum fun t => t.prod f := by
  simp_rw [add_comm, Finset.prod_add]
  congr
  ext t
  convert mul_one (Finset.prod t fun a => f a)
  exact Finset.prod_eq_one (fun i _ => rfl)

theorem MvPowerSeries.coeff_eq_apply {σ α : Type _} [Semiring α] (f : MvPowerSeries σ α)
    (d : σ →₀ ℕ) : MvPowerSeries.coeff α d f = f d :=
  rfl

namespace MvPowerSeries

open Function

variable (σ : Type _) (α : Type _)

section Topological

variable [TopologicalSpace α]

namespace WithPiTopology

/-- The pointwise topology on MvPowerSeries -/
scoped instance topologicalSpace : TopologicalSpace (MvPowerSeries σ α) :=
  Pi.topologicalSpace

/-- Components are continuous -/
theorem continuous_component :
    ∀ d : σ →₀ ℕ, Continuous fun a : MvPowerSeries σ α => a d :=
  continuous_pi_iff.mp continuous_id

variable {σ α}

/-- coeff are continuous -/
theorem continuous_coeff [Semiring α] (d : σ →₀ ℕ) :
    Continuous (MvPowerSeries.coeff α d) :=
  continuous_component σ α d

/-- constant_coeff is continuous -/
theorem continuous_constantCoeff [Semiring α] :
    Continuous (constantCoeff σ α) :=
  continuous_component σ α 0

/-- A family of power series converges iff it converges coefficientwise -/
theorem tendsto_iff_coeff_tendsto [Semiring α] {ι : Type _}
    (f : ι → MvPowerSeries σ α) (u : Filter ι) (g : MvPowerSeries σ α) :
    Filter.Tendsto f u (nhds g) ↔
    ∀ d : σ →₀ ℕ, Filter.Tendsto (fun i => coeff α d (f i)) u (nhds (coeff α d g)) := by
  rw [nhds_pi, Filter.tendsto_pi]
  exact forall_congr' (fun d => Iff.rfl)

variable (σ α)

/-- The semiring topology on MvPowerSeries of a topological semiring -/
@[scoped instance] theorem topologicalSemiring [Semiring α] [TopologicalSemiring α] :
    TopologicalSemiring (MvPowerSeries σ α) where
    continuous_add := continuous_pi fun d => Continuous.comp continuous_add
      (Continuous.prod_mk (Continuous.fst' (continuous_component σ α d))
        (Continuous.snd' (continuous_component σ α d)))
    continuous_mul := continuous_pi fun _ => continuous_finset_sum _ (fun i _ => Continuous.comp
      continuous_mul (Continuous.prod_mk (Continuous.fst' (continuous_component σ α i.fst))
        (Continuous.snd' (continuous_component σ α i.snd))))

/-- The ring topology on MvPowerSeries of a topological ring -/
@[scoped instance] theorem topologicalRing [Ring α] [TopologicalRing α] :
    TopologicalRing (MvPowerSeries σ α) :=
  { topologicalSemiring σ α with
    continuous_neg := continuous_pi fun d ↦ Continuous.comp continuous_neg
      (continuous_component σ α d) }

/-- MvPowerSeries on a T2Space form a T2Space -/
@[scoped instance] theorem t2Space [T2Space α] : T2Space (MvPowerSeries σ α) where
  t2 x y h := by
    obtain ⟨d, h⟩ := Function.ne_iff.mp h
    obtain ⟨u, v, ⟨hu, hv, hx, hy, huv⟩⟩ := t2_separation h
    exact ⟨(fun x => x d) ⁻¹' u, (fun x => x d) ⁻¹' v,
      IsOpen.preimage (continuous_component σ α d) hu,
      IsOpen.preimage (continuous_component σ α d) hv, hx, hy,
      Disjoint.preimage _ huv⟩

end WithPiTopology

end Topological

section Uniform

namespace WithPiUniformity

open WithPiTopology

variable [UniformSpace α]

/-- The componentwise uniformity on MvPowerSeries -/
scoped instance uniformSpace : UniformSpace (MvPowerSeries σ α) :=
  Pi.uniformSpace fun _ : σ →₀ ℕ => α

/-- Components are uniformly continuous -/
theorem uniformContinuous_component :
    ∀ d : σ →₀ ℕ, UniformContinuous fun a : MvPowerSeries σ α => a d :=
  uniformContinuous_pi.mp uniformContinuous_id

/-- The uniform_add_group structure on MvPowerSeries of a uniform_add_group -/
@[scoped instance] theorem uniformAddGroup [AddGroup α] [UniformAddGroup α] :
    UniformAddGroup (MvPowerSeries σ α) where
  uniformContinuous_sub := uniformContinuous_pi.mpr fun _ => UniformContinuous.comp
    uniformContinuous_sub
    (UniformContinuous.prod_mk
      (UniformContinuous.comp (uniformContinuous_component _ _ _) uniformContinuous_fst)
      (UniformContinuous.comp (uniformContinuous_component _ _ _) uniformContinuous_snd))

/-- Completeness of the uniform structure on MvPowerSeries -/
@[scoped instance] theorem completeSpace [AddGroup α] [CompleteSpace α] :
    CompleteSpace (MvPowerSeries σ α) where
  complete := by
    intro f hf
    suffices ∀ d, ∃ x, (f.map fun a => a d) ≤ nhds x by
      use fun d => (this d).choose
      rw [nhds_pi, Filter.le_pi]
      exact fun d => (this d).choose_spec
    intro d
    use lim (f.map fun a => a d)
    exact (Cauchy.map hf (uniformContinuous_component σ α d)).le_nhds_lim

/-- Separation of the uniform structure on MvPowerSeries -/
@[scoped instance] theorem t0Space [T0Space α] : T0Space (MvPowerSeries σ α) := by
  suffices T2Space (MvPowerSeries σ α) by infer_instance
  exact WithPiTopology.t2Space σ α

/-- The ring of multivariate power series is a uniform topological ring -/
@[scoped instance] theorem uniform_topologicalRing [Ring α] [UniformAddGroup α] [TopologicalRing α] :
    TopologicalRing (MvPowerSeries σ α) :=
  { uniformAddGroup σ α with
    continuous_add :=  (@uniformContinuous_add _ _ _ (uniformAddGroup σ α)).continuous
    continuous_mul := continuous_pi fun _ => continuous_finset_sum _ fun i _ => Continuous.comp
      continuous_mul (Continuous.prod_mk (Continuous.fst' (continuous_component σ α i.fst))
        (Continuous.snd' (continuous_component σ α i.snd)))
    continuous_neg := (@uniformContinuous_neg _ _ _ (uniformAddGroup σ α)).continuous
    }

end WithPiUniformity

end Uniform

section

variable {σ α} [DecidableEq σ]

variable [TopologicalSpace α] [CommRing α] [TopologicalRing α]

open WithPiTopology WithPiUniformity

theorem continuous_C :
    Continuous (C σ α) := by
  apply continuous_of_continuousAt_zero
  rw [continuousAt_pi]
  intro d
  change ContinuousAt (fun y => coeff α d ((C σ α) y)) 0
  by_cases hd : d = 0
  · convert continuousAt_id
    rw [hd, coeff_zero_C, id_eq]
  · convert continuousAt_const
    rw [coeff_C, if_neg hd]

theorem variables_tendsto_zero :
    Filter.Tendsto (fun s : σ => (X s : MvPowerSeries σ α)) Filter.cofinite (nhds 0) := by
  classical
  rw [tendsto_pi_nhds]
  intro d s hs
  rw [Filter.mem_map, Filter.mem_cofinite, ← Set.preimage_compl]
  by_cases h : ∃ i, d = Finsupp.single i 1
  · obtain ⟨i, rfl⟩ := h
    apply Set.Finite.subset (Set.finite_singleton i)
    intro x
    simp only [OfNat.ofNat, Zero.zero] at hs
    rw [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, not_imp_comm]
    intro hx
    convert mem_of_mem_nhds hs
    rw [← coeff_eq_apply (X x) (Finsupp.single i 1), coeff_X, if_neg]
    rfl
    · simp only [Finsupp.single_eq_single_iff, Ne.symm hx, and_true, one_ne_zero, and_self,
      or_self, not_false_eq_true]
  · convert Set.finite_empty
    rw [Set.eq_empty_iff_forall_not_mem]
    intro x
    rw [Set.mem_preimage, Set.not_mem_compl_iff]
    convert mem_of_mem_nhds hs using 1
    rw [← coeff_eq_apply (X x) d, coeff_X, if_neg]
    rfl
    · intro h'
      apply h
      exact ⟨x, h'⟩

theorem tendsto_pow_zero_of_constantCoeff_nilpotent {f} (hf : IsNilpotent (constantCoeff σ α f)) :
    Filter.Tendsto (fun n : ℕ => f ^ n) Filter.atTop (nhds 0) := by
  classical
  obtain ⟨m, hm⟩ := hf
  simp_rw [tendsto_iff_coeff_tendsto, coeff_zero]
  exact fun d =>  tendsto_atTop_of_eventually_const fun n hn =>
    coeff_eq_zero_of_constantCoeff_nilpotent f m hm d n hn

theorem tendsto_pow_zero_of_constantCoeff_zero {f} (hf : constantCoeff σ α f = 0) :
    Filter.Tendsto (fun n : ℕ => f ^ n) Filter.atTop (nhds 0) := by
  apply tendsto_pow_zero_of_constantCoeff_nilpotent
  rw [hf]
  exact IsNilpotent.zero

/-- [bourbaki1981], chap. 4, §4, n°2, corollaire de la prop. 3 -/
theorem tendsto_pow_of_constantCoeff_nilpotent_iff [DiscreteTopology α] (f) :
    Filter.Tendsto (fun n : ℕ => f ^ n) Filter.atTop (nhds 0) ↔
      IsNilpotent (constantCoeff σ α f) := by
  refine' ⟨_, tendsto_pow_zero_of_constantCoeff_nilpotent ⟩
  · intro h
    suffices Filter.Tendsto (fun n : ℕ => constantCoeff σ α (f ^ n)) Filter.atTop (nhds 0) by
      simp only [Filter.tendsto_def] at this
      specialize this {0} _
      suffices  ∀ x : α, {x} ∈ nhds x by exact this 0
      rw [← discreteTopology_iff_singleton_mem_nhds]; infer_instance
      simp only [map_pow, Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage,
        Set.mem_singleton_iff] at this
      obtain ⟨m, hm⟩ := this
      use m
      apply hm m (le_refl m)
    simp only [← @comp_apply _ α ℕ]
    rw [← Filter.tendsto_map'_iff]
    simp only [Filter.Tendsto, Filter.map_le_iff_le_comap] at h ⊢
    apply le_trans h
    apply Filter.comap_mono
    rw [← Filter.map_le_iff_le_comap]
    apply continuous_constantCoeff.continuousAt

end

section Summable

variable [Semiring α] [TopologicalSpace α]

open WithPiTopology

variable {σ α}

/-- A power series is the sum (in the sense of summable families) of its monomials -/
theorem hasSum_of_monomials_self (f : MvPowerSeries σ α) :
    HasSum (fun d : σ →₀ ℕ => monomial α d (coeff α d f)) f := by
  rw [Pi.hasSum]
  intro d
  convert hasSum_single d ?_ using 1
  exact (coeff_monomial_same d _).symm
  exact fun d' h ↦ coeff_monomial_ne (Ne.symm h) _

/-- If the coefficient space is T2, then the power series is `tsum` of its monomials -/
theorem as_tsum [T2Space α] (f : MvPowerSeries σ α) :
    f = tsum fun d : σ →₀ ℕ => monomial α d (coeff α d f) :=
  (HasSum.tsum_eq (hasSum_of_monomials_self _)).symm

end Summable

end MvPowerSeries
