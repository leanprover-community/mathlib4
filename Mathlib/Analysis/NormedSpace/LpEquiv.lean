/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux

! This file was ported from Lean 3 source module analysis.normed_space.lp_equiv
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.LpSpace
import Mathbin.Analysis.NormedSpace.PiLp
import Mathbin.Topology.ContinuousFunction.Bounded

/-!
# Equivalences among $L^p$ spaces

In this file we collect a variety of equivalences among various $L^p$ spaces.  In particular,
when `α` is a `fintype`, given `E : α → Type u` and `p : ℝ≥0∞`, there is a natural linear isometric
equivalence `lp_pi_Lpₗᵢ : lp E p ≃ₗᵢ pi_Lp p E`. In addition, when `α` is a discrete topological
space, the bounded continuous functions `α →ᵇ β` correspond exactly to `lp (λ _, β) ∞`. Here there
can be more structure, including ring and algebra structures, and we implement these equivalences
accordingly as well.

We keep this as a separate file so that the various $L^p$ space files don't import the others.

Recall that `pi_Lp` is just a type synonym for `Π i, E i` but given a different metric and norm
structure, although the topological, uniform and bornological structures coincide definitionally.
These structures are only defined on `pi_Lp` for `fintype α`, so there are no issues of convergence
to consider.

While `pre_lp` is also a type synonym for `Π i, E i`, it allows for infinite index types. On this
type there is a predicate `mem_ℓp` which says that the relevant `p`-norm is finite and `lp E p` is
the subtype of `pre_lp` satisfying `mem_ℓp`.

## TODO

* Equivalence between `lp` and `measure_theory.Lp`, for `f : α → E` (i.e., functions rather than
  pi-types) and the counting measure on `α`

-/


open scoped ENNReal

section LpPiLp

variable {α : Type _} {E : α → Type _} [∀ i, NormedAddCommGroup (E i)] {p : ℝ≥0∞}

/-- When `α` is `finite`, every `f : pre_lp E p` satisfies `mem_ℓp f p`. -/
theorem Memℓp.all [Finite α] (f : ∀ i, E i) : Memℓp f p :=
  by
  rcases p.trichotomy with (rfl | rfl | h)
  · exact mem_ℓp_zero_iff.mpr { i : α | f i ≠ 0 }.toFinite
  · exact mem_ℓp_infty_iff.mpr (Set.Finite.bddAbove (Set.range fun i : α => ‖f i‖).toFinite)
  · cases nonempty_fintype α; exact memℓp_gen ⟨finset.univ.sum _, hasSum_fintype _⟩
#align mem_ℓp.all Memℓp.all

variable [Fintype α]

/-- The canonical `equiv` between `lp E p ≃ pi_Lp p E` when `E : α → Type u` with `[fintype α]`. -/
def Equiv.lpPiLp : lp E p ≃ PiLp p E where
  toFun f := f
  invFun f := ⟨f, Memℓp.all f⟩
  left_inv f := lp.ext <| funext fun x => rfl
  right_inv f := funext fun x => rfl
#align equiv.lp_pi_Lp Equiv.lpPiLp

theorem coe_equiv_lpPiLp (f : lp E p) : Equiv.lpPiLp f = f :=
  rfl
#align coe_equiv_lp_pi_Lp coe_equiv_lpPiLp

theorem coe_equiv_lpPiLp_symm (f : PiLp p E) : (Equiv.lpPiLp.symm f : ∀ i, E i) = f :=
  rfl
#align coe_equiv_lp_pi_Lp_symm coe_equiv_lpPiLp_symm

theorem equiv_lpPiLp_norm (f : lp E p) : ‖Equiv.lpPiLp f‖ = ‖f‖ :=
  by
  rcases p.trichotomy with (rfl | rfl | h)
  · rw [PiLp.norm_eq_card, lp.norm_eq_card_dsupport]; rfl
  · rw [PiLp.norm_eq_ciSup, lp.norm_eq_ciSup]; rfl
  · rw [PiLp.norm_eq_sum h, lp.norm_eq_tsum_rpow h, tsum_fintype]; rfl
#align equiv_lp_pi_Lp_norm equiv_lpPiLp_norm

/-- The canonical `add_equiv` between `lp E p` and `pi_Lp p E` when `E : α → Type u` with
`[fintype α]` and `[fact (1 ≤ p)]`. -/
def AddEquiv.lpPiLp [Fact (1 ≤ p)] : lp E p ≃+ PiLp p E :=
  { Equiv.lpPiLp with map_add' := fun f g => rfl }
#align add_equiv.lp_pi_Lp AddEquiv.lpPiLp

theorem coe_addEquiv_lpPiLp [Fact (1 ≤ p)] (f : lp E p) : AddEquiv.lpPiLp f = f :=
  rfl
#align coe_add_equiv_lp_pi_Lp coe_addEquiv_lpPiLp

theorem coe_addEquiv_lpPiLp_symm [Fact (1 ≤ p)] (f : PiLp p E) :
    (AddEquiv.lpPiLp.symm f : ∀ i, E i) = f :=
  rfl
#align coe_add_equiv_lp_pi_Lp_symm coe_addEquiv_lpPiLp_symm

section Equivₗᵢ

variable (𝕜 : Type _) [NontriviallyNormedField 𝕜] [∀ i, NormedSpace 𝕜 (E i)]

/-- The canonical `linear_isometry_equiv` between `lp E p` and `pi_Lp p E` when `E : α → Type u`
with `[fintype α]` and `[fact (1 ≤ p)]`. -/
noncomputable def lpPiLpₗᵢ [Fact (1 ≤ p)] : lp E p ≃ₗᵢ[𝕜] PiLp p E :=
  { AddEquiv.lpPiLp with
    map_smul' := fun k f => rfl
    norm_map' := equiv_lpPiLp_norm }
#align lp_pi_Lpₗᵢ lpPiLpₗᵢ

variable {𝕜}

theorem coe_lpPiLpₗᵢ [Fact (1 ≤ p)] (f : lp E p) : lpPiLpₗᵢ 𝕜 f = f :=
  rfl
#align coe_lp_pi_Lpₗᵢ coe_lpPiLpₗᵢ

theorem coe_lpPiLpₗᵢ_symm [Fact (1 ≤ p)] (f : PiLp p E) : ((lpPiLpₗᵢ 𝕜).symm f : ∀ i, E i) = f :=
  rfl
#align coe_lp_pi_Lpₗᵢ_symm coe_lpPiLpₗᵢ_symm

end Equivₗᵢ

end LpPiLp

section LpBcf

open scoped BoundedContinuousFunction

open BoundedContinuousFunction

-- note: `R` and `A` are explicit because otherwise Lean has elaboration problems
variable {α E : Type _} (R A 𝕜 : Type _) [TopologicalSpace α] [DiscreteTopology α]

variable [NormedRing A] [NormOneClass A] [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 A]

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NonUnitalNormedRing R]

section NormedAddCommGroup

/-- The canonical map between `lp (λ (_ : α), E) ∞` and `α →ᵇ E` as an `add_equiv`. -/
noncomputable def AddEquiv.lpBcf : lp (fun _ : α => E) ∞ ≃+ (α →ᵇ E)
    where
  toFun f := ofNormedAddCommGroupDiscrete f ‖f‖ <| le_ciSup (memℓp_infty_iff.mp f.Prop)
  invFun f := ⟨f, f.bddAbove_range_norm_comp⟩
  left_inv f := lp.ext rfl
  right_inv f := ext fun x => rfl
  map_add' f g := ext fun x => rfl
#align add_equiv.lp_bcf AddEquiv.lpBcf

theorem coe_addEquiv_lpBcf (f : lp (fun _ : α => E) ∞) : (AddEquiv.lpBcf f : α → E) = f :=
  rfl
#align coe_add_equiv_lp_bcf coe_addEquiv_lpBcf

theorem coe_addEquiv_lpBcf_symm (f : α →ᵇ E) : (AddEquiv.lpBcf.symm f : α → E) = f :=
  rfl
#align coe_add_equiv_lp_bcf_symm coe_addEquiv_lpBcf_symm

/-- The canonical map between `lp (λ (_ : α), E) ∞` and `α →ᵇ E` as a `linear_isometry_equiv`. -/
noncomputable def lpBcfₗᵢ : lp (fun _ : α => E) ∞ ≃ₗᵢ[𝕜] α →ᵇ E :=
  { AddEquiv.lpBcf with
    map_smul' := fun k f => rfl
    norm_map' := fun f => by simp only [norm_eq_supr_norm, lp.norm_eq_ciSup]; rfl }
#align lp_bcfₗᵢ lpBcfₗᵢ

variable {𝕜}

theorem coe_lpBcfₗᵢ (f : lp (fun _ : α => E) ∞) : (lpBcfₗᵢ 𝕜 f : α → E) = f :=
  rfl
#align coe_lp_bcfₗᵢ coe_lpBcfₗᵢ

theorem coe_lpBcfₗᵢ_symm (f : α →ᵇ E) : ((lpBcfₗᵢ 𝕜).symm f : α → E) = f :=
  rfl
#align coe_lp_bcfₗᵢ_symm coe_lpBcfₗᵢ_symm

end NormedAddCommGroup

section RingAlgebra

/-- The canonical map between `lp (λ (_ : α), R) ∞` and `α →ᵇ R` as a `ring_equiv`. -/
noncomputable def RingEquiv.lpBcf : lp (fun _ : α => R) ∞ ≃+* (α →ᵇ R) :=
  { @AddEquiv.lpBcf _ R _ _ _ with map_mul' := fun f g => ext fun x => rfl }
#align ring_equiv.lp_bcf RingEquiv.lpBcf

variable {R}

theorem coe_ringEquiv_lpBcf (f : lp (fun _ : α => R) ∞) : (RingEquiv.lpBcf R f : α → R) = f :=
  rfl
#align coe_ring_equiv_lp_bcf coe_ringEquiv_lpBcf

theorem coe_ringEquiv_lpBcf_symm (f : α →ᵇ R) : ((RingEquiv.lpBcf R).symm f : α → R) = f :=
  rfl
#align coe_ring_equiv_lp_bcf_symm coe_ringEquiv_lpBcf_symm

variable (α)

-- even `α` needs to be explicit here for elaboration
-- the `norm_one_class A` shouldn't really be necessary, but currently it is for
-- `one_mem_ℓp_infty` to get the `ring` instance on `lp`.
/-- The canonical map between `lp (λ (_ : α), A) ∞` and `α →ᵇ A` as an `alg_equiv`. -/
noncomputable def AlgEquiv.lpBcf : lp (fun _ : α => A) ∞ ≃ₐ[𝕜] α →ᵇ A :=
  { RingEquiv.lpBcf A with commutes' := fun k => rfl }
#align alg_equiv.lp_bcf AlgEquiv.lpBcf

variable {α A 𝕜}

theorem coe_algEquiv_lpBcf (f : lp (fun _ : α => A) ∞) : (AlgEquiv.lpBcf α A 𝕜 f : α → A) = f :=
  rfl
#align coe_alg_equiv_lp_bcf coe_algEquiv_lpBcf

theorem coe_algEquiv_lpBcf_symm (f : α →ᵇ A) : ((AlgEquiv.lpBcf α A 𝕜).symm f : α → A) = f :=
  rfl
#align coe_alg_equiv_lp_bcf_symm coe_algEquiv_lpBcf_symm

end RingAlgebra

end LpBcf

