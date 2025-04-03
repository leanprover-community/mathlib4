/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.NormedSpace.lpSpace
import Mathlib.Analysis.NormedSpace.PiLp
import Mathlib.Topology.ContinuousFunction.Bounded

#align_import analysis.normed_space.lp_equiv from "leanprover-community/mathlib"@"6afc9b06856ad973f6a2619e3e8a0a8d537a58f2"

/-!
# Equivalences among $L^p$ spaces

In this file we collect a variety of equivalences among various $L^p$ spaces.  In particular,
when `α` is a `Fintype`, given `E : α → Type u` and `p : ℝ≥0∞`, there is a natural linear isometric
equivalence `lpPiLpₗᵢₓ : lp E p ≃ₗᵢ PiLp p E`. In addition, when `α` is a discrete topological
space, the bounded continuous functions `α →ᵇ β` correspond exactly to `lp (fun _ ↦ β) ∞`.
Here there can be more structure, including ring and algebra structures,
and we implement these equivalences accordingly as well.

We keep this as a separate file so that the various $L^p$ space files don't import the others.

Recall that `PiLp` is just a type synonym for `Π i, E i` but given a different metric and norm
structure, although the topological, uniform and bornological structures coincide definitionally.
These structures are only defined on `PiLp` for `Fintype α`, so there are no issues of convergence
to consider.

While `PreLp` is also a type synonym for `Π i, E i`, it allows for infinite index types. On this
type there is a predicate `Memℓp` which says that the relevant `p`-norm is finite and `lp E p` is
the subtype of `PreLp` satisfying `Memℓp`.

## TODO

* Equivalence between `lp` and `MeasureTheory.Lp`, for `f : α → E` (i.e., functions rather than
  pi-types) and the counting measure on `α`

-/


open scoped ENNReal

section LpPiLp

set_option linter.uppercaseLean3 false

variable {α : Type*} {E : α → Type*} [∀ i, NormedAddCommGroup (E i)] {p : ℝ≥0∞}

section Finite

variable [Finite α]

/-- When `α` is `Finite`, every `f : PreLp E p` satisfies `Memℓp f p`. -/
theorem Memℓp.all (f : ∀ i, E i) : Memℓp f p := by
  rcases p.trichotomy with (rfl | rfl | _h)
  · exact memℓp_zero_iff.mpr { i : α | f i ≠ 0 }.toFinite
  · exact memℓp_infty_iff.mpr (Set.Finite.bddAbove (Set.range fun i : α ↦ ‖f i‖).toFinite)
  · cases nonempty_fintype α; exact memℓp_gen ⟨Finset.univ.sum _, hasSum_fintype _⟩
#align mem_ℓp.all Memℓp.all

/-- The canonical `Equiv` between `lp E p ≃ PiLp p E` when `E : α → Type u` with `[Finite α]`. -/
def Equiv.lpPiLp : lp E p ≃ PiLp p E where
  toFun f := ⇑f
  invFun f := ⟨f, Memℓp.all f⟩
  left_inv _f := rfl
  right_inv _f := rfl
#align equiv.lp_pi_Lp Equiv.lpPiLp

theorem coe_equiv_lpPiLp (f : lp E p) : Equiv.lpPiLp f = ⇑f :=
  rfl
#align coe_equiv_lp_pi_Lp coe_equiv_lpPiLp

theorem coe_equiv_lpPiLp_symm (f : PiLp p E) : (Equiv.lpPiLp.symm f : ∀ i, E i) = f :=
  rfl
#align coe_equiv_lp_pi_Lp_symm coe_equiv_lpPiLp_symm

/-- The canonical `AddEquiv` between `lp E p` and `PiLp p E` when `E : α → Type u` with
`[Fintype α]`. -/
def AddEquiv.lpPiLp : lp E p ≃+ PiLp p E :=
  { Equiv.lpPiLp with map_add' := fun _f _g ↦ rfl }
#align add_equiv.lp_pi_Lp AddEquiv.lpPiLp

theorem coe_addEquiv_lpPiLp  (f : lp E p) : AddEquiv.lpPiLp f = ⇑f :=
  rfl
#align coe_add_equiv_lp_pi_Lp coe_addEquiv_lpPiLp

theorem coe_addEquiv_lpPiLp_symm (f : PiLp p E) :
    (AddEquiv.lpPiLp.symm f : ∀ i, E i) = f :=
  rfl
#align coe_add_equiv_lp_pi_Lp_symm coe_addEquiv_lpPiLp_symm

end Finite

theorem equiv_lpPiLp_norm [Fintype α] (f : lp E p) : ‖Equiv.lpPiLp f‖ = ‖f‖ := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp [Equiv.lpPiLp, PiLp.norm_eq_card, lp.norm_eq_card_dsupport]
  · rw [PiLp.norm_eq_ciSup, lp.norm_eq_ciSup]; rfl
  · rw [PiLp.norm_eq_sum h, lp.norm_eq_tsum_rpow h, tsum_fintype]; rfl
#align equiv_lp_pi_Lp_norm equiv_lpPiLp_norm

section Equivₗᵢ

variable [Fintype α] (𝕜 : Type*) [NontriviallyNormedField 𝕜] [∀ i, NormedSpace 𝕜 (E i)]
variable (E)
/- porting note: Lean is unable to work with `lpPiLpₗᵢ` if `E` is implicit without
annotating with `(E := E)` everywhere, so we just make it explicit. This file has no
dependencies. -/

/-- The canonical `LinearIsometryEquiv` between `lp E p` and `PiLp p E` when `E : α → Type u`
with `[Fintype α]` and `[Fact (1 ≤ p)]`. -/
noncomputable def lpPiLpₗᵢ [Fact (1 ≤ p)] : lp E p ≃ₗᵢ[𝕜] PiLp p E :=
  { AddEquiv.lpPiLp with
    map_smul' := fun _k _f ↦ rfl
    norm_map' := equiv_lpPiLp_norm }
#align lp_pi_Lpₗᵢ lpPiLpₗᵢₓ
-- Porting note: `#align`ed with an `ₓ` because `E` is now explicit, see above

variable {𝕜 E}

theorem coe_lpPiLpₗᵢ [Fact (1 ≤ p)] (f : lp E p) : (lpPiLpₗᵢ E 𝕜 f : ∀ i, E i) = ⇑f :=
  rfl
#align coe_lp_pi_Lpₗᵢ coe_lpPiLpₗᵢ

theorem coe_lpPiLpₗᵢ_symm [Fact (1 ≤ p)] (f : PiLp p E) :
    ((lpPiLpₗᵢ E 𝕜).symm f : ∀ i, E i) = f :=
  rfl
#align coe_lp_pi_Lpₗᵢ_symm coe_lpPiLpₗᵢ_symm

end Equivₗᵢ

end LpPiLp

section LpBCF

open scoped BoundedContinuousFunction

open BoundedContinuousFunction

-- note: `R` and `A` are explicit because otherwise Lean has elaboration problems
variable {α E : Type*} (R A 𝕜 : Type*) [TopologicalSpace α] [DiscreteTopology α]
variable [NormedRing A] [NormOneClass A] [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 A]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NonUnitalNormedRing R]

section NormedAddCommGroup

/-- The canonical map between `lp (fun _ : α ↦ E) ∞` and `α →ᵇ E` as an `AddEquiv`. -/
noncomputable def AddEquiv.lpBCF : lp (fun _ : α ↦ E) ∞ ≃+ (α →ᵇ E) where
  toFun f := ofNormedAddCommGroupDiscrete f ‖f‖ <| le_ciSup (memℓp_infty_iff.mp f.prop)
  invFun f := ⟨⇑f, f.bddAbove_range_norm_comp⟩
  left_inv _f := lp.ext rfl
  right_inv _f := rfl
  map_add' _f _g := rfl
#align add_equiv.lp_bcf AddEquiv.lpBCF

@[deprecated (since := "2024-03-16")] alias AddEquiv.lpBcf := AddEquiv.lpBCF

theorem coe_addEquiv_lpBCF (f : lp (fun _ : α ↦ E) ∞) : (AddEquiv.lpBCF f : α → E) = f :=
  rfl
#align coe_add_equiv_lp_bcf coe_addEquiv_lpBCF

theorem coe_addEquiv_lpBCF_symm (f : α →ᵇ E) : (AddEquiv.lpBCF.symm f : α → E) = f :=
  rfl
#align coe_add_equiv_lp_bcf_symm coe_addEquiv_lpBCF_symm

variable (E)
/- porting note: Lean is unable to work with `lpPiLpₗᵢ` if `E` is implicit without
annotating with `(E := E)` everywhere, so we just make it explicit. This file has no
dependencies. -/

/-- The canonical map between `lp (fun _ : α ↦ E) ∞` and `α →ᵇ E` as a `LinearIsometryEquiv`. -/
noncomputable def lpBCFₗᵢ : lp (fun _ : α ↦ E) ∞ ≃ₗᵢ[𝕜] α →ᵇ E :=
  { AddEquiv.lpBCF with
    map_smul' := fun k f ↦ rfl
    norm_map' := fun f ↦ by simp only [norm_eq_iSup_norm, lp.norm_eq_ciSup]; rfl }
#align lp_bcfₗᵢ lpBCFₗᵢₓ
-- Porting note: `#align`ed with an `ₓ` because `E` is now explicit, see above

@[deprecated (since := "2024-03-16")] alias lpBcfₗᵢ := lpBCFₗᵢ

variable {𝕜 E}

theorem coe_lpBCFₗᵢ (f : lp (fun _ : α ↦ E) ∞) : (lpBCFₗᵢ E 𝕜 f : α → E) = f :=
  rfl
#align coe_lp_bcfₗᵢ coe_lpBCFₗᵢ

theorem coe_lpBCFₗᵢ_symm (f : α →ᵇ E) : ((lpBCFₗᵢ E 𝕜).symm f : α → E) = f :=
  rfl
#align coe_lp_bcfₗᵢ_symm coe_lpBCFₗᵢ_symm

end NormedAddCommGroup

section RingAlgebra

/-- The canonical map between `lp (fun _ : α ↦ R) ∞` and `α →ᵇ R` as a `RingEquiv`. -/
noncomputable def RingEquiv.lpBCF : lp (fun _ : α ↦ R) ∞ ≃+* (α →ᵇ R) :=
  { @AddEquiv.lpBCF _ R _ _ _ with
    map_mul' := fun _f _g => rfl }
#align ring_equiv.lp_bcf RingEquiv.lpBCF

@[deprecated (since := "2024-03-16")] alias RingEquiv.lpBcf := RingEquiv.lpBCF

variable {R}

theorem coe_ringEquiv_lpBCF (f : lp (fun _ : α ↦ R) ∞) : (RingEquiv.lpBCF R f : α → R) = f :=
  rfl
#align coe_ring_equiv_lp_bcf coe_ringEquiv_lpBCF

theorem coe_ringEquiv_lpBCF_symm (f : α →ᵇ R) : ((RingEquiv.lpBCF R).symm f : α → R) = f :=
  rfl
#align coe_ring_equiv_lp_bcf_symm coe_ringEquiv_lpBCF_symm

variable (α)

-- even `α` needs to be explicit here for elaboration
-- the `NormOneClass A` shouldn't really be necessary, but currently it is for
-- `one_memℓp_infty` to get the `Ring` instance on `lp`.
/-- The canonical map between `lp (fun _ : α ↦ A) ∞` and `α →ᵇ A` as an `AlgEquiv`. -/
noncomputable def AlgEquiv.lpBCF : lp (fun _ : α ↦ A) ∞ ≃ₐ[𝕜] α →ᵇ A :=
  { RingEquiv.lpBCF A with commutes' := fun _k ↦ rfl }
#align alg_equiv.lp_bcf AlgEquiv.lpBCF

@[deprecated (since := "2024-03-16")] alias AlgEquiv.lpBcf := AlgEquiv.lpBCF

variable {α A 𝕜}

theorem coe_algEquiv_lpBCF (f : lp (fun _ : α ↦ A) ∞) : (AlgEquiv.lpBCF α A 𝕜 f : α → A) = f :=
  rfl
#align coe_alg_equiv_lp_bcf coe_algEquiv_lpBCF

theorem coe_algEquiv_lpBCF_symm (f : α →ᵇ A) : ((AlgEquiv.lpBCF α A 𝕜).symm f : α → A) = f :=
  rfl
#align coe_alg_equiv_lp_bcf_symm coe_algEquiv_lpBCF_symm

end RingAlgebra

end LpBCF
