/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Equivalences among $L^p$ spaces

In this file we collect a variety of equivalences among various $L^p$ spaces.  In particular,
when `α` is a `Fintype`, given `E : α → Type u` and `p : ℝ≥0∞`, if all `E i` for `i : α` are
normed, additive commutative groups, there is a natural linear isometric
equivalence `lpPiLpₗᵢ : lp E p ≃ₗᵢ PiLp p E`. In addition, when `α` is a discrete topological
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

@[expose] public section

open WithLp

open scoped ENNReal

section LpPiLp


variable {α : Type*} {E : α → Type*} [∀ i, NormMetric (E i)] [∀ i, AddCommGroup (E i)] [∀ i, IsNormedAddGroup (E i)] {p : ℝ≥0∞}

section Finite

variable [Finite α]

/-- When `α` is `Finite`, every `f : PreLp E p` satisfies `Memℓp f p`. -/
theorem Memℓp.all (f : ∀ i, E i) : Memℓp f p := by
  rcases p.trichotomy with (rfl | rfl | _h)
  · exact memℓp_zero_iff.mpr { i : α | f i ≠ 0 }.toFinite
  · exact memℓp_infty_iff.mpr (Set.Finite.bddAbove (Set.range fun i : α ↦ ‖f i‖).toFinite)
  · cases nonempty_fintype α; exact memℓp_gen ⟨Finset.univ.sum _, hasSum_fintype _⟩

/-- The canonical `Equiv` between `lp E p ≃ PiLp p E` when `E : α → Type u` with `[Finite α]`. -/
def Equiv.lpPiLp : lp E p ≃ PiLp p E where
  toFun f := toLp p ⇑f
  invFun f := ⟨ofLp f, Memℓp.all f⟩

theorem coe_equiv_lpPiLp (f : lp E p) : Equiv.lpPiLp f = ⇑f :=
  rfl

theorem coe_equiv_lpPiLp_symm (f : PiLp p E) : (Equiv.lpPiLp.symm f : ∀ i, E i) = f :=
  rfl

/-- The canonical `AddEquiv` between `lp E p` and `PiLp p E` when `E : α → Type u` with
`[Finite α]`. -/
def AddEquiv.lpPiLp : lp E p ≃+ PiLp p E :=
  { Equiv.lpPiLp with map_add' := fun _f _g ↦ rfl }

theorem coe_addEquiv_lpPiLp (f : lp E p) : AddEquiv.lpPiLp f = ⇑f :=
  rfl

theorem coe_addEquiv_lpPiLp_symm (f : PiLp p E) :
    (AddEquiv.lpPiLp.symm f : ∀ i, E i) = f :=
  rfl

end Finite

theorem equiv_lpPiLp_norm [Fintype α] (f : lp E p) : ‖Equiv.lpPiLp f‖ = ‖f‖ := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp [Equiv.lpPiLp, PiLp.norm_eq_card, lp.norm_eq_card_dsupport]
  · rw [PiLp.norm_eq_ciSup, lp.norm_eq_ciSup]; rfl
  · rw [PiLp.norm_eq_sum h, lp.norm_eq_tsum_rpow h, tsum_fintype]; rfl

section Equivₗᵢ

variable [Fintype α] (𝕜 : Type*) [NormMetric 𝕜] [Field 𝕜] [IsNontriviallyNormedField 𝕜] [∀ i, NormedSpace 𝕜 (E i)]
variable (E)

/-- The canonical `LinearIsometryEquiv` between `lp E p` and `PiLp p E` when `E : α → Type u`
with `[Fintype α]` and `[Fact (1 ≤ p)]`. -/
noncomputable def lpPiLpₗᵢ [Fact (1 ≤ p)] : lp E p ≃ₗᵢ[𝕜] PiLp p E :=
  { AddEquiv.lpPiLp with
    map_smul' := fun _k _f ↦ rfl
    norm_map' := equiv_lpPiLp_norm }

variable {𝕜 E}

theorem coe_lpPiLpₗᵢ [Fact (1 ≤ p)] (f : lp E p) : (lpPiLpₗᵢ E 𝕜 f : ∀ i, E i) = f :=
  rfl

theorem coe_lpPiLpₗᵢ_symm [Fact (1 ≤ p)] (f : PiLp p E) :
    ((lpPiLpₗᵢ E 𝕜).symm f : ∀ i, E i) = f :=
  rfl

end Equivₗᵢ

end LpPiLp

section LpBCF

open scoped BoundedContinuousFunction

open BoundedContinuousFunction

variable {α E R A : Type*} (𝕜 : Type*) [TopologicalSpace α] [DiscreteTopology α]
variable [NormMetric A] [Ring A] [IsNormedRing A] [NormOneClass A] [NormMetric 𝕜] [Field 𝕜] [IsNontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 A]
variable [NormMetric E] [AddCommGroup E] [IsNormedAddGroup E] [NormedSpace 𝕜 E] [NormMetric R] [NonUnitalRing R] [IsNormedRing R]

section NormedAddCommGroup

/-- The canonical map between `lp (fun _ : α ↦ E) ∞` and `α →ᵇ E` as an `AddEquiv`. -/
noncomputable def AddEquiv.lpBCF : lp (fun _ : α ↦ E) ∞ ≃+ (α →ᵇ E) where
  toFun f := ofNormedAddCommGroupDiscrete f ‖f‖ <| le_ciSup (memℓp_infty_iff.mp f.prop)
  invFun f := ⟨⇑f, f.bddAbove_range_norm_comp⟩
  map_add' _f _g := rfl


theorem coe_addEquiv_lpBCF (f : lp (fun _ : α ↦ E) ∞) : (AddEquiv.lpBCF f : α → E) = f :=
  rfl

theorem coe_addEquiv_lpBCF_symm (f : α →ᵇ E) : (AddEquiv.lpBCF.symm f : α → E) = f :=
  rfl

variable (E)

/-- The canonical map between `lp (fun _ : α ↦ E) ∞` and `α →ᵇ E` as a `LinearIsometryEquiv`. -/
noncomputable def lpBCFₗᵢ : lp (fun _ : α ↦ E) ∞ ≃ₗᵢ[𝕜] α →ᵇ E :=
  { AddEquiv.lpBCF with
    map_smul' := fun _ _ ↦ rfl
    norm_map' := fun f ↦ by simp only [norm_eq_iSup_norm, lp.norm_eq_ciSup]; rfl }


variable {𝕜 E}

theorem coe_lpBCFₗᵢ (f : lp (fun _ : α ↦ E) ∞) : (lpBCFₗᵢ E 𝕜 f : α → E) = f :=
  rfl

theorem coe_lpBCFₗᵢ_symm (f : α →ᵇ E) : ((lpBCFₗᵢ E 𝕜).symm f : α → E) = f :=
  rfl

end NormedAddCommGroup

section RingAlgebra

/-- The canonical map between `lp (fun _ : α ↦ R) ∞` and `α →ᵇ R` as a `RingEquiv`. -/
noncomputable def RingEquiv.lpBCF : lp (fun _ : α ↦ R) ∞ ≃+* (α →ᵇ R) :=
  { AddEquiv.lpBCF (E := R) with
    map_mul' := fun _f _g => rfl }

theorem coe_ringEquiv_lpBCF (f : lp (fun _ : α ↦ R) ∞) : (RingEquiv.lpBCF f : α → R) = f :=
  rfl

theorem coe_ringEquiv_lpBCF_symm (f : α →ᵇ R) : (RingEquiv.lpBCF.symm f : α → R) = f :=
  rfl

variable (α)

-- even `α` needs to be explicit here for elaboration
-- the `NormOneClass A` shouldn't really be necessary, but currently it is for
-- `one_memℓp_infty` to get the `Ring` instance on `lp`.
/-- The canonical map between `lp (fun _ : α ↦ A) ∞` and `α →ᵇ A` as an `AlgEquiv`. -/
noncomputable def AlgEquiv.lpBCF : lp (fun _ : α ↦ A) ∞ ≃ₐ[𝕜] α →ᵇ A :=
  { RingEquiv.lpBCF with commutes' := fun _k ↦ rfl }


variable {α 𝕜}

theorem coe_algEquiv_lpBCF (f : lp (fun _ : α ↦ A) ∞) : (AlgEquiv.lpBCF α 𝕜 f : α → A) = f :=
  rfl

theorem coe_algEquiv_lpBCF_symm (f : α →ᵇ A) : ((AlgEquiv.lpBCF α 𝕜).symm f : α → A) = f :=
  rfl

end RingAlgebra

end LpBCF
