/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Xavier Roblot
-/
module

public import Mathlib.Data.Int.Associated
public import Mathlib.Data.Int.NatAbs
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

/-! # Cardinal of quotient of free finite `ℤ`-modules by submodules of full rank

## Main results

* `Submodule.natAbs_det_basis_change`: let `b` be a `ℤ`-basis for a module `M` over `ℤ` and
  let `bN` be a basis for a submodule `N` of the same dimension. Then the cardinal of `M ⧸ N`
  is given by taking the determinant of `bN` over `b`.

-/

public section

open scoped AddCommGroup

open Module Submodule

section Submodule

variable {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]

/-- Let `e : M ≃ N` be an additive isomorphism (therefore a `ℤ`-linear equiv).
Then an alternative way to compute the cardinality of the quotient `M ⧸ N` is given by taking
the determinant of `e`.
See `natAbs_det_basis_change` for a more familiar formulation of this result. -/
theorem Submodule.natAbs_det_equiv (N : Submodule ℤ M) {E : Type*} [EquivLike E M N]
    [AddEquivClass E M N] (e : E) :
    Int.natAbs
      (LinearMap.det
        (N.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : M →+ N))) =
      Nat.card (M ⧸ N) := by
  let b := Module.Free.chooseBasis ℤ M
  -- Since `e : M ≃ₗ[ℤ] N`, the submodule `N` has full rank.
  have h : Module.finrank ℤ N = Module.finrank ℤ M :=
    (AddEquiv.toIntLinearEquiv e : M ≃ₗ[ℤ] N).symm.finrank_eq
  -- Use the Smith normal form to choose a nice basis for `N`.
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  have ab_eq := smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[ℤ] N := b'.equiv ab (Equiv.refl _)
  let f : M →ₗ[ℤ] M := N.subtype.comp (e' : M →ₗ[ℤ] N)
  let f_apply : ∀ x, f x = b'.equiv ab (Equiv.refl _) x := fun x ↦ rfl
  suffices (LinearMap.det f).natAbs = Nat.card (M ⧸ N) by
    calc
      _ = (LinearMap.det (N.subtype ∘ₗ
            (AddEquiv.toIntLinearEquiv e : M ≃ₗ[ℤ] N))).natAbs := rfl
      _ = (LinearMap.det (N.subtype ∘ₗ _)).natAbs :=
            Int.natAbs_eq_iff_associated.mpr (LinearMap.associated_det_comp_equiv _ _ _)
      _ = Nat.card (M ⧸ N) := this
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    rw [f_apply, b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  calc
    Int.natAbs (LinearMap.det f) = Int.natAbs (LinearMap.toMatrix b' b' f).det := by
      rw [LinearMap.det_toMatrix]
    _ = Int.natAbs (Matrix.diagonal a).det := ?_
    _ = Int.natAbs (∏ i, a i) := by rw [Matrix.det_diagonal]
    _ = ∏ i, Int.natAbs (a i) := map_prod Int.natAbsHom a Finset.univ
    _ = Nat.card (M ⧸ N) := ?_
  -- since `LinearMap.toMatrix b' b' f` is the diagonal matrix with `a` along the diagonal.
  · congr 2; ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases h : i = j
    · rw [h, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ h, Finsupp.single_eq_of_ne h]
  -- Now we map everything through the linear equiv `M ≃ₗ (ι → ℤ)`,
  -- which maps `(M ⧸ N)` to `Π i, ZMod (a i).nat_abs`.
  simp_rw [Nat.card_congr (quotientEquivPiZMod N b h).toEquiv, Nat.card_pi, Nat.card_zmod, a]

/-- Let `b` be a basis for `M` over `ℤ` and `bN` a basis for `N` over `ℤ` of the same dimension.
Then an alternative way to compute the cardinality of `M ⧸ N` is given by taking the determinant
of `bN` over `b`. -/
theorem Submodule.natAbs_det_basis_change {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ M)
    (N : Submodule ℤ M) (bN : Basis ι ℤ N) :
    (b.det ((↑) ∘ bN)).natAbs = Nat.card (M ⧸ N) := by
  let e := b.equiv bN (Equiv.refl _)
  calc
    (b.det (N.subtype ∘ bN)).natAbs = (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[ℤ] N))).natAbs := by
      rw [Basis.det_comp_basis]
    _ = _ := natAbs_det_equiv N e

end Submodule

section AddSubgroup

theorem AddSubgroup.index_eq_natAbs_det {E : Type*} [AddCommGroup E] {ι : Type*}
    [DecidableEq ι] [Fintype ι] (bE : Basis ι ℤ E) (N : AddSubgroup E) (bN : Basis ι ℤ N) :
    N.index = (bE.det (bN ·)).natAbs :=
  have : Module.Free ℤ E := Module.Free.of_basis bE
  have : Module.Finite ℤ E := Module.Finite.of_basis bE
  (Submodule.natAbs_det_basis_change bE N.toIntSubmodule bN).symm

theorem AddSubgroup.relIndex_eq_natAbs_det {E : Type*} [AddCommGroup E]
    (L₁ L₂ : AddSubgroup E) (H : L₁ ≤ L₂) {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ : Basis ι ℤ L₁.toIntSubmodule) (b₂ : Basis ι ℤ L₂.toIntSubmodule) :
    L₁.relIndex L₂ = (b₂.det (fun i ↦ ⟨b₁ i, (H (SetLike.coe_mem _))⟩)).natAbs := by
  rw [relIndex, index_eq_natAbs_det b₂ _ (b₁.map (addSubgroupOfEquivOfLe H).toIntLinearEquiv.symm)]
  rfl

@[deprecated (since := "2025-08-12")]
alias AddSubgroup.relindex_eq_natAbs_det := AddSubgroup.relIndex_eq_natAbs_det

theorem AddSubgroup.relIndex_eq_abs_det {E : Type*} [AddCommGroup E] [Module ℚ E]
    (L₁ L₂ : AddSubgroup E) (H : L₁ ≤ L₂) {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ b₂ : Basis ι ℚ E) (h₁ : L₁ = .closure (Set.range b₁)) (h₂ : L₂ = .closure (Set.range b₂)) :
    L₁.relIndex L₂ = |b₂.det b₁| := by
  rw [AddSubgroup.relIndex_eq_natAbs_det L₁ L₂ H (b₁.addSubgroupOfClosure L₁ h₁)
    (b₂.addSubgroupOfClosure L₂ h₂), Nat.cast_natAbs, Int.cast_abs]
  change |algebraMap ℤ ℚ _| = _
  rw [Basis.det_apply, Basis.det_apply, RingHom.map_det]
  congr; ext
  simp [Basis.toMatrix_apply]

@[deprecated (since := "2025-08-12")]
alias AddSubgroup.relindex_eq_abs_det := AddSubgroup.relIndex_eq_abs_det

end AddSubgroup
