/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Xavier Roblot
-/
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Quotient.Pi

/-! # Quotient of submodules of full rank in free finite modules over PIDs

## Main results

* `Submodule.quotientEquivPiSpan`: `M ⧸ N`, if `M` is free finite module over a PID `R` and `N`
  is a submodule of full rank, can be written as a product of quotients of `R` by principal ideals.

-/

open Module
open scoped DirectSum

namespace Submodule

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [IsDomain R] [IsPrincipalIdealRing R] [Finite ι]

/--
We can write the quotient by a submodule of full rank over a PID as a product of quotients
by principal ideals.
-/
noncomputable def quotientEquivPiSpan (N : Submodule R M) (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) :
    (M ⧸ N) ≃ₗ[R] Π i, R ⧸ Ideal.span ({smithNormalFormCoeffs b h i} : Set R) := by
  haveI := Fintype.ofFinite ι
  -- Choose `e : M ≃ₗ N` and a basis `b'` for `M` that turns the map
  -- `f := ((Submodule.subtype N).comp e` into a diagonal matrix:
  -- there is an `a : ι → ℤ` such that `f (b' i) = a i • b' i`.
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  have ab_eq := smithNormalFormBotBasis_def b h
  have mem_I_iff : ∀ x, x ∈ N ↔ ∀ i, a i ∣ b'.repr x i := by
    intro x
    simp_rw [ab.mem_submodule_iff', ab, ab_eq]
    have : ∀ (c : ι → R) (i), b'.repr (∑ j : ι, c j • a j • b' j) i = a i * c i := by
      intro c i
      simp only [← MulAction.mul_smul, b'.repr_sum_self, mul_comm]
    constructor
    · rintro ⟨c, rfl⟩ i
      exact ⟨c i, this c i⟩
    · rintro ha
      choose c hc using ha
      exact ⟨c, b'.ext_elem fun i => Eq.trans (hc i) (this c i).symm⟩
  -- Now we map everything through the linear equiv `M ≃ₗ (ι → R)`,
  -- which maps `N` to `N' := Π i, a i ℤ`.
  let N' : Submodule R (ι → R) := Submodule.pi Set.univ fun i => span R ({a i} : Set R)
  have : Submodule.map (b'.equivFun : M →ₗ[R] ι → R) N = N' := by
    ext x
    simp only [N', Submodule.mem_map, Submodule.mem_pi, mem_span_singleton, Set.mem_univ,
      mem_I_iff, smul_eq_mul, forall_true_left, LinearEquiv.coe_coe,
      Basis.equivFun_apply, mul_comm _ (a _), eq_comm (b := (x _))]
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      exact hy i
    · rintro hdvd
      refine ⟨∑ i, x i • b' i, fun i => ?_, ?_⟩ <;> rw [b'.repr_sum_self]
      · exact hdvd i
  refine (Submodule.Quotient.equiv N N' b'.equivFun this).trans (re₂₃ := inferInstance)
    (re₃₂ := inferInstance) ?_
  classical
  exact Submodule.quotientPi (show _ → Submodule R R from fun i => span R ({a i} : Set R))

/--
Quotients by submodules of full rank of free finite `ℤ`-modules are isomorphic
to a direct product of `ZMod`.
-/
noncomputable def quotientEquivPiZMod (N : Submodule ℤ M) (b : Basis ι ℤ M)
    (h : Module.finrank ℤ N = Module.finrank ℤ M) :
    M ⧸ N ≃+ Π i, ZMod (smithNormalFormCoeffs b h i).natAbs :=
  let a := smithNormalFormCoeffs b h
  let e := N.quotientEquivPiSpan b h
  let e' : (∀ i : ι, ℤ ⧸ Ideal.span ({a i} : Set ℤ)) ≃+ ∀ i : ι, ZMod (a i).natAbs :=
    AddEquiv.piCongrRight fun i => ↑(Int.quotientSpanEquivZMod (a i))
  (↑(e : (M ⧸ N) ≃ₗ[ℤ] _) : M ⧸ N ≃+ _).trans e'

/--
A submodule of full rank of a free finite `ℤ`-module has a finite quotient.
It can't be an instance because of the side condition `Module.finrank ℤ N = Module.finrank ℤ M`.
-/
theorem finiteQuotientOfFreeOfRankEq [Module.Free ℤ M] [Module.Finite ℤ M]
    (N : Submodule ℤ M) (h : Module.finrank ℤ N = Module.finrank ℤ M) : Finite (M ⧸ N) := by
  let b := Module.Free.chooseBasis ℤ M
  let a := smithNormalFormCoeffs b h
  let e := N.quotientEquivPiZMod b h
  have : ∀ i, NeZero (a i).natAbs := fun i ↦
    ⟨Int.natAbs_ne_zero.mpr (smithNormalFormCoeffs_ne_zero b h i)⟩
  exact Finite.of_equiv (Π i, ZMod (a i).natAbs) e.symm

theorem finiteQuotient_iff [Module.Free ℤ M] [Module.Finite ℤ M] (N : Submodule ℤ M) :
    Finite (M ⧸ N) ↔ Module.finrank ℤ N = Module.finrank ℤ M := by
  refine ⟨fun h ↦ le_antisymm (finrank_le N) <|
    ((LinearMap.lsmul ℤ M (Nat.card (M ⧸ N))).codRestrict N
      fun x ↦ ?_).finrank_le_finrank_of_injective ?_, fun h ↦ finiteQuotientOfFreeOfRankEq N h⟩
  · simpa using AddSubgroup.nsmul_index_mem N.toAddSubgroup x
  · refine (LinearMap.lsmul_injective ?_).codRestrict _
    exact Int.ofNat_ne_zero.mpr <| Nat.card_ne_zero.mpr
      ⟨Set.nonempty_iff_univ_nonempty.mpr Set.univ_nonempty, h⟩

variable (F : Type*) [CommRing F] [Algebra F R] [Module F M] [IsScalarTower F R M]
  (b : Basis ι R M) {N : Submodule R M}

/-- Decompose `M⧸N` as a direct sum of cyclic `R`-modules
  (quotients by the ideals generated by Smith coefficients of `N`). -/
noncomputable def quotientEquivDirectSum (h : Module.finrank R N = Module.finrank R M) :
    (M ⧸ N) ≃ₗ[F] ⨁ i, R ⧸ Ideal.span ({smithNormalFormCoeffs b h i} : Set R) := by
  haveI := Fintype.ofFinite ι
  exact ((N.quotientEquivPiSpan b _).restrictScalars F).trans
    (DirectSum.linearEquivFunOnFintype _ _ _).symm

theorem finrank_quotient_eq_sum {ι} [Fintype ι] (b : Basis ι R M) [Nontrivial F]
    (h : Module.finrank R N = Module.finrank R M)
    [∀ i, Module.Free F (R ⧸ Ideal.span ({smithNormalFormCoeffs b h i} : Set R))]
    [∀ i, Module.Finite F (R ⧸ Ideal.span ({smithNormalFormCoeffs b h i} : Set R))] :
    Module.finrank F (M ⧸ N) =
      ∑ i, Module.finrank F (R ⧸ Ideal.span ({smithNormalFormCoeffs b h i} : Set R)) := by
  rw [LinearEquiv.finrank_eq <| quotientEquivDirectSum F b h, Module.finrank_directSum]

end Submodule
