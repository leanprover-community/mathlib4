/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Data.ZMod.Quotient
import Mathlib.LinearAlgebra.FreeModule.Finite.Rank
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.QuotientPi

#align_import linear_algebra.free_module.ideal_quotient from "leanprover-community/mathlib"@"90b0d53ee6ffa910e5c2a977ce7e2fc704647974"

/-! # Ideals in free modules over PIDs

## Main results

 - `Ideal.quotientEquivPiSpan`: `S ⧸ I`, if `S` is finite free as a module over a PID `R`,
   can be written as a product of quotients of `R` by principal ideals.

-/

namespace Ideal

open scoped BigOperators DirectSum

variable {ι R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable [IsDomain R] [IsPrincipalIdealRing R] [IsDomain S] [Finite ι]

/-- We can write the quotient of an ideal over a PID as a product of quotients by principal ideals.
-/
noncomputable def quotientEquivPiSpan (I : Ideal S) (b : Basis ι R S) (hI : I ≠ ⊥) :
    (S ⧸ I) ≃ₗ[R] ∀ i, R ⧸ span ({I.smithCoeffs b hI i} : Set R) := by
  haveI := Fintype.ofFinite ι
  -- ⊢ (S ⧸ I) ≃ₗ[R] (i : ι) → R ⧸ span {smithCoeffs b I hI i}
  -- Choose `e : S ≃ₗ I` and a basis `b'` for `S` that turns the map
  -- `f := ((Submodule.subtype I).restrictScalars R).comp e` into a diagonal matrix:
  -- there is an `a : ι → ℤ` such that `f (b' i) = a i • b' i`.
  let a := I.smithCoeffs b hI
  -- ⊢ (S ⧸ I) ≃ₗ[R] (i : ι) → R ⧸ span {smithCoeffs b I hI i}
  let b' := I.ringBasis b hI
  -- ⊢ (S ⧸ I) ≃ₗ[R] (i : ι) → R ⧸ span {smithCoeffs b I hI i}
  let ab := I.selfBasis b hI
  -- ⊢ (S ⧸ I) ≃ₗ[R] (i : ι) → R ⧸ span {smithCoeffs b I hI i}
  have ab_eq := I.selfBasis_def b hI
  -- ⊢ (S ⧸ I) ≃ₗ[R] (i : ι) → R ⧸ span {smithCoeffs b I hI i}
  have mem_I_iff : ∀ x, x ∈ I ↔ ∀ i, a i ∣ b'.repr x i := by
    intro x
    -- Porting note: these lines used to be `simp_rw [ab.mem_ideal_iff', ab_eq]`
    rw [ab.mem_ideal_iff']
    simp_rw [ab_eq]
    have : ∀ (c : ι → R) (i), b'.repr (∑ j : ι, c j • a j • b' j) i = a i * c i := by
      intro c i
      simp only [← MulAction.mul_smul, b'.repr_sum_self, mul_comm]
    constructor
    · rintro ⟨c, rfl⟩ i
      exact ⟨c i, this c i⟩
    · rintro ha
      choose c hc using ha
      exact ⟨c, b'.ext_elem fun i => Eq.trans (hc i) (this c i).symm⟩
  -- Now we map everything through the linear equiv `S ≃ₗ (ι → R)`,
  -- which maps `I` to `I' := Π i, a i ℤ`.
  let I' : Submodule R (ι → R) := Submodule.pi Set.univ fun i => span ({a i} : Set R)
  -- ⊢ (S ⧸ I) ≃ₗ[R] (i : ι) → R ⧸ span {smithCoeffs b I hI i}
  have : Submodule.map (b'.equivFun : S →ₗ[R] ι → R) (I.restrictScalars R) = I' := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_pi, mem_span_singleton, Set.mem_univ,
      Submodule.restrictScalars_mem, mem_I_iff, smul_eq_mul, forall_true_left, LinearEquiv.coe_coe,
      Basis.equivFun_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      exact hy i
    · rintro hdvd
      refine' ⟨∑ i, x i • b' i, fun i => _, _⟩ <;> rw [b'.repr_sum_self]
      · exact hdvd i
  refine' ((Submodule.Quotient.restrictScalarsEquiv R I).restrictScalars R).symm.trans
    (σ₁₂ := RingHom.id R) (σ₃₂ := RingHom.id R) _
  · infer_instance
    -- 🎉 no goals
  · infer_instance
    -- 🎉 no goals
  refine' (Submodule.Quotient.equiv (I.restrictScalars R) I' b'.equivFun this).trans
    (σ₁₂ := RingHom.id R) (σ₃₂ := RingHom.id R) _
  · infer_instance
    -- 🎉 no goals
  · infer_instance
    -- 🎉 no goals
  classical
    let this :=
      Submodule.quotientPi (show ∀ _, Submodule R R from fun i => span ({a i} : Set R))
    exact this
#align ideal.quotient_equiv_pi_span Ideal.quotientEquivPiSpan

/-- Ideal quotients over a free finite extension of `ℤ` are isomorphic to a direct product of
`ZMod`. -/
noncomputable def quotientEquivPiZMod (I : Ideal S) (b : Basis ι ℤ S) (hI : I ≠ ⊥) :
    S ⧸ I ≃+ ∀ i, ZMod (I.smithCoeffs b hI i).natAbs :=
  let a := I.smithCoeffs b hI
  let e := I.quotientEquivPiSpan b hI
  let e' : (∀ i : ι, ℤ ⧸ span ({a i} : Set ℤ)) ≃+ ∀ i : ι, ZMod (a i).natAbs :=
    AddEquiv.piCongrRight fun i => ↑(Int.quotientSpanEquivZMod (a i))
  (↑(e : (S ⧸ I) ≃ₗ[ℤ] _) : S ⧸ I ≃+ _).trans e'
#align ideal.quotient_equiv_pi_zmod Ideal.quotientEquivPiZMod

/-- A nonzero ideal over a free finite extension of `ℤ` has a finite quotient.

Can't be an instance because of the side condition `I ≠ ⊥`, and more importantly,
because the choice of `Fintype` instance is non-canonical.
-/
noncomputable def fintypeQuotientOfFreeOfNeBot [Module.Free ℤ S] [Module.Finite ℤ S]
    (I : Ideal S) (hI : I ≠ ⊥) : Fintype (S ⧸ I) := by
  let b := Module.Free.chooseBasis ℤ S
  -- ⊢ Fintype (S ⧸ I)
  let a := I.smithCoeffs b hI
  -- ⊢ Fintype (S ⧸ I)
  let e := I.quotientEquivPiZMod b hI
  -- ⊢ Fintype (S ⧸ I)
  haveI : ∀ i, NeZero (a i).natAbs := fun i =>
    ⟨Int.natAbs_ne_zero.mpr (smithCoeffs_ne_zero b I hI i)⟩
  classical exact Fintype.ofEquiv (∀ i, ZMod (a i).natAbs) e.symm
  -- 🎉 no goals
#align ideal.fintype_quotient_of_free_of_ne_bot Ideal.fintypeQuotientOfFreeOfNeBot

variable (F : Type*) [CommRing F] [Algebra F R] [Algebra F S] [IsScalarTower F R S]
  (b : Basis ι R S) {I : Ideal S} (hI : I ≠ ⊥)

/-- Decompose `S⧸I` as a direct sum of cyclic `R`-modules
  (quotients by the ideals generated by Smith coefficients of `I`). -/
noncomputable def quotientEquivDirectSum :
    (S ⧸ I) ≃ₗ[F] ⨁ i, R ⧸ span ({I.smithCoeffs b hI i} : Set R) := by
  haveI := Fintype.ofFinite ι
  -- ⊢ (S ⧸ I) ≃ₗ[F] ⨁ (i : ι), R ⧸ span {smithCoeffs b I hI i}
  -- porting note: manual construction of `CompatibleSmul` typeclass no longer needed
  exact ((I.quotientEquivPiSpan b _).restrictScalars F).trans
    (DirectSum.linearEquivFunOnFintype _ _ _).symm
#align ideal.quotient_equiv_direct_sum Ideal.quotientEquivDirectSum

theorem finrank_quotient_eq_sum {ι} [Fintype ι] (b : Basis ι R S) [Nontrivial F]
    [∀ i, Module.Free F (R ⧸ span ({I.smithCoeffs b hI i} : Set R))]
    [∀ i, Module.Finite F (R ⧸ span ({I.smithCoeffs b hI i} : Set R))] :
    FiniteDimensional.finrank F (S ⧸ I) =
      ∑ i, FiniteDimensional.finrank F (R ⧸ span ({I.smithCoeffs b hI i} : Set R)) := by
  -- slow, and dot notation doesn't work
  rw [LinearEquiv.finrank_eq <| quotientEquivDirectSum F b hI, FiniteDimensional.finrank_directSum]
  -- 🎉 no goals
#align ideal.finrank_quotient_eq_sum Ideal.finrank_quotient_eq_sum

end Ideal
