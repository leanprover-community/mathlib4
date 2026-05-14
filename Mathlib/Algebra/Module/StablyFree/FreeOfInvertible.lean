/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
This file proves that a finite stably free module `M` is free if it is invertible.
-/

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {n : ℕ}

/-- The map linear in the first argument and alternating in the remaining arguments that
underlies the cofactor expansion along the `M`-summand of `M × N`. -/
noncomputable def exteriorPower.cofactorLinear (bN : Module.Basis (Fin n) R N) :
    M × N →ₗ[R] (M × N) [⋀^Fin n]→ₗ[R] M where
  toFun x := (bN.det.compLinearMap (LinearMap.snd R M N)).smulRight x.1
  map_add' x y := AlternatingMap.ext fun _ ↦ by simp
  map_smul' c x := AlternatingMap.ext fun _ ↦ by simp [smul_smul, mul_comm]

/-- The linear map from the top exterior power of `M × N` to `M` induced by the cofactor
expansion along the `M`-summand. -/
noncomputable def exteriorPower.cofactorToLeft (bN : Module.Basis (Fin n) R N) :
    ⋀[R]^(n + 1) (M × N) →ₗ[R] M :=
  exteriorPower.alternatingMapLinearEquiv (AlternatingMap.alternatizeUncurryFin (cofactorLinear bN))

lemma exteriorPower.cofactorToLeft_ιMulti_cons (bN : Module.Basis (Fin n) R N) (m : M) :
    cofactorToLeft bN (exteriorPower.ιMulti R (n + 1) (Fin.cons (m, 0) fun i ↦ (0, bN i))) = m := by
  simp [cofactorToLeft, cofactorLinear, AlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_succ, Module.Basis.det_self]

variable (R M) in
/-- Let `R` be a commutative ring, `M` be a finite stably free `R`-module.
  Then `M` is free if it is invertible. -/
public theorem Module.free_of_isStablyFree_of_invertible
    [IsStablyFree R M] [Module.Invertible R M] : Module.Free R M := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Module.Free.of_subsingleton' R M
  obtain ⟨N, _, _, _, _, _⟩ := IsStablyFree.exist_free_prod R M
  let n := Module.finrank R N
  have hp : Module.finrank R (M × N) = n + 1 := by
    let 𝔭 : PrimeSpectrum R := Nonempty.some inferInstance
    have h1 : rankAtStalk M 𝔭 = 1 := by simp [rankAtStalk, Invertible.finrank_eq_one]
    have heq := congr($(rankAtStalk_prod M N) 𝔭)
    simp only [rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Pi.add_apply, h1] at heq
    grind
  let e : R ≃ₗ[R] ⋀[R]^(n + 1) (M × N) :=
    (Module.nonempty_linearEquiv_of_finrank_eq_one <| by simp [exteriorPower.finrank_eq, hp]).some
  let bN : Module.Basis (Fin n) R N := Module.finBasis R N
  let f : R →ₗ[R] M := exteriorPower.cofactorToLeft bN ∘ₗ e
  exact Module.Free.of_equiv <| LinearEquiv.ofBijective f <| Invertible.bijective_of_surjective <|
    fun x ↦ ⟨e.symm (exteriorPower.ιMulti R (n + 1) (Fin.cons (x, 0) fun i ↦ (0, bN i))), by
      simp [f, exteriorPower.cofactorToLeft_ιMulti_cons]⟩
