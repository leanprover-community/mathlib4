/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
This file proves that a finite stably free module `M` is free if it is invertible.
-/

public section

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {n : ℕ}

/-- The map linear in the first argument and alternating in the remaining arguments that
underlies the cofactor expansion along the `M`-summand of `M × N`. -/
private noncomputable def cofactorLinear (bN : Module.Basis (Fin n) R N) :
    M × N →ₗ[R] (M × N) [⋀^Fin n]→ₗ[R] M where
  toFun x := (bN.det.compLinearMap (LinearMap.snd R M N)).smulRight x.1
  map_add' x y := AlternatingMap.ext fun _ ↦ by simp
  map_smul' c x := AlternatingMap.ext fun _ ↦ by simp [smul_smul, mul_comm]

/-- The linear map from the top exterior power of `M × N` to `M` induced by the cofactor
expansion along the `M`-summand. -/
private noncomputable def cofactorToLeft (bN : Module.Basis (Fin n) R N) :
    ⋀[R]^(n + 1) (M × N) →ₗ[R] M :=
  exteriorPower.alternatingMapLinearEquiv (AlternatingMap.alternatizeUncurryFin (cofactorLinear bN))

private lemma cofactorToLeft_ιMulti_cons (bN : Module.Basis (Fin n) R N) (m : M) :
    cofactorToLeft bN (exteriorPower.ιMulti R (n + 1) (Fin.cons (m, 0) fun i ↦ (0, bN i))) = m := by
  simp [cofactorToLeft, cofactorLinear, AlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_succ, Module.Basis.det_self]

variable (R M) in
/-- Let `R` be a commutative ring, `M` be a finite stably free `R`-module.
  Then `M` is free if it is invertible. -/
theorem Module.free_of_isStablyFree_of_invertible [IsStablyFree R M] [Module.Invertible R M] :
    Module.Free R M := by
  rcases subsingleton_or_nontrivial R with _ | _
  · have : Subsingleton M := Module.Finite.subsingleton_of_ring_subsingleton R M
    infer_instance
  have hp : Module.finrank R (M × N) = n + 1 := by
    let 𝔭 : PrimeSpectrum R := Nonempty.some inferInstance
    have h1 : rankAtStalk M 𝔭 = 1 := by simp [rankAtStalk, Invertible.finrank_eq_one]
    have := congr($(Module.rankAtStalk_prod M N) 𝔭)
    simp only [rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Pi.add_apply] at this
    grind [Module.rankAtStalk_eq_finrank_of_free]
  let bN : Module.Basis (Fin n) R N := Module.finBasis R N
  let b : Module.Basis (Fin (n + 1)) R (M × N) := Module.finBasisOfFinrankEq R (M × N) hp
  let e : R ≃ₗ[R] ⋀[R]^(n + 1) (M × N) := Classical.choice <|
    Module.nonempty_linearEquiv_of_finrank_eq_one <| by simp [exteriorPower.finrank_eq, hp]
  let f : R →ₗ[R] M := cofactorToLeft bN ∘ₗ e
  have hfs : Function.Surjective f := fun x ↦
    ⟨e.symm (exteriorPower.ιMulti R (n + 1) (Fin.cons (x, 0) fun i ↦ (0, bN i))),
      by simp [f, cofactorToLeft_ιMulti_cons]⟩
  exact Module.Free.of_equiv (LinearEquiv.ofBijective f (Invertible.bijective_of_surjective hfs))
