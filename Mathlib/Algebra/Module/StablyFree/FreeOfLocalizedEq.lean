/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
This file proves that a finite stably free module `M` is free if it is locally free of rank `1`.
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

/-- The linear equivalence from the top exterior power of a finite free module to the base ring
associated to a chosen basis. -/
noncomputable def topExteriorLinearEquiv (b : Module.Basis (Fin n) R M) : ⋀[R]^n M ≃ₗ[R] R := by
  refine LinearEquiv.ofLinear (exteriorPower.alternatingMapLinearEquiv b.det)
    (LinearMap.id.smulRight (exteriorPower.ιMulti R n b)) ?_ ?_
  · ext
    simp [Module.Basis.det_self]
  · refine exteriorPower.linearMap_ext <| Module.Basis.ext_alternating b (fun v hv ↦ ?_)
    let e : Equiv.Perm (Fin n) := Equiv.ofBijective v hv.bijective_of_finite
    have hdet : b.det (fun i ↦ b (v i)) = Equiv.Perm.sign e := by
      simpa [Units.smul_def, Module.Basis.det_self] using AlternatingMap.map_perm b.det b e
    simpa [hdet] using (AlternatingMap.map_perm (exteriorPower.ιMulti R n) b e).symm

/-- Let `R` be a commutative ring, `M` be a finite stably free `R`-module.
  Then `M` is free if it is locally free of rank `1`. -/
theorem Module.free_of_isStablyFree_of_localized_eq_ring [Nontrivial R] [Module.Finite R M]
    [IsStablyFree R M] (hlo : ∀ (m : Ideal R) [m.IsMaximal],
      LocalizedModule.AtPrime m M ≃ₗ[Localization.AtPrime m] Localization.AtPrime m) :
    Module.Free R M := by
  obtain ⟨N, _, _, _, _, _⟩ := IsStablyFree.exist_free_prod R M
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal R
  have h1 : Module.rankAtStalk M ⟨𝔪, h𝔪.isPrime⟩ = 1 := by simp [rankAtStalk, (hlo 𝔪).finrank_eq]
  let n := Module.finrank R N
  have hp : Module.finrank R (M × N) = n + 1 := by
    simpa [← h1, n, Nat.add_comm] using congrArg (fun f ↦ f ⟨𝔪, h𝔪.isPrime⟩) <|
      Module.rankAtStalk_eq_finrank_of_free.symm.trans (Module.rankAtStalk_prod M N)
  let bN : Module.Basis (Fin n) R N := Module.finBasis R N
  let b : Module.Basis (Fin (n + 1)) R (M × N) := Module.finBasisOfFinrankEq R (M × N) hp
  let f : R →ₗ[R] M := cofactorToLeft bN ∘ₗ (topExteriorLinearEquiv b).symm
  have hfs : Function.Surjective f := fun x ↦
    ⟨topExteriorLinearEquiv b (exteriorPower.ιMulti R (n + 1) (Fin.cons (x, 0) fun i ↦ (0, bN i))),
      by simp [f, cofactorToLeft_ιMulti_cons]⟩
  exact Module.Free.of_equiv <| LinearEquiv.ofBijective f <| bijective_of_localized_maximal f <| by
    intro m _
    have : Module.Invertible _ (LocalizedModule.AtPrime m M) := Module.Invertible.congr (hlo m).symm
    exact Invertible.bijective_of_surjective (LocalizedModule.map_surjective m.primeCompl f hfs)
