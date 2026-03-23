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
This file proves that a finite stably free module `M` is free if all of its localizations at
maximal ideals are free of rank `1`.
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

private lemma cofactorLinear_apply (bN : Module.Basis (Fin n) R N) (x : M × N)
    (v : Fin n → M × N) : cofactorLinear bN x v = (bN.det fun k => (v k).2) • x.1 := by
  simp [cofactorLinear, AlternatingMap.smulRight_apply]

/-- The linear map from the top exterior power of `M × N` to `M` induced by the cofactor
expansion along the `M`-summand. -/
private noncomputable def cofactorToLeft (bN : Module.Basis (Fin n) R N) :
    ⋀[R]^(n + 1) (M × N) →ₗ[R] M :=
  exteriorPower.alternatingMapLinearEquiv (AlternatingMap.alternatizeUncurryFin (cofactorLinear bN))

private lemma cofactorToLeft_ιMulti_cons (bN : Module.Basis (Fin n) R N) (m : M) :
    cofactorToLeft bN
      (exteriorPower.ιMulti R (n + 1) (Fin.cons (m, 0) fun i => (0, bN i))) = m := by
  rw [cofactorToLeft, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rw [AlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ]
  simp [cofactorLinear_apply, Module.Basis.det_self, Fin.removeNth_zero]

/-- The linear equivalence from the top exterior power of a finite free module to the base ring
associated to a chosen basis. -/
noncomputable def topExteriorLinearEquiv (b : Module.Basis (Fin n) R M) : ⋀[R]^n M ≃ₗ[R] R := by
  refine LinearEquiv.ofLinear (exteriorPower.alternatingMapLinearEquiv b.det)
    (LinearMap.id.smulRight (exteriorPower.ιMulti R n b)) ?_ ?_
  · ext
    simp [Module.Basis.det_self]
  · refine exteriorPower.linearMap_ext <| Module.Basis.ext_alternating b (fun v hv => ?_)
    let e : Equiv.Perm (Fin n) := Equiv.ofBijective v ⟨hv, Finite.injective_iff_surjective.mp hv⟩
    have hdet : b.det (b ∘ e) = (Equiv.Perm.sign e : R) :=
      (AlternatingMap.map_perm b.det b e).trans <| by simp [Units.smul_def, Module.Basis.det_self]
    have hω : _ = (Equiv.Perm.sign e : R) • (exteriorPower.ιMulti R n b) :=
      AlternatingMap.map_perm (exteriorPower.ιMulti R n) b e
    simp [show (fun i => b (v i)) = (b ∘ e) from rfl]
    simp [hdet, hω]

/-- Let `R` be a commutative ring, `M` be a finite stably free `R`-module.
  If `Mₘ ≃ Rₘ` for any maximal ideal `m` of `R`, then `M` is free. -/
theorem Module.free_of_isStablyFree_of_localized_eq_ring [Nontrivial R] [Module.Finite R M]
    (h : IsStablyFree R M) (hloc : ∀ (m : Ideal R) [m.IsMaximal],
      LocalizedModule.AtPrime m M ≃ₗ[Localization.AtPrime m] Localization.AtPrime m) :
    Module.Free R M := by
  have : Module.Projective R M := h.projective
  obtain ⟨N, _, _, _, _, _⟩ := h
  obtain ⟨m0, hm0max, _⟩ := Ideal.exists_le_maximal (⊥ : Ideal R) (by simp)
  let p0 : PrimeSpectrum R := PrimeSpectrum.mk m0 hm0max.isPrime
  have hp0 : Module.rankAtStalk M p0 = 1 :=
    Module.finrank_eq_card_basis ((Module.Basis.singleton (Fin 1) (Localization.AtPrime m0)).map
      (hloc m0).symm) |>.trans (by simp)
  let n := Module.finrank R N
  have hp : Module.finrank R (M × N) = n + 1 :=
    (congrArg (fun f => f p0) Module.rankAtStalk_eq_finrank_of_free).symm.trans <|
      (congrArg (fun f => f p0) (Module.rankAtStalk_prod M N)).trans <| by
        simp [← hp0, n, Nat.add_comm]
  let bN : Module.Basis (Fin n) R N := Module.finBasisOfFinrankEq R N rfl
  let bF : Module.Basis (Fin (n + 1)) R (M × N) := Module.finBasisOfFinrankEq R (M × N) hp
  let f : R →ₗ[R] M := cofactorToLeft bN ∘ₗ (topExteriorLinearEquiv bF).symm.toLinearMap
  have hfs : Function.Surjective f := by
    refine fun x ↦ ⟨topExteriorLinearEquiv bF
      (exteriorPower.ιMulti R (n + 1) (Fin.cons (x, 0) fun i => (0, bN i))), ?_⟩
    change cofactorToLeft bN ((topExteriorLinearEquiv bF).symm _) = x
    simpa using cofactorToLeft_ιMulti_cons bN x
  exact Module.Free.of_equiv <| LinearEquiv.ofBijective f <| bijective_of_localized_maximal f <| by
    intro m _
    have := Module.Invertible.congr (hloc m).symm
    exact Invertible.bijective_of_surjective (LocalizedModule.map_surjective m.primeCompl f hfs)
