/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

public section

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {n : ℕ}

/-- The multilinear map that takes the left component of the first input and multiplies it
by the determinant of the right components of the remaining inputs. -/
private noncomputable def term0ML (bN : Module.Basis (Fin n) R N) :
    MultilinearMap R (fun _ : Fin (n + 1) => M × N) M := by
  let tailDet : MultilinearMap R (fun _ : Fin n => M × N) R :=
    (bN.det.compLinearMap (LinearMap.snd R M N) : (M × N) [⋀^Fin n]→ₗ[R] R)
  let g : M × N →ₗ[R] MultilinearMap R (fun _ : Fin n => M × N) M :=
    { toFun := fun x => tailDet.smulRight x.1
      map_add' := by
        intro x y
        ext v
        simp [tailDet]
      map_smul' := by
        intro c x
        ext v
        simp [tailDet, smul_smul, mul_comm] }
  exact LinearMap.uncurryLeft g

/-- The `i`-th signed term in the Laplace expansion along the `M`-summand of `M × N`. -/
private noncomputable def laplaceTerm (bN : Module.Basis (Fin n) R N) (i : Fin (n + 1)) :
    MultilinearMap R (fun _ : Fin (n + 1) => M × N) M :=
  (Equiv.Perm.sign i.cycleRange : R) • (term0ML bN).domDomCongr i.cycleRange.symm

private lemma laplaceTerm_apply (bN : Module.Basis (Fin n) R N) (i : Fin (n + 1))
    (v : Fin (n + 1) → M × N) : laplaceTerm bN i v = (Equiv.Perm.sign i.cycleRange : R) •
      ((bN.det fun k => (v (i.succAbove k)).2) • (v i).1) := by
  simp [laplaceTerm, term0ML, Fin.tail, Fin.cycleRange_symm_zero, Fin.cycleRange_symm_succ]

/-- The multilinear Laplace expansion along the `M`-summand of `M × N`. -/
private noncomputable def laplaceML (bN : Module.Basis (Fin n) R N) :
    MultilinearMap R (fun _ : Fin (n + 1) => M × N) M :=
  ∑ i : Fin (n + 1), laplaceTerm bN i

private lemma laplaceML_apply (bN : Module.Basis (Fin n) R N) (v : Fin (n + 1) → M × N) :
    laplaceML bN v = ∑ i : Fin (n + 1), laplaceTerm bN i v := by
  simp [laplaceML]

private lemma laplaceTerm_eq_zero_of_eq (bN : Module.Basis (Fin n) R N) (v : Fin (n + 1) → M × N)
    {i j p : Fin (n + 1)} (hij : i ≠ j) (hp_i : p ≠ i) (hp_j : p ≠ j) (hv : v i = v j) :
    laplaceTerm bN p v = 0 := by
  rw [laplaceTerm_apply]
  rcases (Fin.eq_self_or_eq_succAbove p i).resolve_left hp_i.symm with ⟨ai, hai⟩
  rcases (Fin.eq_self_or_eq_succAbove p j).resolve_left hp_j.symm with ⟨bi, hbi⟩
  have hdet : (bN.det fun k => (v (p.succAbove k)).2) = 0 :=
    bN.det.map_eq_zero_of_eq _ (by simpa [hai, hbi] using congrArg Prod.snd hv)
      (fun h => hij (by simp [hai, hbi, h]))
  simp [hdet]

private lemma laplaceTerm_add_eq_zero_of_lt (bN : Module.Basis (Fin n) R N)
    (v : Fin (n + 1) → M × N) {i j : Fin (n + 1)} (h : i < j) (hv : v i = v j) :
      laplaceTerm bN i v + laplaceTerm bN j v = 0 := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    fun p q => Fin.cases (if q = i ∨ q = j then 1 else 0) (fun k => bN.repr ((v q).2) k) p
  have hcol : ∀ p, A p i = A p j :=
    Fin.cases (by simp [A, h.ne]) (fun k ↦ by simp [A, hv])
  have hdet0 : A.det = 0 := Matrix.det_zero_of_column_eq h.ne hcol
  have hminor (p : Fin (n + 1)) :
      (A.submatrix Fin.succ p.succAbove).det = bN.det (fun k => (v (p.succAbove k)).2) := by
    rw [Module.Basis.det_apply]
    refine congrArg Matrix.det ?_
    ext a b
    simp [A, Module.Basis.toMatrix]
  have hsum : (∑ x, if x = i ∨ x = j then (- 1) ^ (x : ℕ) * (bN.det fun k => (v (x.succAbove k)).2)
      else 0) = 0 := by
    rw [Matrix.det_succ_row_zero] at hdet0
    simpa [A, h.ne, hminor] using hdet0
  have hcoeff :
      (Equiv.Perm.sign i.cycleRange : R) * (bN.det fun k => (v (i.succAbove k)).2) +
        (Equiv.Perm.sign j.cycleRange : R) * (bN.det fun k => (v (j.succAbove k)).2) = 0 := by
    rw [Finset.sum_ite] at hsum
    have hsum' : (∑ x with x = i ∨ x = j,
        (- 1) ^ (x : ℕ) * (bN.det fun k => (v (x.succAbove k)).2)) = 0 := by
      simpa using hsum
    have hfilter : Finset.filter (fun x : Fin (n + 1) => x = i ∨ x = j) Finset.univ = {i, j} := by
      ext x
      simp [eq_comm]
    rw [hfilter, Finset.sum_insert, Finset.sum_singleton] at hsum'
    · simpa [Fin.sign_cycleRange, add_comm] using hsum'
    · simp [h.ne]
  simp only [laplaceTerm_apply, laplaceTerm_apply, hv, smul_smul, ← add_smul]
  simpa using congrArg (fun c : R => c • (v j).1) hcoeff

/-- The alternating map on `M × N` obtained from the Laplace expansion along the `M`-summand. -/
private noncomputable def laplaceAlternating (bN : Module.Basis (Fin n) R N) :
    (M × N) [⋀^Fin (n + 1)]→ₗ[R] M where
  __ := laplaceML bN
  map_eq_zero_of_eq' := by
    intro v i j hv hij
    change laplaceML bN v = 0
    rw [laplaceML_apply, ← Finset.add_sum_erase Finset.univ _ (by simp),
      ← Finset.add_sum_erase _ _ (by simpa using hij.symm)]
    have hrest : Finset.sum ((Finset.univ.erase i).erase j) (fun p => laplaceTerm bN p v) = 0 :=
      Finset.sum_eq_zero <| fun p hp => laplaceTerm_eq_zero_of_eq bN v hij
        (Finset.mem_erase.mp (Finset.mem_of_mem_erase hp)).1 (Finset.mem_erase.mp hp).1 hv
    by_cases hlt : i < j
    · simpa [hrest, add_assoc] using laplaceTerm_add_eq_zero_of_lt bN v hlt hv
    · simpa [hrest, add_assoc, add_left_comm, add_comm] using
        laplaceTerm_add_eq_zero_of_lt bN v (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm) hv.symm

/-- The linear map from the top exterior power of `M × N` to `M` induced by the Laplace
expansion along the `M`-summand. -/
private noncomputable def laplaceToLeft (bN : Module.Basis (Fin n) R N) :
    ⋀[R]^(n + 1) (M × N) →ₗ[R] M :=
  exteriorPower.alternatingMapLinearEquiv (laplaceAlternating bN)

private lemma laplaceML_cons_apply (bN : Module.Basis (Fin n) R N) (m : M) :
    laplaceML bN (Fin.cons (m, 0) fun i => (0, bN i)) = m := by
  simp [laplaceML_apply, Fin.sum_univ_succ, laplaceTerm_apply, Module.Basis.det_self]

private lemma laplaceToLeft_ιMulti_cons (bN : Module.Basis (Fin n) R N) (m : M) :
    laplaceToLeft bN (exteriorPower.ιMulti R (n + 1) (Fin.cons (m, 0) fun i => (0, bN i))) = m := by
  rw [laplaceToLeft, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  simpa [laplaceAlternating] using laplaceML_cons_apply bN m

/-- The linear equivalence from the top exterior power of a finite free module to the base ring
associated to a chosen basis. -/
noncomputable def topExteriorLinearEquiv {F : Type*} [AddCommGroup F] [Module R F]
    (b : Module.Basis (Fin n) R F) : ⋀[R]^n F ≃ₗ[R] R := by
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
    have hv_eq : (fun i => b (v i)) = (b ∘ e) := by
      ext i
      simp [e]
    simp [hv_eq]
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
  let f : R →ₗ[R] M := laplaceToLeft bN ∘ₗ (topExteriorLinearEquiv bF).symm.toLinearMap
  have hf_surj : Function.Surjective f := by
    intro x
    refine ⟨topExteriorLinearEquiv bF
      (exteriorPower.ιMulti R (n + 1) (Fin.cons (x, 0) fun i => (0, bN i))), ?_⟩
    change laplaceToLeft bN ((topExteriorLinearEquiv bF).symm _) = x
    simpa [LinearEquiv.symm_apply_apply] using laplaceToLeft_ιMulti_cons bN x
  have hbij : Function.Bijective f := bijective_of_localized_maximal f <| by
    intro m _
    have : Module.Invertible (Localization.AtPrime m) (LocalizedModule.AtPrime m M) :=
      Module.Invertible.congr (hloc m).symm
    exact Module.Invertible.bijective_of_surjective
      (LocalizedModule.map_surjective m.primeCompl f hf_surj)
  exact Module.Free.of_equiv (LinearEquiv.ofBijective f hbij)
