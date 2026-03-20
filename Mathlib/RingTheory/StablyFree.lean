/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

public section

universe u v

/-- A module `M` over a ring `R` is *stably free* if there exists a finite free `N` over `R`
  such that `M ⊕ N` is free. -/
def IsStablyFree (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module R N),
    Module.Finite R N ∧ Module.Free R N ∧ Module.Free R (M × N)

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
  have hj0 : j ≠ 0 := ((Fin.zero_le i).trans_lt h).ne'
  have hiLast : i ≠ Fin.last n := Fin.ne_of_lt (h.trans_le j.le_last)
  let ai : Fin n := i.castPred hiLast
  let bi : Fin n := j.pred hj0
  have h_ai_le_bi : ai ≤ bi := Nat.le_sub_one_of_lt h
  have : NeZero n := NeZero.of_pos (Fin.pos ai)
  have htail : (fun k : Fin n => v (i.succAbove k)) =
      (fun k : Fin n => v (j.succAbove k)) ∘ Fin.cycleIcc ai bi := by
    funext k
    have hj : bi.succ = j := by simp [bi]
    have hi : ai.castSucc = i := by simp [ai]
    rcases lt_or_ge k ai with hk | hk
    · rw [Function.comp_apply, Fin.cycleIcc_of_lt hk]
      have hk_i : k.castSucc < i := by simpa [hi] using hk
      rw [Fin.succAbove_of_castSucc_lt _ _ hk_i, Fin.succAbove_of_castSucc_lt _ _ (hk_i.trans h)]
    rcases lt_or_ge bi k with hk' | hk'
    · rw [Function.comp_apply, Fin.cycleIcc_of_gt hk']
      have hj_k : j ≤ k.castSucc := by simpa [hj] using show bi.succ ≤ k.castSucc from hk'
      rw [Fin.succAbove_of_le_castSucc _ _ (h.le.trans hj_k), Fin.succAbove_of_le_castSucc _ _ hj_k]
    rcases Fin.lt_or_eq_of_le hk' with hk' | rfl
    · rw [Function.comp_apply, Fin.cycleIcc_of_ge_of_lt hk hk']
      have hj_k1' : ((k + 1 : Fin n)).castSucc < bi.succ := by
        apply Fin.lt_def.mpr
        have hval : (((k + 1 : Fin n) : ℕ)) = (k : ℕ) + 1 := Fin.val_add_one_of_lt' (by omega)
        simpa [hval] using hk'
      have hj_k1 : ((k + 1 : Fin n)).castSucc < j := by simpa [hj] using hj_k1'
      have hi_k : i ≤ k.castSucc := by simpa [hi] using hk
      rw [Fin.succAbove_of_le_castSucc _ _ hi_k, Fin.succAbove_of_castSucc_lt _ _ hj_k1]
      have hidx : k.succ = (k + 1 : Fin n).castSucc := by
        apply Fin.ext
        have hval : (((k + 1 : Fin n) : ℕ)) = (k : ℕ) + 1 := Fin.val_add_one_of_lt' (by omega)
        simp [hval]
      simp [hidx]
    · rw [Function.comp_apply, Fin.cycleIcc_of_last h_ai_le_bi]
      have hj : bi.succ = j := by simp [bi]
      have h' : i < bi.succ := by simpa [hj] using h
      have hbi : i.succAbove bi = j := by simpa [hj] using (Fin.succAbove_of_lt_succ i bi h')
      have hai_idx : bi.predAbove i = ai := by simpa [ai] using (Fin.predAbove_of_lt_succ bi i h')
      have hai : j.succAbove ai = i := by
        have hne : i ≠ bi.succ := by simpa [hj] using h.ne
        rw [← hj, ← hai_idx]
        simpa using Fin.succ_succAbove_predAbove hne
      rw [hbi, hai, hv]
  have htail₂ : (fun k : Fin n => (v (i.succAbove k)).2) =
      (fun k : Fin n => (v (j.succAbove k)).2) ∘ Fin.cycleIcc ai bi := by
    ext k
    exact congrArg Prod.snd (congrArg (fun f : Fin n → M × N => f k) htail)
  have hdet : (bN.det fun k => (v (i.succAbove k)).2) =
      (Equiv.Perm.sign (Fin.cycleIcc ai bi) : R) * (bN.det fun k => (v (j.succAbove k)).2) := by
    simpa [Units.smul_def, htail₂] using
      AlternatingMap.map_perm bN.det (fun k : Fin n => (v (j.succAbove k)).2) (Fin.cycleIcc ai bi)
  have hsign : (Equiv.Perm.sign i.cycleRange : R) * Equiv.Perm.sign (Fin.cycleIcc ai bi) =
      - (Equiv.Perm.sign j.cycleRange : R) := by
    rw [Fin.sign_cycleRange, Fin.sign_cycleIcc_of_le h_ai_le_bi, Fin.sign_cycleRange]
    norm_num
    change (-1 : R) ^ (i : ℕ) * (-1 : R) ^ ((j : ℕ) - 1 - i) = -((-1 : R) ^ (j : ℕ))
    have hexp : (i : ℕ) + ((j : ℕ) - 1 - i) = (j : ℕ) - 1 := Nat.add_sub_of_le h_ai_le_bi
    rw [← pow_add, hexp]
    nth_rw 2 [← Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.zero_lt_of_lt h))]
    simp [pow_add, pow_one]
  simp only [laplaceTerm_apply, laplaceTerm_apply, hdet, smul_smul]
  rw [← mul_assoc, hsign, congrArg Prod.fst hv]
  simp

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
    · have hgt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) hij.symm
      simpa [hrest, add_assoc, add_left_comm, add_comm] using
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

/-- Let `R` be a commutative ring such that `Spec R` is irreducible, `M` be a finite stably free
  `R`-module. If `Mₘ ≃ Rₘ` for any maximal ideal `m` of `R`, then `M` is free. -/
theorem Module.free_of_isStablyFree_of_localized_eq_ring
    [Nontrivial R] [PreconnectedSpace (PrimeSpectrum R)] [Module.Finite R M]
    (hstable : IsStablyFree R M) (hloc : ∀ (m : Ideal R) [m.IsMaximal],
      LocalizedModule m.primeCompl M ≃ₗ[Localization.AtPrime m] Localization.AtPrime m) :
    Module.Free R M := by
  -- Choose a finite free complement `N` such that `M ⊕ N` is free.
  obtain ⟨N, _, _, _, _, _⟩ := hstable
  let i : M →ₗ[R] M × N := LinearMap.inl R M N
  let s : M × N →ₗ[R] M := LinearMap.fst R M N
  have hs : s ∘ₗ i = LinearMap.id := by
    ext x
    rfl
  -- Since `M` is a direct summand of a free module, it is projective, hence flat and
  -- finitely presented. Therefore its stalk rank is locally constant on `PrimeSpectrum R`.
  have : Module.Projective R M := Module.Projective.of_split i s hs
  have : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  obtain ⟨m0, hm0max, _⟩ := Ideal.exists_le_maximal (⊥ : Ideal R) (by simp)
  let p0 : PrimeSpectrum R := PrimeSpectrum.mk m0 hm0max.isPrime
  have hlocconst : IsLocallyConstant (Module.rankAtStalk (R := R) M) :=
    Module.isLocallyConstant_rankAtStalk
  -- At every maximal ideal, the localization of `M` is isomorphic to the localized ring,
  -- so the stalk rank is `1`; preconnectedness forces this rank to be `1` everywhere.
  have hp0 : Module.rankAtStalk M p0 = 1 :=
    Module.finrank_eq_card_basis ((Module.Basis.singleton (Fin 1) (Localization.AtPrime m0)).map
      (hloc m0).symm) |>.trans (by simp)
  have hrank1 (p : PrimeSpectrum R) : Module.rankAtStalk M p = 1 :=
    Eq.trans (by simpa using (hlocconst.apply_eq_of_preconnectedSpace p p0)) hp0
  let n := Module.finrank R N
  -- Comparing stalk ranks at one maximal point gives `rank (M ⊕ N) = rank N + 1`.
  have hfinrank_prod : Module.finrank R (M × N) = n + 1 :=
    (congrArg (fun f => f p0) Module.rankAtStalk_eq_finrank_of_free).symm.trans <|
      (congrArg (fun f => f p0) (Module.rankAtStalk_prod M N)).trans <| by
        simp [← hp0, n, Nat.add_comm]
  let bN : Module.Basis (Fin n) R N := Module.finBasisOfFinrankEq R N rfl
  let bF : Module.Basis (Fin (n + 1)) R (M × N) :=
    Module.finBasisOfFinrankEq R (M × N) hfinrank_prod
  -- Laplace expansion along the `M`-summand gives a surjective map
  -- `Λ^(n + 1) (M ⊕ N) → M`, and after identifying the top exterior power of the free
  -- module `M ⊕ N` with `R`, this becomes a surjective linear map `f : R → M`.
  let f : R →ₗ[R] M := laplaceToLeft bN ∘ₗ (topExteriorLinearEquiv bF).symm.toLinearMap
  have hf_surj : Function.Surjective f := by
    intro x
    refine ⟨topExteriorLinearEquiv bF
      (exteriorPower.ιMulti R (n + 1) (Fin.cons (x, 0) fun i => (0, bN i))), ?_⟩
    change laplaceToLeft bN ((topExteriorLinearEquiv bF).symm _) = x
    simpa [LinearEquiv.symm_apply_apply] using laplaceToLeft_ιMulti_cons bN x
  -- After localizing at a maximal ideal `m`, the map `f_m` is still surjective.
  -- Since `Mₘ ≃ Rₘ`, it is a surjective endomorphism of a free rank-one module, hence bijective.
  -- By the local criterion for bijectivity, `f` is bijective over `R`, so `M ≃ R`.
  have hbij : Function.Bijective f := bijective_of_localized_maximal f <| by
    intro m _
    have : Module.Invertible (Localization.AtPrime m) (LocalizedModule m.primeCompl M) :=
      Module.Invertible.congr (hloc m).symm
    exact Module.Invertible.bijective_of_surjective
      (LocalizedModule.map_surjective m.primeCompl f hf_surj)
  let e : R ≃ₗ[R] M := LinearEquiv.ofBijective f hbij
  exact Module.Free.of_equiv' inferInstance e
