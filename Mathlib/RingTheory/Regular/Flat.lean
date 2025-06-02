/-
Copyright (c) 2025 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Nailin Guan
-/
import Mathlib

/-!
# `RingTheory.Sequence.IsWeaklyRegular` is stable under flat base change

## Main results
* `RingTheory.Sequence.isWeaklyRegular.of_flat_isBaseChange`: Let `R` be a comm ring, `M` is an
  `R`-module, `S` is a flat $R$-algebra. If `[r₁, …, rₙ]` is a weakly regular `M`-sequence,
  then its image in `M ⊗[R] S` is a weakly regular `M ⊗[R] S`-sequence.
-/

abbrev SemiLinearMapAlgebraMapOfLinearMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M →ₗ[R] N) : M →ₛₗ[algebraMap R A] N where
  __ := f
  map_smul' m r := by simp

abbrev LinearMapOfSemiLinearMapAlgebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M →ₛₗ[algebraMap R A] N) : M →ₗ[R] N where
  __ := f
  map_smul' m r := by simp

open RingTheory.Sequence Pointwise Module

section IsLocalization

variable {R : Type*} [CommRing R] (p : Ideal R)

lemma ENat.add_right_cancel_iff (a b c : ℕ∞) (netop : c ≠ ⊤) : a + c = b + c ↔ a = b :=
  ⟨fun h ↦ ENat.add_left_injective_of_ne_top netop h, fun h ↦ by rw [h]⟩

lemma withBotENat_add_coe_cancel (a b : WithBot ℕ∞) (c : ℕ) : a + c = b + c ↔ a = b := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  by_cases eqbot : a = ⊥
  · simp [eqbot, WithBot.bot_add] at h
    rw [WithBot.add_coe_eq_bot_iff.mp h.symm, eqbot]
  · by_cases eqbot' : b = ⊥
    · absurd eqbot
      simpa [eqbot'] using h
    · have : a.unbot eqbot + c = b.unbot eqbot' + c := by
        apply WithBot.coe_inj.mp
        convert h
        repeat simp;rfl
      rw [← WithBot.coe_unbot a eqbot, ← WithBot.coe_unbot b eqbot', WithBot.coe_inj]
      simpa [ENat.add_right_cancel_iff _ _ _ (ENat.coe_ne_top c)] using this

variable [p.IsPrime] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]

open Pointwise
omit [IsLocalization.AtPrime Rₚ p] in
lemma isLocaliation_map_isSMulRegular_of_isSMulRegular (r : R)
    (M : Type*) [AddCommGroup M] [Module R M] (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ]
    [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f]
    (reg : IsSMulRegular M r) : IsSMulRegular Mₚ (algebraMap R Rₚ r) := by
  rw [isSMulRegular_algebraMap_iff r, isSMulRegular_iff_ker_lsmul_eq_bot Mₚ r,
    LinearMap.ker_eq_bot']
  intro m hm
  rcases IsLocalizedModule.mk'_surjective p.primeCompl f m with ⟨a, ha⟩
  simp only [← ha, LinearMap.lsmul_apply] at hm ⊢
  have : r • IsLocalizedModule.mk' f a.1 a.2 = 0 := hm
  rw [← IsLocalizedModule.mk'_smul, IsLocalizedModule.mk'_eq_zero'] at this
  simp only [Subtype.exists, Submonoid.mk_smul, exists_prop] at this
  rcases this with ⟨s, mem, hs⟩
  rw [smul_smul, mul_comm, ← smul_smul] at hs
  apply (IsLocalizedModule.mk'_eq_zero' f a.2).mpr ⟨⟨s, mem⟩, ?_⟩
  simp only [Submonoid.mk_smul, ← Submodule.mem_bot (R := R),
    ← (isSMulRegular_iff_ker_lsmul_eq_bot M r).mp reg]
  exact hs

abbrev quotSMulTop_isLocalizedModule_map (x : R) (M : Type*) [AddCommGroup M] [Module R M]
    (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]
    (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f] :
    QuotSMulTop x M →ₗ[R] QuotSMulTop ((algebraMap R Rₚ) x) Mₚ :=
  LinearMapOfSemiLinearMapAlgebraMap (Submodule.mapQ _ _
    (SemiLinearMapAlgebraMapOfLinearMap f)
    (fun m hm ↦ by
      rw [← Submodule.ideal_span_singleton_smul] at hm
      simp only [Submodule.mem_comap, LinearMap.coe_mk, LinearMap.coe_toAddHom]
      refine Submodule.smul_induction_on hm (fun r hr m hm ↦ ?_)
        (fun m1 m2 hm1 hm2 ↦ by simpa using Submodule.add_mem _ hm1 hm2)
      rcases Ideal.mem_span_singleton'.mp hr with ⟨r', hr'⟩
      simpa only [← hr', map_smul, mul_comm r' x, ← smul_smul,
        algebra_compatible_smul Rₚ x (r' • f m)]
        using Submodule.smul_mem_pointwise_smul (r' • f m) ((algebraMap R Rₚ) x) ⊤ hm))

lemma isLocalizedModule_quotSMulTop_isLocalizedModule_map (x : R)
    (M : Type*) [AddCommGroup M] [Module R M] (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ]
    [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f] :
    IsLocalizedModule.AtPrime p (quotSMulTop_isLocalizedModule_map p Rₚ x M Mₚ f) where
  map_units r := by
    let alg := (Algebra.algHom R Rₚ (Module.End Rₚ (QuotSMulTop ((algebraMap R Rₚ) x) Mₚ)))
    rcases isUnit_iff_exists.mp (IsUnit.algebraMap_of_algebraMap (r := r.1) alg.toLinearMap
      (map_one alg) (IsLocalization.map_units Rₚ r)) with ⟨s, hs1, hs2⟩
    exact isUnit_iff_exists.mpr ⟨LinearMap.restrictScalars R s,
      ⟨LinearMap.ext (fun x ↦ by simpa using DFunLike.congr hs1 (Eq.refl x)),
        LinearMap.ext (fun x ↦ by simpa using DFunLike.congr hs2 (Eq.refl x))⟩⟩
  surj' y := by
    induction' y using Submodule.Quotient.induction_on with y
    rcases IsLocalizedModule.surj' (S := p.primeCompl) (f := f) y with ⟨z, hz⟩
    use (Submodule.Quotient.mk z.1, z.2)
    simp [← hz]
  exists_of_eq {y1 y2} h := by
    induction' y1 using Submodule.Quotient.induction_on with y1
    induction' y2 using Submodule.Quotient.induction_on with y2
    simp only [LinearMap.coe_mk, LinearMap.coe_toAddHom, Submodule.mapQ_apply] at h
    have h := (Submodule.Quotient.mk_eq_zero _).mp (sub_eq_zero_of_eq h)
    rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h with ⟨m, _, hm⟩
    rcases IsLocalizedModule.surj p.primeCompl f m with ⟨⟨z, s⟩, hz⟩
    have eq : f (s • (y1 - y2)) = f (x • z) := by simp [← hm, ← hz, smul_comm s x m]
    rcases IsLocalizedModule.exists_of_eq (S := p.primeCompl) eq with ⟨c, hc⟩
    use c * s
    apply sub_eq_zero.mp
    have h : (0 : QuotSMulTop x M) = Submodule.Quotient.mk (c • s • (y1 - y2)) := by
      simpa [hc] using (smul_eq_zero_of_right c <| (Submodule.Quotient.mk_eq_zero _).mpr <|
        Submodule.smul_mem_pointwise_smul z x ⊤ Submodule.mem_top).symm
    simp [h, smul_sub, mul_smul]

lemma isLocaliation_map_is_weakly_regular_of_is_weakly_regular (rs : List R)
    (M : Type*) [AddCommGroup M] [Module R M] (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ]
    [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f]
    (reg : IsWeaklyRegular M rs) : IsWeaklyRegular Mₚ (rs.map (algebraMap R Rₚ)) := by
  generalize len : rs.length = n
  induction' n with n ih generalizing M Mₚ rs
  · simp [List.length_eq_zero_iff.mp len]
  · match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      simp only [isWeaklyRegular_cons_iff, List.map_cons] at reg ⊢
      refine ⟨isLocaliation_map_isSMulRegular_of_isSMulRegular p Rₚ x M Mₚ f reg.1, ?_⟩
      let g := quotSMulTop_isLocalizedModule_map p Rₚ x M Mₚ f
      have := isLocalizedModule_quotSMulTop_isLocalizedModule_map p Rₚ x M Mₚ f
      exact ih rs' (QuotSMulTop x M) (QuotSMulTop ((algebraMap R Rₚ) x) Mₚ) g reg.2 len

end IsLocalization

section

open TensorProduct

variable {R S M N Ms Ns : Type*} [CommRing R] [CommRing S] [Algebra R S] [Flat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup Ms] [Module R Ms] [Module S Ms] [IsScalarTower R S Ms]
  {gm : M →ₗ[R] Ms} (hm : IsBaseChange S gm)
  [AddCommGroup N] [Module R N] [AddCommGroup Ns] [Module R Ns] [Module S Ns] [IsScalarTower R S Ns]
  {gn : N →ₗ[R] Ns} (hn : IsBaseChange S gn)
  (f : M →ₗ[R] N) (hf : Function.Injective f)

omit [Flat R S] in
theorem smul_lTensor (s : S) (m : S ⊗[R] M) :
    s • (LinearMap.lTensor S f) m = (LinearMap.lTensor S f) (s • m) := by
  have h : s • (LinearMap.lTensor S f) =
      (LinearMap.lTensor S f).comp ((LinearMap.lsmul S (S ⊗[R] M) s).restrictScalars R) :=
    TensorProduct.ext rfl
  exact congrFun (congrArg DFunLike.coe h) m

include hn hf
theorem Module.Flat.isBaseChange_preserves_injective_linearMap :
    Function.Injective (hm.lift (gn ∘ₗ f)) := by
  have h : hm.lift (gn ∘ₗ f) = hn.equiv ∘ ((LinearMap.lTensor S f) ∘ hm.equiv.symm) := by
    ext x
    refine hm.inductionOn x _ ?_ ?_ ?_ ?_
    · simp only [map_zero, Function.comp_apply]
    · intro _
      simp [hm.lift_eq, hm.equiv_symm_apply, hn.equiv_tmul]
    · intro s m h
      simp only [map_smul, h, Function.comp_apply]
      rw [← map_smul, smul_lTensor f s (hm.equiv.symm m)]
    · intro _ _ h₁ h₂
      simp only [map_add, h₁, Function.comp_apply, h₂]
  simp only [h, EmbeddingLike.comp_injective, EquivLike.injective_comp]
  exact Module.Flat.lTensor_preserves_injective_linearMap f hf

end

@[simp]
theorem Submodule.Quotient.mk_out {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {p : Submodule R M} (m : M ⧸ p) : Submodule.Quotient.mk (Quotient.out m) = m :=
  Quotient.out_eq m

section flat

variable {R S M N: Type*} [CommRing R] [CommRing S] [Algebra R S] [Flat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N] {f : M →ₗ[R] N} (hf : IsBaseChange S f) (x : R)

def QuotSMulTop.congr (e : M ≃ₗ[R] N) : QuotSMulTop x M ≃ₗ[R] QuotSMulTop x N :=
  Submodule.Quotient.equiv (x • ⊤) (x • ⊤) e <|
    (Submodule.map_pointwise_smul x _ e.toLinearMap).trans (by simp)

open TensorProduct QuotSMulTop

include hf

theorem IsSMulRegular.of_flat_isBaseChange (reg : IsSMulRegular M x) :
    IsSMulRegular N (algebraMap R S x) := by
  have eq : hf.lift (f ∘ₗ (LinearMap.lsmul R M) x) = (LinearMap.lsmul S N) (algebraMap R S x) :=
    hf.algHom_ext _ _ (fun _ ↦ by simp [hf.lift_eq])
  convert Module.Flat.isBaseChange_preserves_injective_linearMap hf hf ((LinearMap.lsmul R M) x) reg
  rw [eq]
  rfl
/-
noncomputable def tensorQuotSMulTopEquivQuotSMulTopAlgebraMapAux :
    (S ⊗[R] QuotSMulTop x M) ≃ₗ[R] (QuotSMulTop ((algebraMap R S) x) N) :=
  tensorQuotSMulTopEquivQuotSMulTop x S M ≪≫ₗ QuotSMulTop.congr x (hf.equiv.restrictScalars R) ≪≫ₗ
    Submodule.quotEquivOfEq (x • ⊤) ((algebraMap R S) x • ⊤)
      (Submodule.ext <| fun _ ↦ by simp [Submodule.mem_smul_pointwise_iff_exists])
 -/

variable (S) (M) in
noncomputable def tensorQuotSMulTopEquivQuotSMulTopAlgebraMapTensorAux :
    S ⊗[R] QuotSMulTop x M ≃ₗ[R] QuotSMulTop ((algebraMap R S) x) (S ⊗[R] M) :=
  tensorQuotSMulTopEquivQuotSMulTop x S M ≪≫ₗ
      Submodule.quotEquivOfEq (x • ⊤) ((algebraMap R S) x • ⊤)
        (Submodule.ext <| fun _ ↦ by simp [Submodule.mem_smul_pointwise_iff_exists])


/- variable (S) (M) in
noncomputable def tensorQuotSMulTopEquivQuotSMulTopAlgebraMapTensor :
    S ⊗[R] QuotSMulTop x M ≃ₗ[S] QuotSMulTop ((algebraMap R S) x) (S ⊗[R] M) where
  __ := tensorQuotSMulTopEquivQuotSMulTopAlgebraMapTensorAux S M x
  map_smul' := by
    intro s m
    simp [tensorQuotSMulTopEquivQuotSMulTopAlgebraMapTensorAux, tensorQuotSMulTopEquivQuotSMulTop]
    have h : ((LinearEquiv.lTensor S (equivTensorQuot x M)) (s • m)) =
    s • ((LinearEquiv.lTensor S (equivTensorQuot x M)) m) := sorry
    simp [h]
    rfl
    /- let f₁ := (LinearMap.lsmul S (S ⊗[R] QuotSMulTop x M) s).restrictScalars R
    let f := (tensorQuotSMulTopEquivQuotSMulTopAlgebraMapTensorAux S M x).toLinearMap
    let g := f ∘ₗ ((LinearMap.lsmul S (S ⊗[R] QuotSMulTop x M) s).restrictScalars R)
    let h :=
      ((LinearMap.lsmul S (QuotSMulTop ((algebraMap R S) x) (S ⊗[R] M)) s).restrictScalars R) ∘ₗ f
    have h : f ∘ₗ ((LinearMap.lsmul S (S ⊗[R] QuotSMulTop x M) s).restrictScalars R) =
        ((LinearMap.lsmul S (QuotSMulTop ((algebraMap R S) x) (S ⊗[R] M)) s).restrictScalars R) ∘ₗ f
        := by
      apply TensorProduct.ext
      ext t m
      simp [f, tensorQuotSMulTopEquivQuotSMulTopAlgebraMapTensorAux,
      tensorQuotSMulTopEquivQuotSMulTop]
      --show f ((s • t) ⊗ₜ[R] Submodule.Quotient.mk m) = _

    exact congrFun (congrArg DFunLike.coe h) m -/ -/

variable (S) (M) in
noncomputable def tensorQuotSMulTopLinearMapQuotSMulTopAlgebraMapTensor :
    S ⊗[R] QuotSMulTop x M →ₗ[S] QuotSMulTop ((algebraMap R S) x) (S ⊗[R] M) := by
  apply LinearMap.liftBaseChange S ?_
  apply Submodule.mapQ (x • ⊤) ((algebraMap R S) x • ⊤) (TensorProduct.mk R S M 1) (fun _ ↦ ?_)
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
    Submodule.mem_comap, forall_exists_index]
  intro _ hm
  simp [← hm]

omit [Flat R S] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] hf in
theorem TensorProduct.tsmul_eq_smul_one_tuml (s : S) (m : M) : s ⊗ₜ[R] m = s • (1 ⊗ₜ[R] m) := by
  nth_rw 1 [show s = s • 1 from by simp]
  rfl

variable (S) (M) in
noncomputable def tensorQuotSMulTopEquivQuotSMulTopAlgebraMapTensor' :
    S ⊗[R] QuotSMulTop x M ≃ₗ[S] QuotSMulTop ((algebraMap R S) x) (S ⊗[R] M) := by
  let f := tensorQuotSMulTopLinearMapQuotSMulTopAlgebraMapTensor S M x
  let N : Submodule S (S ⊗[R] M) := (algebraMap R S) x • ⊤
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · refine LinearMap.ker_eq_bot.mp ?_
    refine LinearMap.ker_eq_bot'.mpr ?_
    intro m h
    induction' m with s m m₁ m₂
    · rfl
    · have hsm : f (s ⊗ₜ[R] m) = N.mkQ (s ⊗ₜ[R] Quotient.out m) := by
        nth_rw 1 [← Quotient.out_eq m]
        simp only [LinearMap.liftBaseChange_tmul, tsmul_eq_smul_one_tuml s (Quotient.out m)]
        rfl
      rw [hsm] at h
      obtain ⟨b, _, h⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp <|
        (Submodule.Quotient.mk_eq_zero N).mp h

      sorry
    · sorry
  · intro m
    use LinearMap.lTensor S (Submodule.mkQ (x • ⊤)) (Quotient.out m)
    sorry

variable (S) (M) in
noncomputable def tensorQuotSMulTopEquivQuotSMulTopAlgebraMapTensor :
    S ⊗[R] QuotSMulTop x M ≃ₗ[S] QuotSMulTop ((algebraMap R S) x) (S ⊗[R] M) :=
  let f := tensorQuotSMulTopLinearMapQuotSMulTopAlgebraMapTensor S M x
  let N : Submodule S (S ⊗[R] M) := (algebraMap R S) x • ⊤
{ __ := f
  invFun m := LinearMap.lTensor S (Submodule.mkQ (x • ⊤)) (Quotient.out m)
  left_inv := by
    intro m
    have h : (LinearMap.lsmul R (S ⊗[R] QuotSMulTop x M)) x = 0 := by
      apply TensorProduct.ext
      ext s m
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.compr₂_apply, mk_apply,
        LinearMap.lsmul_apply, LinearMap.zero_apply]
      rw [← tmul_smul, show x • _ = (0 : QuotSMulTop x M) from
          (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_pointwise_smul m x ⊤ trivial)]
      exact tmul_zero _ s
    have hx (m : S ⊗[R] QuotSMulTop x M) : x • m = 0 := congrFun (congrArg DFunLike.coe h) m
    induction' m with s m m₁ m₂
    · obtain ⟨b, _, h⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp <|
        (Submodule.Quotient.mk_eq_zero N).mp (Quotient.out_eq (0 : _ ⧸ N))
      simp [← h, hx]
    · have hsm : N.mkQ (s ⊗ₜ[R] Quotient.out m) = f (s ⊗ₜ[R] m) := by
        nth_rw 2 [← Quotient.out_eq m]
        simp only [tensorQuotSMulTopLinearMapQuotSMulTopAlgebraMapTensor,
          LinearMap.liftBaseChange_tmul, tsmul_eq_smul_one_tuml s (Quotient.out m)]
        rfl
      obtain ⟨b, _, h⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp <|
        (Submodule.Quotient.eq' N).mp (hsm.trans (Quotient.out_eq _).symm)
      simp only [← add_eq_of_eq_sub <| h.trans (neg_add_eq_sub _ _), hx, LinearMap.coe_toAddHom,
        AddHom.toFun_eq_coe, algebraMap_smul, map_add, map_smul, LinearMap.lTensor_tmul, zero_add]
      congr 1
      exact Quotient.out_eq m
    · have hm : N.mkQ (Quotient.out (f m₁ + f m₂)) =
        N.mkQ (Quotient.out (f m₁) + Quotient.out (f m₂)) := by simp
      obtain ⟨b, _, h⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp <|
        (Submodule.Quotient.eq' N).mp hm.symm
      simpa [← add_eq_of_eq_sub <| h.trans (neg_add_eq_sub _ _), hx] using by congr 1
  right_inv := sorry }

noncomputable def tensorQuotSMulTopEquivQuotSMulTopAlgebraMap :
    (S ⊗[R] QuotSMulTop x M) ≃ₗ[S] (QuotSMulTop ((algebraMap R S) x) N) :=
  tensorQuotSMulTopEquivQuotSMulTopAlgebraMapTensor S M x ≪≫ₗ
    QuotSMulTop.congr ((algebraMap R S) x) hf.equiv

theorem RingTheory.Sequence.isWeaklyRegular.of_flat_isBaseChange (rs : List R)
    (reg : IsWeaklyRegular M rs) : IsWeaklyRegular N (rs.map (algebraMap R S)) := by
  generalize len : rs.length = n
  induction' n with n ih generalizing M N rs
  · simp [List.length_eq_zero_iff.mp len]
  · match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      simp only [isWeaklyRegular_cons_iff, List.map_cons] at reg ⊢
      let e := (tensorQuotSMulTopEquivQuotSMulTopAlgebraMap hf x)
      have hg : IsBaseChange S <|
          e.toLinearMap.restrictScalars R ∘ₗ TensorProduct.mk R S (QuotSMulTop x M) 1 :=
        IsBaseChange.of_equiv e (fun _ ↦ by simp)
      exact ⟨IsSMulRegular.of_flat_isBaseChange hf x reg.1, ih hg rs' reg.2 len⟩

end flat
