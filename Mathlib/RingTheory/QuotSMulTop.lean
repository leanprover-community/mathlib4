/-
Copyright (c) 2024 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Reducing a module modulo an element of the ring

Given a commutative ring `R` and an element `r : R`, the association
`M ↦ M ⧸ rM` extends to a functor on the category of `R`-modules. This functor
is isomorphic to the functor of tensoring by `R ⧸ (r)` on either side, but can
be more convenient to work with since we can work with quotient types instead
of fiddling with simple tensors.

## Tags

module, commutative algebra
-/

open scoped Pointwise

variable {R} [CommRing R] (r : R) (M : Type*) {M' M''}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M'']

/-- An abbreviation for `M⧸rM` that keeps us from having to write
`(⊤ : Submodule R M)` over and over to satisfy the typechecker. -/
abbrev QuotSMulTop := M ⧸ r • (⊤ : Submodule R M)

namespace QuotSMulTop

open Submodule Function TensorProduct

/-- If `M'` is isomorphic to `M''` as `R`-modules, then `M'⧸rM'` is isomorphic to `M''⧸rM''`. -/
protected def congr (e : M' ≃ₗ[R] M'') : QuotSMulTop r M' ≃ₗ[R] QuotSMulTop r M'' :=
  Submodule.Quotient.equiv (r • ⊤) (r • ⊤) e <|
    (Submodule.map_pointwise_smul r _ e.toLinearMap).trans (by simp)

/-- Reducing a module modulo `r` is the same as left tensoring with `R/(r)`. -/
noncomputable def equivQuotTensor :
    QuotSMulTop r M ≃ₗ[R] (R ⧸ Ideal.span {r}) ⊗[R] M :=
  quotEquivOfEq _ _ (ideal_span_singleton_smul _ _).symm ≪≫ₗ
   (quotTensorEquivQuotSMul M _).symm

/-- Reducing a module modulo `r` is the same as right tensoring with `R/(r)`. -/
noncomputable def equivTensorQuot :
    QuotSMulTop r M ≃ₗ[R] M ⊗[R] (R ⧸ Ideal.span {r}) :=
  quotEquivOfEq _ _ (ideal_span_singleton_smul _ _).symm ≪≫ₗ
   (tensorQuotEquivQuotSMul M _).symm

variable {M}

/-- The action of the functor `QuotSMulTop r` on morphisms. -/
def map : (M →ₗ[R] M') →ₗ[R] QuotSMulTop r M →ₗ[R] QuotSMulTop r M'  :=
  Submodule.mapQLinear _ _ ∘ₗ LinearMap.id.codRestrict _ fun _ =>
    map_le_iff_le_comap.mp <| le_of_eq_of_le (map_pointwise_smul _ _ _) <|
      smul_mono_right r le_top

@[simp]
lemma map_apply_mk (f : M →ₗ[R] M') (x : M) :
    map r f (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (f x) : QuotSMulTop r M') := rfl

-- weirdly expensive to typecheck the type here?
lemma map_comp_mkQ (f : M →ₗ[R] M') :
    map r f ∘ₗ mkQ (r • ⊤) = mkQ (r • ⊤) ∘ₗ f := by
  ext; rfl

variable (M)

@[simp]
lemma map_id : map r (LinearMap.id : M →ₗ[R] M) = .id :=
  DFunLike.ext _ _ <| (mkQ_surjective _).forall.mpr fun _ => rfl

variable {M}

@[simp]
lemma map_comp (g : M' →ₗ[R] M'') (f : M →ₗ[R] M') :
    map r (g ∘ₗ f) = map r g ∘ₗ map r f :=
  DFunLike.ext _ _ <| (mkQ_surjective _).forall.mpr fun _ => rfl

lemma equivQuotTensor_naturality_mk (f : M →ₗ[R] M') (x : M) :
    equivQuotTensor r M' (map r f (Submodule.Quotient.mk x)) =
      f.lTensor (R ⧸ Ideal.span {r})
        (equivQuotTensor r M (Submodule.Quotient.mk x)) :=
  (LinearMap.lTensor_tmul (R ⧸ Ideal.span {r}) f 1 x).symm

lemma equivQuotTensor_naturality (f : M →ₗ[R] M') :
    equivQuotTensor r M' ∘ₗ map r f =
      f.lTensor (R ⧸ Ideal.span {r}) ∘ₗ equivQuotTensor r M :=
  quot_hom_ext _ _ _ (equivQuotTensor_naturality_mk r f)

lemma equivTensorQuot_naturality_mk (f : M →ₗ[R] M') (x : M) :
    equivTensorQuot r M' (map r f (Submodule.Quotient.mk x)) =
      f.rTensor (R ⧸ Ideal.span {r})
        (equivTensorQuot r M (Submodule.Quotient.mk x)) :=
  (LinearMap.rTensor_tmul (R ⧸ Ideal.span {r}) f 1 x).symm

lemma equivTensorQuot_naturality (f : M →ₗ[R] M') :
    equivTensorQuot r M' ∘ₗ map r f =
      f.rTensor (R ⧸ Ideal.span {r}) ∘ₗ equivTensorQuot r M :=
  quot_hom_ext _ _ _ (equivTensorQuot_naturality_mk r f)

lemma map_surjective {f : M →ₗ[R] M'} (hf : Surjective f) : Surjective (map r f) :=
  have H₁ := (mkQ_surjective (r • ⊤ : Submodule R M')).comp hf
  @Surjective.of_comp _ _ _ _ (mkQ (r • ⊤ : Submodule R M)) <| by
    rwa [← LinearMap.coe_comp, map_comp_mkQ, LinearMap.coe_comp]

lemma map_exact {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hfg : Exact f g) (hg : Surjective g) : Exact (map r f) (map r g) :=
  (Exact.iff_of_ladder_linearEquiv (equivQuotTensor_naturality r f).symm
                             (equivQuotTensor_naturality r g).symm).mp
    (lTensor_exact (R ⧸ Ideal.span {r}) hfg hg)

variable (M M')

/-- Tensoring on the left and applying `QuotSMulTop · r` commute. -/
noncomputable def tensorQuotSMulTopEquivQuotSMulTop :
    M ⊗[R] QuotSMulTop r M' ≃ₗ[R] QuotSMulTop r (M ⊗[R] M') :=
  (equivTensorQuot r M').lTensor M ≪≫ₗ
    (TensorProduct.assoc R M M' (R ⧸ Ideal.span {r})).symm ≪≫ₗ
      (equivTensorQuot r (M ⊗[R] M')).symm

/-- Tensoring on the right and applying `QuotSMulTop · r` commute. -/
noncomputable def quotSMulTopTensorEquivQuotSMulTop :
    QuotSMulTop r M' ⊗[R] M ≃ₗ[R] QuotSMulTop r (M' ⊗[R] M) :=
  (equivQuotTensor r M').rTensor M ≪≫ₗ
    TensorProduct.assoc R (R ⧸ Ideal.span {r}) M' M ≪≫ₗ
      (equivQuotTensor r (M' ⊗[R] M)).symm

variable (S : Type*) [CommRing S] [Algebra R S]

variable {M S} in
theorem _root_.TensorProduct.tsmul_eq_smul_one_tuml (s : S) (m : M) :
    s ⊗ₜ[R] m = s • (1 ⊗ₜ[R] m) := by
  nth_rw 1 [show s = s • 1 from by simp]
  rfl

@[simp]
theorem Submodule.Quotient.mk_out {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {p : Submodule R M} (m : M ⧸ p) : Submodule.Quotient.mk (Quotient.out m) = m :=
  Quotient.out_eq m

/-- Let `R` be a commutative ring, `M` be an `R`-module, `S` be an `R`-algebra, then
  `S ⊗[R] (M/rM)` is isomorphic to `(S ⊗[R] M)⧸r(S ⊗[R] M)` as `S`-modules. -/
noncomputable def tensorQuotSMulTopEquivQuotSMulTopAlgebraMapTensor :
    S ⊗[R] QuotSMulTop r M ≃ₗ[S] QuotSMulTop ((algebraMap R S) r) (S ⊗[R] M) :=
  let f : S ⊗[R] QuotSMulTop r M →ₗ[S] QuotSMulTop ((algebraMap R S) r) (S ⊗[R] M) := by
    apply LinearMap.liftBaseChange S ?_
    apply Submodule.mapQ (r • ⊤) ((algebraMap R S) r • ⊤) (TensorProduct.mk R S M 1) (fun _ ↦ ?_)
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
      Submodule.mem_comap, forall_exists_index]
    intro _ hm
    simp [← hm]
  let N : Submodule S (S ⊗[R] M) := (algebraMap R S) r • ⊤
  have hsm (s : S) (m : M) : N.mkQ (s ⊗ₜ[R] m) = f (s ⊗ₜ[R] Submodule.Quotient.mk m) := by
    simpa [tsmul_eq_smul_one_tuml s m] using by rfl
{ __ := f
  invFun m := LinearMap.lTensor S (Submodule.mkQ (r • ⊤)) (Quotient.out m)
  left_inv := by
    intro m
    have h : (LinearMap.lsmul R (S ⊗[R] QuotSMulTop r M)) r = 0 := by
      apply TensorProduct.ext
      ext s m
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.compr₂_apply, mk_apply,
        LinearMap.lsmul_apply, LinearMap.zero_apply]
      rw [← tmul_smul, show r • _ = (0 : QuotSMulTop r M) from
          (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_pointwise_smul m r ⊤ trivial)]
      exact tmul_zero _ s
    have hx (m : S ⊗[R] QuotSMulTop r M) : r • m = 0 := congrFun (congrArg DFunLike.coe h) m
    induction' m with s m m₁ m₂
    · obtain ⟨b, _, h⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp <|
        (Submodule.Quotient.mk_eq_zero N).mp (Quotient.out_eq (0 : _ ⧸ N))
      simp [← h, hx]
    · have hsm : _ = f (s ⊗ₜ[R] m) := (hsm s (Quotient.out m)).trans (by simp)
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
  right_inv := by
    intro m
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    nth_rw 2 [← Submodule.Quotient.mk_out m]
    induction Quotient.out m
    · simp
    · simp [← hsm]
    · simpa using by congr 1 }

end QuotSMulTop
