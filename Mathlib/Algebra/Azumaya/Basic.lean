import Mathlib.Algebra.Azumaya.Defs
import Mathlib.Algebra.Central.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.SimpleRing.Matrix

section

open TensorProduct

universe u v

variable (K : Type u) [Field K]

lemma IsSimpleRing.left_of_tensor (B C : Type*)
    [Ring B] [Ring C] [Algebra K C] [Algebra K B]
    [hbc : IsSimpleRing (B ⊗[K] C)] :
    IsSimpleRing B := sorry

lemma IsSimpleRing.right_of_tensor (B C : Type*)
    [Ring B] [Ring C] [Algebra K C] [Algebra K B]
    [hbc : IsSimpleRing (B ⊗[K] C)] :
    IsSimpleRing C := sorry

lemma center_tensorProduct
    (B C : Type*) [Ring B] [Algebra K B] [Ring C] [Algebra K C] :
    Subalgebra.center K (B ⊗[K] C) =
      (Algebra.TensorProduct.map (Subalgebra.center K B).val
        (Subalgebra.center K C).val).range := by sorry

lemma IsCentral.left_of_tensor (B C : Type*)
    [Ring B] [Ring C] [Nontrivial B] [Nontrivial C] [Algebra K C] [Algebra K B]
    [hbc : Algebra.IsCentral K (B ⊗[K] C)] :
    Algebra.IsCentral K B := by
  letI : Nontrivial (B ⊗[K] C) := sorry
  have h := (Subalgebra.equivOfEq (R := K) (A := B ⊗[K] C) _ _ <|
    hbc.center_eq_bot K (B ⊗[K] C)) |>.trans <| Algebra.botEquiv K (B ⊗[K] C)
  rw [center_tensorProduct, Algebra.TensorProduct.map_range] at h
  sorry

lemma IsSimpleRing.ofAlgEquiv (A B : Type*) [Ring A] [Ring B] [Algebra K A] [Algebra K B]
    (e : A ≃ₐ[K] B) (hA : IsSimpleRing A) : IsSimpleRing B := sorry

lemma bijective_of_dim_eq_of_isCentralSimple
    (A B : Type*) [Ring A] [Ring B] [Algebra K A] [Algebra K B] [csa_source : IsSimpleRing A]
    [fin_source : FiniteDimensional K A]
    [fin_target : FiniteDimensional K B]
    (f : A →ₐ[K] B) (h : Module.finrank K A = Module.finrank K B) :
    Function.Bijective f := by
  obtain hA|hA := subsingleton_or_nontrivial A
  · have eq1 : Module.finrank K A = 0 := by
      rw [finrank_zero_iff_forall_zero]
      intro x
      apply Subsingleton.elim
    rw [eq1] at h
    replace h : Subsingleton B := by
      constructor
      symm at h
      rw [finrank_zero_iff_forall_zero] at h
      intro a b
      rw [h a, h b]
    rw [Function.bijective_iff_existsUnique]
    intro b
    refine ⟨0, Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩
  sorry
  -- · have := IsSimpleRing.iff_injective_ringHom_or_subsingleton_codomain A |>.1 csa_source
  --     f.toRingHom
  --   rcases this with (H|H)
  --   · refine ⟨H, ?_⟩
  --     change Function.Surjective f.toLinearMap
  --     have := f.toLinearMap.finrank_range_add_finrank_ker
  --     rw [show Module.finrank K (LinearMap.ker f.toLinearMap) = 0 by
  --       rw [finrank_zero_iff_forall_zero]
  --       rintro ⟨x, hx⟩
  --       rw [LinearMap.ker_eq_bot (f := f.toLinearMap) |>.2 H] at hx
  --       ext
  --       exact hx, add_zero, h] at this
  --     rw [← LinearMap.range_eq_top]

  --     apply Submodule.eq_top_of_finrank_eq
  --     exact this
  --   · have : (1 : A) ∈ TwoSidedIdeal.ker f.toRingHom := by
  --       simp only [AlgHom.toRingHom_eq_coe, TwoSidedIdeal.mem_ker, RingHom.coe_coe, map_one]
  --       exact Subsingleton.elim _ _
  --     simp only [AlgHom.toRingHom_eq_coe, TwoSidedIdeal.mem_ker, map_one] at this
  --     have hmm : Nontrivial B := by
  --       let e := LinearEquiv.ofFinrankEq _ _ h
  --       exact Equiv.nontrivial e.symm.toEquiv

  --     exact one_ne_zero this |>.elim
lemma dim_eq (A : Type*) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] :
    Module.finrank K (A ⊗[K] Aᵐᵒᵖ) = Module.finrank K (Module.End K A) := by
  rw [Module.finrank_tensorProduct]
  rw [show Module.finrank K (Module.End K A) =
    Module.finrank K (Matrix (Fin <| Module.finrank K A) (Fin <| Module.finrank K A) K) from
    (algEquivMatrix <| Module.finBasis _ _).toLinearEquiv.finrank_eq]
  rw [Module.finrank_matrix, Fintype.card_fin]
  rw [show Module.finrank K Aᵐᵒᵖ = Module.finrank K A from
    (MulOpposite.opLinearEquiv K : A ≃ₗ[K] Aᵐᵒᵖ).symm.finrank_eq]
  simp only [Module.finrank_self, mul_one]

noncomputable def equivEnd (A : Type*) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A]: A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Module.End K A :=
  AlgEquiv.ofBijective (TensorProduct.Algebra.moduleAux' K A) <| sorry
  -- bijective_of_dim_eq_of_isCentralSimple _ _ _ _ <|
  --   dim_eq K A
end

section Field

variable (F A : Type*) [Field F] [Ring A] [Algebra F A]

open TensorProduct

lemma Algebra.IsCentral_ofAlgEquiv (A B : Type*) [Ring A] [Ring B] [Algebra F A] [Algebra F B]
    (e : A ≃ₐ[F] B) (hA : Algebra.IsCentral F A):  Algebra.IsCentral F B where
  out x hx := by
    obtain ⟨k, hk⟩ := hA.1 (show e.symm x ∈ _ by
      simp only [Subalgebra.mem_center_iff] at hx ⊢
      exact fun x => by simpa using congr(e.symm $(hx (e x))))
    exact ⟨k, by apply_fun e.symm; rw [← hk]; simp [ofId_apply]⟩


theorem IsAzumaya_iff_CentralSimple [Nontrivial A]: IsAzumaya F A ↔ FiniteDimensional F A ∧
    Algebra.IsCentral F A ∧ IsSimpleRing A :=
  ⟨fun ⟨bij⟩ ↦
    letI e := AlgEquiv.ofBijective _ bij|>.trans <| algEquivMatrix <| Module.finBasis _ _
    letI : Nonempty (Fin (Module.finrank F A)) := ⟨⟨_, Module.finrank_pos⟩⟩
    ⟨IsAzumaya.toFinite, ⟨by
    have : Algebra.IsCentral F (A ⊗[F] Aᵐᵒᵖ) :=
      Algebra.IsCentral_ofAlgEquiv F _ _ e.symm <| Algebra.IsCentral.matrix F F
        (Fin (Module.finrank F A))
    exact IsCentral.left_of_tensor F A Aᵐᵒᵖ, by
    haveI := IsSimpleRing.matrix (Fin (Module.finrank F A)) F
    have sim : IsSimpleRing (A ⊗[F] Aᵐᵒᵖ) := IsSimpleRing.ofAlgEquiv F _ _ e.symm this
    exact IsSimpleRing.left_of_tensor F A Aᵐᵒᵖ⟩⟩,
    fun ⟨fin, cen, sim⟩ ↦ {
      out := Module.Projective.out
      eq_of_smul_eq_smul {k1} {k2} ha := by
        specialize ha (1 : A)
        rw [← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one] at ha
        exact NoZeroSMulDivisors.algebraMap_injective _ _ ha
      fg_top := fin.1
      bij := sorry
    }⟩

end Field
