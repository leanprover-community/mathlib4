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
  ⟨fun ⟨fg, bij⟩ ↦
    letI e := AlgEquiv.ofBijective _ bij|>.trans <| algEquivMatrix <| Module.finBasis _ _
    letI : Nonempty (Fin (Module.finrank F A)) := ⟨⟨_, Module.finrank_pos⟩⟩
    ⟨fg, ⟨by
    have : Algebra.IsCentral F (A ⊗[F] Aᵐᵒᵖ) :=
      Algebra.IsCentral_ofAlgEquiv F _ _ e.symm <| Algebra.IsCentral.matrix F F
        (Fin (Module.finrank F A))
    exact IsCentral.left_of_tensor F A Aᵐᵒᵖ, by
    haveI := IsSimpleRing.matrix (Fin (Module.finrank F A)) F
    have sim : IsSimpleRing (A ⊗[F] Aᵐᵒᵖ) := IsSimpleRing.ofAlgEquiv F _ _ e.symm this
    exact IsSimpleRing.left_of_tensor F A Aᵐᵒᵖ⟩⟩,
    fun ⟨fin, cen, sim⟩ ↦ sorry⟩

end Field
