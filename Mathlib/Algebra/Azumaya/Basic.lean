import Mathlib.Algebra.Azumaya.Defs
import Mathlib.Algebra.Central.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin

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
    ⟨fg, ⟨by
    have : Algebra.IsCentral F (A ⊗[F] Aᵐᵒᵖ) :=
      Algebra.IsCentral_ofAlgEquiv F _ _ e.symm <| Algebra.IsCentral.matrix F F
        (Fin (Module.finrank F A))

    sorry, sorry⟩⟩, sorry⟩

end Field
