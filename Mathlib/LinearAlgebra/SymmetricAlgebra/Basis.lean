/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles, Zhixuan Dai, Zhenyan Fu, Yiming Fu, Jingting Wang
-/
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.RingTheory.MvPolynomial

/-!
# Main Definitions

1. `SymmetricAlgebra.equivMvPolynomial` give an algebra isomorphism between symmetric algebra over a
  free module and multivariate polynomial over the basis, which is analogous to
  `TensorAlgebra.equivFreeAlgebra`.
-/

universe uR uM

namespace SymmetricAlgebra

section equivMvPolynomial

variable {R : Type uR} {M : Type uM} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- `SymmetricAlgebra.equivMvPolynomial` give an algebra isomorphism between symmetric algebra over
a free module and multivariate polynomial over the basis. -/
noncomputable def equivMvPolynomial {I : Type*} (b : Basis I R M) :
    SymmetricAlgebra R M ≃ₐ[R] MvPolynomial I R :=
  .ofAlgHom
    (SymmetricAlgebra.lift <| Basis.constr b R .X)
    (MvPolynomial.aeval fun i ↦ ι R M (b i))
    (MvPolynomial.algHom_ext fun i ↦ by simp)
    (algHom_ext <| b.ext fun i ↦ by simp)

@[simp]
lemma equivMvPolynomial_ι_apply {I : Type*} (b : Basis I R M) (i : I) :
    equivMvPolynomial b (ι R M (b i)) = .X (R := R) i :=
  (SymmetricAlgebra.lift_ι_apply _ _).trans <| by simp

@[simp]
lemma equivMvPolynomial_symm_X {I : Type*} (b : Basis I R M) (i : I) :
    (equivMvPolynomial b).symm (MvPolynomial.X i) = ι R M (b i) :=
  (equivMvPolynomial b).toEquiv.symm_apply_eq.mpr <| equivMvPolynomial_ι_apply b i |>.symm

end equivMvPolynomial

section Basis

variable {R : Type uR} {M : Type uM} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A basis on `M` can be lifted to a basis on `SymmetricAlgebra R M`. -/
@[simps! repr_apply]
noncomputable def _root_.Basis.symmetricAlgebra {I : Type*} (b : Basis I R M) :
    Basis (I →₀ ℕ) R (SymmetricAlgebra R M) :=
  (MvPolynomial.basisMonomials I R).map <| (SymmetricAlgebra.equivMvPolynomial b).symm.toLinearEquiv

/-- `SymmetricAlgebra R M` is free when `M` is. -/
instance instModuleFree [Module.Free R M] : Module.Free R (SymmetricAlgebra R M) :=
  let ⟨⟨_I, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  .of_basis b.symmetricAlgebra

end Basis

section rank

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

open Cardinal in
lemma rank_eq [Nontrivial R] [Nontrivial M] [Module.Free R M] :
    Module.rank R (SymmetricAlgebra R M) =
      Cardinal.lift.{uR} (max (Module.rank R M) Cardinal.aleph0) := by
  let ⟨⟨I, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  have : Nonempty I := Basis.index_nonempty b
  rw [(equivMvPolynomial b).toLinearEquiv.rank_eq, MvPolynomial.rank_eq_lift,
    Cardinal.mk_finsupp_nat, Basis.mk_eq_rank'' b]

end rank

end SymmetricAlgebra
