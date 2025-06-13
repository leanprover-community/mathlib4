/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles, Zhixuan Dai, Zhenyan Fu, Yiming Fu, Jingting Wang, Eric Wieser
-/
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.RingTheory.MvPolynomial

/-!
# A basis for `SymmetricAlgebra R M`

## Main definitions

* `SymmetricAlgebra.equivMvPolynomial b : SymmetricAlgebra R M ≃ₐ[R] MvPolynomial I R`:
  the isomorphism given by a basis `b : Basis I R M`.
* `Basis.symmetricAlgebra b : Basis (I →₀ ℕ) R (SymmetricAlgebra R M)`:
  the basis on the symmetric algebra given by a basis `b : Basis I R M`.

## Main results

* `SymmetricAlgebra.instFreeModule`: the symmetric algebra over `M` is free when `M` is free.
* `SymmetricAlgebra.rank_eq`: the rank of `SymmetricAlgebra R M` when `M` is a nontrivial free
  module is equal to `max (Module.rank R M) Cardinal.aleph0`.

## Implementation notes

This file closely mirrors the corresponding file for `TensorAlgebra`.
-/

namespace SymmetricAlgebra

universe uκ uR uM
variable {κ : Type uκ} {R : Type uR} {M : Type uM}

section CommSemiring
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- `SymmetricAlgebra.equivMvPolynomial` gives an algebra isomorphism between the symmetric algebra
over a free module and multivariate polynomials over a basis. This is analogous to
`TensorAlgebra.equivFreeAlgebra`. -/
noncomputable def equivMvPolynomial (b : Basis κ R M) :
    SymmetricAlgebra R M ≃ₐ[R] MvPolynomial κ R :=
  .ofAlgHom
    (SymmetricAlgebra.lift <| Basis.constr b R .X)
    (MvPolynomial.aeval fun i ↦ ι R M (b i))
    (MvPolynomial.algHom_ext fun i ↦ by simp)
    (algHom_ext <| b.ext fun i ↦ by simp)

@[simp]
lemma equivMvPolynomial_ι_apply (b : Basis κ R M) (i : κ) :
    equivMvPolynomial b (ι R M (b i)) = .X (R := R) i :=
  (SymmetricAlgebra.lift_ι_apply _ _).trans <| by simp

@[simp]
lemma equivMvPolynomial_symm_X (b : Basis κ R M) (i : κ) :
    (equivMvPolynomial b).symm (MvPolynomial.X i) = ι R M (b i) :=
  (equivMvPolynomial b).toEquiv.symm_apply_eq.mpr <| equivMvPolynomial_ι_apply b i |>.symm

/-- A basis on `M` can be lifted to a basis on `SymmetricAlgebra R M`. -/
@[simps! repr_apply]
noncomputable def _root_.Basis.symmetricAlgebra (b : Basis κ R M) :
    Basis (κ →₀ ℕ) R (SymmetricAlgebra R M) :=
  (MvPolynomial.basisMonomials κ R).map <| (SymmetricAlgebra.equivMvPolynomial b).symm.toLinearEquiv

/-- `SymmetricAlgebra R M` is free when `M` is. -/
instance instModuleFree [Module.Free R M] : Module.Free R (SymmetricAlgebra R M) :=
  let ⟨⟨_I, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  .of_basis b.symmetricAlgebra

/-- The `SymmetricAlgebra` of a free module over a commutative semiring with no zero-divisors has
no zero-divisors. -/
instance instNoZeroDivisors [NoZeroDivisors R] [Module.Free R M] :
    NoZeroDivisors (SymmetricAlgebra R M) :=
  have ⟨⟨_, b⟩⟩ := ‹Module.Free R M›
  (equivMvPolynomial b).toMulEquiv.noZeroDivisors

end CommSemiring

section CommRing
variable [CommRing R] [AddCommGroup M] [Module R M]

/-- The `TensorAlgebra` of a free module over an integral domain is a domain. -/
instance instIsDomain [IsDomain R] [Module.Free R M] : IsDomain (SymmetricAlgebra R M) :=
  NoZeroDivisors.to_isDomain _

attribute [pp_with_univ] Cardinal.lift

open Cardinal in
lemma rank_eq [Nontrivial M] [Module.Free R M] :
    Module.rank R (SymmetricAlgebra R M) = Cardinal.lift.{uR} (max (Module.rank R M) ℵ₀) := by
  let ⟨⟨κ, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  have : Nonempty κ := Basis.index_nonempty b
  have : Nontrivial R := Module.nontrivial R M
  rw [(equivMvPolynomial b).toLinearEquiv.rank_eq, MvPolynomial.rank_eq_lift,
    Cardinal.mk_finsupp_nat, Basis.mk_eq_rank'' b]

end CommRing

end SymmetricAlgebra
