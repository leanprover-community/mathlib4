/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.Rank

/-!
# A basis for `TensorAlgebra R M`

## Main definitions

* `TensorAlgebra.equivMonoidAlgebra b : TensorAlgebra R M ≃ₐ[R] MonoidAlgebra R (FreeMonoid κ)`:
  the isomorphism given by a basis `b : Basis κ R M`.
* `Basis.tensorAlgebra b : Basis (FreeMonoid κ) R (TensorAlgebra R M`:
  the basis on the tensor algebra given by a basis `b : Basis κ R M`.

## Main results

* `TensorAlgebra.instFreeModule`: the tensor algebra over `M` is free when `M` is
* `TensorAlgebra.rank_eq`

-/
namespace TensorAlgebra

open scoped BigOperators

universe uκ uR uM
variable {κ : Type uκ} {R : Type uR} {M : Type uM}

section CommSemiring
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A map into the monoid algebra over the free monoid, using the indices of a basis.

This is the forward direction of `TensorAlgebra.equivMonoidAlgebra`. -/
noncomputable def toMonoidAlgebra (b : Basis κ R M) :
    TensorAlgebra R M →ₐ[R] MonoidAlgebra R (FreeMonoid κ) :=
  TensorAlgebra.lift _ (Finsupp.lmapDomain _ _ FreeMonoid.of ∘ₗ b.repr.toLinearMap)

@[simp]
lemma toMonoidAlgebra_ι (b : Basis κ R M) (m : M) :
  toMonoidAlgebra b (ι R m) = (b.repr m).mapDomain FreeMonoid.of := TensorAlgebra.lift_ι_apply _ _

/-- A map from the monoid algebra over the free monoid, using the indices of a basis.

This is the reverse direction of `TensorAlgebra.equivMonoidAlgebra`. -/
noncomputable def ofMonoidAlgebra (b : Basis κ R M) :
    MonoidAlgebra R (FreeMonoid κ) →ₐ[R] TensorAlgebra R M :=
  MonoidAlgebra.lift _ _ _ <| FreeMonoid.lift <| fun i => ι R (b i)

lemma ofMonoidAlgebra_of_of (b : Basis κ R M) (i : κ) :
    ofMonoidAlgebra b (MonoidAlgebra.of _ _ (FreeMonoid.of i)) = ι R (b i) :=
  MonoidAlgebra.lift_of _ _

@[simp] lemma ofMonoidAlgebra_single_one_of (b : Basis κ R M) (i : κ) :
    ofMonoidAlgebra b (MonoidAlgebra.single (FreeMonoid.of i) 1) = ι R (b i) :=
  ofMonoidAlgebra_of_of b i

/-- The tensor algebra is isomorphic as an algebra to the monoid algebra over a free monoid, given
a basis. -/
@[simps!]
noncomputable def equivMonoidAlgebra (b : Basis κ R M) :
    TensorAlgebra R M ≃ₐ[R] MonoidAlgebra R (FreeMonoid κ) :=
  AlgEquiv.ofAlgHom
    (toMonoidAlgebra b)
    (ofMonoidAlgebra b)
    (by ext; simp)
    (hom_ext <| b.ext <| fun i => by simp)

/-- A basis on `M` can be lifted to a basis on `TensorAlgebra R M` -/
@[simps]
noncomputable def _root_.Basis.tensorAlgebra (b : Basis κ R M) :
    Basis (FreeMonoid κ) R (TensorAlgebra R M) :=
  .ofRepr (equivMonoidAlgebra b).toLinearEquiv

/-- `TensorAlgebra R M` is free when `M` is. -/
instance instModuleFree [Module.Free R M] : Module.Free R (TensorAlgebra R M) :=
  let ⟨⟨_κ, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  .of_basis b.tensorAlgebra

end CommSemiring

section CommRing
variable [CommRing R] [AddCommGroup M] [Module R M]

local infixr:80 " ^ℕ " => @HPow.hPow Cardinal ℕ Cardinal _

attribute [pp_with_univ] Cardinal.lift

open Cardinal in
lemma rank_eq [StrongRankCondition R] [Module.Free R M] :
    Module.rank R (TensorAlgebra R M) =
      Cardinal.lift.{uR} (sum fun n : ℕ ↦ Module.rank R M ^ℕ n) := by
  let ⟨⟨κ, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  simp_rw [←Basis.mk_eq_rank'' b, ←Cardinal.mk_list_eq_sum_pow]
  rw [←(Basis.mk_eq_rank'.{_,_,_,max uR uM} b.tensorAlgebra).trans (Cardinal.lift_id _),
    Cardinal.lift_umax'.{uM,uR}, FreeMonoid]

end CommRing

end TensorAlgebra
