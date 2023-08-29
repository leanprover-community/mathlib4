/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.Rank
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.FreeAlgebra

/-!
# A basis for `TensorAlgebra R M`

## Main definitions

* `TensorAlgebra.equivMonoidAlgebra b : TensorAlgebra R M ≃ₐ[R] FreeAlgebra R κ`:
  the isomorphism given by a basis `b : Basis κ R M`.
* `Basis.tensorAlgebra b : Basis (FreeMonoid κ) R (TensorAlgebra R M)`:
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

/-- A basis provides an algebra isomorphism with the free algebra, replacing each basis vector
with its index. -/
noncomputable def equivFreeAlgebra (b : Basis κ R M) :
    TensorAlgebra R M ≃ₐ[R] FreeAlgebra R κ :=
  AlgEquiv.ofAlgHom
    (TensorAlgebra.lift _ (Finsupp.total _ _ _ (FreeAlgebra.ι _) ∘ₗ b.repr.toLinearMap))
    (FreeAlgebra.lift _ (ι R ∘ b))
    (by ext; simp)
        -- ⊢ (↑(AlgHom.comp (↑(lift R) (LinearMap.comp (Finsupp.total κ (FreeAlgebra R κ) …
             -- 🎉 no goals
    (hom_ext <| b.ext <| fun i => by simp)
                                     -- 🎉 no goals

@[simp]
lemma equivFreeAlgebra_ι_apply (b : Basis κ R M) (i : κ) :
    equivFreeAlgebra b (ι R (b i)) = FreeAlgebra.ι R i :=
  (TensorAlgebra.lift_ι_apply _ _).trans <| by simp
                                               -- 🎉 no goals

@[simp]
lemma equivFreeAlgebra_symm_ι (b : Basis κ R M) (i : κ) :
    (equivFreeAlgebra b).symm (FreeAlgebra.ι R i) = ι R (b i) :=
  (equivFreeAlgebra b).toEquiv.symm_apply_eq.mpr <| equivFreeAlgebra_ι_apply b i |>.symm

/-- A basis on `M` can be lifted to a basis on `TensorAlgebra R M` -/
@[simps! repr_apply]
noncomputable def _root_.Basis.tensorAlgebra (b : Basis κ R M) :
    Basis (FreeMonoid κ) R (TensorAlgebra R M) :=
  (FreeAlgebra.basisFreeMonoid R κ).map <| (equivFreeAlgebra b).symm.toLinearEquiv

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
lemma rank_eq [Nontrivial R] [Module.Free R M] :
    Module.rank R (TensorAlgebra R M) = Cardinal.lift.{uR} (sum fun n ↦ Module.rank R M ^ℕ n) := by
  let ⟨⟨κ, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  -- ⊢ Module.rank R (TensorAlgebra R M) = Cardinal.lift.{uR, uM} (sum fun n => Mod …
  rw [(equivFreeAlgebra b).toLinearEquiv.rank_eq, FreeAlgebra.rank_eq, mk_list_eq_sum_pow,
    Basis.mk_eq_rank'' b]

end CommRing

end TensorAlgebra
