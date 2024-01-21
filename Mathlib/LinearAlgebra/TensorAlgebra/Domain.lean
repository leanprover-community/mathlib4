/-
Copyright (c) 2024 Richard Copley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Copley
-/
import Mathlib.LinearAlgebra.TensorAlgebra.Basis

/-!
# Instances for the zero-product property in the tensor algebra of a free module

This file provides the following instances:
  * instNoZeroDivisorsMonoidAlgebraFreeMonoid
      If `R` is a semiring with no zero-divisors and `κ` is a type with
      decidable equality then `MonoidAlgebra (FreeMonoid κ) has no zero-divisors.
  * TensorAlgebra.instNoZeroDivisors
      If `R` is a commutative semiring with no zero-divisors and `M` is a
      free `Module` over `R` then `TensorAlgebra R M` has no zero-divisors.
  * TensorAlgebra.instIsDomain
      If `R` is an integral domain and `M` is a free module over `R` then
      `TensorAlgebra R M` is a domain.
-/

-- Following https://math.stackexchange.com/a/75219/411545 by Mariano Suárez-Álvarez

noncomputable section
suppress_compilation

open FreeMonoid in
instance instNoZeroDivisorsMonoidAlgebraFreeMonoid {R : Type*} [Semiring R] [NoZeroDivisors R]
    {κ : Type*} : NoZeroDivisors (MonoidAlgebra R (FreeMonoid κ)) where
  eq_zero_or_eq_zero_of_mul_eq_zero := fun hxy =>
    letI := Classical.decEq κ
    or_iff_not_and_not.mpr <| not_and.mpr <| fun hx hy => not_not.mpr hxy <| by
    haveI : DecidableEq (FreeMonoid κ) := inferInstanceAs (DecidableEq (List κ))
    have max_length {x : MonoidAlgebra R (FreeMonoid κ)} (hx : x ≠ 0) :
        ∃ w ∈ x.support, ∀ u ∈ x.support, u.length ≤ w.length :=
      ⟨(x.support.toList.argmax (List.length ∘ FreeMonoid.toList)).get <|
          Option.ne_none_iff_isSome.mp <| fun h => hx <| Finsupp.support_eq_empty.mp <|
            Finset.toList_eq_nil.mp <| List.argmax_eq_none.mp <| h,
        Finset.mem_toList.mp <| List.argmax_mem <| Option.get_mem _,
        fun _ hu => List.le_of_mem_argmax (Finset.mem_toList.mpr hu) (Option.get_mem _)⟩
    have ⟨xmax, hxmax_mem, hxmax_spec⟩ := max_length hx
    have ⟨ymax, hymax_mem, hymax_spec⟩ := max_length hy
    refine Finsupp.support_nonempty_iff.mp ⟨xmax * ymax, ?_⟩
    rewrite [MonoidAlgebra.mul_def]
    unfold Finsupp.sum
    rewrite [← Finset.sum_product', Finsupp.mem_support_iff, ← Finsupp.applyAddHom_apply,
      map_sum, Finset.sum_congr rfl (fun _ _ => by
        rw [Finsupp.applyAddHom_apply, MonoidAlgebra.single_apply]),
      Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_eq_single_of_mem (xmax, ymax) ?mem (fun p => ?zero)]
    case mem
    · rewrite [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hxmax_mem, hymax_mem⟩, rfl⟩
    case zero
    · rewrite [Finset.mem_filter, Finset.mem_product, ne_eq, Prod.ext_iff.not]
      refine fun ⟨⟨hmem₁, hmem₂⟩, heq⟩ hne => False.elim <| hne <| List.append_inj heq ?_
      apply And.left
      rewrite [← toList.apply_eq_iff_eq, toList_mul, toList_mul] at heq
      rewrite [← add_eq_add_iff_eq_and_eq (hxmax_spec _ hmem₁) (hymax_spec _ hmem₂),
        ← List.length_append, ← List.length_append]
      exact congrArg List.length heq
    exact mul_ne_zero
      (Finsupp.mem_support_iff.mp hxmax_mem) (Finsupp.mem_support_iff.mp hymax_mem)

instance FreeAlgebra.instNoZeroDivisors {R X : Type*} [CommSemiring R] [NoZeroDivisors R] :
      NoZeroDivisors (FreeAlgebra R X) :=
    FreeAlgebra.equivMonoidAlgebraFreeMonoid.toMulEquiv.noZeroDivisors
namespace TensorAlgebra

instance instNoZeroDivisors {R M : Type*} [CommSemiring R] [NoZeroDivisors R]
    [AddCommMonoid M] [Module R M] [Module.Free R M] :
    NoZeroDivisors (TensorAlgebra R M) :=
  have ⟨⟨κ, b⟩⟩ := ‹Module.Free R M›
  (equivFreeAlgebra b).toMulEquiv.noZeroDivisors

instance instIsDomain {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommMonoid M] [Module R M] [Module.Free R M] :
    IsDomain (TensorAlgebra R M) :=
  NoZeroDivisors.to_isDomain _

end TensorAlgebra
end
