/-
Copyright (c) 2024 Richard Copley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Copley, Eric Wieser
-/
import Mathlib.LinearAlgebra.TensorAlgebra.Basis
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
# Instances for the zero-product property in the tensor algebra of a free module

This file provides the following instances:
  * instNoZeroDivisorsMonoidAlgebraFreeMonoid
      If `R` is a semiring with no zero-divisors and `κ` is any type
      then `MonoidAlgebra (FreeMonoid κ) has no zero-divisors.
  * FreeMonoid.instUniqueProds
      The free monoid on any type has the UniqueProds property.
      (This provides `NoZeroDivisors (MonoidAlgebra R (FreeMonoid κ))`, where
      `R` is a semiring and `κ` is any type, via the instance
      `MonoidAlgebra.instNoZeroDivisorsOfUniqueProds`.)
  * FreeAlgebra.instNoZeroDivisors
      If `R` is a commutative semiring with no zero-divisors and `X` is any type
      then `MonoidAlgebra R X` has no zero-divisors.
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

instance FreeMonoid.instUniqueProds {κ : Type*} : UniqueProds (FreeMonoid κ) where
  uniqueMul_of_nonempty := fun ha hb =>
    have max_length {s : Finset (FreeMonoid κ)} (hs : s.Nonempty) :
        ∃ w ∈ s, ∀ u ∈ s, u.length ≤ w.length :=
      ⟨(s.toList.argmax (List.length ∘ FreeMonoid.toList)).get <|
          Option.ne_none_iff_isSome.mp <| fun h => (Finset.nonempty_iff_ne_empty.mp hs) <|
            Finset.toList_eq_nil.mp <| List.argmax_eq_none.mp h,
        Finset.mem_toList.mp <| List.argmax_mem <| Option.get_mem _,
        fun _ hu => List.le_of_mem_argmax (Finset.mem_toList.mpr hu) (Option.get_mem _)⟩
    have ⟨x, hx, hx_spec⟩ := max_length ha
    have ⟨y, hy, hy_spec⟩ := max_length hb
    ⟨x, hx, y, hy, fun u v hu hv h => List.append_inj h <| And.left <| by
      rewrite [← add_eq_add_iff_eq_and_eq (hx_spec u hu) (hy_spec v hv),
        ← List.length_append, ← List.length_append]
      exact congrArg List.length h⟩

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
