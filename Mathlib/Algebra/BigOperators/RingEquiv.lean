/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Opposite

#align_import algebra.big_operators.ring_equiv from "leanprover-community/mathlib"@"008205aa645b3f194c1da47025c5f110c8406eab"

/-!
# Results about mapping big operators across ring equivalences
-/


namespace RingEquiv

variable {α R S : Type*}

protected theorem map_list_prod [Semiring R] [Semiring S] (f : R ≃+* S) (l : List R) :
    f l.prod = (l.map f).prod := map_list_prod f l
#align ring_equiv.map_list_prod RingEquiv.map_list_prod

protected theorem map_list_sum [NonAssocSemiring R] [NonAssocSemiring S] (f : R ≃+* S)
    (l : List R) : f l.sum = (l.map f).sum := map_list_sum f l
#align ring_equiv.map_list_sum RingEquiv.map_list_sum

/-- An isomorphism into the opposite ring acts on the product by acting on the reversed elements -/
protected theorem unop_map_list_prod [Semiring R] [Semiring S] (f : R ≃+* Sᵐᵒᵖ) (l : List R) :
    MulOpposite.unop (f l.prod) = (l.map (MulOpposite.unop ∘ f)).reverse.prod :=
  unop_map_list_prod f l
#align ring_equiv.unop_map_list_prod RingEquiv.unop_map_list_prod

protected theorem map_multiset_prod [CommSemiring R] [CommSemiring S] (f : R ≃+* S)
    (s : Multiset R) : f s.prod = (s.map f).prod :=
  map_multiset_prod f s
#align ring_equiv.map_multiset_prod RingEquiv.map_multiset_prod

protected theorem map_multiset_sum [NonAssocSemiring R] [NonAssocSemiring S] (f : R ≃+* S)
    (s : Multiset R) : f s.sum = (s.map f).sum :=
  map_multiset_sum f s
#align ring_equiv.map_multiset_sum RingEquiv.map_multiset_sum

protected theorem map_prod [CommSemiring R] [CommSemiring S] (g : R ≃+* S) (f : α → R)
    (s : Finset α) : g (∏ x ∈ s, f x) = ∏ x ∈ s, g (f x) :=
  map_prod g f s
#align ring_equiv.map_prod RingEquiv.map_prod

protected theorem map_sum [NonAssocSemiring R] [NonAssocSemiring S] (g : R ≃+* S) (f : α → R)
    (s : Finset α) : g (∑ x ∈ s, f x) = ∑ x ∈ s, g (f x) :=
  map_sum g f s
#align ring_equiv.map_sum RingEquiv.map_sum

end RingEquiv
