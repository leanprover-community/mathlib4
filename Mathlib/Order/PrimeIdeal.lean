/-
Copyright (c) 2021 Noam Atar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noam Atar

! This file was ported from Lean 3 source module order.prime_ideal
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Ideal
import Mathbin.Order.Pfilter

/-!
# Prime ideals

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections require more
structure, such as a bottom element, a top element, or a join-semilattice structure.

- `order.ideal.prime_pair`: A pair of an `ideal` and a `pfilter` which form a partition of `P`.
  This is useful as giving the data of a prime ideal is the same as giving the data of a prime
  filter.
- `order.ideal.is_prime`: a predicate for prime ideals. Dual to the notion of a prime filter.
- `order.pfilter.is_prime`: a predicate for prime filters. Dual to the notion of a prime ideal.

## References

- <https://en.wikipedia.org/wiki/Ideal_(order_theory)>

## Tags

ideal, prime

-/


open Order.Pfilter

namespace Order

variable {P : Type _}

namespace Ideal

/-- A pair of an `ideal` and a `pfilter` which form a partition of `P`.
-/
@[nolint has_nonempty_instance]
structure PrimePair (P : Type _) [Preorder P] where
  i : Ideal P
  f : Pfilter P
  isCompl_i_f : IsCompl (I : Set P) F
#align order.ideal.prime_pair Order.Ideal.PrimePair

namespace PrimePair

variable [Preorder P] (IF : PrimePair P)

theorem compl_i_eq_f : (IF.i : Set P)ᶜ = IF.f :=
  IF.isCompl_i_f.compl_eq
#align order.ideal.prime_pair.compl_I_eq_F Order.Ideal.PrimePair.compl_i_eq_f

theorem compl_f_eq_i : (IF.f : Set P)ᶜ = IF.i :=
  IF.isCompl_i_f.eq_compl.symm
#align order.ideal.prime_pair.compl_F_eq_I Order.Ideal.PrimePair.compl_f_eq_i

theorem i_isProper : IsProper IF.i := by
  cases IF.F.nonempty
  apply is_proper_of_not_mem (_ : w ∉ IF.I)
  rwa [← IF.compl_I_eq_F] at h
#align order.ideal.prime_pair.I_is_proper Order.Ideal.PrimePair.i_isProper

theorem disjoint : Disjoint (IF.i : Set P) IF.f :=
  IF.isCompl_i_f.Disjoint
#align order.ideal.prime_pair.disjoint Order.Ideal.PrimePair.disjoint

theorem i_union_f : (IF.i : Set P) ∪ IF.f = Set.univ :=
  IF.isCompl_i_f.sup_eq_top
#align order.ideal.prime_pair.I_union_F Order.Ideal.PrimePair.i_union_f

theorem f_union_i : (IF.f : Set P) ∪ IF.i = Set.univ :=
  IF.isCompl_i_f.symm.sup_eq_top
#align order.ideal.prime_pair.F_union_I Order.Ideal.PrimePair.f_union_i

end PrimePair

/-- An ideal `I` is prime if its complement is a filter.
-/
@[mk_iff]
class IsPrime [Preorder P] (I : Ideal P) extends IsProper I : Prop where
  compl_filter : IsPfilter ((I : Set P)ᶜ)
#align order.ideal.is_prime Order.Ideal.IsPrime

section Preorder

variable [Preorder P]

/-- Create an element of type `order.ideal.prime_pair` from an ideal satisfying the predicate
`order.ideal.is_prime`. -/
def IsPrime.toPrimePair {I : Ideal P} (h : IsPrime I) : PrimePair P :=
  { i
    f := h.compl_filter.toPfilter
    isCompl_i_f := isCompl_compl }
#align order.ideal.is_prime.to_prime_pair Order.Ideal.IsPrime.toPrimePair

theorem PrimePair.i_isPrime (IF : PrimePair P) : IsPrime IF.i :=
  { IF.i_isProper with
    compl_filter := by
      rw [IF.compl_I_eq_F]
      exact IF.F.is_pfilter }
#align order.ideal.prime_pair.I_is_prime Order.Ideal.PrimePair.i_isPrime

end Preorder

section SemilatticeInf

variable [SemilatticeInf P] {x y : P} {I : Ideal P}

theorem IsPrime.mem_or_mem (hI : IsPrime I) {x y : P} : x ⊓ y ∈ I → x ∈ I ∨ y ∈ I :=
  by
  contrapose!
  let F := hI.compl_filter.to_pfilter
  show x ∈ F ∧ y ∈ F → x ⊓ y ∈ F
  exact fun h => inf_mem h.1 h.2
#align order.ideal.is_prime.mem_or_mem Order.Ideal.IsPrime.mem_or_mem

theorem IsPrime.of_mem_or_mem [IsProper I] (hI : ∀ {x y : P}, x ⊓ y ∈ I → x ∈ I ∨ y ∈ I) :
    IsPrime I := by
  rw [is_prime_iff]
  use ‹_›
  apply is_pfilter.of_def
  · exact Set.nonempty_compl.2 (I.is_proper_iff.1 ‹_›)
  · intro x _ y _
    refine' ⟨x ⊓ y, _, inf_le_left, inf_le_right⟩
    have := mt hI
    tauto
  · exact @mem_compl_of_ge _ _ _
#align order.ideal.is_prime.of_mem_or_mem Order.Ideal.IsPrime.of_mem_or_mem

theorem isPrime_iff_mem_or_mem [IsProper I] : IsPrime I ↔ ∀ {x y : P}, x ⊓ y ∈ I → x ∈ I ∨ y ∈ I :=
  ⟨IsPrime.mem_or_mem, IsPrime.of_mem_or_mem⟩
#align order.ideal.is_prime_iff_mem_or_mem Order.Ideal.isPrime_iff_mem_or_mem

end SemilatticeInf

section DistribLattice

variable [DistribLattice P] {I : Ideal P}

instance (priority := 100) IsMaximal.isPrime [IsMaximal I] : IsPrime I :=
  by
  rw [is_prime_iff_mem_or_mem]
  intro x y
  contrapose!
  rintro ⟨hx, hynI⟩ hxy
  apply hynI
  let J := I ⊔ principal x
  have hJuniv : (J : Set P) = Set.univ :=
    is_maximal.maximal_proper (lt_sup_principal_of_not_mem ‹_›)
  have hyJ : y ∈ ↑J := set.eq_univ_iff_forall.mp hJuniv y
  rw [coe_sup_eq] at hyJ
  rcases hyJ with ⟨a, ha, b, hb, hy⟩
  rw [hy]
  refine' sup_mem ha (I.lower (le_inf hb _) hxy)
  rw [hy]
  exact le_sup_right
#align order.ideal.is_maximal.is_prime Order.Ideal.IsMaximal.isPrime

end DistribLattice

section BooleanAlgebra

variable [BooleanAlgebra P] {x : P} {I : Ideal P}

theorem IsPrime.mem_or_compl_mem (hI : IsPrime I) : x ∈ I ∨ xᶜ ∈ I :=
  by
  apply hI.mem_or_mem
  rw [inf_compl_eq_bot]
  exact I.bot_mem
#align order.ideal.is_prime.mem_or_compl_mem Order.Ideal.IsPrime.mem_or_compl_mem

theorem IsPrime.mem_compl_of_not_mem (hI : IsPrime I) (hxnI : x ∉ I) : xᶜ ∈ I :=
  hI.mem_or_compl_mem.resolve_left hxnI
#align order.ideal.is_prime.mem_compl_of_not_mem Order.Ideal.IsPrime.mem_compl_of_not_mem

theorem isPrime_of_mem_or_compl_mem [IsProper I] (h : ∀ {x : P}, x ∈ I ∨ xᶜ ∈ I) : IsPrime I :=
  by
  simp only [is_prime_iff_mem_or_mem, or_iff_not_imp_left]
  intro x y hxy hxI
  have hxcI : xᶜ ∈ I := h.resolve_left hxI
  have ass : x ⊓ y ⊔ y ⊓ xᶜ ∈ I := sup_mem hxy (I.lower inf_le_right hxcI)
  rwa [inf_comm, sup_inf_inf_compl] at ass
#align order.ideal.is_prime_of_mem_or_compl_mem Order.Ideal.isPrime_of_mem_or_compl_mem

theorem isPrime_iff_mem_or_compl_mem [IsProper I] : IsPrime I ↔ ∀ {x : P}, x ∈ I ∨ xᶜ ∈ I :=
  ⟨fun h _ => h.mem_or_compl_mem, isPrime_of_mem_or_compl_mem⟩
#align order.ideal.is_prime_iff_mem_or_compl_mem Order.Ideal.isPrime_iff_mem_or_compl_mem

instance (priority := 100) IsPrime.isMaximal [IsPrime I] : IsMaximal I :=
  by
  simp only [is_maximal_iff, Set.eq_univ_iff_forall, is_prime.to_is_proper, true_and_iff]
  intro J hIJ x
  rcases Set.exists_of_ssubset hIJ with ⟨y, hyJ, hyI⟩
  suffices ass : x ⊓ y ⊔ x ⊓ yᶜ ∈ J
  · rwa [sup_inf_inf_compl] at ass
  exact
    sup_mem (J.lower inf_le_right hyJ)
      (hIJ.le <| I.lower inf_le_right <| is_prime.mem_compl_of_not_mem ‹_› hyI)
#align order.ideal.is_prime.is_maximal Order.Ideal.IsPrime.isMaximal

end BooleanAlgebra

end Ideal

namespace Pfilter

variable [Preorder P]

/-- A filter `F` is prime if its complement is an ideal.
-/
@[mk_iff]
class IsPrime (F : Pfilter P) : Prop where
  compl_ideal : IsIdeal ((F : Set P)ᶜ)
#align order.pfilter.is_prime Order.Pfilter.IsPrime

/-- Create an element of type `order.ideal.prime_pair` from a filter satisfying the predicate
`order.pfilter.is_prime`. -/
def IsPrime.toPrimePair {F : Pfilter P} (h : IsPrime F) : Ideal.PrimePair P :=
  { i := h.compl_ideal.toIdeal
    f
    isCompl_i_f := isCompl_compl.symm }
#align order.pfilter.is_prime.to_prime_pair Order.Pfilter.IsPrime.toPrimePair

theorem Order.Ideal.PrimePair.f_isPrime (IF : Ideal.PrimePair P) : IsPrime IF.f :=
  {
    compl_ideal := by
      rw [IF.compl_F_eq_I]
      exact IF.I.is_ideal }
#align order.ideal.prime_pair.F_is_prime Order.Ideal.PrimePair.f_isPrime

end Pfilter

end Order

