/-
Copyright (c) 2021 Noam Atar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noam Atar
-/
import Mathlib.Order.Ideal
import Mathlib.Order.PFilter

#align_import order.prime_ideal from "leanprover-community/mathlib"@"740acc0e6f9adf4423f92a485d0456fc271482da"

/-!
# Prime ideals

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections require more
structure, such as a bottom element, a top element, or a join-semilattice structure.

- `Order.Ideal.PrimePair`: A pair of an `Order.Ideal` and an `Order.PFilter` which form a partition
  of `P`.  This is useful as giving the data of a prime ideal is the same as giving the data of a
  prime filter.
- `Order.Ideal.IsPrime`: a predicate for prime ideals. Dual to the notion of a prime filter.
- `Order.PFilter.IsPrime`: a predicate for prime filters. Dual to the notion of a prime ideal.

## References

- <https://en.wikipedia.org/wiki/Ideal_(order_theory)>

## Tags

ideal, prime

-/


open Order.PFilter

namespace Order

variable {P : Type*}

namespace Ideal

/-- A pair of an `Order.Ideal` and an `Order.PFilter` which form a partition of `P`.
-/
-- Porting note(#5171): this linter isn't ported yet.
-- @[nolint has_nonempty_instance]
structure PrimePair (P : Type*) [Preorder P] where
  I : Ideal P
  F : PFilter P
  isCompl_I_F : IsCompl (I : Set P) F
#align order.ideal.prime_pair Order.Ideal.PrimePair

namespace PrimePair

variable [Preorder P] (IF : PrimePair P)

theorem compl_I_eq_F : (IF.I : Set P)ᶜ = IF.F :=
  IF.isCompl_I_F.compl_eq
set_option linter.uppercaseLean3 false in
#align order.ideal.prime_pair.compl_I_eq_F Order.Ideal.PrimePair.compl_I_eq_F

theorem compl_F_eq_I : (IF.F : Set P)ᶜ = IF.I :=
  IF.isCompl_I_F.eq_compl.symm
set_option linter.uppercaseLean3 false in
#align order.ideal.prime_pair.compl_F_eq_I Order.Ideal.PrimePair.compl_F_eq_I

theorem I_isProper : IsProper IF.I := by
  cases' IF.F.nonempty with w h
  apply isProper_of_not_mem (_ : w ∉ IF.I)
  rwa [← IF.compl_I_eq_F] at h
set_option linter.uppercaseLean3 false in
#align order.ideal.prime_pair.I_is_proper Order.Ideal.PrimePair.I_isProper

protected theorem disjoint : Disjoint (IF.I : Set P) IF.F :=
  IF.isCompl_I_F.disjoint
#align order.ideal.prime_pair.disjoint Order.Ideal.PrimePair.disjoint

theorem I_union_F : (IF.I : Set P) ∪ IF.F = Set.univ :=
  IF.isCompl_I_F.sup_eq_top
set_option linter.uppercaseLean3 false in
#align order.ideal.prime_pair.I_union_F Order.Ideal.PrimePair.I_union_F

theorem F_union_I : (IF.F : Set P) ∪ IF.I = Set.univ :=
  IF.isCompl_I_F.symm.sup_eq_top
set_option linter.uppercaseLean3 false in
#align order.ideal.prime_pair.F_union_I Order.Ideal.PrimePair.F_union_I

end PrimePair

/-- An ideal `I` is prime if its complement is a filter.
-/
@[mk_iff]
class IsPrime [Preorder P] (I : Ideal P) extends IsProper I : Prop where
  compl_filter : IsPFilter (I : Set P)ᶜ
#align order.ideal.is_prime Order.Ideal.IsPrime

section Preorder

variable [Preorder P]

/-- Create an element of type `Order.Ideal.PrimePair` from an ideal satisfying the predicate
`Order.Ideal.IsPrime`. -/
def IsPrime.toPrimePair {I : Ideal P} (h : IsPrime I) : PrimePair P :=
  { I
    F := h.compl_filter.toPFilter
    isCompl_I_F := isCompl_compl }
#align order.ideal.is_prime.to_prime_pair Order.Ideal.IsPrime.toPrimePair

theorem PrimePair.I_isPrime (IF : PrimePair P) : IsPrime IF.I :=
  { IF.I_isProper with
    compl_filter := by
      rw [IF.compl_I_eq_F]
      exact IF.F.isPFilter }
set_option linter.uppercaseLean3 false in
#align order.ideal.prime_pair.I_is_prime Order.Ideal.PrimePair.I_isPrime

end Preorder

section SemilatticeInf

variable [SemilatticeInf P] {x y : P} {I : Ideal P}

theorem IsPrime.mem_or_mem (hI : IsPrime I) {x y : P} : x ⊓ y ∈ I → x ∈ I ∨ y ∈ I := by
  contrapose!
  let F := hI.compl_filter.toPFilter
  show x ∈ F ∧ y ∈ F → x ⊓ y ∈ F
  exact fun h => inf_mem h.1 h.2
#align order.ideal.is_prime.mem_or_mem Order.Ideal.IsPrime.mem_or_mem

theorem IsPrime.of_mem_or_mem [IsProper I] (hI : ∀ {x y : P}, x ⊓ y ∈ I → x ∈ I ∨ y ∈ I) :
    IsPrime I := by
  rw [isPrime_iff]
  use ‹_›
  refine .of_def ?_ ?_ ?_
  · exact Set.nonempty_compl.2 (I.isProper_iff.1 ‹_›)
  · intro x hx y hy
    exact ⟨x ⊓ y, fun h => (hI h).elim hx hy, inf_le_left, inf_le_right⟩
  · exact @mem_compl_of_ge _ _ _
#align order.ideal.is_prime.of_mem_or_mem Order.Ideal.IsPrime.of_mem_or_mem

theorem isPrime_iff_mem_or_mem [IsProper I] : IsPrime I ↔ ∀ {x y : P}, x ⊓ y ∈ I → x ∈ I ∨ y ∈ I :=
  ⟨IsPrime.mem_or_mem, IsPrime.of_mem_or_mem⟩
#align order.ideal.is_prime_iff_mem_or_mem Order.Ideal.isPrime_iff_mem_or_mem

end SemilatticeInf

section DistribLattice

variable [DistribLattice P] {I : Ideal P}

instance (priority := 100) IsMaximal.isPrime [IsMaximal I] : IsPrime I := by
  rw [isPrime_iff_mem_or_mem]
  intro x y
  contrapose!
  rintro ⟨hx, hynI⟩ hxy
  apply hynI
  let J := I ⊔ principal x
  have hJuniv : (J : Set P) = Set.univ :=
    IsMaximal.maximal_proper (lt_sup_principal_of_not_mem ‹_›)
  have hyJ : y ∈ (J : Set P) := Set.eq_univ_iff_forall.mp hJuniv y
  rw [coe_sup_eq] at hyJ
  rcases hyJ with ⟨a, ha, b, hb, hy⟩
  rw [hy]
  refine sup_mem ha (I.lower (le_inf hb ?_) hxy)
  rw [hy]
  exact le_sup_right
#align order.ideal.is_maximal.is_prime Order.Ideal.IsMaximal.isPrime

end DistribLattice

section BooleanAlgebra

variable [BooleanAlgebra P] {x : P} {I : Ideal P}

theorem IsPrime.mem_or_compl_mem (hI : IsPrime I) : x ∈ I ∨ xᶜ ∈ I := by
  apply hI.mem_or_mem
  rw [inf_compl_eq_bot]
  exact I.bot_mem
#align order.ideal.is_prime.mem_or_compl_mem Order.Ideal.IsPrime.mem_or_compl_mem

theorem IsPrime.mem_compl_of_not_mem (hI : IsPrime I) (hxnI : x ∉ I) : xᶜ ∈ I :=
  hI.mem_or_compl_mem.resolve_left hxnI
#align order.ideal.is_prime.mem_compl_of_not_mem Order.Ideal.IsPrime.mem_compl_of_not_mem

theorem isPrime_of_mem_or_compl_mem [IsProper I] (h : ∀ {x : P}, x ∈ I ∨ xᶜ ∈ I) : IsPrime I := by
  simp only [isPrime_iff_mem_or_mem, or_iff_not_imp_left]
  intro x y hxy hxI
  have hxcI : xᶜ ∈ I := h.resolve_left hxI
  have ass : x ⊓ y ⊔ y ⊓ xᶜ ∈ I := sup_mem hxy (I.lower inf_le_right hxcI)
  rwa [inf_comm, sup_inf_inf_compl] at ass
#align order.ideal.is_prime_of_mem_or_compl_mem Order.Ideal.isPrime_of_mem_or_compl_mem

theorem isPrime_iff_mem_or_compl_mem [IsProper I] : IsPrime I ↔ ∀ {x : P}, x ∈ I ∨ xᶜ ∈ I :=
  ⟨fun h _ => h.mem_or_compl_mem, isPrime_of_mem_or_compl_mem⟩
#align order.ideal.is_prime_iff_mem_or_compl_mem Order.Ideal.isPrime_iff_mem_or_compl_mem

instance (priority := 100) IsPrime.isMaximal [IsPrime I] : IsMaximal I := by
  simp only [isMaximal_iff, Set.eq_univ_iff_forall, IsPrime.toIsProper, true_and]
  intro J hIJ x
  rcases Set.exists_of_ssubset hIJ with ⟨y, hyJ, hyI⟩
  suffices ass : x ⊓ y ⊔ x ⊓ yᶜ ∈ J by rwa [sup_inf_inf_compl] at ass
  exact
    sup_mem (J.lower inf_le_right hyJ)
      (hIJ.le <| I.lower inf_le_right <| IsPrime.mem_compl_of_not_mem ‹_› hyI)
#align order.ideal.is_prime.is_maximal Order.Ideal.IsPrime.isMaximal

end BooleanAlgebra

end Ideal

namespace PFilter

variable [Preorder P]

/-- A filter `F` is prime if its complement is an ideal.
-/
@[mk_iff]
class IsPrime (F : PFilter P) : Prop where
  compl_ideal : IsIdeal (F : Set P)ᶜ
#align order.pfilter.is_prime Order.PFilter.IsPrime

/-- Create an element of type `Order.Ideal.PrimePair` from a filter satisfying the predicate
`Order.PFilter.IsPrime`. -/
def IsPrime.toPrimePair {F : PFilter P} (h : IsPrime F) : Ideal.PrimePair P :=
  { I := h.compl_ideal.toIdeal
    F
    isCompl_I_F := isCompl_compl.symm }
#align order.pfilter.is_prime.to_prime_pair Order.PFilter.IsPrime.toPrimePair

theorem _root_.Order.Ideal.PrimePair.F_isPrime (IF : Ideal.PrimePair P) : IsPrime IF.F :=
  {
    compl_ideal := by
      rw [IF.compl_F_eq_I]
      exact IF.I.isIdeal }
set_option linter.uppercaseLean3 false in
#align order.ideal.prime_pair.F_is_prime Order.Ideal.PrimePair.F_isPrime

end PFilter

end Order
