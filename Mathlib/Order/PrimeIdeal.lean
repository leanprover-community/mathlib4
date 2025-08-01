/-
Copyright (c) 2021 Noam Atar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noam Atar
-/
import Mathlib.Order.Ideal
import Mathlib.Order.PFilter

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
structure PrimePair (P : Type*) [Preorder P] where
  I : Ideal P
  F : PFilter P
  isCompl_I_F : IsCompl (I : Set P) F

namespace PrimePair

variable [Preorder P] (IF : PrimePair P)

theorem compl_I_eq_F : (IF.I : Set P)ᶜ = IF.F :=
  IF.isCompl_I_F.compl_eq

theorem compl_F_eq_I : (IF.F : Set P)ᶜ = IF.I :=
  IF.isCompl_I_F.eq_compl.symm

theorem I_isProper : IsProper IF.I := by
  obtain ⟨w, h⟩ := IF.F.nonempty
  apply isProper_of_notMem (_ : w ∉ IF.I)
  rwa [← IF.compl_I_eq_F] at h

protected theorem disjoint : Disjoint (IF.I : Set P) IF.F :=
  IF.isCompl_I_F.disjoint

theorem I_union_F : (IF.I : Set P) ∪ IF.F = Set.univ :=
  IF.isCompl_I_F.sup_eq_top

theorem F_union_I : (IF.F : Set P) ∪ IF.I = Set.univ :=
  IF.isCompl_I_F.symm.sup_eq_top

end PrimePair

/-- An ideal `I` is prime if its complement is a filter.
-/
@[mk_iff]
class IsPrime [Preorder P] (I : Ideal P) : Prop extends IsProper I where
  compl_filter : IsPFilter (I : Set P)ᶜ

section Preorder

variable [Preorder P]

/-- Create an element of type `Order.Ideal.PrimePair` from an ideal satisfying the predicate
`Order.Ideal.IsPrime`. -/
def IsPrime.toPrimePair {I : Ideal P} (h : IsPrime I) : PrimePair P :=
  { I
    F := h.compl_filter.toPFilter
    isCompl_I_F := isCompl_compl }

theorem PrimePair.I_isPrime (IF : PrimePair P) : IsPrime IF.I :=
  { IF.I_isProper with
    compl_filter := by
      rw [IF.compl_I_eq_F]
      exact IF.F.isPFilter }

end Preorder

section SemilatticeInf

variable [SemilatticeInf P] {I : Ideal P}

theorem IsPrime.mem_or_mem (hI : IsPrime I) {x y : P} : x ⊓ y ∈ I → x ∈ I ∨ y ∈ I := by
  contrapose!
  let F := hI.compl_filter.toPFilter
  change x ∈ F ∧ y ∈ F → x ⊓ y ∈ F
  exact fun h => inf_mem h.1 h.2

theorem IsPrime.of_mem_or_mem [IsProper I] (hI : ∀ {x y : P}, x ⊓ y ∈ I → x ∈ I ∨ y ∈ I) :
    IsPrime I := by
  rw [isPrime_iff]
  use ‹_›
  refine .of_def ?_ ?_ ?_
  · exact Set.nonempty_compl.2 (I.isProper_iff.1 ‹_›)
  · intro x hx y hy
    exact ⟨x ⊓ y, fun h => (hI h).elim hx hy, inf_le_left, inf_le_right⟩
  · exact @mem_compl_of_ge _ _ _

theorem isPrime_iff_mem_or_mem [IsProper I] : IsPrime I ↔ ∀ {x y : P}, x ⊓ y ∈ I → x ∈ I ∨ y ∈ I :=
  ⟨IsPrime.mem_or_mem, IsPrime.of_mem_or_mem⟩

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
    IsMaximal.maximal_proper (lt_sup_principal_of_notMem ‹_›)
  have hyJ : y ∈ (J : Set P) := Set.eq_univ_iff_forall.mp hJuniv y
  rw [coe_sup_eq] at hyJ
  rcases hyJ with ⟨a, ha, b, hb, hy⟩
  rw [hy]
  refine sup_mem ha (I.lower (le_inf hb ?_) hxy)
  rw [hy]
  exact le_sup_right

end DistribLattice

section BooleanAlgebra

variable [BooleanAlgebra P] {x : P} {I : Ideal P}

theorem IsPrime.mem_or_compl_mem (hI : IsPrime I) : x ∈ I ∨ xᶜ ∈ I := by
  apply hI.mem_or_mem
  rw [inf_compl_eq_bot]
  exact I.bot_mem

theorem IsPrime.compl_mem_of_notMem (hI : IsPrime I) (hxnI : x ∉ I) : xᶜ ∈ I :=
  hI.mem_or_compl_mem.resolve_left hxnI

@[deprecated (since := "2025-05-23")]
alias IsPrime.mem_compl_of_not_mem := IsPrime.compl_mem_of_notMem

theorem isPrime_of_mem_or_compl_mem [IsProper I] (h : ∀ {x : P}, x ∈ I ∨ xᶜ ∈ I) : IsPrime I := by
  simp only [isPrime_iff_mem_or_mem, or_iff_not_imp_left]
  intro x y hxy hxI
  have hxcI : xᶜ ∈ I := h.resolve_left hxI
  have ass : x ⊓ y ⊔ y ⊓ xᶜ ∈ I := sup_mem hxy (I.lower inf_le_right hxcI)
  rwa [inf_comm, sup_inf_inf_compl] at ass

theorem isPrime_iff_mem_or_compl_mem [IsProper I] : IsPrime I ↔ ∀ {x : P}, x ∈ I ∨ xᶜ ∈ I :=
  ⟨fun h _ => h.mem_or_compl_mem, isPrime_of_mem_or_compl_mem⟩

instance (priority := 100) IsPrime.isMaximal [IsPrime I] : IsMaximal I := by
  simp only [isMaximal_iff, Set.eq_univ_iff_forall, IsPrime.toIsProper, true_and]
  intro J hIJ x
  rcases Set.exists_of_ssubset hIJ with ⟨y, hyJ, hyI⟩
  suffices ass : x ⊓ y ⊔ x ⊓ yᶜ ∈ J by rwa [sup_inf_inf_compl] at ass
  exact
    sup_mem (J.lower inf_le_right hyJ)
      (hIJ.le <| I.lower inf_le_right <| IsPrime.compl_mem_of_notMem ‹_› hyI)

end BooleanAlgebra

end Ideal

namespace PFilter

variable [Preorder P]

/-- A filter `F` is prime if its complement is an ideal.
-/
@[mk_iff]
class IsPrime (F : PFilter P) : Prop where
  compl_ideal : IsIdeal (F : Set P)ᶜ

/-- Create an element of type `Order.Ideal.PrimePair` from a filter satisfying the predicate
`Order.PFilter.IsPrime`. -/
def IsPrime.toPrimePair {F : PFilter P} (h : IsPrime F) : Ideal.PrimePair P :=
  { I := h.compl_ideal.toIdeal
    F
    isCompl_I_F := isCompl_compl.symm }

theorem _root_.Order.Ideal.PrimePair.F_isPrime (IF : Ideal.PrimePair P) : IsPrime IF.F :=
  {
    compl_ideal := by
      rw [IF.compl_F_eq_I]
      exact IF.I.isIdeal }

end PFilter

end Order
