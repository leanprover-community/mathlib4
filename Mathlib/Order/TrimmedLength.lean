/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/

import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Order.RelSeries
import Mathlib.Data.Fintype.Sort
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Set.Image
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!

# Trimmed Length

Given a relseries `rs : RelSeries (· ≤ ·)`, we define the trimmed length of `rs` to be the
cardinality of the underlying function `rs.toFun` of `rs` minus `1`. This models the number of `<`
relations occuring in `rs`. In this file we develop the main API for working with the trimmed length

-/

open Order

variable {α : Type*}


variable [PartialOrder α] [DecidableEq α]
  (rs : RelSeries (α := α) (· ≤ ·))

/--
Given `rs : RelSeries (α := α) (· ≤ ·)`,  `rs.trimmedLength` measures the number of `<`s appearing
in `rs` defined as the image of the underlying function of `rs`, i.e. `rs.toFun`.
-/
def RelSeries.trimmedLength (rs : RelSeries (α := α) (· ≤ ·)) : ℕ :=
  (Finset.image rs.toFun Finset.univ).card - 1

/--
The trimmed length of a relseries is bounded by the length of that relseries.
-/
lemma RelSeries.trimmedLength_le_length : rs.trimmedLength ≤ rs.length := by
  simp only [RelSeries.trimmedLength, tsub_le_iff_right]
  have := Finset.card_image_le (f := rs.toFun) (s := .univ)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  exact this

/--
The length of a relseries `rs` is equal to the trimmed length if and only if the underlying function
of `rs` (i.e. `rs.toFun`) is injective.
-/
lemma RelSeries.length_eq_trimmedLength_iff :
  rs.length = rs.trimmedLength ↔ rs.toFun.Injective := by
  constructor
  · intro h
    simp only [trimmedLength] at h
    have := Finset.card_image_iff (s := .univ) (f := rs.toFun)
    simp_all only [Finset.card_univ, Finset.one_le_card,
      Finset.image_nonempty, Finset.univ_nonempty,
      Nat.sub_add_cancel, Fintype.card_fin, Finset.coe_univ, true_iff]
    exact fun ⦃a₁ a₂⦄ ↦ this trivial trivial
  · intro h
    apply antisymm (r := (· ≤ ·))
    · have := Finset.card_le_card_of_injOn (s := .univ) (t := Finset.image rs.toFun Finset.univ)
        rs.toFun (by simp) h.injOn
      simp only [Finset.card_univ, Fintype.card_fin, trimmedLength, ge_iff_le] at this ⊢
      omega
    · exact RelSeries.trimmedLength_le_length rs

variable {rs} in
/--
If `rs` has length greater than `0`, there must be some index `i` such that
`rs i.castSucc < rs i.succ`.
-/
theorem RelSeries.trimmedLength_exists_le
(hrs : rs.trimmedLength > 0) : ∃ (i : Fin rs.length), rs i.castSucc < rs i.succ := by
  contrapose! hrs
  replace hrs (i : Fin rs.length) : rs.toFun i.castSucc = rs.toFun i.succ :=
    eq_of_le_of_not_lt (rs.step i) (hrs i)
  have H (i) : rs i = rs 0 := by
    induction' i using Fin.induction with m ih
    · rfl
    · rwa [← hrs m]
  unfold RelSeries.trimmedLength
  suffices Finset.image rs.toFun Finset.univ = {rs.toFun 0} by simp [this]
  suffices rs.toFun = fun i ↦ rs.toFun 0 by
    rw[this, Finset.image_const]
    use 0
    simp
  ext : 1
  apply H


variable {rs} in
/--
If the last two elements of `rs` are equal, then `rs.trimmedLength = rs.eraseLast.trimmedLength`.
Note that if `rs` only has one element, the "last two elements" are both just the unique element of
`rs`.
-/
theorem RelSeries.trimmedLength_eraseLast_of_eq
  (lasteq : ∃ i : Fin (rs.length), rs.toFun i.castSucc = rs.toFun i.succ ∧ (i + 1 : ℕ) = rs.length)
  : rs.trimmedLength = rs.eraseLast.trimmedLength := by
    simp only [trimmedLength, eraseLast_length]
    congr 2
    apply le_antisymm
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, eraseLast_toFun, true_and] at hx ⊢
      obtain ⟨i, rfl⟩ := hx
      by_cases hi : i = Fin.last _
      · obtain ⟨j, hj1, hj2⟩ := lasteq
        use j.cast (m := rs.length - 1 + 1) (by omega)
        subst i
        convert hj1 using 2
        ext
        exact hj2.symm
      · use (i.castPred hi).cast (m := rs.length - 1 + 1) (by omega)
        rfl
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, eraseLast_toFun, true_and] at hx ⊢
      obtain ⟨i, rfl⟩ := hx
      exact ⟨_, rfl⟩


variable {rs} in
/--
If the last two elements `a, b` of `rs` satisfy `a < b`, then
`rs.trimmedLength = rs.eraseLast.trimmedLength`. Note that if `rs` only has one element,
the "last two elements" are both just the unique element of `rs`.
In this case the condition is vacuous.
-/
theorem RelSeries.trimmedLength_eraseLast_of_lt
    (lastlt : ∃ i : Fin (rs.length), rs i.castSucc < rs i.succ ∧ (i + 1:ℕ) = rs.length)
    : rs.trimmedLength = rs.eraseLast.trimmedLength + 1 := by
      simp only [trimmedLength, eraseLast_length, Finset.one_le_card, Finset.image_nonempty,
        Finset.univ_nonempty, Nat.sub_add_cancel]
      obtain ⟨i, hi1, hi2⟩ := lastlt
      suffices (Finset.image rs.toFun Finset.univ).card =
               (Finset.image rs.eraseLast.toFun Finset.univ ∪ {rs.toFun i.succ}).card by
        simp_all only [eraseLast_length]
        rw[Finset.card_union_of_disjoint]
        · simp
        · simp only [Finset.disjoint_singleton_right, Finset.mem_image, Finset.mem_univ,
          eraseLast_toFun, true_and, not_exists]
          intro x
          suffices rs.toFun ⟨↑x, by omega⟩ < rs.toFun i.succ from ne_of_lt this
          apply LT.lt.trans_le' (b := rs.toFun i.castSucc)
          · exact hi1
          · apply rs.rel_of_le
            apply Fin.mk_le_of_le_val
            simp only [Fin.coe_castSucc]; omega
      congr
      apply le_antisymm
      · intro x hx
        simp only [Finset.mem_image, Finset.mem_univ, eraseLast_toFun, true_and] at hx ⊢
        obtain ⟨j, rfl⟩ := hx
        by_cases hj : j = i.succ
        · simp only [eraseLast_length, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
          eraseLast_toFun, true_and, Finset.mem_singleton]
          apply Or.inr
          rw[hj]
        · simp only [eraseLast_length, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
          eraseLast_toFun, true_and, Finset.mem_singleton]
          apply Or.inl
          use (j.castPred (ne_of_ne_of_eq hj ((Fin.eq_of_val_eq hi2) : i.succ = Fin.last _))).cast
           (m := rs.length - 1 + 1) (by omega)
          rfl
      · intro x hx
        simp only [eraseLast_length, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
          eraseLast_toFun, true_and, Finset.mem_singleton] at hx
        obtain h | h := hx
        · simp only [Finset.mem_image, Finset.mem_univ, eraseLast_toFun, true_and] at h ⊢
          obtain ⟨i, rfl⟩ := h
          exact ⟨_, rfl⟩
        · simp[h]


/--
The trimmed length of `rs.eraseLast` is less than or equal to the trimmed length of `rs`.
-/
theorem RelSeries.trimmedLength_eraseLast_le :
  rs.eraseLast.trimmedLength ≤ rs.trimmedLength := by
    by_cases h : ∃ i : Fin rs.length, rs.toFun i.castSucc = rs.toFun i.succ ∧ ↑i + 1 = rs.length
    · exact Nat.le_of_eq (id (Eq.symm (rs.trimmedLength_eraseLast_of_eq h)))
    · by_cases nontriv : rs.length = 0
      · simp_all only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, exists_false,
        not_false_eq_true]
        have : rs.eraseLast = rs := by aesop
        exact Nat.le_of_eq (congrArg trimmedLength this)
      have : ∃ i : Fin rs.length, rs.toFun i.castSucc < rs.toFun i.succ ∧ ↑i + 1 = rs.length := by
        simp_all only [not_exists, not_and]
        let secondlast : Fin rs.length := ⟨rs.length - 1, by omega⟩
        use secondlast
        specialize h secondlast
        have neq : rs secondlast.succ ≠ rs secondlast.castSucc := by
          contrapose h
          simp_all only [ne_eq, Decidable.not_not, forall_const, secondlast]
          omega
        have := rs.step secondlast
        constructor
        · apply lt_of_le_of_ne
          · exact this
          · exact id (Ne.symm neq)
        · exact Nat.succ_pred_eq_of_ne_zero nontriv
      have := rs.trimmedLength_eraseLast_of_lt this
      omega

variable [DecidableRel (α := α) (· ≤ ·)]

instance (rs : RelSeries (α := α) (· ≤ ·)) :
  LinearOrder { x // x ∈ Finset.image rs.toFun Finset.univ } where
    __ := Subtype.partialOrder _
    le_total := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
      obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      simp only [Subtype.mk_le_mk]
      exact (le_total i j).imp (RelSeries.rel_of_le rs) (RelSeries.rel_of_le rs)
    decidableLE := inferInstance

/--
Constructs the `LTSeries` associated to a given `RelSeries (α := α) (· ≤ ·)` constructed by
taking only those places where the relation is not equality.
-/
@[simps]
def RelSeries.trim (rs : RelSeries (α := α) (· ≤ ·)) :
 RelSeries (α := α) (· < ·) where
   length := rs.trimmedLength
   toFun := Subtype.val ∘ monoEquivOfFin (Finset.image rs.toFun Finset.univ)
    (by simp[RelSeries.trimmedLength])
   step := by
    intro i
    simp


section Module

variable {R M M': Type*}
         [Ring R]
         [AddCommGroup M]
         [AddCommGroup M']
         [Module R M]
         [Module R M']

 theorem RelSeries.exists_ltSeries_ge_head_bot
  (rs : RelSeries (α := Submodule R M) (· < ·)) :
  ∃ xs : RelSeries (α := Submodule R M) (· < ·),
  xs.length ≥ rs.length ∧ xs.head = ⊥ ∧ xs.last = rs.last :=
    Or.elim (em (rs.head = ⊥)) (by aesop)
    (by intro h; use cons rs ⊥ (by exact Ne.bot_lt' fun a ↦ h (id (Eq.symm a))); simp)

  theorem RelSeries.exists_ltSeries_le_last_top
  (rs : RelSeries (α := Submodule R M) (· < ·)) :
  ∃ xs : RelSeries (α := Submodule R M) (· < ·),
  xs.length ≥ rs.length ∧ xs.last = ⊤ ∧ xs.head = rs.head :=
    Or.elim (em (rs.last = ⊤)) (by aesop)
    (by intro h; use snoc rs ⊤ (by exact Ne.lt_top' fun a ↦ h (id (Eq.symm a))); simp)

  /--
  Given an LTSeries rs, there always exists an LTSeries xs with xs.length ≥ rs.length and
  the head of xs equal to ⊥ and the last of xs equal to ⊤.
  -/
  theorem RelSeries.exists_ltSeries_ge_head_bot_last_top
  (rs : RelSeries (fun (a : Submodule R M) (b : Submodule R M) => a < b))
  : ∃ xs : RelSeries (α := Submodule R M) (· < ·),
    xs.length ≥ rs.length ∧ xs.head = ⊥ ∧ xs.last = ⊤ := by
    obtain ⟨rs', hrs'⟩ := rs.exists_ltSeries_ge_head_bot
    obtain ⟨rs'', hrs''⟩ := rs'.exists_ltSeries_le_last_top
    use rs''; exact ⟨le_trans hrs'.1 hrs''.1, by aesop⟩


  def RelSeries.submoduleMap (rs : RelSeries (α := Submodule R M) (· < ·))
    (f : M →ₗ[R] M') : RelSeries (α := Submodule R M') (· ≤ ·) :=
      RelSeries.map rs {toFun := Submodule.map f, map_rel' := fun a ↦ Submodule.map_mono (a.le)}

  def RelSeries.submoduleComap (rs : RelSeries (α := Submodule R M') (· < ·))
    (f : M →ₗ[R] M') : RelSeries (α := Submodule R M) (· ≤ ·) :=
      RelSeries.map rs {toFun := Submodule.comap f, map_rel' := fun a ↦ Submodule.comap_mono (a.le)}


  theorem RelSeries.submodule_comap_lt_of_map_eq_exact
    {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (rs : RelSeries (α := Submodule R S.X₂) (· < ·)) (i : Fin rs.length)
    (p : (rs.submoduleMap S.g.hom).toFun i.castSucc = (rs.submoduleMap S.g.hom).toFun i.succ)
    : (rs.submoduleComap S.f.hom).toFun i.castSucc < (rs.submoduleComap S.f.hom).toFun i.succ := by
      have kernelInt : LinearMap.ker S.g.hom ⊓ (rs.toFun i.castSucc) <
        LinearMap.ker S.g.hom ⊓ (rs.toFun i.succ) :=
          LinearMap.ker_inf_lt_ker_inf (rs.step i) (by aesop)
      rw[← CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hS.exact] at kernelInt
      apply Set.range_inter_ssubset_iff_preimage_ssubset.mp kernelInt



    theorem RelSeries.submodule_map_lt_of_comap_eq_exact
        {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact)
        (rs : RelSeries (α := Submodule R S.X₂) (· < ·)) (i : Fin rs.length)
        (p : (rs.submoduleComap S.f.hom).toFun i.castSucc =
        (rs.submoduleComap S.f.hom).toFun i.succ) :
        (rs.submoduleMap S.g.hom).toFun i.castSucc < (rs.submoduleMap S.g.hom).toFun i.succ := by
      have imInt : LinearMap.range S.f.hom ⊓ (rs.toFun i.castSucc) =
                   LinearMap.range S.f.hom ⊓ (rs.toFun i.succ) := by
        rw[← Submodule.map_comap_eq, ←Submodule.map_comap_eq]
        exact congrArg (Submodule.map S.f.hom) p
      rw[CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hS.exact] at imInt
      apply LinearMap.map_lt_map_of_ker_inf_eq (rs.step i) imInt
open Classical in
  /--
  Given a short exact sequence S and rs : RelSeries (α := Submodule R S.X₂) (· < ·),
  we have that the length of rs is bounded above by the trimmed length of rs.submoduleMap S.g.hom
  plus the trimmed length of rs.submoduleComap S.f.hom.

  This is the main ingredient in our proof that the module length is additive.
  -/
theorem RelSeries.trimmedLength_additive
    {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact)
      (rs : RelSeries (α := Submodule R S.X₂) (· < ·)) :
      rs.length ≤ RelSeries.trimmedLength (rs.submoduleMap S.g.hom) +
                  RelSeries.trimmedLength (rs.submoduleComap S.f.hom) := by
        induction' o : rs.length with n ih generalizing rs
        · aesop
        · let n' : Fin (rs.length) := {val := n, isLt := by rw[o] ; exact lt_add_one n}
          have rserasedLen : rs.eraseLast.length = n := by aesop
          by_cases q : rs.submoduleMap S.g.hom (n'.castSucc) = rs.submoduleMap S.g.hom n'.succ
          · rw[RelSeries.trimmedLength_eraseLast_of_eq ⟨n', ⟨id q, id (Eq.symm o)⟩⟩]
            specialize ih rs.eraseLast rserasedLen
            have leftlt : ∃ i : Fin (rs.submoduleComap S.f.hom).length,
                (rs.submoduleComap S.f.hom).toFun i.castSucc <
                (rs.submoduleComap S.f.hom).toFun i.succ ∧
                ↑i + 1 = (rs.submoduleComap S.f.hom).length :=
                ⟨n', ⟨RelSeries.submodule_comap_lt_of_map_eq_exact hS rs n' q, o.symm⟩⟩
            rw[RelSeries.trimmedLength_eraseLast_of_lt leftlt]; exact Nat.add_le_add_right ih 1
          · rw[RelSeries.trimmedLength_eraseLast_of_lt
              ⟨n', ⟨lt_of_le_of_ne ((rs.submoduleMap S.g.hom).step n') q, id (Eq.symm o)⟩⟩]
            specialize ih rs.eraseLast rserasedLen
            suffices n + 1 ≤ (rs.submoduleMap S.g.hom).eraseLast.trimmedLength +
                             1 + (rs.submoduleComap S.f.hom).eraseLast.trimmedLength by
              exact le_add_of_le_add_left this
                (RelSeries.trimmedLength_eraseLast_le (rs.submoduleComap S.f.hom))
            ring_nf
            have proof := Nat.add_le_add_left ih 1
            ring_nf at proof; exact proof

end Module
