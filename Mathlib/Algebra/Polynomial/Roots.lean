/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker, Johan Commelin
-/

import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Localization.FractionRing

#align_import data.polynomial.ring_division from "leanprover-community/mathlib"@"8efcf8022aac8e01df8d302dcebdbc25d6a886c8"

/-!
# Theory of univariate polynomials

We define the multiset of roots of a polynomial, and prove basic results about it.

## Main definitions

* `Polynomial.roots p`: The multiset containing all the roots of `p`, including their
  multiplicities.
* `Polynomial.rootSet p E`: The set of distinct roots of `p` in an algebra `E`.

## Main statements

* `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C`: If a polynomial has as many roots as its
  degree, it can be written as the product of its leading coefficient with `∏ (X - a)` where `a`
  ranges through its roots.

-/

noncomputable section

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

section CommRing

variable [CommRing R] [IsDomain R] {p q : R[X]}

section Roots

open Multiset Finset

/-- `roots p` noncomputably gives a multiset containing all the roots of `p`,
including their multiplicities. -/
noncomputable def roots (p : R[X]) : Multiset R :=
  haveI := Classical.decEq R
  haveI := Classical.dec (p = 0)
  if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h)
#align polynomial.roots Polynomial.roots

theorem roots_def [DecidableEq R] (p : R[X]) [Decidable (p = 0)] :
    p.roots = if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h) := by
  -- porting noteL `‹_›` doesn't work for instance arguments
  rename_i iR ip0
  obtain rfl := Subsingleton.elim iR (Classical.decEq R)
  obtain rfl := Subsingleton.elim ip0 (Classical.dec (p = 0))
  rfl
#align polynomial.roots_def Polynomial.roots_def

@[simp]
theorem roots_zero : (0 : R[X]).roots = 0 :=
  dif_pos rfl
#align polynomial.roots_zero Polynomial.roots_zero

theorem card_roots (hp0 : p ≠ 0) : (Multiset.card (roots p) : WithBot ℕ) ≤ degree p := by
  classical
  unfold roots
  rw [dif_neg hp0]
  exact (Classical.choose_spec (exists_multiset_roots hp0)).1
#align polynomial.card_roots Polynomial.card_roots

theorem card_roots' (p : R[X]) : Multiset.card p.roots ≤ natDegree p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact WithBot.coe_le_coe.1 (le_trans (card_roots hp0) (le_of_eq <| degree_eq_natDegree hp0))
#align polynomial.card_roots' Polynomial.card_roots'

theorem card_roots_sub_C {p : R[X]} {a : R} (hp0 : 0 < degree p) :
    (Multiset.card (p - C a).roots : WithBot ℕ) ≤ degree p :=
  calc
    (Multiset.card (p - C a).roots : WithBot ℕ) ≤ degree (p - C a) :=
      card_roots <| mt sub_eq_zero.1 fun h => not_le_of_gt hp0 <| h.symm ▸ degree_C_le
    _ = degree p := by rw [sub_eq_add_neg, ← C_neg]; exact degree_add_C hp0
set_option linter.uppercaseLean3 false in
#align polynomial.card_roots_sub_C Polynomial.card_roots_sub_C

theorem card_roots_sub_C' {p : R[X]} {a : R} (hp0 : 0 < degree p) :
    Multiset.card (p - C a).roots ≤ natDegree p :=
  WithBot.coe_le_coe.1
    (le_trans (card_roots_sub_C hp0)
      (le_of_eq <| degree_eq_natDegree fun h => by simp_all [lt_irrefl]))
set_option linter.uppercaseLean3 false in
#align polynomial.card_roots_sub_C' Polynomial.card_roots_sub_C'

@[simp]
theorem count_roots [DecidableEq R] (p : R[X]) : p.roots.count a = rootMultiplicity a p := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  rw [roots_def, dif_neg hp]
  exact (Classical.choose_spec (exists_multiset_roots hp)).2 a
#align polynomial.count_roots Polynomial.count_roots

@[simp]
theorem mem_roots' : a ∈ p.roots ↔ p ≠ 0 ∧ IsRoot p a := by
  classical
  rw [← count_pos, count_roots p, rootMultiplicity_pos']
#align polynomial.mem_roots' Polynomial.mem_roots'

theorem mem_roots (hp : p ≠ 0) : a ∈ p.roots ↔ IsRoot p a :=
  mem_roots'.trans <| and_iff_right hp
#align polynomial.mem_roots Polynomial.mem_roots

theorem ne_zero_of_mem_roots (h : a ∈ p.roots) : p ≠ 0 :=
  (mem_roots'.1 h).1
#align polynomial.ne_zero_of_mem_roots Polynomial.ne_zero_of_mem_roots

theorem isRoot_of_mem_roots (h : a ∈ p.roots) : IsRoot p a :=
  (mem_roots'.1 h).2
#align polynomial.is_root_of_mem_roots Polynomial.isRoot_of_mem_roots

-- Porting note: added during port.
lemma mem_roots_iff_aeval_eq_zero {x : R} (w : p ≠ 0) : x ∈ roots p ↔ aeval x p = 0 := by
  rw [mem_roots w, IsRoot.def, aeval_def, eval₂_eq_eval_map]
  simp

theorem card_le_degree_of_subset_roots {p : R[X]} {Z : Finset R} (h : Z.val ⊆ p.roots) :
    Z.card ≤ p.natDegree :=
  (Multiset.card_le_card (Finset.val_le_iff_val_subset.2 h)).trans (Polynomial.card_roots' p)
#align polynomial.card_le_degree_of_subset_roots Polynomial.card_le_degree_of_subset_roots

theorem finite_setOf_isRoot {p : R[X]} (hp : p ≠ 0) : Set.Finite { x | IsRoot p x } := by
  classical
  simpa only [← Finset.setOf_mem, Multiset.mem_toFinset, mem_roots hp]
    using p.roots.toFinset.finite_toSet
#align polynomial.finite_set_of_is_root Polynomial.finite_setOf_isRoot

theorem eq_zero_of_infinite_isRoot (p : R[X]) (h : Set.Infinite { x | IsRoot p x }) : p = 0 :=
  not_imp_comm.mp finite_setOf_isRoot h
#align polynomial.eq_zero_of_infinite_is_root Polynomial.eq_zero_of_infinite_isRoot

theorem exists_max_root [LinearOrder R] (p : R[X]) (hp : p ≠ 0) : ∃ x₀, ∀ x, p.IsRoot x → x ≤ x₀ :=
  Set.exists_upper_bound_image _ _ <| finite_setOf_isRoot hp
#align polynomial.exists_max_root Polynomial.exists_max_root

theorem exists_min_root [LinearOrder R] (p : R[X]) (hp : p ≠ 0) : ∃ x₀, ∀ x, p.IsRoot x → x₀ ≤ x :=
  Set.exists_lower_bound_image _ _ <| finite_setOf_isRoot hp
#align polynomial.exists_min_root Polynomial.exists_min_root

theorem eq_of_infinite_eval_eq (p q : R[X]) (h : Set.Infinite { x | eval x p = eval x q }) :
    p = q := by
  rw [← sub_eq_zero]
  apply eq_zero_of_infinite_isRoot
  simpa only [IsRoot, eval_sub, sub_eq_zero]
#align polynomial.eq_of_infinite_eval_eq Polynomial.eq_of_infinite_eval_eq

theorem roots_mul {p q : R[X]} (hpq : p * q ≠ 0) : (p * q).roots = p.roots + q.roots := by
  classical
  exact Multiset.ext.mpr fun r => by
    rw [count_add, count_roots, count_roots, count_roots, rootMultiplicity_mul hpq]
#align polynomial.roots_mul Polynomial.roots_mul

theorem roots.le_of_dvd (h : q ≠ 0) : p ∣ q → roots p ≤ roots q := by
  rintro ⟨k, rfl⟩
  exact Multiset.le_iff_exists_add.mpr ⟨k.roots, roots_mul h⟩
#align polynomial.roots.le_of_dvd Polynomial.roots.le_of_dvd

theorem mem_roots_sub_C' {p : R[X]} {a x : R} : x ∈ (p - C a).roots ↔ p ≠ C a ∧ p.eval x = a := by
  rw [mem_roots', IsRoot.def, sub_ne_zero, eval_sub, sub_eq_zero, eval_C]
set_option linter.uppercaseLean3 false in
#align polynomial.mem_roots_sub_C' Polynomial.mem_roots_sub_C'

theorem mem_roots_sub_C {p : R[X]} {a x : R} (hp0 : 0 < degree p) :
    x ∈ (p - C a).roots ↔ p.eval x = a :=
  mem_roots_sub_C'.trans <| and_iff_right fun hp => hp0.not_le <| hp.symm ▸ degree_C_le
set_option linter.uppercaseLean3 false in
#align polynomial.mem_roots_sub_C Polynomial.mem_roots_sub_C

@[simp]
theorem roots_X_sub_C (r : R) : roots (X - C r) = {r} := by
  classical
  ext s
  rw [count_roots, rootMultiplicity_X_sub_C, count_singleton]
set_option linter.uppercaseLean3 false in
#align polynomial.roots_X_sub_C Polynomial.roots_X_sub_C

@[simp]
theorem roots_X : roots (X : R[X]) = {0} := by rw [← roots_X_sub_C, C_0, sub_zero]
set_option linter.uppercaseLean3 false in
#align polynomial.roots_X Polynomial.roots_X

@[simp]
theorem roots_C (x : R) : (C x).roots = 0 := by
  classical exact
  if H : x = 0 then by rw [H, C_0, roots_zero]
  else
    Multiset.ext.mpr fun r => (by
      rw [count_roots, count_zero, rootMultiplicity_eq_zero (not_isRoot_C _ _ H)])
set_option linter.uppercaseLean3 false in
#align polynomial.roots_C Polynomial.roots_C

@[simp]
theorem roots_one : (1 : R[X]).roots = ∅ :=
  roots_C 1
#align polynomial.roots_one Polynomial.roots_one

@[simp]
theorem roots_C_mul (p : R[X]) (ha : a ≠ 0) : (C a * p).roots = p.roots := by
  by_cases hp : p = 0 <;>
    simp only [roots_mul, *, Ne, mul_eq_zero, C_eq_zero, or_self_iff, not_false_iff, roots_C,
      zero_add, mul_zero]
set_option linter.uppercaseLean3 false in
#align polynomial.roots_C_mul Polynomial.roots_C_mul

@[simp]
theorem roots_smul_nonzero (p : R[X]) (ha : a ≠ 0) : (a • p).roots = p.roots := by
  rw [smul_eq_C_mul, roots_C_mul _ ha]
#align polynomial.roots_smul_nonzero Polynomial.roots_smul_nonzero

@[simp]
lemma roots_neg (p : R[X]) : (-p).roots = p.roots := by
  rw [← neg_one_smul R p, roots_smul_nonzero p (neg_ne_zero.mpr one_ne_zero)]

theorem roots_list_prod (L : List R[X]) :
    (0 : R[X]) ∉ L → L.prod.roots = (L : Multiset R[X]).bind roots :=
  List.recOn L (fun _ => roots_one) fun hd tl ih H => by
    rw [List.mem_cons, not_or] at H
    rw [List.prod_cons, roots_mul (mul_ne_zero (Ne.symm H.1) <| List.prod_ne_zero H.2), ←
      Multiset.cons_coe, Multiset.cons_bind, ih H.2]
#align polynomial.roots_list_prod Polynomial.roots_list_prod

theorem roots_multiset_prod (m : Multiset R[X]) : (0 : R[X]) ∉ m → m.prod.roots = m.bind roots := by
  rcases m with ⟨L⟩
  simpa only [Multiset.prod_coe, quot_mk_to_coe''] using roots_list_prod L
#align polynomial.roots_multiset_prod Polynomial.roots_multiset_prod

theorem roots_prod {ι : Type*} (f : ι → R[X]) (s : Finset ι) :
    s.prod f ≠ 0 → (s.prod f).roots = s.val.bind fun i => roots (f i) := by
  rcases s with ⟨m, hm⟩
  simpa [Multiset.prod_eq_zero_iff, Multiset.bind_map] using roots_multiset_prod (m.map f)
#align polynomial.roots_prod Polynomial.roots_prod

@[simp]
theorem roots_pow (p : R[X]) (n : ℕ) : (p ^ n).roots = n • p.roots := by
  induction' n with n ihn
  · rw [pow_zero, roots_one, zero_smul, empty_eq_zero]
  · rcases eq_or_ne p 0 with (rfl | hp)
    · rw [zero_pow n.succ_ne_zero, roots_zero, smul_zero]
    · rw [pow_succ, roots_mul (mul_ne_zero (pow_ne_zero _ hp) hp), ihn, add_smul, one_smul]
#align polynomial.roots_pow Polynomial.roots_pow

theorem roots_X_pow (n : ℕ) : (X ^ n : R[X]).roots = n • ({0} : Multiset R) := by
  rw [roots_pow, roots_X]
set_option linter.uppercaseLean3 false in
#align polynomial.roots_X_pow Polynomial.roots_X_pow

theorem roots_C_mul_X_pow (ha : a ≠ 0) (n : ℕ) :
    Polynomial.roots (C a * X ^ n) = n • ({0} : Multiset R) := by
  rw [roots_C_mul _ ha, roots_X_pow]
set_option linter.uppercaseLean3 false in
#align polynomial.roots_C_mul_X_pow Polynomial.roots_C_mul_X_pow

@[simp]
theorem roots_monomial (ha : a ≠ 0) (n : ℕ) : (monomial n a).roots = n • ({0} : Multiset R) := by
  rw [← C_mul_X_pow_eq_monomial, roots_C_mul_X_pow ha]
#align polynomial.roots_monomial Polynomial.roots_monomial

theorem roots_prod_X_sub_C (s : Finset R) : (s.prod fun a => X - C a).roots = s.val := by
  apply (roots_prod (fun a => X - C a) s ?_).trans
  · simp_rw [roots_X_sub_C]
    rw [Multiset.bind_singleton, Multiset.map_id']
  · refine prod_ne_zero_iff.mpr (fun a _ => X_sub_C_ne_zero a)
set_option linter.uppercaseLean3 false in
#align polynomial.roots_prod_X_sub_C Polynomial.roots_prod_X_sub_C

@[simp]
theorem roots_multiset_prod_X_sub_C (s : Multiset R) : (s.map fun a => X - C a).prod.roots = s := by
  rw [roots_multiset_prod, Multiset.bind_map]
  · simp_rw [roots_X_sub_C]
    rw [Multiset.bind_singleton, Multiset.map_id']
  · rw [Multiset.mem_map]
    rintro ⟨a, -, h⟩
    exact X_sub_C_ne_zero a h
set_option linter.uppercaseLean3 false in
#align polynomial.roots_multiset_prod_X_sub_C Polynomial.roots_multiset_prod_X_sub_C

theorem card_roots_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) :
    Multiset.card (roots ((X : R[X]) ^ n - C a)) ≤ n :=
  WithBot.coe_le_coe.1 <|
    calc
      (Multiset.card (roots ((X : R[X]) ^ n - C a)) : WithBot ℕ) ≤ degree ((X : R[X]) ^ n - C a) :=
        card_roots (X_pow_sub_C_ne_zero hn a)
      _ = n := degree_X_pow_sub_C hn a
set_option linter.uppercaseLean3 false in
#align polynomial.card_roots_X_pow_sub_C Polynomial.card_roots_X_pow_sub_C

section NthRoots

/-- `nthRoots n a` noncomputably returns the solutions to `x ^ n = a`-/
def nthRoots (n : ℕ) (a : R) : Multiset R :=
  roots ((X : R[X]) ^ n - C a)
#align polynomial.nth_roots Polynomial.nthRoots

@[simp]
theorem mem_nthRoots {n : ℕ} (hn : 0 < n) {a x : R} : x ∈ nthRoots n a ↔ x ^ n = a := by
  rw [nthRoots, mem_roots (X_pow_sub_C_ne_zero hn a), IsRoot.def, eval_sub, eval_C, eval_pow,
    eval_X, sub_eq_zero]
#align polynomial.mem_nth_roots Polynomial.mem_nthRoots

@[simp]
theorem nthRoots_zero (r : R) : nthRoots 0 r = 0 := by
  simp only [empty_eq_zero, pow_zero, nthRoots, ← C_1, ← C_sub, roots_C]
#align polynomial.nth_roots_zero Polynomial.nthRoots_zero

@[simp]
theorem nthRoots_zero_right {R} [CommRing R] [IsDomain R] (n : ℕ) :
    nthRoots n (0 : R) = Multiset.replicate n 0 := by
  rw [nthRoots, C.map_zero, sub_zero, roots_pow, roots_X, Multiset.nsmul_singleton]

theorem card_nthRoots (n : ℕ) (a : R) : Multiset.card (nthRoots n a) ≤ n := by
  classical exact
  (if hn : n = 0 then
    if h : (X : R[X]) ^ n - C a = 0 then by
      simp [Nat.zero_le, nthRoots, roots, h, dif_pos rfl, empty_eq_zero, Multiset.card_zero]
    else
      WithBot.coe_le_coe.1
        (le_trans (card_roots h)
          (by
            rw [hn, pow_zero, ← C_1, ← RingHom.map_sub]
            exact degree_C_le))
  else by
    rw [← Nat.cast_le (α := WithBot ℕ)]
    rw [← degree_X_pow_sub_C (Nat.pos_of_ne_zero hn) a]
    exact card_roots (X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) a))
#align polynomial.card_nth_roots Polynomial.card_nthRoots

@[simp]
theorem nthRoots_two_eq_zero_iff {r : R} : nthRoots 2 r = 0 ↔ ¬IsSquare r := by
  simp_rw [isSquare_iff_exists_sq, eq_zero_iff_forall_not_mem, mem_nthRoots (by norm_num : 0 < 2),
    ← not_exists, eq_comm]
#align polynomial.nth_roots_two_eq_zero_iff Polynomial.nthRoots_two_eq_zero_iff

/-- The multiset `nthRoots ↑n (1 : R)` as a Finset. -/
def nthRootsFinset (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] : Finset R :=
  haveI := Classical.decEq R
  Multiset.toFinset (nthRoots n (1 : R))
#align polynomial.nth_roots_finset Polynomial.nthRootsFinset

lemma nthRootsFinset_def (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] [DecidableEq R] :
    nthRootsFinset n R = Multiset.toFinset (nthRoots n (1 : R)) := by
  unfold nthRootsFinset
  convert rfl

@[simp]
theorem mem_nthRootsFinset {n : ℕ} (h : 0 < n) {x : R} :
    x ∈ nthRootsFinset n R ↔ x ^ (n : ℕ) = 1 := by
  classical
  rw [nthRootsFinset_def, mem_toFinset, mem_nthRoots h]
#align polynomial.mem_nth_roots_finset Polynomial.mem_nthRootsFinset

@[simp]
theorem nthRootsFinset_zero : nthRootsFinset 0 R = ∅ := by classical simp [nthRootsFinset_def]
#align polynomial.nth_roots_finset_zero Polynomial.nthRootsFinset_zero

theorem mul_mem_nthRootsFinset
    {η₁ η₂ : R} (hη₁ : η₁ ∈ nthRootsFinset n R) (hη₂ : η₂ ∈ nthRootsFinset n R) :
    η₁ * η₂ ∈ nthRootsFinset n R := by
  cases n with
  | zero =>
    simp only [Nat.zero_eq, nthRootsFinset_zero, not_mem_empty] at hη₁
  | succ n =>
    rw [mem_nthRootsFinset n.succ_pos] at hη₁ hη₂ ⊢
    rw [mul_pow, hη₁, hη₂, one_mul]

theorem ne_zero_of_mem_nthRootsFinset {η : R} (hη : η ∈ nthRootsFinset n R) : η ≠ 0 := by
  nontriviality R
  rintro rfl
  cases n with
  | zero =>
    simp only [Nat.zero_eq, nthRootsFinset_zero, not_mem_empty] at hη
  | succ n =>
    rw [mem_nthRootsFinset n.succ_pos, zero_pow n.succ_ne_zero] at hη
    exact zero_ne_one hη

theorem one_mem_nthRootsFinset (hn : 0 < n) : 1 ∈ nthRootsFinset n R := by
  rw [mem_nthRootsFinset hn, one_pow]

end NthRoots

theorem zero_of_eval_zero [Infinite R] (p : R[X]) (h : ∀ x, p.eval x = 0) : p = 0 := by
  classical
  by_contra hp
  refine @Fintype.false R _ ?_
  exact ⟨p.roots.toFinset, fun x => Multiset.mem_toFinset.mpr ((mem_roots hp).mpr (h _))⟩
#align polynomial.zero_of_eval_zero Polynomial.zero_of_eval_zero

theorem funext [Infinite R] {p q : R[X]} (ext : ∀ r : R, p.eval r = q.eval r) : p = q := by
  rw [← sub_eq_zero]
  apply zero_of_eval_zero
  intro x
  rw [eval_sub, sub_eq_zero, ext]
#align polynomial.funext Polynomial.funext

variable [CommRing T]

/-- Given a polynomial `p` with coefficients in a ring `T` and a `T`-algebra `S`, `aroots p S` is
the multiset of roots of `p` regarded as a polynomial over `S`. -/
noncomputable abbrev aroots (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] : Multiset S :=
  (p.map (algebraMap T S)).roots

theorem aroots_def (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] :
    p.aroots S = (p.map (algebraMap T S)).roots :=
  rfl

theorem mem_aroots' [CommRing S] [IsDomain S] [Algebra T S] {p : T[X]} {a : S} :
    a ∈ p.aroots S ↔ p.map (algebraMap T S) ≠ 0 ∧ aeval a p = 0 := by
  rw [mem_roots', IsRoot.def, ← eval₂_eq_eval_map, aeval_def]

theorem mem_aroots [CommRing S] [IsDomain S] [Algebra T S]
    [NoZeroSMulDivisors T S] {p : T[X]} {a : S} : a ∈ p.aroots S ↔ p ≠ 0 ∧ aeval a p = 0 := by
  rw [mem_aroots', Polynomial.map_ne_zero_iff]
  exact NoZeroSMulDivisors.algebraMap_injective T S

theorem aroots_mul [CommRing S] [IsDomain S] [Algebra T S]
    [NoZeroSMulDivisors T S] {p q : T[X]} (hpq : p * q ≠ 0) :
    (p * q).aroots S = p.aroots S + q.aroots S := by
  suffices map (algebraMap T S) p * map (algebraMap T S) q ≠ 0 by
    rw [aroots_def, Polynomial.map_mul, roots_mul this]
  rwa [← Polynomial.map_mul, Polynomial.map_ne_zero_iff
    (NoZeroSMulDivisors.algebraMap_injective T S)]

@[simp]
theorem aroots_X_sub_C [CommRing S] [IsDomain S] [Algebra T S]
    (r : T) : aroots (X - C r) S = {algebraMap T S r} := by
  rw [aroots_def, Polynomial.map_sub, map_X, map_C, roots_X_sub_C]

@[simp]
theorem aroots_X [CommRing S] [IsDomain S] [Algebra T S] :
    aroots (X : T[X]) S = {0} := by
  rw [aroots_def, map_X, roots_X]

@[simp]
theorem aroots_C [CommRing S] [IsDomain S] [Algebra T S] (a : T) : (C a).aroots S = 0 := by
  rw [aroots_def, map_C, roots_C]

@[simp]
theorem aroots_zero (S) [CommRing S] [IsDomain S] [Algebra T S] : (0 : T[X]).aroots S = 0 := by
  rw [← C_0, aroots_C]

@[simp]
theorem aroots_one [CommRing S] [IsDomain S] [Algebra T S] :
    (1 : T[X]).aroots S = 0 :=
  aroots_C 1

@[simp]
theorem aroots_neg [CommRing S] [IsDomain S] [Algebra T S] (p : T[X]) :
    (-p).aroots S = p.aroots S := by
  rw [aroots, Polynomial.map_neg, roots_neg]

@[simp]
theorem aroots_C_mul [CommRing S] [IsDomain S] [Algebra T S]
    [NoZeroSMulDivisors T S] {a : T} (p : T[X]) (ha : a ≠ 0) :
    (C a * p).aroots S = p.aroots S := by
  rw [aroots_def, Polynomial.map_mul, map_C, roots_C_mul]
  rwa [map_ne_zero_iff]
  exact NoZeroSMulDivisors.algebraMap_injective T S

@[simp]
theorem aroots_smul_nonzero [CommRing S] [IsDomain S] [Algebra T S]
    [NoZeroSMulDivisors T S] {a : T} (p : T[X]) (ha : a ≠ 0) :
    (a • p).aroots S = p.aroots S := by
  rw [smul_eq_C_mul, aroots_C_mul _ ha]

@[simp]
theorem aroots_pow [CommRing S] [IsDomain S] [Algebra T S] (p : T[X]) (n : ℕ) :
    (p ^ n).aroots S = n • p.aroots S := by
  rw [aroots_def, Polynomial.map_pow, roots_pow]

theorem aroots_X_pow [CommRing S] [IsDomain S] [Algebra T S] (n : ℕ) :
    (X ^ n : T[X]).aroots S = n • ({0} : Multiset S) := by
  rw [aroots_pow, aroots_X]

theorem aroots_C_mul_X_pow [CommRing S] [IsDomain S] [Algebra T S]
    [NoZeroSMulDivisors T S] {a : T} (ha : a ≠ 0) (n : ℕ) :
    (C a * X ^ n : T[X]).aroots S = n • ({0} : Multiset S) := by
  rw [aroots_C_mul _ ha, aroots_X_pow]

@[simp]
theorem aroots_monomial [CommRing S] [IsDomain S] [Algebra T S]
    [NoZeroSMulDivisors T S] {a : T} (ha : a ≠ 0) (n : ℕ) :
    (monomial n a).aroots S = n • ({0} : Multiset S) := by
  rw [← C_mul_X_pow_eq_monomial, aroots_C_mul_X_pow ha]

/-- The set of distinct roots of `p` in `S`.

If you have a non-separable polynomial, use `Polynomial.aroots` for the multiset
where multiple roots have the appropriate multiplicity. -/
def rootSet (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] : Set S :=
  haveI := Classical.decEq S
  (p.aroots S).toFinset
#align polynomial.root_set Polynomial.rootSet

theorem rootSet_def (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] [DecidableEq S] :
    p.rootSet S = (p.aroots S).toFinset := by
  rw [rootSet]
  convert rfl
#align polynomial.root_set_def Polynomial.rootSet_def

@[simp]
theorem rootSet_C [CommRing S] [IsDomain S] [Algebra T S] (a : T) : (C a).rootSet S = ∅ := by
  classical
  rw [rootSet_def, aroots_C, Multiset.toFinset_zero, Finset.coe_empty]
set_option linter.uppercaseLean3 false in
#align polynomial.root_set_C Polynomial.rootSet_C

@[simp]
theorem rootSet_zero (S) [CommRing S] [IsDomain S] [Algebra T S] : (0 : T[X]).rootSet S = ∅ := by
  rw [← C_0, rootSet_C]
#align polynomial.root_set_zero Polynomial.rootSet_zero

@[simp]
theorem rootSet_one (S) [CommRing S] [IsDomain S] [Algebra T S] : (1 : T[X]).rootSet S = ∅ := by
  rw [← C_1, rootSet_C]

@[simp]
theorem rootSet_neg (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] :
    (-p).rootSet S = p.rootSet S := by
  rw [rootSet, aroots_neg, rootSet]

instance rootSetFintype (p : T[X]) (S : Type*) [CommRing S] [IsDomain S] [Algebra T S] :
    Fintype (p.rootSet S) :=
  FinsetCoe.fintype _
#align polynomial.root_set_fintype Polynomial.rootSetFintype

theorem rootSet_finite (p : T[X]) (S : Type*) [CommRing S] [IsDomain S] [Algebra T S] :
    (p.rootSet S).Finite :=
  Set.toFinite _
#align polynomial.root_set_finite Polynomial.rootSet_finite

/-- The set of roots of all polynomials of bounded degree and having coefficients in a finite set
is finite. -/
theorem bUnion_roots_finite {R S : Type*} [Semiring R] [CommRing S] [IsDomain S] [DecidableEq S]
    (m : R →+* S) (d : ℕ) {U : Set R} (h : U.Finite) :
    (⋃ (f : R[X]) (_ : f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ U),
        ((f.map m).roots.toFinset.toSet : Set S)).Finite :=
  Set.Finite.biUnion
    (by
      -- We prove that the set of polynomials under consideration is finite because its
      -- image by the injective map `π` is finite
      let π : R[X] → Fin (d + 1) → R := fun f i => f.coeff i
      refine ((Set.Finite.pi fun _ => h).subset <| ?_).of_finite_image (?_ : Set.InjOn π _)
      · exact Set.image_subset_iff.2 fun f hf i _ => hf.2 i
      · refine fun x hx y hy hxy => (ext_iff_natDegree_le hx.1 hy.1).2 fun i hi => ?_
        exact id congr_fun hxy ⟨i, Nat.lt_succ_of_le hi⟩)
    fun i _ => Finset.finite_toSet _
#align polynomial.bUnion_roots_finite Polynomial.bUnion_roots_finite

theorem mem_rootSet' {p : T[X]} {S : Type*} [CommRing S] [IsDomain S] [Algebra T S] {a : S} :
    a ∈ p.rootSet S ↔ p.map (algebraMap T S) ≠ 0 ∧ aeval a p = 0 := by
  classical
  rw [rootSet_def, Finset.mem_coe, mem_toFinset, mem_aroots']
#align polynomial.mem_root_set' Polynomial.mem_rootSet'

theorem mem_rootSet {p : T[X]} {S : Type*} [CommRing S] [IsDomain S] [Algebra T S]
    [NoZeroSMulDivisors T S] {a : S} : a ∈ p.rootSet S ↔ p ≠ 0 ∧ aeval a p = 0 := by
  rw [mem_rootSet', Polynomial.map_ne_zero_iff (NoZeroSMulDivisors.algebraMap_injective T S)]
#align polynomial.mem_root_set Polynomial.mem_rootSet

theorem mem_rootSet_of_ne {p : T[X]} {S : Type*} [CommRing S] [IsDomain S] [Algebra T S]
    [NoZeroSMulDivisors T S] (hp : p ≠ 0) {a : S} : a ∈ p.rootSet S ↔ aeval a p = 0 :=
  mem_rootSet.trans <| and_iff_right hp
#align polynomial.mem_root_set_of_ne Polynomial.mem_rootSet_of_ne

theorem rootSet_maps_to' {p : T[X]} {S S'} [CommRing S] [IsDomain S] [Algebra T S] [CommRing S']
    [IsDomain S'] [Algebra T S'] (hp : p.map (algebraMap T S') = 0 → p.map (algebraMap T S) = 0)
    (f : S →ₐ[T] S') : (p.rootSet S).MapsTo f (p.rootSet S') := fun x hx => by
  rw [mem_rootSet'] at hx ⊢
  rw [aeval_algHom, AlgHom.comp_apply, hx.2, _root_.map_zero]
  exact ⟨mt hp hx.1, rfl⟩
#align polynomial.root_set_maps_to' Polynomial.rootSet_maps_to'

theorem ne_zero_of_mem_rootSet {p : T[X]} [CommRing S] [IsDomain S] [Algebra T S] {a : S}
    (h : a ∈ p.rootSet S) : p ≠ 0 := fun hf => by rwa [hf, rootSet_zero] at h
#align polynomial.ne_zero_of_mem_root_set Polynomial.ne_zero_of_mem_rootSet

theorem aeval_eq_zero_of_mem_rootSet {p : T[X]} [CommRing S] [IsDomain S] [Algebra T S] {a : S}
    (hx : a ∈ p.rootSet S) : aeval a p = 0 :=
  (mem_rootSet'.1 hx).2
#align polynomial.aeval_eq_zero_of_mem_root_set Polynomial.aeval_eq_zero_of_mem_rootSet

theorem rootSet_mapsTo {p : T[X]} {S S'} [CommRing S] [IsDomain S] [Algebra T S] [CommRing S']
    [IsDomain S'] [Algebra T S'] [NoZeroSMulDivisors T S'] (f : S →ₐ[T] S') :
    (p.rootSet S).MapsTo f (p.rootSet S') := by
  refine rootSet_maps_to' (fun h₀ => ?_) f
  obtain rfl : p = 0 :=
    map_injective _ (NoZeroSMulDivisors.algebraMap_injective T S') (by rwa [Polynomial.map_zero])
  exact Polynomial.map_zero _
#align polynomial.root_set_maps_to Polynomial.rootSet_mapsTo

end Roots

lemma eq_zero_of_natDegree_lt_card_of_eval_eq_zero {R} [CommRing R] [IsDomain R]
    (p : R[X]) {ι} [Fintype ι] {f : ι → R} (hf : Function.Injective f)
    (heval : ∀ i, p.eval (f i) = 0) (hcard : natDegree p < Fintype.card ι) : p = 0 := by
  classical
  by_contra hp
  apply not_lt_of_le (le_refl (Finset.card p.roots.toFinset))
  calc
    Finset.card p.roots.toFinset ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ natDegree p := Polynomial.card_roots' p
    _ < Fintype.card ι := hcard
    _ = Fintype.card (Set.range f) := (Set.card_range_of_injective hf).symm
    _ = Finset.card (Finset.univ.image f) := by rw [← Set.toFinset_card, Set.toFinset_range]
    _ ≤ Finset.card p.roots.toFinset := Finset.card_mono ?_
  intro _
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Multiset.mem_toFinset, mem_roots', ne_eq,
    IsRoot.def, forall_exists_index, hp, not_false_eq_true]
  rintro x rfl
  exact heval _

lemma eq_zero_of_natDegree_lt_card_of_eval_eq_zero' {R} [CommRing R] [IsDomain R]
    (p : R[X]) (s : Finset R) (heval : ∀ i ∈ s, p.eval i = 0) (hcard : natDegree p < s.card) :
    p = 0 :=
  eq_zero_of_natDegree_lt_card_of_eval_eq_zero p Subtype.val_injective
    (fun i : s ↦ heval i i.prop) (hcard.trans_eq (Fintype.card_coe s).symm)

open Cardinal in
lemma eq_zero_of_forall_eval_zero_of_natDegree_lt_card
    (f : R[X]) (hf : ∀ r, f.eval r = 0) (hfR : f.natDegree < #R) : f = 0 := by
  obtain hR|hR := finite_or_infinite R
  · have := Fintype.ofFinite R
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero f Function.injective_id hf
    simpa only [mk_fintype, Nat.cast_lt] using hfR
  · exact zero_of_eval_zero _ hf

open Cardinal in
lemma exists_eval_ne_zero_of_natDegree_lt_card (f : R[X]) (hf : f ≠ 0) (hfR : f.natDegree < #R) :
    ∃ r, f.eval r ≠ 0 := by
  contrapose! hf
  exact eq_zero_of_forall_eval_zero_of_natDegree_lt_card f hf hfR

theorem monic_prod_multiset_X_sub_C : Monic (p.roots.map fun a => X - C a).prod :=
  monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a
set_option linter.uppercaseLean3 false in
#align polynomial.monic_prod_multiset_X_sub_C Polynomial.monic_prod_multiset_X_sub_C

theorem prod_multiset_root_eq_finset_root [DecidableEq R] :
    (p.roots.map fun a => X - C a).prod =
      p.roots.toFinset.prod fun a => (X - C a) ^ rootMultiplicity a p := by
  simp only [count_roots, Finset.prod_multiset_map_count]
#align polynomial.prod_multiset_root_eq_finset_root Polynomial.prod_multiset_root_eq_finset_root

/-- The product `∏ (X - a)` for `a` inside the multiset `p.roots` divides `p`. -/
theorem prod_multiset_X_sub_C_dvd (p : R[X]) : (p.roots.map fun a => X - C a).prod ∣ p := by
  classical
  rw [← map_dvd_map _ (IsFractionRing.injective R <| FractionRing R) monic_prod_multiset_X_sub_C]
  rw [prod_multiset_root_eq_finset_root, Polynomial.map_prod]
  refine Finset.prod_dvd_of_coprime (fun a _ b _ h => ?_) fun a _ => ?_
  · simp_rw [Polynomial.map_pow, Polynomial.map_sub, map_C, map_X]
    exact (pairwise_coprime_X_sub_C (IsFractionRing.injective R <| FractionRing R) h).pow
  · exact Polynomial.map_dvd _ (pow_rootMultiplicity_dvd p a)
set_option linter.uppercaseLean3 false in
#align polynomial.prod_multiset_X_sub_C_dvd Polynomial.prod_multiset_X_sub_C_dvd

/-- A Galois connection. -/
theorem _root_.Multiset.prod_X_sub_C_dvd_iff_le_roots {p : R[X]} (hp : p ≠ 0) (s : Multiset R) :
    (s.map fun a => X - C a).prod ∣ p ↔ s ≤ p.roots := by
  classical exact
  ⟨fun h =>
    Multiset.le_iff_count.2 fun r => by
      rw [count_roots, le_rootMultiplicity_iff hp, ← Multiset.prod_replicate, ←
        Multiset.map_replicate fun a => X - C a, ← Multiset.filter_eq]
      exact (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| s.filter_le _).trans h,
    fun h =>
    (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map h).trans p.prod_multiset_X_sub_C_dvd⟩
set_option linter.uppercaseLean3 false in
#align multiset.prod_X_sub_C_dvd_iff_le_roots Multiset.prod_X_sub_C_dvd_iff_le_roots

theorem exists_prod_multiset_X_sub_C_mul (p : R[X]) :
    ∃ q,
      (p.roots.map fun a => X - C a).prod * q = p ∧
        Multiset.card p.roots + q.natDegree = p.natDegree ∧ q.roots = 0 := by
  obtain ⟨q, he⟩ := p.prod_multiset_X_sub_C_dvd
  use q, he.symm
  obtain rfl | hq := eq_or_ne q 0
  · rw [mul_zero] at he
    subst he
    simp
  constructor
  · conv_rhs => rw [he]
    rw [monic_prod_multiset_X_sub_C.natDegree_mul' hq, natDegree_multiset_prod_X_sub_C_eq_card]
  · replace he := congr_arg roots he.symm
    rw [roots_mul, roots_multiset_prod_X_sub_C] at he
    exacts [add_right_eq_self.1 he, mul_ne_zero monic_prod_multiset_X_sub_C.ne_zero hq]
set_option linter.uppercaseLean3 false in
#align polynomial.exists_prod_multiset_X_sub_C_mul Polynomial.exists_prod_multiset_X_sub_C_mul

/-- A polynomial `p` that has as many roots as its degree
can be written `p = p.leadingCoeff * ∏(X - a)`, for `a` in `p.roots`. -/
theorem C_leadingCoeff_mul_prod_multiset_X_sub_C (hroots : Multiset.card p.roots = p.natDegree) :
    C p.leadingCoeff * (p.roots.map fun a => X - C a).prod = p :=
  (eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le monic_prod_multiset_X_sub_C
      p.prod_multiset_X_sub_C_dvd
      ((natDegree_multiset_prod_X_sub_C_eq_card _).trans hroots).ge).symm
set_option linter.uppercaseLean3 false in
#align polynomial.C_leading_coeff_mul_prod_multiset_X_sub_C Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C

/-- A monic polynomial `p` that has as many roots as its degree
can be written `p = ∏(X - a)`, for `a` in `p.roots`. -/
theorem prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp : p.Monic)
    (hroots : Multiset.card p.roots = p.natDegree) : (p.roots.map fun a => X - C a).prod = p := by
  convert C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  rw [hp.leadingCoeff, C_1, one_mul]
set_option linter.uppercaseLean3 false in
#align polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq

theorem Monic.isUnit_leadingCoeff_of_dvd {a p : R[X]} (hp : Monic p) (hap : a ∣ p) :
    IsUnit a.leadingCoeff :=
  isUnit_of_dvd_one (by simpa only [hp.leadingCoeff] using leadingCoeff_dvd_leadingCoeff hap)

/-- To check a monic polynomial is irreducible, it suffices to check only for
divisors that have smaller degree.

See also: `Polynomial.Monic.irreducible_iff_natDegree`.
-/
theorem Monic.irreducible_iff_degree_lt {p : R[X]} (p_monic : Monic p) (p_1 : p ≠ 1) :
    Irreducible p ↔ ∀ q, degree q ≤ ↑(p.natDegree / 2) → q ∣ p → IsUnit q := by
  simp only [p_monic.irreducible_iff_lt_natDegree_lt p_1, Finset.mem_Ioc, and_imp,
    natDegree_pos_iff_degree_pos, natDegree_le_iff_degree_le]
  constructor
  · rintro h q deg_le dvd
    by_contra q_unit
    have := degree_pos_of_not_isUnit_of_dvd_monic p_monic q_unit dvd
    have hu := p_monic.isUnit_leadingCoeff_of_dvd dvd
    refine (h _ (monic_of_isUnit_leadingCoeff_inv_smul hu) ?_ ?_ (dvd_trans ?_ dvd)).elim
    · rwa [degree_smul_of_smul_regular _ (isSMulRegular_of_group _)]
    · rwa [degree_smul_of_smul_regular _ (isSMulRegular_of_group _)]
    · rw [Units.smul_def, Polynomial.smul_eq_C_mul, (isUnit_C.mpr (Units.isUnit _)).mul_left_dvd]
  · rintro h q _ deg_pos deg_le dvd
    exact deg_pos.ne' <| degree_eq_zero_of_isUnit (h q deg_le dvd)

end CommRing

section

variable {A B : Type*} [CommRing A] [CommRing B]

theorem le_rootMultiplicity_map {p : A[X]} {f : A →+* B} (hmap : map f p ≠ 0) (a : A) :
    rootMultiplicity a p ≤ rootMultiplicity (f a) (p.map f) := by
  rw [le_rootMultiplicity_iff hmap]
  refine _root_.trans ?_ ((mapRingHom f).map_dvd (pow_rootMultiplicity_dvd p a))
  rw [map_pow, map_sub, coe_mapRingHom, map_X, map_C]
#align polynomial.le_root_multiplicity_map Polynomial.le_rootMultiplicity_map

theorem eq_rootMultiplicity_map {p : A[X]} {f : A →+* B} (hf : Function.Injective f) (a : A) :
    rootMultiplicity a p = rootMultiplicity (f a) (p.map f) := by
  by_cases hp0 : p = 0; · simp only [hp0, rootMultiplicity_zero, Polynomial.map_zero]
  apply le_antisymm (le_rootMultiplicity_map ((Polynomial.map_ne_zero_iff hf).mpr hp0) a)
  rw [le_rootMultiplicity_iff hp0, ← map_dvd_map f hf ((monic_X_sub_C a).pow _),
    Polynomial.map_pow, Polynomial.map_sub, map_X, map_C]
  apply pow_rootMultiplicity_dvd
#align polynomial.eq_root_multiplicity_map Polynomial.eq_rootMultiplicity_map

theorem count_map_roots [IsDomain A] [DecidableEq B] {p : A[X]} {f : A →+* B} (hmap : map f p ≠ 0)
    (b : B) :
    (p.roots.map f).count b ≤ rootMultiplicity b (p.map f) := by
  rw [le_rootMultiplicity_iff hmap, ← Multiset.prod_replicate, ←
    Multiset.map_replicate fun a => X - C a]
  rw [← Multiset.filter_eq]
  refine
    (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| Multiset.filter_le (Eq b) _).trans ?_
  convert Polynomial.map_dvd f p.prod_multiset_X_sub_C_dvd
  simp only [Polynomial.map_multiset_prod, Multiset.map_map]
  congr; ext1
  simp only [Function.comp_apply, Polynomial.map_sub, map_X, map_C]
#align polynomial.count_map_roots Polynomial.count_map_roots

theorem count_map_roots_of_injective [IsDomain A] [DecidableEq B] (p : A[X]) {f : A →+* B}
    (hf : Function.Injective f) (b : B) :
    (p.roots.map f).count b ≤ rootMultiplicity b (p.map f) := by
  by_cases hp0 : p = 0
  · simp only [hp0, roots_zero, Multiset.map_zero, Multiset.count_zero, Polynomial.map_zero,
      rootMultiplicity_zero, le_refl]
  · exact count_map_roots ((Polynomial.map_ne_zero_iff hf).mpr hp0) b
#align polynomial.count_map_roots_of_injective Polynomial.count_map_roots_of_injective

theorem map_roots_le [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B} (h : p.map f ≠ 0) :
    p.roots.map f ≤ (p.map f).roots := by
  classical
  exact Multiset.le_iff_count.2 fun b => by
    rw [count_roots]
    apply count_map_roots h
#align polynomial.map_roots_le Polynomial.map_roots_le

theorem map_roots_le_of_injective [IsDomain A] [IsDomain B] (p : A[X]) {f : A →+* B}
    (hf : Function.Injective f) : p.roots.map f ≤ (p.map f).roots := by
  by_cases hp0 : p = 0
  · simp only [hp0, roots_zero, Multiset.map_zero, Polynomial.map_zero, le_rfl]
  exact map_roots_le ((Polynomial.map_ne_zero_iff hf).mpr hp0)
#align polynomial.map_roots_le_of_injective Polynomial.map_roots_le_of_injective

theorem card_roots_le_map [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B} (h : p.map f ≠ 0) :
    Multiset.card p.roots ≤ Multiset.card (p.map f).roots := by
  rw [← p.roots.card_map f]
  exact Multiset.card_le_card (map_roots_le h)
#align polynomial.card_roots_le_map Polynomial.card_roots_le_map

theorem card_roots_le_map_of_injective [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B}
    (hf : Function.Injective f) : Multiset.card p.roots ≤ Multiset.card (p.map f).roots := by
  by_cases hp0 : p = 0
  · simp only [hp0, roots_zero, Polynomial.map_zero, Multiset.card_zero, le_rfl]
  exact card_roots_le_map ((Polynomial.map_ne_zero_iff hf).mpr hp0)
#align polynomial.card_roots_le_map_of_injective Polynomial.card_roots_le_map_of_injective

theorem roots_map_of_injective_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p : A[X]}
    {f : A →+* B} (hf : Function.Injective f) (hroots : Multiset.card p.roots = p.natDegree) :
    p.roots.map f = (p.map f).roots := by
  apply Multiset.eq_of_le_of_card_le (map_roots_le_of_injective p hf)
  simpa only [Multiset.card_map, hroots] using (card_roots' _).trans (natDegree_map_le f p)
#align polynomial.roots_map_of_injective_of_card_eq_nat_degree Polynomial.roots_map_of_injective_of_card_eq_natDegree

end

end Polynomial
