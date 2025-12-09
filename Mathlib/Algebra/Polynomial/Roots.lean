/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker, Johan Commelin
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.SetTheory.Cardinal.Order

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

@[expose] public section

assert_not_exists Ideal

open Multiset Finset

noncomputable section

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

section CommRing

variable [CommRing R] [IsDomain R] {p q : R[X]}

section Roots

/-- `roots p` noncomputably gives a multiset containing all the roots of `p`,
including their multiplicities. -/
noncomputable def roots (p : R[X]) : Multiset R :=
  haveI := Classical.decEq R
  haveI := Classical.dec (p = 0)
  if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h)

theorem roots_def [DecidableEq R] (p : R[X]) [Decidable (p = 0)] :
    p.roots = if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h) := by
  rename_i iR ip0
  obtain rfl := Subsingleton.elim iR (Classical.decEq R)
  obtain rfl := Subsingleton.elim ip0 (Classical.dec (p = 0))
  rfl

@[simp]
theorem roots_zero : (0 : R[X]).roots = 0 :=
  dif_pos rfl

theorem card_roots (hp0 : p ≠ 0) : (Multiset.card (roots p) : WithBot ℕ) ≤ degree p := by
  classical
  unfold roots
  rw [dif_neg hp0]
  exact (Classical.choose_spec (exists_multiset_roots hp0)).1

theorem card_roots' (p : R[X]) : Multiset.card p.roots ≤ natDegree p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact WithBot.coe_le_coe.1 (le_trans (card_roots hp0) (le_of_eq <| degree_eq_natDegree hp0))

theorem card_roots_sub_C {p : R[X]} {a : R} (hp0 : 0 < degree p) :
    (Multiset.card (p - C a).roots : WithBot ℕ) ≤ degree p :=
  calc
    (Multiset.card (p - C a).roots : WithBot ℕ) ≤ degree (p - C a) :=
      card_roots <| mt sub_eq_zero.1 fun h => not_le_of_gt hp0 <| h.symm ▸ degree_C_le
    _ = degree p := by rw [sub_eq_add_neg, ← C_neg]; exact degree_add_C hp0

theorem card_roots_sub_C' {p : R[X]} {a : R} (hp0 : 0 < degree p) :
    Multiset.card (p - C a).roots ≤ natDegree p :=
  WithBot.coe_le_coe.1
    (le_trans (card_roots_sub_C hp0)
      (le_of_eq <| degree_eq_natDegree fun h => by simp_all))

@[simp]
theorem count_roots [DecidableEq R] (p : R[X]) : p.roots.count a = rootMultiplicity a p := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  rw [roots_def, dif_neg hp]
  exact (Classical.choose_spec (exists_multiset_roots hp)).2 a

@[simp]
theorem mem_roots' : a ∈ p.roots ↔ p ≠ 0 ∧ IsRoot p a := by
  classical
  rw [← count_pos, count_roots p, rootMultiplicity_pos']

theorem mem_roots (hp : p ≠ 0) : a ∈ p.roots ↔ IsRoot p a :=
  mem_roots'.trans <| and_iff_right hp

theorem ne_zero_of_mem_roots (h : a ∈ p.roots) : p ≠ 0 :=
  (mem_roots'.1 h).1

theorem isRoot_of_mem_roots (h : a ∈ p.roots) : IsRoot p a :=
  (mem_roots'.1 h).2

theorem roots_eq_zero_iff_isRoot_eq_bot (hp0 : p ≠ 0) : p.roots = 0 ↔ p.IsRoot = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ eq_zero_of_forall_notMem fun x hx ↦ h ▸ mem_roots hp0 |>.mp hx⟩
  ext a
  simp only [Pi.bot_apply, Prop.bot_eq_false, mem_roots hp0 |>.not.mp <| by simp [h]]

theorem roots_eq_zero_iff_eq_zero_or_isRoot_eq_bot : p.roots = 0 ↔ p = 0 ∨ p.IsRoot = ⊥ := by
  rcases eq_or_ne p 0 with rfl | hp0; · simp
  simp [roots_eq_zero_iff_isRoot_eq_bot hp0, hp0]

theorem mem_roots_map_of_injective [Semiring S] {p : S[X]} {f : S →+* R}
    (hf : Function.Injective f) {x : R} (hp : p ≠ 0) : x ∈ (p.map f).roots ↔ p.eval₂ f x = 0 := by
  rw [mem_roots ((Polynomial.map_ne_zero_iff hf).mpr hp), IsRoot, eval_map]

lemma mem_roots_iff_aeval_eq_zero {x : R} (w : p ≠ 0) : x ∈ roots p ↔ aeval x p = 0 := by
  rw [aeval_def, ← mem_roots_map_of_injective (FaithfulSMul.algebraMap_injective _ _) w,
    Algebra.algebraMap_self, map_id]

theorem card_le_degree_of_subset_roots {p : R[X]} {Z : Finset R} (h : Z.val ⊆ p.roots) :
    #Z ≤ p.natDegree :=
  (Multiset.card_le_card (Finset.val_le_iff_val_subset.2 h)).trans (Polynomial.card_roots' p)

theorem finite_setOf_isRoot {p : R[X]} (hp : p ≠ 0) : Set.Finite { x | IsRoot p x } := by
  classical
  simpa only [← Finset.setOf_mem, Multiset.mem_toFinset, mem_roots hp]
    using p.roots.toFinset.finite_toSet

theorem eq_zero_of_infinite_isRoot (p : R[X]) (h : Set.Infinite { x | IsRoot p x }) : p = 0 :=
  not_imp_comm.mp finite_setOf_isRoot h

theorem exists_max_root [LinearOrder R] (p : R[X]) (hp : p ≠ 0) : ∃ x₀, ∀ x, p.IsRoot x → x ≤ x₀ :=
  Set.exists_upper_bound_image _ _ <| finite_setOf_isRoot hp

theorem exists_min_root [LinearOrder R] (p : R[X]) (hp : p ≠ 0) : ∃ x₀, ∀ x, p.IsRoot x → x₀ ≤ x :=
  Set.exists_lower_bound_image _ _ <| finite_setOf_isRoot hp

theorem eq_of_infinite_eval_eq (p q : R[X]) (h : Set.Infinite { x | eval x p = eval x q }) :
    p = q := by
  rw [← sub_eq_zero]
  apply eq_zero_of_infinite_isRoot
  simpa only [IsRoot, eval_sub, sub_eq_zero]

theorem roots_mul {p q : R[X]} (hpq : p * q ≠ 0) : (p * q).roots = p.roots + q.roots := by
  classical
  exact Multiset.ext.mpr fun r => by
    rw [count_add, count_roots, count_roots, count_roots, rootMultiplicity_mul hpq]

theorem roots.le_of_dvd (h : q ≠ 0) : p ∣ q → roots p ≤ roots q := by
  rintro ⟨k, rfl⟩
  exact Multiset.le_iff_exists_add.mpr ⟨k.roots, roots_mul h⟩

theorem mem_roots_sub_C' {p : R[X]} {a x : R} : x ∈ (p - C a).roots ↔ p ≠ C a ∧ p.eval x = a := by
  rw [mem_roots', IsRoot.def, sub_ne_zero, eval_sub, sub_eq_zero, eval_C]

theorem mem_roots_sub_C {p : R[X]} {a x : R} (hp0 : 0 < degree p) :
    x ∈ (p - C a).roots ↔ p.eval x = a :=
  mem_roots_sub_C'.trans <| and_iff_right fun hp => hp0.not_ge <| hp.symm ▸ degree_C_le

@[simp]
theorem roots_X_sub_C (r : R) : roots (X - C r) = {r} := by
  classical
  ext s
  rw [count_roots, rootMultiplicity_X_sub_C, count_singleton]

@[simp]
theorem roots_X_add_C (r : R) : roots (X + C r) = {-r} := by simpa using roots_X_sub_C (-r)

@[simp]
theorem roots_X : roots (X : R[X]) = {0} := by rw [← roots_X_sub_C, C_0, sub_zero]

@[simp]
theorem roots_C (x : R) : (C x).roots = 0 := by
  classical exact
  if H : x = 0 then by rw [H, C_0, roots_zero]
  else
    Multiset.ext.mpr fun r => (by
      rw [count_roots, count_zero, rootMultiplicity_eq_zero (not_isRoot_C _ _ H)])

@[simp]
theorem roots_one : (1 : R[X]).roots = ∅ :=
  roots_C 1

@[simp]
theorem roots_C_mul (p : R[X]) (ha : a ≠ 0) : (C a * p).roots = p.roots := by
  by_cases hp : p = 0 <;>
    simp only [roots_mul, *, Ne, mul_eq_zero, C_eq_zero, or_self_iff, not_false_iff, roots_C,
      zero_add, mul_zero]

theorem _root_.Associated.roots_eq {p q : R[X]} (h : Associated p q) : p.roots = q.roots := by
  obtain ⟨u, rfl⟩ := h
  rw [eq_C_of_degree_eq_zero <| degree_coe_units u, mul_comm,
    roots_C_mul _ <| coeff_coe_units_zero_ne_zero u]

@[simp]
theorem roots_smul_nonzero (p : R[X]) (ha : a ≠ 0) : (a • p).roots = p.roots := by
  rw [smul_eq_C_mul, roots_C_mul _ ha]

@[simp]
lemma roots_neg (p : R[X]) : (-p).roots = p.roots := by
  rw [← neg_one_smul R p, roots_smul_nonzero p (neg_ne_zero.mpr one_ne_zero)]

@[simp]
theorem roots_C_mul_X_sub_C_of_IsUnit (b : R) (a : Rˣ) : (C (a : R) * X - C b).roots =
    {a⁻¹ * b} := by
  rw [← roots_C_mul _ (Units.ne_zero a⁻¹), mul_sub, ← mul_assoc, ← C_mul, ← C_mul,
    Units.inv_mul, C_1, one_mul]
  exact roots_X_sub_C (a⁻¹ * b)

@[simp]
theorem roots_C_mul_X_add_C_of_IsUnit (b : R) (a : Rˣ) : (C (a : R) * X + C b).roots =
    {-(a⁻¹ * b)} := by
  rw [← sub_neg_eq_add, ← C_neg, roots_C_mul_X_sub_C_of_IsUnit, mul_neg]

theorem roots_list_prod (L : List R[X]) :
    (0 : R[X]) ∉ L → L.prod.roots = (L : Multiset R[X]).bind roots :=
  List.recOn L (fun _ => roots_one) fun hd tl ih H => by
    rw [List.mem_cons, not_or] at H
    rw [List.prod_cons, roots_mul (mul_ne_zero (Ne.symm H.1) <| List.prod_ne_zero H.2), ←
      Multiset.cons_coe, Multiset.cons_bind, ih H.2]

theorem roots_multiset_prod (m : Multiset R[X]) : (0 : R[X]) ∉ m → m.prod.roots = m.bind roots := by
  rcases m with ⟨L⟩
  simpa only [Multiset.prod_coe, quot_mk_to_coe''] using roots_list_prod L

theorem roots_prod {ι : Type*} (f : ι → R[X]) (s : Finset ι) :
    s.prod f ≠ 0 → (s.prod f).roots = s.val.bind fun i => roots (f i) := by
  rcases s with ⟨m, hm⟩
  simpa [Multiset.prod_eq_zero_iff, Multiset.bind_map] using roots_multiset_prod (m.map f)

@[simp]
theorem roots_pow (p : R[X]) (n : ℕ) : (p ^ n).roots = n • p.roots := by
  induction n with
  | zero => rw [pow_zero, roots_one, zero_smul, empty_eq_zero]
  | succ n ihn =>
    rcases eq_or_ne p 0 with (rfl | hp)
    · rw [zero_pow n.succ_ne_zero, roots_zero, smul_zero]
    · rw [pow_succ, roots_mul (mul_ne_zero (pow_ne_zero _ hp) hp), ihn, add_smul, one_smul]

theorem roots_X_pow (n : ℕ) : (X ^ n : R[X]).roots = n • ({0} : Multiset R) := by
  rw [roots_pow, roots_X]

theorem roots_C_mul_X_pow (ha : a ≠ 0) (n : ℕ) :
    Polynomial.roots (C a * X ^ n) = n • ({0} : Multiset R) := by
  rw [roots_C_mul _ ha, roots_X_pow]

@[simp]
theorem roots_monomial (ha : a ≠ 0) (n : ℕ) : (monomial n a).roots = n • ({0} : Multiset R) := by
  rw [← C_mul_X_pow_eq_monomial, roots_C_mul_X_pow ha]

theorem roots_prod_X_sub_C (s : Finset R) : (s.prod fun a => X - C a).roots = s.val := by
  apply (roots_prod (fun a => X - C a) s ?_).trans
  · simp_rw [roots_X_sub_C]
    rw [Multiset.bind_singleton, Multiset.map_id']
  · refine prod_ne_zero_iff.mpr (fun a _ => X_sub_C_ne_zero a)

@[simp]
theorem roots_multiset_prod_X_sub_C (s : Multiset R) : (s.map fun a => X - C a).prod.roots = s := by
  rw [roots_multiset_prod, Multiset.bind_map]
  · simp_rw [roots_X_sub_C]
    rw [Multiset.bind_singleton, Multiset.map_id']
  · rw [Multiset.mem_map]
    rintro ⟨a, -, h⟩
    exact X_sub_C_ne_zero a h

theorem roots_ofMultiset (s : Multiset R) : (ofMultiset s).roots = s := by
  simp

variable (R) in
theorem rightInverse_ofMultiset_roots : Function.RightInverse (α := R[X]) ofMultiset roots :=
  roots_ofMultiset

variable (R) in
theorem ofMultiset_injective : Function.Injective (ofMultiset (R := R)) :=
  rightInverse_ofMultiset_roots R |>.injective

theorem card_roots_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) :
    Multiset.card (roots ((X : R[X]) ^ n - C a)) ≤ n :=
  WithBot.coe_le_coe.1 <|
    calc
      (Multiset.card (roots ((X : R[X]) ^ n - C a)) : WithBot ℕ) ≤ degree ((X : R[X]) ^ n - C a) :=
        card_roots (X_pow_sub_C_ne_zero hn a)
      _ = n := degree_X_pow_sub_C hn a

theorem roots_eq_of_degree_le_card_of_ne_zero {S : Finset R}
    (hS : ∀ x ∈ S, p.eval x = 0) (hcard : p.degree ≤ S.card) (hp : p ≠ 0) : p.roots = S.val := by
  refine (Multiset.eq_of_le_of_card_le ?_ ?_).symm
  · exact (Finset.val_le_iff_val_subset.mpr (fun x hx ↦ (p.mem_roots hp).mpr (hS x hx)))
  · simpa using (p.card_roots hp).trans hcard

theorem roots_eq_of_degree_eq_card {S : Finset R}
    (hS : ∀ x ∈ S, p.eval x = 0) (hcard : S.card = p.degree) : p.roots = S.val :=
  roots_eq_of_degree_le_card_of_ne_zero hS (by lia) (by contrapose! hcard; simp [hcard])

theorem roots_eq_of_natDegree_le_card_of_ne_zero {S : Finset R}
    (hS : ∀ x ∈ S, p.eval x = 0) (hcard : p.natDegree ≤ S.card) (hp : p ≠ 0) : p.roots = S.val :=
  roots_eq_of_degree_le_card_of_ne_zero hS (degree_le_of_natDegree_le hcard) hp

section NthRoots

/-- `nthRoots n a` noncomputably returns the solutions to `x ^ n = a`. -/
def nthRoots (n : ℕ) (a : R) : Multiset R :=
  roots ((X : R[X]) ^ n - C a)

@[simp]
theorem mem_nthRoots {n : ℕ} (hn : 0 < n) {a x : R} : x ∈ nthRoots n a ↔ x ^ n = a := by
  rw [nthRoots, mem_roots (X_pow_sub_C_ne_zero hn a), IsRoot.def, eval_sub, eval_C, eval_pow,
    eval_X, sub_eq_zero]

@[simp]
theorem nthRoots_zero (r : R) : nthRoots 0 r = 0 := by
  simp only [pow_zero, nthRoots, ← C_1, ← C_sub, roots_C]

@[simp]
theorem nthRoots_zero_right {R} [CommRing R] [IsDomain R] (n : ℕ) :
    nthRoots n (0 : R) = Multiset.replicate n 0 := by
  rw [nthRoots, C.map_zero, sub_zero, roots_pow, roots_X, Multiset.nsmul_singleton]

theorem card_nthRoots (n : ℕ) (a : R) : Multiset.card (nthRoots n a) ≤ n := by
  classical exact
  (if hn : n = 0 then
    if h : (X : R[X]) ^ n - C a = 0 then by
      simp [nthRoots, roots, h, empty_eq_zero, Multiset.card_zero]
    else
      WithBot.coe_le_coe.1
        (le_trans (card_roots h)
          (by
            rw [hn, pow_zero, ← C_1, ← map_sub]
            exact degree_C_le))
  else by
    rw [← Nat.cast_le (α := WithBot ℕ)]
    rw [← degree_X_pow_sub_C (Nat.pos_of_ne_zero hn) a]
    exact card_roots (X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) a))

@[simp]
theorem nthRoots_two_eq_zero_iff {r : R} : nthRoots 2 r = 0 ↔ ¬IsSquare r := by
  simp_rw [isSquare_iff_exists_sq, eq_zero_iff_forall_notMem, mem_nthRoots (by simp : 0 < 2),
    ← not_exists, eq_comm]

/-- The multiset `nthRoots ↑n a` as a Finset. Previously `nthRootsFinset n` was defined to be
`nthRoots n (1 : R)` as a Finset. That situation can be recovered by setting `a` to be `(1 : R)` -/
def nthRootsFinset (n : ℕ) {R : Type*} (a : R) [CommRing R] [IsDomain R] : Finset R :=
  haveI := Classical.decEq R
  Multiset.toFinset (nthRoots n a)

lemma nthRootsFinset_def (n : ℕ) {R : Type*} (a : R) [CommRing R] [IsDomain R] [DecidableEq R] :
    nthRootsFinset n a = Multiset.toFinset (nthRoots n a) := by
  unfold nthRootsFinset
  convert rfl

@[simp]
theorem mem_nthRootsFinset {n : ℕ} (h : 0 < n) (a : R) {x : R} :
    x ∈ nthRootsFinset n a ↔ x ^ (n : ℕ) = a := by
  classical
  rw [nthRootsFinset_def, mem_toFinset, mem_nthRoots h]

@[simp]
theorem nthRootsFinset_zero (a : R) : nthRootsFinset 0 a = ∅ := by
  classical simp [nthRootsFinset_def]

theorem map_mem_nthRootsFinset {S F : Type*} [CommRing S] [IsDomain S] [FunLike F R S]
    [MonoidHomClass F R S] {a : R} {x : R} (hx : x ∈ nthRootsFinset n a) (f : F) :
    f x ∈ nthRootsFinset n (f a) := by
  by_cases hn : n = 0
  · simp [hn] at hx
  · rw [mem_nthRootsFinset <| Nat.pos_of_ne_zero hn, ← map_pow, (mem_nthRootsFinset
      (Nat.pos_of_ne_zero hn) a).1 hx]

theorem map_mem_nthRootsFinset_one {S F : Type*} [CommRing S] [IsDomain S] [FunLike F R S]
    [RingHomClass F R S] {x : R} (hx : x ∈ nthRootsFinset n 1) (f : F) :
    f x ∈ nthRootsFinset n 1 := by
  rw [← (map_one f)]
  exact map_mem_nthRootsFinset hx _

theorem mul_mem_nthRootsFinset
    {η₁ η₂ : R} {a₁ a₂ : R} (hη₁ : η₁ ∈ nthRootsFinset n a₁) (hη₂ : η₂ ∈ nthRootsFinset n a₂) :
    η₁ * η₂ ∈ nthRootsFinset n (a₁ * a₂) := by
  cases n with
  | zero =>
    simp only [nthRootsFinset_zero, notMem_empty] at hη₁
  | succ n =>
    rw [mem_nthRootsFinset n.succ_pos] at hη₁ hη₂ ⊢
    rw [mul_pow, hη₁, hη₂]

theorem ne_zero_of_mem_nthRootsFinset {η : R} {a : R} (ha : a ≠ 0) (hη : η ∈ nthRootsFinset n a) :
    η ≠ 0 := by
  nontriviality R
  rintro rfl
  cases n with
  | zero =>
    simp only [nthRootsFinset_zero, notMem_empty] at hη
  | succ n =>
    rw [mem_nthRootsFinset n.succ_pos, zero_pow n.succ_ne_zero] at hη
    exact ha hη.symm

theorem one_mem_nthRootsFinset (hn : 0 < n) : 1 ∈ nthRootsFinset n (1 : R) := by
  rw [mem_nthRootsFinset hn, one_pow]

lemma nthRoots_two_one : Polynomial.nthRoots 2 (1 : R) = {-1,1} := by
  have h₁ : (X ^ 2 - C 1 : R[X]) = (X + C 1) * (X - C 1) := by simp [← sq_sub_sq]
  have h₂ : (X ^ 2 - C 1 : R[X]) ≠ 0 := fun h ↦ by simpa using congrArg (coeff · 0) h
  rw [nthRoots, h₁, roots_mul (h₁ ▸ h₂), roots_X_add_C, roots_X_sub_C]; rfl

end NthRoots

theorem zero_of_eval_zero [Infinite R] (p : R[X]) (h : ∀ x, p.eval x = 0) : p = 0 := by
  classical
  by_contra hp
  refine @Fintype.false R _ ?_
  exact ⟨p.roots.toFinset, fun x => Multiset.mem_toFinset.mpr ((mem_roots hp).mpr (h _))⟩

theorem funext [Infinite R] {p q : R[X]} (ext : ∀ r : R, p.eval r = q.eval r) : p = q := by
  rw [← sub_eq_zero]
  apply zero_of_eval_zero
  intro x
  rw [eval_sub, sub_eq_zero, ext]

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

theorem mem_aroots [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {p : T[X]} {a : S} : a ∈ p.aroots S ↔ p ≠ 0 ∧ aeval a p = 0 := by
  rw [mem_aroots', Polynomial.map_ne_zero_iff]
  exact FaithfulSMul.algebraMap_injective T S

theorem aroots_mul [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {p q : T[X]} (hpq : p * q ≠ 0) :
    (p * q).aroots S = p.aroots S + q.aroots S := by
  suffices map (algebraMap T S) p * map (algebraMap T S) q ≠ 0 by
    rw [aroots_def, Polynomial.map_mul, roots_mul this]
  rwa [← Polynomial.map_mul, Polynomial.map_ne_zero_iff
    (FaithfulSMul.algebraMap_injective T S)]

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
theorem aroots_C_mul [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {a : T} (p : T[X]) (ha : a ≠ 0) :
    (C a * p).aroots S = p.aroots S := by
  rw [aroots_def, Polynomial.map_mul, map_C, roots_C_mul]
  rwa [map_ne_zero_iff]
  exact FaithfulSMul.algebraMap_injective T S

@[simp]
theorem aroots_smul_nonzero [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {a : T} (p : T[X]) (ha : a ≠ 0) :
    (a • p).aroots S = p.aroots S := by
  rw [smul_eq_C_mul, aroots_C_mul _ ha]

@[simp]
theorem aroots_pow [CommRing S] [IsDomain S] [Algebra T S] (p : T[X]) (n : ℕ) :
    (p ^ n).aroots S = n • p.aroots S := by
  rw [aroots_def, Polynomial.map_pow, roots_pow]

theorem aroots_X_pow [CommRing S] [IsDomain S] [Algebra T S] (n : ℕ) :
    (X ^ n : T[X]).aroots S = n • ({0} : Multiset S) := by
  rw [aroots_pow, aroots_X]

theorem aroots_C_mul_X_pow [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {a : T} (ha : a ≠ 0) (n : ℕ) :
    (C a * X ^ n : T[X]).aroots S = n • ({0} : Multiset S) := by
  rw [aroots_C_mul _ ha, aroots_X_pow]

@[simp]
theorem aroots_monomial [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {a : T} (ha : a ≠ 0) (n : ℕ) :
    (monomial n a).aroots S = n • ({0} : Multiset S) := by
  rw [← C_mul_X_pow_eq_monomial, aroots_C_mul_X_pow ha]

variable (R S) in
@[simp]
theorem aroots_map (p : T[X]) [CommRing S] [Algebra T S] [Algebra S R] [Algebra T R]
    [IsScalarTower T S R] :
    (p.map (algebraMap T S)).aroots R = p.aroots R := by
  rw [aroots_def, aroots_def, map_map, IsScalarTower.algebraMap_eq T S R]

/-- The set of distinct roots of `p` in `S`.

If you have a non-separable polynomial, use `Polynomial.aroots` for the multiset
where multiple roots have the appropriate multiplicity. -/
def rootSet (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] : Set S :=
  haveI := Classical.decEq S
  (p.aroots S).toFinset

theorem rootSet_def (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] [DecidableEq S] :
    p.rootSet S = (p.aroots S).toFinset := by
  rw [rootSet]
  convert rfl

@[simp]
theorem rootSet_C [CommRing S] [IsDomain S] [Algebra T S] (a : T) : (C a).rootSet S = ∅ := by
  classical
  rw [rootSet_def, aroots_C, Multiset.toFinset_zero, Finset.coe_empty]

@[simp]
theorem rootSet_zero (S) [CommRing S] [IsDomain S] [Algebra T S] : (0 : T[X]).rootSet S = ∅ := by
  rw [← C_0, rootSet_C]

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

theorem rootSet_finite (p : T[X]) (S : Type*) [CommRing S] [IsDomain S] [Algebra T S] :
    (p.rootSet S).Finite :=
  Set.toFinite _

/-- The set of roots of all polynomials of bounded degree and having coefficients in a finite set
is finite. -/
theorem bUnion_roots_finite {R S : Type*} [Semiring R] [CommRing S] [IsDomain S] [DecidableEq S]
    (m : R →+* S) (d : ℕ) {U : Set R} (h : U.Finite) :
    (⋃ (f : R[X]) (_ : f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ U),
        ((f.map m).roots.toFinset : Set S)).Finite :=
  Set.Finite.biUnion
    (by
      -- We prove that the set of polynomials under consideration is finite because its
      -- image by the injective map `π` is finite
      let π : R[X] → Fin (d + 1) → R := fun f i => f.coeff i
      refine ((Set.Finite.pi fun _ => h).subset <| ?_).of_finite_image (?_ : Set.InjOn π _)
      · exact Set.image_subset_iff.2 fun f hf i _ => hf.2 i
      · refine fun x hx y hy hxy => (ext_iff_natDegree_le hx.1 hy.1).2 fun i hi => ?_
        exact id congr_fun hxy ⟨i, Nat.lt_succ_of_le hi⟩)
    fun _ _ => Finset.finite_toSet _

/-- A version of `mem_rootSet` that requires the polynomial to be non-zero after mapping
instead of requiring it to be non-zero and `NoZeroSMulDivisors`. -/
theorem mem_rootSet' {p : T[X]} {S : Type*} [CommRing S] [IsDomain S] [Algebra T S] {a : S} :
    a ∈ p.rootSet S ↔ p.map (algebraMap T S) ≠ 0 ∧ aeval a p = 0 := by
  classical
  rw [rootSet_def, Finset.mem_coe, mem_toFinset, mem_aroots']

/-- A version of `mem_rootSet'` that requires `Module.IsTorsionFree` and for the polynomial to be
non-zero instead of requiring it to be non-zero after mapping. -/
theorem mem_rootSet {p : T[X]} {S : Type*} [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {a : S} : a ∈ p.rootSet S ↔ p ≠ 0 ∧ aeval a p = 0 := by
  rw [mem_rootSet', Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective T S)]

lemma mem_rootSet_of_ne {p : T[X]} {S : Type*} [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] (hp : p ≠ 0) {a : S} : a ∈ p.rootSet S ↔ aeval a p = 0 :=
  mem_rootSet.trans <| and_iff_right hp

theorem Monic.mem_rootSet {p : T[X]} (hp : Monic p) {S : Type*} [CommRing S] [IsDomain S]
    [Algebra T S] {a : S} : a ∈ p.rootSet S ↔ aeval a p = 0 := by
  simp [Polynomial.mem_rootSet', (hp.map (algebraMap T S)).ne_zero]

theorem rootSet_maps_to' {p : T[X]} {S S'} [CommRing S] [IsDomain S] [Algebra T S] [CommRing S']
    [IsDomain S'] [Algebra T S'] (hp : p.map (algebraMap T S') = 0 → p.map (algebraMap T S) = 0)
    (f : S →ₐ[T] S') : (p.rootSet S).MapsTo f (p.rootSet S') := fun x hx => by
  rw [mem_rootSet'] at hx ⊢
  rw [aeval_algHom, AlgHom.comp_apply, hx.2, _root_.map_zero]
  exact ⟨mt hp hx.1, rfl⟩

theorem ne_zero_of_mem_rootSet {p : T[X]} [CommRing S] [IsDomain S] [Algebra T S] {a : S}
    (h : a ∈ p.rootSet S) : p ≠ 0 := fun hf => by rwa [hf, rootSet_zero] at h

theorem aeval_eq_zero_of_mem_rootSet {p : T[X]} [CommRing S] [IsDomain S] [Algebra T S] {a : S}
    (hx : a ∈ p.rootSet S) : aeval a p = 0 :=
  (mem_rootSet'.1 hx).2

lemma rootSet_mapsTo {p : T[X]} [IsDomain T] {S S' : Type*} [CommRing S] [IsDomain S] [Algebra T S]
    [CommRing S'] [IsDomain S'] [Algebra T S'] [Module.IsTorsionFree T S'] (f : S →ₐ[T] S') :
    (p.rootSet S).MapsTo f (p.rootSet S') := by
  refine rootSet_maps_to' (fun h₀ => ?_) f
  obtain rfl : p = 0 :=
    map_injective _ (FaithfulSMul.algebraMap_injective T S') (by rwa [Polynomial.map_zero])
  exact Polynomial.map_zero _

theorem mem_rootSet_of_injective [CommRing S] {p : S[X]} [Algebra S R]
    (h : Function.Injective (algebraMap S R)) {x : R} (hp : p ≠ 0) :
    x ∈ p.rootSet R ↔ aeval x p = 0 := by
  classical
  exact Multiset.mem_toFinset.trans (mem_roots_map_of_injective h hp)

@[simp]
theorem nthRootsFinset_toSet {n : ℕ} (h : 0 < n) (a : R) :
    nthRootsFinset n a = {r | r ^ n = a} := by
  ext x
  simp_all

end Roots

lemma eq_zero_of_natDegree_lt_card_of_eval_eq_zero {R} [CommRing R] [IsDomain R]
    (p : R[X]) {ι} [Fintype ι] {f : ι → R} (hf : Function.Injective f)
    (heval : ∀ i, p.eval (f i) = 0) (hcard : natDegree p < Fintype.card ι) : p = 0 := by
  classical
  by_contra hp
  refine lt_irrefl #p.roots.toFinset ?_
  calc
    #p.roots.toFinset ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ natDegree p := Polynomial.card_roots' p
    _ < Fintype.card ι := hcard
    _ = Fintype.card (Set.range f) := (Set.card_range_of_injective hf).symm
    _ = #(Finset.univ.image f) := by rw [← Set.toFinset_card, Set.toFinset_range]
    _ ≤ #p.roots.toFinset := Finset.card_mono ?_
  intro _
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Multiset.mem_toFinset, mem_roots', ne_eq,
    IsRoot.def, forall_exists_index, hp, not_false_eq_true]
  rintro x rfl
  exact heval _

lemma eq_of_natDegree_lt_card_of_eval_eq {R} [CommRing R] [IsDomain R]
    (p q : R[X]) {ι} [Fintype ι] {f : ι → R} (hf : Function.Injective f)
    (heval : ∀ i : ι, eval (f i) p = eval (f i) q)
    (hcard : max p.natDegree q.natDegree < Fintype.card ι) : p = q := by
  rw [← sub_eq_zero]
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hf
  · simpa [sub_eq_zero]
  · grind [natDegree_sub_le]

lemma eq_zero_of_natDegree_lt_card_of_eval_eq_zero' {R} [CommRing R] [IsDomain R]
    (p : R[X]) (s : Finset R) (heval : ∀ i ∈ s, p.eval i = 0) (hcard : natDegree p < #s) :
    p = 0 :=
  eq_zero_of_natDegree_lt_card_of_eval_eq_zero p Subtype.val_injective
    (fun i : s ↦ heval i i.prop) (hcard.trans_eq (Fintype.card_coe s).symm)

lemma eq_of_natDegree_lt_card_of_eval_eq' {R} [CommRing R] [IsDomain R]
    (p q : R[X]) (s : Finset R) (heval : ∀ i ∈ s, p.eval i = q.eval i)
    (hcard : max p.natDegree q.natDegree < #s) : p = q :=
  eq_of_natDegree_lt_card_of_eval_eq p q Subtype.val_injective
    (fun i : s ↦ heval i i.prop) (hcard.trans_eq (Fintype.card_coe s).symm)

open Cardinal in
lemma eq_zero_of_forall_eval_zero_of_natDegree_lt_card
    (f : R[X]) (hf : ∀ r, f.eval r = 0) (hfR : f.natDegree < #R) : f = 0 := by
  obtain hR | hR := finite_or_infinite R
  · have := Fintype.ofFinite R
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero f Function.injective_id hf
    simpa only [mk_fintype, Nat.cast_lt] using hfR
  · exact zero_of_eval_zero _ hf

open Cardinal in
lemma exists_eval_ne_zero_of_natDegree_lt_card (f : R[X]) (hf : f ≠ 0) (hfR : f.natDegree < #R) :
    ∃ r, f.eval r ≠ 0 := by
  contrapose! hf
  exact eq_zero_of_forall_eval_zero_of_natDegree_lt_card f hf hfR

section

omit [IsDomain R]

theorem monic_multisetProd_X_sub_C (s : Multiset R) : Monic (s.map fun a => X - C a).prod :=
  monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a

theorem monic_prod_X_sub_C {α : Type*} (b : α → R) (s : Finset α) :
    Monic (∏ a ∈ s, (X - C (b a))) :=
  monic_prod_of_monic _ _ fun a _ => monic_X_sub_C (b a)

theorem monic_finprod_X_sub_C {α : Type*} (b : α → R) : Monic (∏ᶠ k, (X - C (b k))) :=
  monic_finprod_of_monic _ _ fun a _ => monic_X_sub_C (b a)

end

theorem prod_multiset_root_eq_finset_root [DecidableEq R] :
    (p.roots.map fun a => X - C a).prod =
      p.roots.toFinset.prod fun a => (X - C a) ^ rootMultiplicity a p := by
  simp only [count_roots, Finset.prod_multiset_map_count]

/-- The product `∏ (X - a)` for `a` inside the multiset `p.roots` divides `p`. -/
theorem prod_multiset_X_sub_C_dvd (p : R[X]) : (p.roots.map fun a => X - C a).prod ∣ p := by
  classical
  rw [← map_dvd_map _ (IsFractionRing.injective R <| FractionRing R)
    (monic_multisetProd_X_sub_C p.roots)]
  rw [prod_multiset_root_eq_finset_root, Polynomial.map_prod]
  refine Finset.prod_dvd_of_coprime (fun a _ b _ h => ?_) fun a _ => ?_
  · simp_rw [Polynomial.map_pow, Polynomial.map_sub, map_C, map_X]
    exact (pairwise_coprime_X_sub_C (IsFractionRing.injective R <| FractionRing R) h).pow
  · exact Polynomial.map_dvd _ (pow_rootMultiplicity_dvd p a)

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
    rw [(monic_multisetProd_X_sub_C p.roots).natDegree_mul' hq,
      natDegree_multiset_prod_X_sub_C_eq_card]
  · replace he := congr_arg roots he.symm
    rw [roots_mul, roots_multiset_prod_X_sub_C] at he
    exacts [add_eq_left.1 he, mul_ne_zero (monic_multisetProd_X_sub_C p.roots).ne_zero hq]

/-- A polynomial `p` that has as many roots as its degree
can be written `p = p.leadingCoeff * ∏(X - a)`, for `a` in `p.roots`. -/
theorem C_leadingCoeff_mul_prod_multiset_X_sub_C (hroots : Multiset.card p.roots = p.natDegree) :
    C p.leadingCoeff * (p.roots.map fun a => X - C a).prod = p :=
  (eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (monic_multisetProd_X_sub_C p.roots)
      p.prod_multiset_X_sub_C_dvd
      ((natDegree_multiset_prod_X_sub_C_eq_card _).trans hroots).ge).symm

/-- A monic polynomial `p` that has as many roots as its degree
can be written `p = ∏(X - a)`, for `a` in `p.roots`. -/
theorem prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp : p.Monic)
    (hroots : Multiset.card p.roots = p.natDegree) : (p.roots.map fun a => X - C a).prod = p := by
  convert C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  rw [hp.leadingCoeff, C_1, one_mul]

theorem Monic.isUnit_leadingCoeff_of_dvd {a p : R[X]} (hp : Monic p) (hap : a ∣ p) :
    IsUnit a.leadingCoeff :=
  isUnit_of_dvd_one (by simpa only [hp.leadingCoeff] using leadingCoeff_dvd_leadingCoeff hap)

theorem card_roots_le_one_of_irreducible (hirr : Irreducible p) : p.roots.card ≤ 1 := by
  obtain hp | ⟨x, hx⟩ := p.roots.empty_or_exists_mem
  · simp [hp]
  convert p.card_roots'
  exact (natDegree_eq_of_degree_eq_some <| degree_eq_one_of_irreducible_of_root hirr <|
    isRoot_of_mem_roots hx).symm

theorem roots_eq_zero_of_irreducible_of_natDegree_ne_one (hirr : Irreducible p)
    (hdeg : p.natDegree ≠ 1) : p.roots = 0 := by
  by_contra hroots
  have ⟨x, hx⟩ := exists_mem_of_ne_zero hroots
  exact hdeg <| natDegree_eq_of_degree_eq_some <|
    degree_eq_one_of_irreducible_of_root hirr (mem_roots'.mp hx).right

/-- To check a monic polynomial is irreducible, it suffices to check only for
divisors that have smaller degree.

See also: `Polynomial.Monic.irreducible_iff_natDegree`.
-/
theorem Monic.irreducible_iff_degree_lt (p_monic : Monic p) (p_1 : p ≠ 1) :
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
  refine _root_.trans ?_ (_root_.map_dvd (mapRingHom f) (pow_rootMultiplicity_dvd p a))
  rw [map_pow, map_sub, coe_mapRingHom, map_X, map_C]

theorem eq_rootMultiplicity_map {p : A[X]} {f : A →+* B} (hf : Function.Injective f) (a : A) :
    rootMultiplicity a p = rootMultiplicity (f a) (p.map f) := by
  by_cases hp0 : p = 0; · simp only [hp0, rootMultiplicity_zero, Polynomial.map_zero]
  apply le_antisymm (le_rootMultiplicity_map ((Polynomial.map_ne_zero_iff hf).mpr hp0) a)
  rw [le_rootMultiplicity_iff hp0, ← map_dvd_map f hf ((monic_X_sub_C a).pow _),
    Polynomial.map_pow, Polynomial.map_sub, map_X, map_C]
  apply pow_rootMultiplicity_dvd

theorem count_map_roots [IsDomain A] [DecidableEq B] {p : A[X]} {f : A →+* B} (hmap : map f p ≠ 0)
    (b : B) :
    (p.roots.map f).count b ≤ rootMultiplicity b (p.map f) := by
  rw [le_rootMultiplicity_iff hmap, ← Multiset.prod_replicate, ←
    Multiset.map_replicate fun a => X - C a]
  rw [← Multiset.filter_eq]
  refine
    (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| Multiset.filter_le (Eq b) _).trans ?_
  convert Polynomial.map_dvd f p.prod_multiset_X_sub_C_dvd
  simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_apply,
    Polynomial.map_sub, map_X, map_C]

theorem count_map_roots_of_injective [IsDomain A] [DecidableEq B] (p : A[X]) {f : A →+* B}
    (hf : Function.Injective f) (b : B) :
    (p.roots.map f).count b ≤ rootMultiplicity b (p.map f) := by
  by_cases hp0 : p = 0
  · simp only [hp0, roots_zero, Multiset.map_zero, Multiset.count_zero, Polynomial.map_zero,
      rootMultiplicity_zero, le_refl]
  · exact count_map_roots ((Polynomial.map_ne_zero_iff hf).mpr hp0) b

theorem map_roots_le [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B} (h : p.map f ≠ 0) :
    p.roots.map f ≤ (p.map f).roots := by
  classical
  exact Multiset.le_iff_count.2 fun b => by
    rw [count_roots]
    apply count_map_roots h

theorem map_roots_le_of_injective [IsDomain A] [IsDomain B] (p : A[X]) {f : A →+* B}
    (hf : Function.Injective f) : p.roots.map f ≤ (p.map f).roots := by
  by_cases hp0 : p = 0
  · simp only [hp0, roots_zero, Multiset.map_zero, Polynomial.map_zero, le_rfl]
  exact map_roots_le ((Polynomial.map_ne_zero_iff hf).mpr hp0)

theorem card_roots_map_le_degree {A B : Type*} [Semiring A] [CommRing B] [IsDomain B]
    {f : A →+* B} (p : A[X]) (hp0 : p ≠ 0) : (p.map f).roots.card ≤ p.degree := by
  by_cases hpm0 : p.map f = 0
  · simp [hp0, hpm0, zero_le_degree_iff]
  exact card_roots hpm0 |>.trans degree_map_le

theorem card_roots_map_le_natDegree {A B : Type*} [Semiring A] [CommRing B] [IsDomain B]
    {f : A →+* B} (p : A[X]) : (p.map f).roots.card ≤ p.natDegree :=
  card_roots' _ |>.trans natDegree_map_le

theorem filter_roots_map_range_eq_map_roots [IsDomain A] [IsDomain B] {f : A →+* B}
    [DecidablePred (· ∈ f.range)] (hf : Function.Injective f)
    (p : A[X]) : (p.map f).roots.filter (· ∈ f.range) = p.roots.map f := by
  classical
  ext b
  rw [Multiset.count_filter]
  split_ifs with h
  · obtain ⟨a, rfl⟩ := h
    simp [hf, Multiset.count_map_eq_count', eq_rootMultiplicity_map hf]
  · refine (Multiset.count_eq_zero.mpr fun h' ↦ h ?_).symm
    exact Exists.imp (fun _ ↦ And.right) <| Multiset.mem_map.mp h'

theorem card_roots_le_map [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B} (h : p.map f ≠ 0) :
    Multiset.card p.roots ≤ Multiset.card (p.map f).roots := by
  rw [← p.roots.card_map f]
  exact Multiset.card_le_card (map_roots_le h)

theorem card_roots_le_map_of_injective [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B}
    (hf : Function.Injective f) : Multiset.card p.roots ≤ Multiset.card (p.map f).roots := by
  by_cases hp0 : p = 0
  · simp only [hp0, roots_zero, Polynomial.map_zero, Multiset.card_zero, le_rfl]
  exact card_roots_le_map ((Polynomial.map_ne_zero_iff hf).mpr hp0)

theorem roots_map_of_injective_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p : A[X]}
    {f : A →+* B} (hf : Function.Injective f) (hroots : Multiset.card p.roots = p.natDegree) :
    p.roots.map f = (p.map f).roots := by
  apply Multiset.eq_of_le_of_card_le (map_roots_le_of_injective p hf)
  simpa only [Multiset.card_map, hroots] using card_roots_map_le_natDegree p

theorem roots_map_of_map_ne_zero_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p : A[X]}
    (f : A →+* B) (h : p.map f ≠ 0) (hroots : p.roots.card = p.natDegree) :
    p.roots.map f = (p.map f).roots :=
  eq_of_le_of_card_le (map_roots_le h) <| by
    simpa only [Multiset.card_map, hroots] using card_roots_map_le_natDegree p

theorem Monic.roots_map_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p : A[X]} (hm : p.Monic)
    (f : A →+* B) (hroots : p.roots.card = p.natDegree) : p.roots.map f = (p.map f).roots :=
  roots_map_of_map_ne_zero_of_card_eq_natDegree f (map_monic_ne_zero hm) hroots

end

end Polynomial
