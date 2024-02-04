/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.PerfectClosure

/-!

# `IsPerfectClosure` predicate

This file contains `IsPerfectClosure` which asserts that `L` is a perfect closure of `K` under a
ring homomorphism `i : K →+* L`, as well as its basic properties.

## Main definitions

- `IsPerfectClosure`: a ring homomorphism `i : K →+* L` makes `L` a perfect closure of `K`, if `L`
  is perfect, `L / K` is purely inseparable, and the kernel of `i` is contained in the
  `p`-nilradical of `K`.

- `PerfectRing.lift`: a map from a purely inseparable ring extension `L` of `K` to a perfect ring
  `M` over `K`.

- `IsPerfectClosure.equiv`: an isomorphism between two perfect closures.

## Main results

- `PerfectClosure.isPerfectClosure`: the absolute perfect closure `PerfectClosure` is a perfect closure.

## Tags

perfect ring, perfect closure, purely inseparable

-/

open scoped Classical Polynomial

open FiniteDimensional Polynomial IntermediateField Field

noncomputable section

-- TODO: move to Mathlib.FieldTheory.SeparableDegree
/-- A field is a perfect field (which means that any irreducible polynomial is separable)
if and only if every separable degree one polynomial splits. -/
theorem perfectField_iff_splits_of_natSepDegree_eq_one (F : Type*) [Field F] :
    PerfectField F ↔ ∀ f : F[X], f.natSepDegree = 1 → f.Splits (RingHom.id F) := by
  refine ⟨fun ⟨h⟩ f hf ↦ or_iff_not_imp_left.2 fun hn g hg hd ↦ ?_, fun h ↦ ?_⟩
  · rw [map_id] at hn hd
    have := natSepDegree_le_of_dvd g f hd hn
    rw [hf, (h hg).natSepDegree_eq_natDegree] at this
    exact (degree_eq_iff_natDegree_eq_of_pos one_pos).2 <| this.antisymm <|
      natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hg)
  obtain ⟨p, _⟩ := ExpChar.exists F
  haveI := PerfectRing.ofSurjective F p fun x ↦ by
    obtain ⟨y, hy⟩ := exists_root_of_splits _
      (h _ (pow_one p ▸ natSepDegree_X_pow_char_sub_C p 1 x))
      ((degree_X_pow_sub_C (expChar_pos F p) x).symm ▸ Nat.cast_pos.2 (expChar_pos F p)).ne'
    exact ⟨y, by rwa [← eval, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hy⟩
  exact PerfectRing.toPerfectField F p

-- TODO: move to suitable location
theorem iterate_frobeniusEquiv_symm_apply_iterate_frobenius (R : Type*) (p : ℕ)
    [CommSemiring R] [ExpChar R p] [PerfectRing R p] (x : R) (n : ℕ) :
    (frobeniusEquiv R p).symm^[n] ((frobenius R p)^[n] x) = x := by
  induction n with
  | zero => rfl
  | succ n ih => rwa [Function.iterate_succ_apply, Function.iterate_succ_apply',
    frobeniusEquiv_symm_apply_frobenius]

-- TODO: move to suitable location
theorem iterate_frobenius_apply_iterate_frobeniusEquiv_symm (R : Type*) (p : ℕ)
    [CommSemiring R] [ExpChar R p] [PerfectRing R p] (x : R) (n : ℕ) :
    (frobenius R p)^[n] ((frobeniusEquiv R p).symm^[n] x) = x := by
  induction n with
  | zero => rfl
  | succ n ih => rwa [Function.iterate_succ_apply, Function.iterate_succ_apply',
    frobenius_apply_frobeniusEquiv_symm]

-- TODO: move to suitable location
theorem iterate_frobeniusEquiv_symm_mul (R : Type*) (p : ℕ)
    [CommSemiring R] [ExpChar R p] [PerfectRing R p] (x y : R) (n : ℕ) :
    (frobeniusEquiv R p).symm^[n] (x * y) =
    (frobeniusEquiv R p).symm^[n] x * (frobeniusEquiv R p).symm^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_mul,
    Function.iterate_succ_apply', Function.iterate_succ_apply']

-- TODO: move to suitable location
theorem iterate_frobeniusEquiv_symm_add (R : Type*) (p : ℕ)
    [CommSemiring R] [ExpChar R p] [PerfectRing R p] (x y : R) (n : ℕ) :
    (frobeniusEquiv R p).symm^[n] (x + y) =
    (frobeniusEquiv R p).symm^[n] x + (frobeniusEquiv R p).symm^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_add,
    Function.iterate_succ_apply', Function.iterate_succ_apply']

-- TODO: move to suitable location
theorem iterate_frobeniusEquiv_symm_pow (R : Type*) (p : ℕ)
    [CommSemiring R] [ExpChar R p] [PerfectRing R p] (x : R) (n m : ℕ) :
    (frobeniusEquiv R p).symm^[n] (x ^ m) =
    (frobeniusEquiv R p).symm^[n] x ^ m := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_pow, Function.iterate_succ_apply']

-- TODO: move to suitable location
theorem iterate_frobeniusEquiv_symm_zero (R : Type*) (p : ℕ)
    [CommSemiring R] [ExpChar R p] [PerfectRing R p] (n : ℕ) :
    (frobeniusEquiv R p).symm^[n] 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_zero]

-- TODO: move to suitable location
theorem iterate_frobeniusEquiv_symm_one (R : Type*) (p : ℕ)
    [CommSemiring R] [ExpChar R p] [PerfectRing R p] (n : ℕ) :
    (frobeniusEquiv R p).symm^[n] 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_one]

/-- The `p`-nilradical of a ring is an ideal consists of elements `x` such that `x ^ p ^ n = 0`
for some `n` (`mem_pNilradical`). It is equal to the nilradical if `p > 1`
(`pNilradical_eq_nilradical`), otherwise it is equal to zero (`pNilradical_eq_bot`). -/
def pNilradical (R : Type*) [CommSemiring R] (p : ℕ) : Ideal R := if 1 < p then nilradical R else ⊥

theorem pNilradical_eq_nilradical {R : Type*} [CommSemiring R] {p : ℕ} (hp : 1 < p) :
    pNilradical R p = nilradical R := by simp_rw [pNilradical, hp, ite_true]

theorem pNilradical_eq_bot {R : Type*} [CommSemiring R] {p : ℕ} (hp : ¬ 1 < p) :
    pNilradical R p = ⊥ := by simp_rw [pNilradical, hp, ite_false]

theorem pNilradical_eq_bot' {R : Type*} [CommSemiring R] {p : ℕ} (hp : p ≤ 1) :
    pNilradical R p = ⊥ := pNilradical_eq_bot (not_lt.2 hp)

theorem mem_pNilradical {R : Type*} [CommSemiring R] {p : ℕ} {x : R} :
    x ∈ pNilradical R p ↔ ∃ n : ℕ, x ^ p ^ n = 0 := by
  by_cases hp : 1 < p
  · rw [pNilradical_eq_nilradical hp]
    refine ⟨fun ⟨n, h⟩ ↦ ⟨n, ?_⟩, fun ⟨n, h⟩ ↦ ⟨p ^ n, h⟩⟩
    rw [← Nat.sub_add_cancel ((Nat.lt_pow_self hp n).le), pow_add, h, mul_zero]
  rw [pNilradical_eq_bot hp, Ideal.mem_bot]
  refine ⟨fun h ↦ ⟨0, by rw [pow_zero, pow_one, h]⟩, fun ⟨n, h⟩ ↦ ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (not_lt.1 hp) with hp | hp
  · by_cases hn : n = 0
    · rwa [hn, pow_zero, pow_one] at h
    rw [hp, zero_pow hn, pow_zero] at h
    haveI := subsingleton_of_zero_eq_one h.symm
    exact Subsingleton.elim _ _
  rwa [hp, one_pow, pow_one] at h

section IsPerfectClosure

variable {K L M : Type*}

section CommSemiring

variable [CommSemiring K] [CommSemiring L] [CommSemiring M]
  (i : K →+* L) (j : K →+* M) (p : ℕ) [ExpChar K p] [ExpChar L p] [ExpChar M p]

/-- If `i : K →+* L` is a ring homomorphism of characteristic `p` rings, then it makes `L`
a perfect closure of `K` if the following conditions are satisfied:

- `L` is a perfect ring.
- `i : K →+* L` is "purely inseparable" in the sense that for any element `x` of `L` there exists
  a natural number `n` such that `x ^ (p ^ n)` is contained in `K`.
- The kernel of `i` is contained in (in fact, equal to, see `IsPerfectClosure.ker_eq`)
  the `p`-nilradical of `K`. -/
@[mk_iff]
class IsPerfectClosure : Prop where
  perfectRing' : PerfectRing L p
  pow_mem' : ∀ x : L, ∃ (n : ℕ) (y : K), i y = x ^ p ^ n
  ker_le' : RingHom.ker i ≤ pNilradical K p

theorem IsPerfectClosure.perfectRing [IsPerfectClosure i p] :
    PerfectRing L p := perfectRing' i

theorem IsPerfectClosure.pow_mem [IsPerfectClosure i p] (x : L) :
    ∃ (n : ℕ) (y : K), i y = x ^ p ^ n := pow_mem' x

theorem IsPerfectClosure.ker_le [IsPerfectClosure i p] :
    RingHom.ker i ≤ pNilradical K p := ker_le'

/-- If `i : K →+* L` is a ring homomorphism of exponential characteristic `p` rings, such that `L`
is perfect, then the `p`-nilradical of `K` is contained in the kernel of `i`. -/
theorem RingHom.pNilradical_le_ker_of_perfectRing [PerfectRing L p] :
    pNilradical K p ≤ RingHom.ker i := fun x h ↦ by
  obtain ⟨n, h⟩ := mem_pNilradical.1 h
  replace h := congr((frobeniusEquiv L p).symm^[n] (i $h))
  rwa [map_pow, ← iterate_frobenius, iterate_frobeniusEquiv_symm_apply_iterate_frobenius,
    map_zero, iterate_frobeniusEquiv_symm_zero] at h

theorem IsPerfectClosure.ker_eq [IsPerfectClosure i p] : RingHom.ker i = pNilradical K p :=
  ker_le'.antisymm (haveI := perfectRing i p; i.pNilradical_le_ker_of_perfectRing p)

/-- A perfect ring is its perfect closure. -/
instance IsPerfectClosure.self_of_perfect [PerfectRing M p] :
    IsPerfectClosure (RingHom.id M) p where
  perfectRing' := ‹_›
  pow_mem' x := ⟨0, x, by simp⟩
  ker_le' x hx := by convert Ideal.zero_mem _

section lift

variable [PerfectRing M p] (H : ∀ x : L, ∃ (n : ℕ) (y : K), i y = x ^ p ^ n)

theorem PerfectRing.lift_aux (x : L) : ∃ y : ℕ × K, i y.2 = x ^ p ^ y.1 := by
  obtain ⟨n, y, h⟩ := H x
  exact ⟨(n, y), h⟩

/-- If `i : K →+* L` and `j : K →+* M` are ring homomorphisms of characteristic `p` rings, such that
`i` is "purely inseparable" and `M` is a perfect ring, then one can define a map
`L → M` which maps an element `x` of `L` to `y ^ (p ^ -n)` if `x ^ (p ^ n)` is equal to some
element `y` of `K`. -/
def PerfectRing.liftAux (x : L) : M :=
  (frobeniusEquiv M p).symm^[(Classical.choose (lift_aux i p H x)).1]
    (j (Classical.choose (lift_aux i p H x)).2)

theorem PerfectRing.liftAux_self_apply [PerfectRing L p] (x : L) : liftAux i i p H x = x := by
  rw [liftAux, Classical.choose_spec (lift_aux i p H x), ← iterate_frobenius,
    iterate_frobeniusEquiv_symm_apply_iterate_frobenius]

theorem PerfectRing.liftAux_self [PerfectRing L p] : liftAux i i p H = id :=
  funext (liftAux_self_apply i p H)

end lift

end CommSemiring

section CommRing

variable [CommRing K] [CommRing L] [CommRing M]
  (i : K →+* L) (j : K →+* M) (p : ℕ) [ExpChar K p] [ExpChar L p] [ExpChar M p]

section lift

variable [PerfectRing M p] (H : ∀ x : L, ∃ (n : ℕ) (y : K), i y = x ^ p ^ n)
  (hk : RingHom.ker i ≤ pNilradical K p)

/-- If `i : K →+* L` and `j : K →+* M` are ring homomorphisms of characteristic `p` rings, such that
`i` is "purely inseparable" and whose kernel is contained in the `p`-nilradical of `K`, and `M` is a
perfect ring, then `PerfectRing.liftAux` is well-defined. -/
theorem PerfectRing.liftAux_apply (x : L) (n : ℕ) (y : K) (h : i y = x ^ p ^ n) :
    liftAux i j p H x = (frobeniusEquiv M p).symm^[n] (j y) := by
  rw [liftAux]
  have h' := Classical.choose_spec (lift_aux i p H x)
  set n' := (Classical.choose (lift_aux i p H x)).1
  replace h := congr($(h.symm) ^ p ^ n')
  rw [← pow_mul, mul_comm, pow_mul, ← h', ← map_pow, ← map_pow, ← sub_eq_zero, ← map_sub,
    ← RingHom.mem_ker] at h
  obtain ⟨m, h⟩ := mem_pNilradical.1 (hk h)
  apply_fun _ using (injective_frobenius M p).iterate (m + n + n')
  conv_lhs => rw [Function.iterate_add_apply, iterate_frobenius_apply_iterate_frobeniusEquiv_symm]
  rw [add_assoc, add_comm n n', ← add_assoc,
    Function.iterate_add_apply _ (m + n') n, iterate_frobenius_apply_iterate_frobeniusEquiv_symm,
    iterate_frobenius, iterate_frobenius, ← sub_eq_zero, ← map_pow, ← map_pow, ← map_sub,
    add_comm m, add_comm m, pow_add, pow_mul, pow_add, pow_mul, ← sub_pow_expChar_pow, h, map_zero]

/-- If `i : K →+* L` and `j : K →+* M` are ring homomorphisms of characteristic `p` rings, such that
`i` is "purely inseparable" and whose kernel is contained in the `p`-nilradical of `K`, and `M` is a
perfect ring, then `PerfectRing.liftAux` is a ring homomorphism. -/
def PerfectRing.lift : L →+* M where
  toFun := liftAux i j p H
  map_one' := by simp [liftAux_apply i j p H hk 1 0 1 (by rw [one_pow, map_one])]
  map_mul' x1 x2 := by
    obtain ⟨n1, y1, h1⟩ := H x1
    obtain ⟨n2, y2, h2⟩ := H x2
    simp only; rw [liftAux_apply i j p H hk _ _ _ h1, liftAux_apply i j p H hk _ _ _ h2,
      liftAux_apply i j p H hk (x1 * x2) (n1 + n2) (y1 ^ p ^ n2 * y2 ^ p ^ n1) (by rw [map_mul,
        map_pow, map_pow, h1, h2, ← pow_mul, ← pow_add, ← pow_mul, ← pow_add,
        add_comm n2, mul_pow]),
      map_mul, map_pow, map_pow, iterate_frobeniusEquiv_symm_mul, ← iterate_frobenius]
    nth_rw 1 [Function.iterate_add_apply]
    rw [iterate_frobeniusEquiv_symm_apply_iterate_frobenius, add_comm, Function.iterate_add_apply,
      ← iterate_frobenius, iterate_frobeniusEquiv_symm_apply_iterate_frobenius]
  map_zero' := by simp [liftAux_apply i j p H hk 0 0 0 (by rw [pow_zero, pow_one, map_zero])]
  map_add' x1 x2 := by
    obtain ⟨n1, y1, h1⟩ := H x1
    obtain ⟨n2, y2, h2⟩ := H x2
    simp only; rw [liftAux_apply i j p H hk _ _ _ h1, liftAux_apply i j p H hk _ _ _ h2,
      liftAux_apply i j p H hk (x1 + x2) (n1 + n2) (y1 ^ p ^ n2 + y2 ^ p ^ n1) (by rw [map_add,
        map_pow, map_pow, h1, h2, ← pow_mul, ← pow_add, ← pow_mul, ← pow_add,
        add_comm n2, add_pow_expChar_pow]),
      map_add, map_pow, map_pow, iterate_frobeniusEquiv_symm_add, ← iterate_frobenius]
    nth_rw 1 [Function.iterate_add_apply]
    rw [iterate_frobeniusEquiv_symm_apply_iterate_frobenius, add_comm n1,
      Function.iterate_add_apply, ← iterate_frobenius,
      iterate_frobeniusEquiv_symm_apply_iterate_frobenius]

theorem PerfectRing.lift_apply (x : L) (n : ℕ) (y : K) (h : i y = x ^ p ^ n) :
    lift i j p H hk x = (frobeniusEquiv M p).symm^[n] (j y) :=
  liftAux_apply i j p H hk _ _ _ h

theorem PerfectRing.lift_self_apply [PerfectRing L p] (x : L) : lift i i p H hk x = x :=
  liftAux_self_apply i p H x

theorem PerfectRing.lift_self [PerfectRing L p] : lift i i p H hk = RingHom.id L :=
  RingHom.ext (liftAux_self_apply i p H)

theorem PerfectRing.lift_comp_apply (x : K) : lift i j p H hk (i x) = j x := by
  rw [lift_apply i j p H hk _ 0 x (by rw [pow_zero, pow_one])]; rfl

theorem PerfectRing.lift_comp : (lift i j p H hk).comp i = j :=
  RingHom.ext (lift_comp_apply i j p H hk)

section comp

variable {N : Type*} [CommRing N] (k : K →+* N) [ExpChar N p] [PerfectRing N p]
  (H' : ∀ x : M, ∃ (n : ℕ) (y : K), j y = x ^ p ^ n)
  (hk' : RingHom.ker j ≤ pNilradical K p)

theorem PerfectRing.lift_comp_lift_apply (x : L) :
    lift j k p H' hk' (lift i j p H hk x) = lift i k p H hk x := by
  obtain ⟨n, y, h⟩ := H x
  rw [lift_apply i j p H hk _ _ _ h, lift_apply i k p H hk _ _ _ h]
  apply_fun _ using (injective_frobenius N p).iterate n
  rw [← RingHom.map_iterate_frobenius, iterate_frobenius_apply_iterate_frobeniusEquiv_symm,
    iterate_frobenius_apply_iterate_frobeniusEquiv_symm, lift_comp_apply]

theorem PerfectRing.lift_comp_lift :
    (lift j k p H' hk').comp (lift i j p H hk) = lift i k p H hk :=
  RingHom.ext (lift_comp_lift_apply i j p H hk k H' hk')

theorem PerfectRing.lift_comp_lift_apply_eq_self [PerfectRing L p] (x : L) :
    lift j i p H' hk' (lift i j p H hk x) = x := by
  rw [lift_comp_lift_apply, lift_self_apply]

theorem PerfectRing.lift_comp_lift_eq_id [PerfectRing L p] :
    (lift j i p H' hk').comp (lift i j p H hk) = RingHom.id L :=
  RingHom.ext (lift_comp_lift_apply_eq_self i j p H hk H' hk')

end comp

end lift

section equiv

variable [IsPerfectClosure i p] [IsPerfectClosure j p]

/-- If `L` and `M` are both perfect closures of `K`, then there is a ring isomorphism `L ≃+* M`. -/
def IsPerfectClosure.equiv : L ≃+* M where
  __ := haveI := perfectRing j p; PerfectRing.lift i j p pow_mem' ker_le'
  invFun := haveI := perfectRing i p; PerfectRing.liftAux j i p pow_mem'
  left_inv := haveI := perfectRing i p; haveI := perfectRing j p;
    PerfectRing.lift_comp_lift_apply_eq_self i j p pow_mem' ker_le' pow_mem' ker_le'
  right_inv := haveI := perfectRing i p; haveI := perfectRing j p;
    PerfectRing.lift_comp_lift_apply_eq_self j i p pow_mem' ker_le' pow_mem' ker_le'

theorem IsPerfectClosure.equiv_toRingHom : haveI := perfectRing j p;
    (equiv i j p).toRingHom = PerfectRing.lift i j p pow_mem' ker_le' := rfl

theorem IsPerfectClosure.equiv_symm : (equiv i j p).symm = equiv j i p := rfl

theorem IsPerfectClosure.equiv_symm_toRingHom : haveI := perfectRing i p;
    (equiv i j p).symm.toRingHom = PerfectRing.lift j i p pow_mem' ker_le' := rfl

theorem IsPerfectClosure.equiv_apply (x : L) (n : ℕ) (y : K) (h : i y = x ^ p ^ n) :
    haveI := perfectRing j p; equiv i j p x = (frobeniusEquiv M p).symm^[n] (j y) :=
  haveI := perfectRing j p; PerfectRing.liftAux_apply i j p pow_mem' ker_le' _ _ _ h

theorem IsPerfectClosure.equiv_symm_apply (x : M) (n : ℕ) (y : K) (h : j y = x ^ p ^ n) :
    haveI := perfectRing i p; (equiv i j p).symm x = (frobeniusEquiv L p).symm^[n] (i y) := by
  rw [equiv_symm, equiv_apply j i p _ _ _ h]

theorem IsPerfectClosure.equiv_self_apply (x : L) : equiv i i p x = x :=
  haveI := perfectRing i p; PerfectRing.liftAux_self_apply i p pow_mem' x

theorem IsPerfectClosure.equiv_self : equiv i i p = RingEquiv.refl L :=
  RingEquiv.ext (equiv_self_apply i p)

theorem IsPerfectClosure.equiv_comp_apply (x : K) : equiv i j p (i x) = j x :=
  haveI := perfectRing j p; PerfectRing.lift_comp_apply i j p pow_mem' ker_le' x

theorem IsPerfectClosure.equiv_comp : (equiv i j p).toRingHom.comp i = j :=
  RingHom.ext (equiv_comp_apply i j p)

section comp

variable {N : Type*} [CommRing N] (k : K →+* N) [ExpChar N p] [IsPerfectClosure k p]

theorem IsPerfectClosure.equiv_comp_equiv_apply (x : L) :
    equiv j k p (equiv i j p x) = equiv i k p x :=
  haveI := perfectRing j p; haveI := perfectRing k p;
  PerfectRing.lift_comp_lift_apply i j p pow_mem' ker_le' k pow_mem' ker_le' x

theorem IsPerfectClosure.equiv_comp_equiv : (equiv i j p).trans (equiv j k p) = equiv i k p :=
  RingEquiv.ext (equiv_comp_equiv_apply i j p k)

theorem IsPerfectClosure.equiv_comp_equiv_apply_eq_self (x : L) :
    equiv j i p (equiv i j p x) = x := by
  rw [equiv_comp_equiv_apply, equiv_self_apply]

theorem IsPerfectClosure.equiv_comp_equiv_eq_id :
    (equiv i j p).trans (equiv j i p) = RingEquiv.refl L :=
  RingEquiv.ext (equiv_comp_equiv_apply_eq_self i j p)

end comp

end equiv

end CommRing

-- TODO: relax `Field` assumption (need to change `PerfectClosure` file)
variable (K) in
/-- The absolute perfect closure `PerfectClosure` is a perfect closure. -/
instance PerfectClosure.isPerfectClosure [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    IsPerfectClosure (PerfectClosure.of K p) p where
  perfectRing' := inferInstance
  pow_mem' x := PerfectClosure.induction_on x fun x ↦ ⟨x.1, x.2, by
    rw [← iterate_frobenius, iterate_frobenius_mk K p x.1 x.2]⟩
  ker_le' x h := by
    rw [RingHom.mem_ker, of_apply, zero_def, eq_iff'] at h
    obtain ⟨n, h⟩ := h
    simp_rw [zero_add, ← coe_iterateFrobenius, map_zero] at h
    exact mem_pNilradical.2 ⟨n, h⟩

end IsPerfectClosure
