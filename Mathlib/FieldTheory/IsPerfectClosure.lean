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

- `PerfectClosure.isPerfectClosure`: the absolute perfect closure `PerfectClosure` is a
  perfect closure.

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
theorem iterateFrobenius_add_apply (R : Type*) [CommSemiring R] (p m n : ℕ) [ExpChar R p] (x : R) :
    iterateFrobenius R p (m + n) x = iterateFrobenius R p m (iterateFrobenius R p n x) :=
  congr($(iterateFrobenius_add R p m n) x)

-- TODO: move to suitable location
theorem frobeniusEquiv_def (R : Type*) (p : ℕ) [CommSemiring R] [ExpChar R p]
    [PerfectRing R p] (x : R) : frobeniusEquiv R p x = x ^ p := rfl

-- TODO: move to suitable location
theorem iterateFrobeniusEquiv_def (R : Type*) (p n : ℕ) [CommSemiring R] [ExpChar R p]
    [PerfectRing R p] (x : R) : iterateFrobeniusEquiv R p n x = x ^ p ^ n := rfl

-- TODO: move to suitable location
theorem iterateFrobeniusEquiv_add_apply (R : Type*) (p m n : ℕ) [CommSemiring R] [ExpChar R p]
    [PerfectRing R p] (x : R) : iterateFrobeniusEquiv R p (m + n) x =
    iterateFrobeniusEquiv R p m (iterateFrobeniusEquiv R p n x) :=
  congr($(iterateFrobenius_add R p m n) x)

-- TODO: move to suitable location
theorem iterateFrobeniusEquiv_add (R : Type*) (p m n : ℕ) [CommSemiring R] [ExpChar R p]
    [PerfectRing R p] : iterateFrobeniusEquiv R p (m + n) =
    (iterateFrobeniusEquiv R p n).trans (iterateFrobeniusEquiv R p m) :=
  RingEquiv.ext (iterateFrobeniusEquiv_add_apply R p m n)

-- TODO: move to suitable location
theorem iterateFrobeniusEquiv_symm_add_apply (R : Type*) (p m n : ℕ) [CommSemiring R] [ExpChar R p]
    [PerfectRing R p] (x : R) : (iterateFrobeniusEquiv R p (m + n)).symm x =
    (iterateFrobeniusEquiv R p m).symm ((iterateFrobeniusEquiv R p n).symm x) := by
  refine (iterateFrobeniusEquiv R p (m + n)).injective ?_
  rw [RingEquiv.apply_symm_apply, add_comm, iterateFrobeniusEquiv_add_apply,
    RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

-- TODO: move to suitable location
theorem iterateFrobeniusEquiv_symm_add (R : Type*) (p m n : ℕ) [CommSemiring R] [ExpChar R p]
    [PerfectRing R p] : (iterateFrobeniusEquiv R p (m + n)).symm =
    (iterateFrobeniusEquiv R p n).symm.trans (iterateFrobeniusEquiv R p m).symm :=
  RingEquiv.ext (iterateFrobeniusEquiv_symm_add_apply R p m n)

-- TODO: move to suitable location
theorem iterateFrobeniusEquiv_zero_apply (R : Type*) (p : ℕ) [CommSemiring R] [ExpChar R p]
    [PerfectRing R p] (x : R) : iterateFrobeniusEquiv R p 0 x = x := by
  rw [iterateFrobeniusEquiv_def, pow_zero, pow_one]

-- TODO: move to suitable location
theorem iterateFrobeniusEquiv_one_apply (R : Type*) (p : ℕ) [CommSemiring R] [ExpChar R p]
    [PerfectRing R p] (x : R) : iterateFrobeniusEquiv R p 1 x = x ^ p := by
  rw [iterateFrobeniusEquiv_def, pow_one]

-- TODO: move to suitable location
theorem iterateFrobeniusEquiv_zero (R : Type*) (p : ℕ) [CommSemiring R] [ExpChar R p]
    [PerfectRing R p] : iterateFrobeniusEquiv R p 0 = RingEquiv.refl R :=
  RingEquiv.ext (iterateFrobeniusEquiv_zero_apply R p)

-- TODO: move to suitable location
theorem iterateFrobeniusEquiv_one (R : Type*) (p : ℕ) [CommSemiring R] [ExpChar R p]
    [PerfectRing R p] : iterateFrobeniusEquiv R p 1 = frobeniusEquiv R p :=
  RingEquiv.ext (iterateFrobeniusEquiv_one_apply R p)

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

theorem pNilradical_prime {R : Type*} [CommSemiring R] {p : ℕ} (hp : p.Prime) :
    pNilradical R p = nilradical R := pNilradical_eq_nilradical hp.one_lt

theorem pNilradical_one {R : Type*} [CommSemiring R] :
    pNilradical R 1 = ⊥ := pNilradical_eq_bot' rfl.le

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

namespace PerfectClosure

variable (K : Type*) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (x : ℕ × K) (n : ℕ)

-- TODO: remove once XX is merged
theorem mk_pow : mk K p x ^ n = mk K p (x.1, x.2 ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, one_def, eq_iff']
    exact ⟨0, by simp_rw [← coe_iterateFrobenius, map_one]⟩
  | succ n ih =>
    rw [pow_succ, pow_succ, ih, mk_mul_mk, eq_iff']
    exact ⟨0, by simp_rw [← coe_iterateFrobenius, add_zero, iterateFrobenius_add_apply, map_mul]⟩

-- TODO: remove once XX is merged
instance instReduced : IsReduced (PerfectClosure K p) where
  eq_zero x := induction_on x fun x ⟨n, h⟩ ↦ by
    replace h : mk K p x ^ p ^ n = 0 := by
      rw [← Nat.sub_add_cancel ((Nat.lt_pow_self (Fact.out : p.Prime).one_lt n).le),
        pow_add, h, mul_zero]
    simp only [zero_def, mk_pow, eq_iff', zero_add, ← coe_iterateFrobenius, map_zero] at h ⊢
    obtain ⟨m, h⟩ := h
    exact ⟨n + m, by simpa only [iterateFrobenius_def, pow_add, pow_mul] using h⟩

-- TODO: remove once XX is merged
instance instPerfectRing :
    PerfectRing (PerfectClosure K p) p := .ofSurjective _ p fun x ↦ induction_on x fun x ↦ by
  use mk K p (x.1 + 1, x.2)
  rw [frobenius_def, mk_pow, eq_iff']
  exact ⟨0, by simp_rw [iterate_frobenius, add_zero, pow_succ, pow_mul]⟩

end PerfectClosure

section IsPerfectClosure

variable {K L M : Type*}

section CommSemiring

variable [CommSemiring K] [CommSemiring L] [CommSemiring M]
  (i : K →+* L) (j : K →+* M) (p : ℕ) [ExpChar K p] [ExpChar L p] [ExpChar M p]

/-- If `i : K →+* L` is a ring homomorphism of characteristic `p` rings, then it is called
`p`-radical if the following conditions are satisfied:

- For any element `x` of `L` there is `n : ℕ` such that `x ^ (p ^ n)` is contained in `K`.
- The kernel of `i` is contained in the `p`-nilradical of `K`.

It is a generalization of purely inseparable extension for fields. -/
@[mk_iff]
class IsPRadical : Prop where
  pow_mem' : ∀ x : L, ∃ (n : ℕ) (y : K), i y = x ^ p ^ n
  ker_le' : RingHom.ker i ≤ pNilradical K p

theorem IsPRadical.pow_mem [IsPRadical i p] (x : L) :
    ∃ (n : ℕ) (y : K), i y = x ^ p ^ n := pow_mem' x

theorem IsPRadical.ker_le [IsPRadical i p] :
    RingHom.ker i ≤ pNilradical K p := ker_le'

/-- If `i : K →+* L` is a ring homomorphism of characteristic `p` rings, then it makes `L`
a perfect closure of `K` if the following conditions are satisfied:

- `L` is a perfect ring.
- `i : K →+* L` is `p`-radical.

In this case the kernel of `i` is equal to the `p`-nilradical of `K`
(see `IsPerfectClosure.ker_eq`). -/
@[mk_iff]
class IsPerfectClosure : Prop where
  [perfectRing' : PerfectRing L p]
  [isPRadical' : IsPRadical i p]

/- Marked as instance, so `IsPerfectClosure` can be deduced automatically from `PerfectRing` and
`IsPRadical`. Will it impact performance? -/
attribute [instance] IsPerfectClosure.mk

theorem IsPerfectClosure.perfectRing [IsPerfectClosure i p] :
    PerfectRing L p := perfectRing' i

instance IsPerfectClosure.isPRadical [IsPerfectClosure i p] :
    IsPRadical i p := isPRadical'

/-- If `i : K →+* L` is a ring homomorphism of exponential characteristic `p` rings, such that `L`
is perfect, then the `p`-nilradical of `K` is contained in the kernel of `i`. -/
theorem RingHom.pNilradical_le_ker_of_perfectRing [PerfectRing L p] :
    pNilradical K p ≤ RingHom.ker i := fun x h ↦ by
  obtain ⟨n, h⟩ := mem_pNilradical.1 h
  replace h := congr((iterateFrobeniusEquiv L p n).symm (i $h))
  rwa [map_pow, ← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply, RingEquiv.symm_apply_apply,
    map_zero, map_zero] at h

theorem IsPerfectClosure.ker_eq [IsPerfectClosure i p] : RingHom.ker i = pNilradical K p :=
  isPRadical'.ker_le'.antisymm (haveI := perfectRing i p; i.pNilradical_le_ker_of_perfectRing p)

/-- A perfect ring is its perfect closure. -/
instance IsPerfectClosure.self_of_perfect [PerfectRing M p] :
    IsPerfectClosure (RingHom.id M) p where
  isPRadical'.pow_mem' x := ⟨0, x, by simp⟩
  isPRadical'.ker_le' x hx := by convert Ideal.zero_mem _

section PerfectRing.lift

/- NOTE: To define `PerfectRing.lift_aux`, only the `IsPRadical.pow_mem` is required, but not
`IsPRadical.ker_le`. But in order to use typeclass, here we require the whole `IsPRadical`. -/

variable [PerfectRing M p] [IsPRadical i p]

theorem PerfectRing.lift_aux (x : L) : ∃ y : ℕ × K, i y.2 = x ^ p ^ y.1 := by
  obtain ⟨n, y, h⟩ := IsPRadical.pow_mem i p x
  exact ⟨(n, y), h⟩

/-- If `i : K →+* L` and `j : K →+* M` are ring homomorphisms of characteristic `p` rings, such that
`i` is "purely inseparable" and `M` is a perfect ring, then one can define a map
`L → M` which maps an element `x` of `L` to `y ^ (p ^ -n)` if `x ^ (p ^ n)` is equal to some
element `y` of `K`. -/
def PerfectRing.liftAux (x : L) : M :=
  (iterateFrobeniusEquiv M p (Classical.choose (lift_aux i p x)).1).symm
    (j (Classical.choose (lift_aux i p x)).2)

theorem PerfectRing.liftAux_self_apply [PerfectRing L p] (x : L) : liftAux i i p x = x := by
  rw [liftAux, Classical.choose_spec (lift_aux i p x), ← iterateFrobenius_def,
    ← iterateFrobeniusEquiv_apply, RingEquiv.symm_apply_apply]

theorem PerfectRing.liftAux_self [PerfectRing L p] : liftAux i i p = id :=
  funext (liftAux_self_apply i p)

end PerfectRing.lift

end CommSemiring

section CommRing

variable [CommRing K] [CommRing L] [CommRing M]
  (i : K →+* L) (j : K →+* M) (p : ℕ) [ExpChar K p] [ExpChar L p] [ExpChar M p]

section PerfectRing.lift

variable [PerfectRing M p] [IsPRadical i p]

/-- If `i : K →+* L` and `j : K →+* M` are ring homomorphisms of characteristic `p` rings, such that
`i` is "purely inseparable" and whose kernel is contained in the `p`-nilradical of `K`, and `M` is a
perfect ring, then `PerfectRing.liftAux` is well-defined. -/
theorem PerfectRing.liftAux_apply (x : L) (n : ℕ) (y : K) (h : i y = x ^ p ^ n) :
    liftAux i j p x = (iterateFrobeniusEquiv M p n).symm (j y) := by
  rw [liftAux]
  have h' := Classical.choose_spec (lift_aux i p x)
  set n' := (Classical.choose (lift_aux i p x)).1
  replace h := congr($(h.symm) ^ p ^ n')
  rw [← pow_mul, mul_comm, pow_mul, ← h', ← map_pow, ← map_pow, ← sub_eq_zero, ← map_sub,
    ← RingHom.mem_ker] at h
  obtain ⟨m, h⟩ := mem_pNilradical.1 (IsPRadical.ker_le i p h)
  refine (iterateFrobeniusEquiv M p (m + n + n')).injective ?_
  conv_lhs => rw [iterateFrobeniusEquiv_add_apply, RingEquiv.apply_symm_apply]
  rw [add_assoc, add_comm n n', ← add_assoc,
    iterateFrobeniusEquiv_add_apply (m := m + n'), RingEquiv.apply_symm_apply,
    iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def,
    ← sub_eq_zero, ← map_pow, ← map_pow, ← map_sub,
    add_comm m, add_comm m, pow_add, pow_mul, pow_add, pow_mul, ← sub_pow_expChar_pow, h, map_zero]

/-- If `i : K →+* L` and `j : K →+* M` are ring homomorphisms of characteristic `p` rings, such that
`i` is "purely inseparable", the kernel of `i` is contained in the `p`-nilradical of `K`, and `M` is
a perfect ring, then `PerfectRing.liftAux` is a ring homomorphism. This is similar to
`IsAlgClosed.lift` and `IsSepClosed.lift`. -/
def PerfectRing.lift : L →+* M where
  toFun := liftAux i j p
  map_one' := by simp [liftAux_apply i j p 1 0 1 (by rw [one_pow, map_one])]
  map_mul' x1 x2 := by
    obtain ⟨n1, y1, h1⟩ := IsPRadical.pow_mem i p x1
    obtain ⟨n2, y2, h2⟩ := IsPRadical.pow_mem i p x2
    simp only; rw [liftAux_apply i j p _ _ _ h1, liftAux_apply i j p _ _ _ h2,
      liftAux_apply i j p (x1 * x2) (n1 + n2) (y1 ^ p ^ n2 * y2 ^ p ^ n1) (by rw [map_mul,
        map_pow, map_pow, h1, h2, ← pow_mul, ← pow_add, ← pow_mul, ← pow_add,
        add_comm n2, mul_pow]),
      map_mul, map_pow, map_pow, map_mul, ← iterateFrobeniusEquiv_def]
    nth_rw 1 [iterateFrobeniusEquiv_symm_add_apply]
    rw [RingEquiv.symm_apply_apply, add_comm n1, iterateFrobeniusEquiv_symm_add_apply,
      ← iterateFrobeniusEquiv_def, RingEquiv.symm_apply_apply]
  map_zero' := by simp [liftAux_apply i j p 0 0 0 (by rw [pow_zero, pow_one, map_zero])]
  map_add' x1 x2 := by
    obtain ⟨n1, y1, h1⟩ := IsPRadical.pow_mem i p x1
    obtain ⟨n2, y2, h2⟩ := IsPRadical.pow_mem i p x2
    simp only; rw [liftAux_apply i j p _ _ _ h1, liftAux_apply i j p _ _ _ h2,
      liftAux_apply i j p (x1 + x2) (n1 + n2) (y1 ^ p ^ n2 + y2 ^ p ^ n1) (by rw [map_add,
        map_pow, map_pow, h1, h2, ← pow_mul, ← pow_add, ← pow_mul, ← pow_add,
        add_comm n2, add_pow_expChar_pow]),
      map_add, map_pow, map_pow, map_add, ← iterateFrobeniusEquiv_def]
    nth_rw 1 [iterateFrobeniusEquiv_symm_add_apply]
    rw [RingEquiv.symm_apply_apply, add_comm n1, iterateFrobeniusEquiv_symm_add_apply,
      ← iterateFrobeniusEquiv_def, RingEquiv.symm_apply_apply]

theorem PerfectRing.lift_apply (x : L) (n : ℕ) (y : K) (h : i y = x ^ p ^ n) :
    lift i j p x = (iterateFrobeniusEquiv M p n).symm (j y) :=
  liftAux_apply i j p _ _ _ h

theorem PerfectRing.lift_self_apply [PerfectRing L p] (x : L) : lift i i p x = x :=
  liftAux_self_apply i p x

theorem PerfectRing.lift_self [PerfectRing L p] : lift i i p = RingHom.id L :=
  RingHom.ext (liftAux_self_apply i p)

theorem PerfectRing.lift_comp_apply (x : K) : lift i j p (i x) = j x := by
  rw [lift_apply i j p _ 0 x (by rw [pow_zero, pow_one]), iterateFrobeniusEquiv_zero]; rfl

theorem PerfectRing.lift_comp : (lift i j p).comp i = j :=
  RingHom.ext (lift_comp_apply i j p)

theorem PerfectRing.comp_lift_apply (f : L →+* M) (x : L) : lift i (f.comp i) p x = f x := by
  obtain ⟨n, y, h⟩ := IsPRadical.pow_mem i p x
  rw [lift_apply i _ p _ _ _ h, RingHom.comp_apply, h, ← iterate_frobenius, f.map_iterate_frobenius,
    ← coe_iterateFrobenius, ← iterateFrobeniusEquiv_apply, RingEquiv.symm_apply_apply]

theorem PerfectRing.comp_lift (f : L →+* M) : lift i (f.comp i) p = f :=
  RingHom.ext (comp_lift_apply i p f)

/-- If `i : K →+* L` is a homomorphisms of characteristic `p` rings, such that
`i` is "purely inseparable", the kernel of `i` is contained in the `p`-nilradical of `K`,
and `M` is a perfect ring of characteristic `p`, then `K →+* M` is one-to-one correspondence to
`L →+* M`, given by `PerfectRing.lift`. This is a generalization to `PerfectClosure.lift`. -/
def PerfectRing.liftEquiv : (K →+* M) ≃ (L →+* M) where
  toFun j := lift i j p
  invFun f := f.comp i
  left_inv f := lift_comp i f p
  right_inv := comp_lift i p

theorem PerfectRing.liftEquiv_apply : liftEquiv i p j = lift i j p := rfl

theorem PerfectRing.liftEquiv_symm_apply (f : L →+* M) : (liftEquiv i p).symm f = f.comp i := rfl

section comp

variable {N : Type*} [CommRing N] (k : K →+* N) [ExpChar N p] [PerfectRing N p]
  [IsPRadical j p]

theorem PerfectRing.lift_comp_lift_apply (x : L) :
    lift j k p (lift i j p x) = lift i k p x := by
  obtain ⟨n, y, h⟩ := IsPRadical.pow_mem i p x
  rw [lift_apply i j p _ _ _ h, lift_apply i k p _ _ _ h]
  refine (injective_frobenius N p).iterate n ?_
  rw [← RingHom.map_iterate_frobenius, ← coe_iterateFrobenius, ← iterateFrobeniusEquiv_apply,
    RingEquiv.apply_symm_apply, ← coe_iterateFrobenius, ← iterateFrobeniusEquiv_apply,
    RingEquiv.apply_symm_apply, lift_comp_apply]

theorem PerfectRing.lift_comp_lift :
    (lift j k p).comp (lift i j p) = lift i k p :=
  RingHom.ext (lift_comp_lift_apply i j p k)

theorem PerfectRing.lift_comp_lift_apply_eq_self [PerfectRing L p] (x : L) :
    lift j i p (lift i j p x) = x := by
  rw [lift_comp_lift_apply, lift_self_apply]

theorem PerfectRing.lift_comp_lift_eq_id [PerfectRing L p] :
    (lift j i p).comp (lift i j p) = RingHom.id L :=
  RingHom.ext (lift_comp_lift_apply_eq_self i j p)

end comp

end PerfectRing.lift

section equiv

variable [IsPerfectClosure i p] [IsPerfectClosure j p]

/-- If `L` and `M` are both perfect closures of `K`, then there is a ring isomorphism `L ≃+* M`.
This is similar to `IsAlgClosure.equiv` and `IsSepClosure.equiv`. -/
def IsPerfectClosure.equiv : L ≃+* M where
  __ := haveI := perfectRing j p; PerfectRing.lift i j p
  invFun := haveI := perfectRing i p; PerfectRing.liftAux j i p
  left_inv := haveI := perfectRing i p; haveI := perfectRing j p;
    PerfectRing.lift_comp_lift_apply_eq_self i j p
  right_inv := haveI := perfectRing i p; haveI := perfectRing j p;
    PerfectRing.lift_comp_lift_apply_eq_self j i p

theorem IsPerfectClosure.equiv_toRingHom : haveI := perfectRing j p;
    (equiv i j p).toRingHom = PerfectRing.lift i j p := rfl

theorem IsPerfectClosure.equiv_symm : (equiv i j p).symm = equiv j i p := rfl

theorem IsPerfectClosure.equiv_symm_toRingHom : haveI := perfectRing i p;
    (equiv i j p).symm.toRingHom = PerfectRing.lift j i p := rfl

theorem IsPerfectClosure.equiv_apply (x : L) (n : ℕ) (y : K) (h : i y = x ^ p ^ n) :
    haveI := perfectRing j p; equiv i j p x = (iterateFrobeniusEquiv M p n).symm (j y) :=
  haveI := perfectRing j p; PerfectRing.liftAux_apply i j p _ _ _ h

theorem IsPerfectClosure.equiv_symm_apply (x : M) (n : ℕ) (y : K) (h : j y = x ^ p ^ n) :
    haveI := perfectRing i p; (equiv i j p).symm x = (iterateFrobeniusEquiv L p n).symm (i y) := by
  rw [equiv_symm, equiv_apply j i p _ _ _ h]

theorem IsPerfectClosure.equiv_self_apply (x : L) : equiv i i p x = x :=
  haveI := perfectRing i p; PerfectRing.liftAux_self_apply i p x

theorem IsPerfectClosure.equiv_self : equiv i i p = RingEquiv.refl L :=
  RingEquiv.ext (equiv_self_apply i p)

theorem IsPerfectClosure.equiv_comp_apply (x : K) : equiv i j p (i x) = j x :=
  haveI := perfectRing j p; PerfectRing.lift_comp_apply i j p x

theorem IsPerfectClosure.equiv_comp : (equiv i j p).toRingHom.comp i = j :=
  RingHom.ext (equiv_comp_apply i j p)

section comp

variable {N : Type*} [CommRing N] (k : K →+* N) [ExpChar N p] [IsPerfectClosure k p]

theorem IsPerfectClosure.equiv_comp_equiv_apply (x : L) :
    equiv j k p (equiv i j p x) = equiv i k p x :=
  haveI := perfectRing j p; haveI := perfectRing k p;
  PerfectRing.lift_comp_lift_apply i j p k x

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

namespace PerfectClosure

-- TODO: relax `Field` assumption (need to change `PerfectClosure` file)
variable (K) in
/-- The absolute perfect closure `PerfectClosure` is a perfect closure. -/
instance isPerfectClosure [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    IsPerfectClosure (PerfectClosure.of K p) p where
  isPRadical'.pow_mem' x := PerfectClosure.induction_on x fun x ↦ ⟨x.1, x.2, by
    rw [← iterate_frobenius, iterate_frobenius_mk K p x.1 x.2]⟩
  isPRadical'.ker_le' x h := by
    rw [RingHom.mem_ker, of_apply, zero_def, eq_iff'] at h
    obtain ⟨n, h⟩ := h
    simp_rw [zero_add, ← coe_iterateFrobenius, map_zero] at h
    exact mem_pNilradical.2 ⟨n, h⟩

end PerfectClosure

end IsPerfectClosure
