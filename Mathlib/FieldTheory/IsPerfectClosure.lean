/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.PurelyInseparable
import Mathlib.FieldTheory.PerfectClosure

/-!

# `IsPerfectClosure` predicate

This file contains `IsPerfectClosure` which asserts that `L` is a perfect closure of `K` under a
ring homomorphism `i : K →+* L`, as well as its basic properties.

## Main definitions

- `pNilradical`: given a natural number `p`, the `p`-nilradical of a ring is defined to be the
  nilradical if `p > 1` (`pNilradical_eq_nilradical`), and defined to be the zero ideal if `p ≤ 1`
  (`pNilradical_eq_bot'`). Equivalently, it is the ideal consisting of elements `x` such that
  `x ^ p ^ n = 0` for some `n` (`mem_pNilradical`).

- `IsPRadical`: a ring homomorphism `i : K →+* L` of characteristic `p` rings is called `p`-radical,
  if or any element `x` of `L` there is `n : ℕ` such that `x ^ (p ^ n)` is contained in `K`,
  and the kernel of `i` is contained in the `p`-nilradical of `K`.
  A generalization of purely inseparable extension for fields.

- `IsPerfectClosure`: a ring homomorphism `i : K →+* L` of characteristic `p` rings makes `L` a
  perfect closure of `K`, if `L` is perfect, and `i` is `p`-radical.

- `PerfectRing.lift`: if a `p`-radical ring homomorphism `K →+* L` is given, `M` is a perfect ring,
  then any ring homomorphism `K →+* M` can be lifted to `L →+* M`.
  This is similar to `IsAlgClosed.lift` and `IsSepClosed.lift`.

- `PerfectRing.liftEquiv`: `K →+* M` is one-to-one correspondence to `L →+* M`,
  given by `PerfectRing.lift`. This is a generalization to `PerfectClosure.lift`.

- `IsPerfectClosure.equiv`: perfect closures of a ring are isomorphic.

## Main results

- `IsPRadical.trans`: composition of `p`-radical ring homomorphisms is also `p`-radical.

- `PerfectClosure.isPerfectClosure`: the absolute perfect closure `PerfectClosure` is a
  perfect closure.

- `IsPRadical.isPurelyInseparable`, `IsPurelyInseparable.isPRadical`: `p`-radical and
  purely inseparable are equivalent for fields.

- `perfectClosure.isPerfectClosure`: the (relative) perfect closure `perfectClosure` is a
  perfect closure.

## Tags

perfect ring, perfect closure, purely inseparable

-/

open scoped Classical Polynomial

open FiniteDimensional Polynomial IntermediateField Field

noncomputable section

/-- Given a natural number `p`, the `p`-nilradical of a ring is defined to be the
nilradical if `p > 1` (`pNilradical_eq_nilradical`), and defined to be the zero ideal if `p ≤ 1`
(`pNilradical_eq_bot'`). Equivalently, it is the ideal consisting of elements `x` such that
`x ^ p ^ n = 0` for some `n` (`mem_pNilradical`). -/
def pNilradical (R : Type*) [CommSemiring R] (p : ℕ) : Ideal R := if 1 < p then nilradical R else ⊥

theorem pNilradical_eq_nilradical {R : Type*} [CommSemiring R] {p : ℕ} (hp : 1 < p) :
    pNilradical R p = nilradical R := by rw [pNilradical, if_pos hp]

theorem pNilradical_eq_bot {R : Type*} [CommSemiring R] {p : ℕ} (hp : ¬ 1 < p) :
    pNilradical R p = ⊥ := by rw [pNilradical, if_neg hp]

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

section IsPerfectClosure

variable {K L M N : Type*}

section CommSemiring

variable [CommSemiring K] [CommSemiring L] [CommSemiring M]
  (i : K →+* L) (j : K →+* M) (f : L →+* M)
  (p : ℕ) [ExpChar K p] [ExpChar L p] [ExpChar M p]

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

theorem IsPRadical.comap_pNilradical [IsPRadical i p] :
    (pNilradical L p).comap i = pNilradical K p := by
  refine le_antisymm (fun x h ↦ mem_pNilradical.2 ?_) (fun x h ↦ ?_)
  · obtain ⟨n, h⟩ := mem_pNilradical.1 <| Ideal.mem_comap.1 h
    obtain ⟨m, h⟩ := mem_pNilradical.1 <| ker_le i p ((map_pow i x _).symm ▸ h)
    exact ⟨n + m, by rwa [pow_add, pow_mul]⟩
  simp only [Ideal.mem_comap, mem_pNilradical] at h ⊢
  obtain ⟨n, h⟩ := h
  exact ⟨n, by simpa only [map_pow, map_zero] using congr(i $h)⟩

variable (K) in
instance IsPRadical.of_id : IsPRadical (RingHom.id K) p where
  pow_mem' x := ⟨0, x, by simp⟩
  ker_le' x h := by convert Ideal.zero_mem _

/-- Composition of `p`-radical ring homomorphisms is also `p`-radical. -/
theorem IsPRadical.trans [IsPRadical i p] [IsPRadical f p] :
    IsPRadical (f.comp i) p where
  pow_mem' x := by
    obtain ⟨n, y, hy⟩ := pow_mem f p x
    obtain ⟨m, z, hz⟩ := pow_mem i p y
    exact ⟨n + m, z, by rw [RingHom.comp_apply, hz, map_pow, hy, pow_add, pow_mul]⟩
  ker_le' x h := by
    rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker] at h
    simpa only [← Ideal.mem_comap, comap_pNilradical] using ker_le f p h

/-- If `i : K →+* L` is a ring homomorphism of characteristic `p` rings, then it makes `L`
a perfect closure of `K` if the following conditions are satisfied:

- `L` is a perfect ring.
- `i : K →+* L` is `p`-radical.

In this case the kernel of `i` is equal to the `p`-nilradical of `K`
(see `IsPerfectClosure.ker_eq`). -/
@[mk_iff]
class IsPerfectClosure extends IsPRadical i p : Prop where
  [perfectRing' : PerfectRing L p]

theorem IsPerfectClosure.perfectRing [IsPerfectClosure i p] : PerfectRing L p := perfectRing' i

/-- If `i : K →+* L` is a ring homomorphism of exponential characteristic `p` rings, such that `L`
is perfect, then the `p`-nilradical of `K` is contained in the kernel of `i`. -/
theorem RingHom.pNilradical_le_ker_of_perfectRing [PerfectRing L p] :
    pNilradical K p ≤ RingHom.ker i := fun x h ↦ by
  obtain ⟨n, h⟩ := mem_pNilradical.1 h
  replace h := congr((iterateFrobeniusEquiv L p n).symm (i $h))
  rwa [map_pow, ← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply, RingEquiv.symm_apply_apply,
    map_zero, map_zero] at h

theorem IsPerfectClosure.ker_eq [IsPerfectClosure i p] : RingHom.ker i = pNilradical K p :=
  toIsPRadical.ker_le'.antisymm (haveI := perfectRing i p; i.pNilradical_le_ker_of_perfectRing p)

/-- A perfect ring is its perfect closure. -/
instance IsPerfectClosure.self_of_perfect [PerfectRing M p] :
    IsPerfectClosure (RingHom.id M) p where

section PerfectRing.lift

/- NOTE: To define `PerfectRing.lift_aux`, only the `IsPRadical.pow_mem` is required, but not
`IsPRadical.ker_le`. But in order to use typeclass, here we require the whole `IsPRadical`. -/

variable [PerfectRing M p] [IsPRadical i p]

theorem PerfectRing.lift_aux (x : L) : ∃ y : ℕ × K, i y.2 = x ^ p ^ y.1 := by
  obtain ⟨n, y, h⟩ := IsPRadical.pow_mem i p x
  exact ⟨(n, y), h⟩

/-- If `i : K →+* L` and `j : K →+* M` are ring homomorphisms of characteristic `p` rings, such that
`i` is `p`-radical (in fact only the `IsPRadical.pow_mem` is required) and `M` is a perfect ring,
then one can define a map `L → M` which maps an element `x` of `L` to `y ^ (p ^ -n)` if
`x ^ (p ^ n)` is equal to some element `y` of `K`. -/
def PerfectRing.liftAux (x : L) : M :=
  (iterateFrobeniusEquiv M p (Classical.choose (lift_aux i p x)).1).symm
    (j (Classical.choose (lift_aux i p x)).2)

@[simp]
theorem PerfectRing.liftAux_self_apply [PerfectRing L p] (x : L) : liftAux i i p x = x := by
  rw [liftAux, Classical.choose_spec (lift_aux i p x), ← iterateFrobenius_def,
    ← iterateFrobeniusEquiv_apply, RingEquiv.symm_apply_apply]

@[simp]
theorem PerfectRing.liftAux_self [PerfectRing L p] : liftAux i i p = id :=
  funext (liftAux_self_apply i p)

@[simp]
theorem PerfectRing.liftAux_id_apply (x : K) : liftAux (RingHom.id K) j p x = j x := by
  have := RingHom.id_apply _ ▸ Classical.choose_spec (lift_aux (RingHom.id K) p x)
  rw [liftAux, this, map_pow, ← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply,
    RingEquiv.symm_apply_apply]

@[simp]
theorem PerfectRing.liftAux_id : liftAux (RingHom.id K) j p = j :=
  funext (liftAux_id_apply j p)

end PerfectRing.lift

end CommSemiring

section CommRing

variable [CommRing K] [CommRing L] [CommRing M] [CommRing N]
  (i : K →+* L) (j : K →+* M) (k : K →+* N) (f : L →+* M) (g : L →+* N)
  (p : ℕ) [ExpChar K p] [ExpChar L p] [ExpChar M p] [ExpChar N p]

section PerfectRing.lift

variable [PerfectRing M p] [IsPRadical i p]

/-- If `i : K →+* L` and `j : K →+* M` are ring homomorphisms of characteristic `p` rings, such that
`i` is `p`-radical, and `M` is a perfect ring, then `PerfectRing.liftAux` is well-defined. -/
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
`i` is `p`-radical, and `M` is a perfect ring, then `PerfectRing.liftAux`
is a ring homomorphism. This is similar to `IsAlgClosed.lift` and `IsSepClosed.lift`. -/
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

@[simp]
theorem PerfectRing.lift_self [PerfectRing L p] : lift i i p = RingHom.id L :=
  RingHom.ext (liftAux_self_apply i p)

theorem PerfectRing.lift_id_apply (x : K) : lift (RingHom.id K) j p x = j x :=
  liftAux_id_apply j p x

@[simp]
theorem PerfectRing.lift_id : lift (RingHom.id K) j p = j :=
  RingHom.ext (liftAux_id_apply j p)

@[simp]
theorem PerfectRing.lift_comp_apply (x : K) : lift i j p (i x) = j x := by
  rw [lift_apply i j p _ 0 x (by rw [pow_zero, pow_one]), iterateFrobeniusEquiv_zero]; rfl

@[simp]
theorem PerfectRing.lift_comp : (lift i j p).comp i = j :=
  RingHom.ext (lift_comp_apply i j p)

theorem PerfectRing.comp_lift_apply (x : L) : lift i (f.comp i) p x = f x := by
  obtain ⟨n, y, h⟩ := IsPRadical.pow_mem i p x
  rw [lift_apply i _ p _ _ _ h, RingHom.comp_apply, h, ← iterate_frobenius, f.map_iterate_frobenius,
    ← coe_iterateFrobenius, ← iterateFrobeniusEquiv_apply, RingEquiv.symm_apply_apply]

@[simp]
theorem PerfectRing.comp_lift : lift i (f.comp i) p = f :=
  RingHom.ext (comp_lift_apply i f p)

variable (M) in
/-- If `i : K →+* L` is a homomorphisms of characteristic `p` rings, such that
`i` is `p`-radical, and `M` is a perfect ring of characteristic `p`,
then `K →+* M` is one-to-one correspondence to
`L →+* M`, given by `PerfectRing.lift`. This is a generalization to `PerfectClosure.lift`. -/
def PerfectRing.liftEquiv : (K →+* M) ≃ (L →+* M) where
  toFun j := lift i j p
  invFun f := f.comp i
  left_inv f := lift_comp i f p
  right_inv f := comp_lift i f p

theorem PerfectRing.liftEquiv_apply : liftEquiv M i p j = lift i j p := rfl

theorem PerfectRing.liftEquiv_symm_apply : (liftEquiv M i p).symm f = f.comp i := rfl

theorem PerfectRing.liftEquiv_id_apply : liftEquiv M (RingHom.id K) p j = j :=
  lift_id j p

@[simp]
theorem PerfectRing.liftEquiv_id : liftEquiv M (RingHom.id K) p = Equiv.refl _ :=
  Equiv.ext (liftEquiv_id_apply · p)

section comp

variable [PerfectRing N p] [IsPRadical j p]

@[simp]
theorem PerfectRing.lift_comp_lift_apply (x : L) :
    lift j k p (lift i j p x) = lift i k p x := by
  obtain ⟨n, y, h⟩ := IsPRadical.pow_mem i p x
  rw [lift_apply i j p _ _ _ h, lift_apply i k p _ _ _ h]
  refine (injective_frobenius N p).iterate n ?_
  rw [← RingHom.map_iterate_frobenius, ← coe_iterateFrobenius, ← iterateFrobeniusEquiv_apply,
    RingEquiv.apply_symm_apply, ← coe_iterateFrobenius, ← iterateFrobeniusEquiv_apply,
    RingEquiv.apply_symm_apply, lift_comp_apply]

@[simp]
theorem PerfectRing.lift_comp_lift :
    (lift j k p).comp (lift i j p) = lift i k p :=
  RingHom.ext (lift_comp_lift_apply i j k p)

theorem PerfectRing.lift_comp_lift_apply_eq_self [PerfectRing L p] (x : L) :
    lift j i p (lift i j p x) = x := by
  rw [lift_comp_lift_apply, lift_self_apply]

theorem PerfectRing.lift_comp_lift_eq_id [PerfectRing L p] :
    (lift j i p).comp (lift i j p) = RingHom.id L :=
  RingHom.ext (lift_comp_lift_apply_eq_self i j p)

end comp

section liftEquiv_comp

variable [IsPRadical g p] [IsPRadical (g.comp i) p]

theorem PerfectRing.lift_lift_apply (x : N) :
    lift g (lift i j p) p x = lift (g.comp i) j p x := by
  obtain ⟨n, y, h⟩ := IsPRadical.pow_mem (g.comp i) p x
  rw [lift_apply (g.comp i) j p _ _ _ h, lift_apply g _ p _ _ _ h,
    lift_apply i j p (i y) 0 y (by rw [pow_zero, pow_one]), iterateFrobeniusEquiv_zero]
  rfl

@[simp]
theorem PerfectRing.lift_lift : lift g (lift i j p) p = lift (g.comp i) j p :=
  RingHom.ext (lift_lift_apply i j g p)

@[simp]
theorem PerfectRing.liftEquiv_comp_apply :
    liftEquiv M g p (liftEquiv M i p j) = liftEquiv M (g.comp i) p j := lift_lift i j g p

@[simp]
theorem PerfectRing.liftEquiv_trans :
    (liftEquiv M i p).trans (liftEquiv M g p) = liftEquiv M (g.comp i) p :=
  Equiv.ext (liftEquiv_comp_apply i · g p)

end liftEquiv_comp

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

@[simp]
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

@[simp]
theorem IsPerfectClosure.equiv_self : equiv i i p = RingEquiv.refl L :=
  RingEquiv.ext (equiv_self_apply i p)

@[simp]
theorem IsPerfectClosure.equiv_comp_apply (x : K) : equiv i j p (i x) = j x :=
  haveI := perfectRing j p; PerfectRing.lift_comp_apply i j p x

@[simp]
theorem IsPerfectClosure.equiv_comp : RingHom.comp (equiv i j p) i = j :=
  RingHom.ext (equiv_comp_apply i j p)

section comp

variable [IsPerfectClosure k p]

@[simp]
theorem IsPerfectClosure.equiv_comp_equiv_apply (x : L) :
    equiv j k p (equiv i j p x) = equiv i k p x :=
  haveI := perfectRing j p; haveI := perfectRing k p;
  PerfectRing.lift_comp_lift_apply i j k p x

@[simp]
theorem IsPerfectClosure.equiv_comp_equiv : (equiv i j p).trans (equiv j k p) = equiv i k p :=
  RingEquiv.ext (equiv_comp_equiv_apply i j k p)

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

variable [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p]

variable (K)

/-- The absolute perfect closure `PerfectClosure` is a `p`-radical extension over the base ring. -/
instance isPRadical : IsPRadical (PerfectClosure.of K p) p where
  pow_mem' x := PerfectClosure.induction_on x fun x ↦ ⟨x.1, x.2, by
    rw [← iterate_frobenius, iterate_frobenius_mk K p x.1 x.2]⟩
  ker_le' x h := by
    rw [RingHom.mem_ker, of_apply, zero_def, mk_eq_iff] at h
    obtain ⟨n, h⟩ := h
    simp_rw [zero_add, ← coe_iterateFrobenius, map_zero] at h
    exact mem_pNilradical.2 ⟨n, h⟩

/-- The absolute perfect closure `PerfectClosure` is a perfect closure. -/
instance isPerfectClosure : IsPerfectClosure (PerfectClosure.of K p) p where

end PerfectClosure

section Field

variable [Field K] [Field L] [Algebra K L] (p : ℕ) [ExpChar K p]

variable (K L)

theorem IsPRadical.isPurelyInseparable [IsPRadical (algebraMap K L) p] :
    IsPurelyInseparable K L :=
  (isPurelyInseparable_iff_pow_mem K p).2 (IsPRadical.pow_mem (algebraMap K L) p)

instance IsPurelyInseparable.isPRadical [IsPurelyInseparable K L] :
    IsPRadical (algebraMap K L) p where
  pow_mem' := (isPurelyInseparable_iff_pow_mem K p).1 ‹_›
  ker_le' := (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap K L).injective ▸ bot_le

/-- If `L` is a perfect field of characteristic `p`, then the (relative) perfect closure
`perfectClosure K L` is a perfect closure of `K`. -/
instance perfectClosure.isPerfectClosure [ExpChar L p] [PerfectRing L p] :
    IsPerfectClosure (algebraMap K (perfectClosure K L)) p where

end Field

end IsPerfectClosure
