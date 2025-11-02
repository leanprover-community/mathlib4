/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.PurelyInseparable.Basic
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

- `IsPerfectClosure`: if `i : K →+* L` is `p`-radical ring homomorphism, then it makes `L` a
  perfect closure of `K`, if `L` is perfect.

  Our definition makes it synonymous to `IsPRadical` if `PerfectRing L p` is present. A caveat is
  that you need to write `[PerfectRing L p] [IsPerfectClosure i p]`. This is similar to
  `PerfectRing` which has `ExpChar` as a prerequisite.

- `PerfectRing.lift`: if a `p`-radical ring homomorphism `K →+* L` is given, `M` is a perfect ring,
  then any ring homomorphism `K →+* M` can be lifted to `L →+* M`.
  This is similar to `IsAlgClosed.lift` and `IsSepClosed.lift`.

- `PerfectRing.liftEquiv`: `K →+* M` is one-to-one correspondence to `L →+* M`,
  given by `PerfectRing.lift`. This is a generalization to `PerfectClosure.lift`.

- `IsPerfectClosure.equiv`: perfect closures of a ring are isomorphic.

## Main results

- `IsPRadical.trans`: composition of `p`-radical ring homomorphisms is also `p`-radical.

- `PerfectClosure.isPRadical`: the absolute perfect closure `PerfectClosure` is a `p`-radical
  extension over the base ring, in particular, it is a perfect closure of the base ring.

- `IsPRadical.isPurelyInseparable`, `IsPurelyInseparable.isPRadical`: `p`-radical and
  purely inseparable are equivalent for fields.

- The (relative) perfect closure `perfectClosure` is a perfect closure
  (inferred from `IsPurelyInseparable.isPRadical` automatically by Lean).

## Tags

perfect ring, perfect closure, purely inseparable

-/

open Module Polynomial IntermediateField Field

noncomputable section

/-- Given a natural number `p`, the `p`-nilradical of a ring is defined to be the
nilradical if `p > 1` (`pNilradical_eq_nilradical`), and defined to be the zero ideal if `p ≤ 1`
(`pNilradical_eq_bot'`). Equivalently, it is the ideal consisting of elements `x` such that
`x ^ p ^ n = 0` for some `n` (`mem_pNilradical`). -/
def pNilradical (R : Type*) [CommSemiring R] (p : ℕ) : Ideal R := if 1 < p then nilradical R else ⊥

theorem pNilradical_le_nilradical {R : Type*} [CommSemiring R] {p : ℕ} :
    pNilradical R p ≤ nilradical R := by
  by_cases hp : 1 < p
  · rw [pNilradical, if_pos hp]
  simp_rw [pNilradical, if_neg hp, bot_le]

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
    rw [← Nat.sub_add_cancel ((n.lt_pow_self hp).le), pow_add, h, mul_zero]
  rw [pNilradical_eq_bot hp, Ideal.mem_bot]
  refine ⟨fun h ↦ ⟨0, by rw [pow_zero, pow_one, h]⟩, fun ⟨n, h⟩ ↦ ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (not_lt.1 hp) with hp | hp
  · by_cases hn : n = 0
    · rwa [hn, pow_zero, pow_one] at h
    rw [hp, zero_pow hn, pow_zero] at h
    subsingleton [subsingleton_of_zero_eq_one h.symm]
  rwa [hp, one_pow, pow_one] at h

theorem sub_mem_pNilradical_iff_pow_expChar_pow_eq {R : Type*} [CommRing R] {p : ℕ} [ExpChar R p]
    {x y : R} : x - y ∈ pNilradical R p ↔ ∃ n : ℕ, x ^ p ^ n = y ^ p ^ n := by
  simp_rw [mem_pNilradical, sub_pow_expChar_pow, sub_eq_zero]

theorem pow_expChar_pow_inj_of_pNilradical_eq_bot (R : Type*) [CommRing R] (p : ℕ) [ExpChar R p]
    (h : pNilradical R p = ⊥) (n : ℕ) : Function.Injective fun x : R ↦ x ^ p ^ n := fun _ _ H ↦
  sub_eq_zero.1 <| Ideal.mem_bot.1 <| h ▸ sub_mem_pNilradical_iff_pow_expChar_pow_eq.2 ⟨n, H⟩

theorem pNilradical_eq_bot_of_frobenius_inj (R : Type*) [CommSemiring R] (p : ℕ) [ExpChar R p]
    (h : Function.Injective (frobenius R p)) : pNilradical R p = ⊥ := bot_unique fun x ↦ by
  rw [mem_pNilradical, Ideal.mem_bot]
  exact fun ⟨n, _⟩ ↦ h.iterate n (by rwa [← coe_iterateFrobenius, map_zero])

theorem PerfectRing.pNilradical_eq_bot (R : Type*) [CommSemiring R] (p : ℕ) [ExpChar R p]
    [PerfectRing R p] : pNilradical R p = ⊥ :=
  pNilradical_eq_bot_of_frobenius_inj R p (injective_frobenius R p)

section IsPerfectClosure

variable {K L M N : Type*}

section CommSemiring

variable [CommSemiring K] [CommSemiring L] [CommSemiring M]
  (i : K →+* L) (j : K →+* M) (f : L →+* M) (p : ℕ)

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

/-- If `i : K →+* L` is a `p`-radical ring homomorphism, then it makes `L` a perfect closure
of `K`, if `L` is perfect.
In this case the kernel of `i` is equal to the `p`-nilradical of `K`
(see `IsPerfectClosure.ker_eq`).

Our definition makes it synonymous to `IsPRadical` if `PerfectRing L p` is present. A caveat is
that you need to write `[PerfectRing L p] [IsPerfectClosure i p]`. This is similar to
`PerfectRing` which has `ExpChar` as a prerequisite. -/
@[nolint unusedArguments]
abbrev IsPerfectClosure [ExpChar L p] [PerfectRing L p] := IsPRadical i p

/-- If `i : K →+* L` is a ring homomorphism of exponential characteristic `p` rings, such that `L`
is perfect, then the `p`-nilradical of `K` is contained in the kernel of `i`. -/
theorem RingHom.pNilradical_le_ker_of_perfectRing [ExpChar L p] [PerfectRing L p] :
    pNilradical K p ≤ RingHom.ker i := fun x h ↦ by
  obtain ⟨n, h⟩ := mem_pNilradical.1 h
  replace h := congr((iterateFrobeniusEquiv L p n).symm (i $h))
  rwa [map_pow, ← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply, RingEquiv.symm_apply_apply,
    map_zero, map_zero] at h

variable [ExpChar L p] in
theorem IsPerfectClosure.ker_eq [PerfectRing L p] [IsPerfectClosure i p] :
    RingHom.ker i = pNilradical K p :=
  IsPRadical.ker_le'.antisymm (i.pNilradical_le_ker_of_perfectRing p)

namespace PerfectRing

/- NOTE: To define `PerfectRing.lift_aux`, only the `IsPRadical.pow_mem` is required, but not
`IsPRadical.ker_le`. But in order to use typeclass, here we require the whole `IsPRadical`. -/

variable [ExpChar M p] [PerfectRing M p] [IsPRadical i p]

theorem lift_aux (x : L) : ∃ y : ℕ × K, i y.2 = x ^ p ^ y.1 := by
  obtain ⟨n, y, h⟩ := IsPRadical.pow_mem i p x
  exact ⟨(n, y), h⟩

/-- If `i : K →+* L` and `j : K →+* M` are ring homomorphisms of characteristic `p` rings, such that
`i` is `p`-radical (in fact only the `IsPRadical.pow_mem` is required) and `M` is a perfect ring,
then one can define a map `L → M` which maps an element `x` of `L` to `y ^ (p ^ -n)` if
`x ^ (p ^ n)` is equal to some element `y` of `K`. -/
def liftAux (x : L) : M := (iterateFrobeniusEquiv M p (Classical.choose (lift_aux i p x)).1).symm
  (j (Classical.choose (lift_aux i p x)).2)

@[simp]
theorem liftAux_self_apply [ExpChar L p] [PerfectRing L p] (x : L) : liftAux i i p x = x := by
  rw [liftAux, Classical.choose_spec (lift_aux i p x), ← iterateFrobenius_def,
    ← iterateFrobeniusEquiv_apply, RingEquiv.symm_apply_apply]

@[simp]
theorem liftAux_self [ExpChar L p] [PerfectRing L p] : liftAux i i p = id :=
  funext (liftAux_self_apply i p)

@[simp]
theorem liftAux_id_apply (x : K) : liftAux (RingHom.id K) j p x = j x := by
  have := RingHom.id_apply _ ▸ Classical.choose_spec (lift_aux (RingHom.id K) p x)
  rw [liftAux, this, map_pow, ← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply,
    RingEquiv.symm_apply_apply]

@[simp]
theorem liftAux_id : liftAux (RingHom.id K) j p = j := funext (liftAux_id_apply j p)

end PerfectRing

end CommSemiring

section CommRing

variable [CommRing K] [CommRing L] [CommRing M] [CommRing N]
  (i : K →+* L) (j : K →+* M) (k : K →+* N) (f : L →+* M) (g : L →+* N)
  (p : ℕ) [ExpChar M p]


namespace IsPRadical

/-- If `i : K →+* L` is `p`-radical, then for any ring `M` of exponential charactistic `p` whose
`p`-nilradical is zero, the map `(L →+* M) → (K →+* M)` induced by `i` is injective. -/
theorem injective_comp_of_pNilradical_eq_bot [IsPRadical i p] (h : pNilradical M p = ⊥) :
    Function.Injective fun f : L →+* M ↦ f.comp i := fun f g heq ↦ by
  ext x
  obtain ⟨n, y, hx⟩ := IsPRadical.pow_mem i p x
  apply_fun _ using pow_expChar_pow_inj_of_pNilradical_eq_bot M p h n
  simpa only [← map_pow, ← hx] using congr($(heq) y)

variable (M)

/-- If `i : K →+* L` is `p`-radical, then for any reduced ring `M` of exponential charactistic `p`,
the map `(L →+* M) → (K →+* M)` induced by `i` is injective.
A special case of `IsPRadical.injective_comp_of_pNilradical_eq_bot`
and a generalization of `IsPurelyInseparable.injective_comp_algebraMap`. -/
theorem injective_comp [IsPRadical i p] [IsReduced M] :
    Function.Injective fun f : L →+* M ↦ f.comp i :=
  injective_comp_of_pNilradical_eq_bot i p <| bot_unique <|
    pNilradical_le_nilradical.trans (nilradical_eq_zero M).le

/-- If `i : K →+* L` is `p`-radical, then for any perfect ring `M` of exponential charactistic `p`,
the map `(L →+* M) → (K →+* M)` induced by `i` is injective.
A special case of `IsPRadical.injective_comp_of_pNilradical_eq_bot`. -/
theorem injective_comp_of_perfect [IsPRadical i p] [PerfectRing M p] :
    Function.Injective fun f : L →+* M ↦ f.comp i :=
  injective_comp_of_pNilradical_eq_bot i p (PerfectRing.pNilradical_eq_bot M p)

end IsPRadical

namespace PerfectRing

variable [ExpChar K p] [PerfectRing M p] [IsPRadical i p]

/-- If `i : K →+* L` and `j : K →+* M` are ring homomorphisms of characteristic `p` rings, such that
`i` is `p`-radical, and `M` is a perfect ring, then `PerfectRing.liftAux` is well-defined. -/
theorem liftAux_apply (x : L) (n : ℕ) (y : K) (h : i y = x ^ p ^ n) :
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

variable [ExpChar L p]

/-- If `i : K →+* L` and `j : K →+* M` are ring homomorphisms of characteristic `p` rings, such that
`i` is `p`-radical, and `M` is a perfect ring, then `PerfectRing.liftAux`
is a ring homomorphism. This is similar to `IsAlgClosed.lift` and `IsSepClosed.lift`. -/
def lift : L →+* M where
  toFun := liftAux i j p
  map_one' := by simp [liftAux_apply i j p 1 0 1 (by rw [one_pow, map_one])]
  map_mul' x1 x2 := by
    obtain ⟨n1, y1, h1⟩ := IsPRadical.pow_mem i p x1
    obtain ⟨n2, y2, h2⟩ := IsPRadical.pow_mem i p x2
    rw [liftAux_apply i j p _ _ _ h1, liftAux_apply i j p _ _ _ h2,
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
    rw [liftAux_apply i j p _ _ _ h1, liftAux_apply i j p _ _ _ h2,
      liftAux_apply i j p (x1 + x2) (n1 + n2) (y1 ^ p ^ n2 + y2 ^ p ^ n1) (by rw [map_add,
        map_pow, map_pow, h1, h2, ← pow_mul, ← pow_add, ← pow_mul, ← pow_add,
        add_comm n2, add_pow_expChar_pow]),
      map_add, map_pow, map_pow, map_add, ← iterateFrobeniusEquiv_def]
    nth_rw 1 [iterateFrobeniusEquiv_symm_add_apply]
    rw [RingEquiv.symm_apply_apply, add_comm n1, iterateFrobeniusEquiv_symm_add_apply,
      ← iterateFrobeniusEquiv_def, RingEquiv.symm_apply_apply]

theorem lift_apply (x : L) (n : ℕ) (y : K) (h : i y = x ^ p ^ n) :
    lift i j p x = (iterateFrobeniusEquiv M p n).symm (j y) :=
  liftAux_apply i j p _ _ _ h

@[simp]
theorem lift_comp_apply (x : K) : lift i j p (i x) = j x := by
  rw [lift_apply i j p _ 0 x (by rw [pow_zero, pow_one]), iterateFrobeniusEquiv_zero]; rfl

@[simp]
theorem lift_comp : (lift i j p).comp i = j := RingHom.ext (lift_comp_apply i j p)

theorem lift_self_apply [PerfectRing L p] (x : L) : lift i i p x = x := liftAux_self_apply i p x

@[simp]
theorem lift_self [PerfectRing L p] : lift i i p = RingHom.id L :=
  RingHom.ext (liftAux_self_apply i p)

theorem lift_id_apply (x : K) : lift (RingHom.id K) j p x = j x := liftAux_id_apply j p x

@[simp]
theorem lift_id : lift (RingHom.id K) j p = j := RingHom.ext (liftAux_id_apply j p)

@[simp]
theorem comp_lift : lift i (f.comp i) p = f :=
  IsPRadical.injective_comp_of_perfect _ i p (lift_comp i _ p)

theorem comp_lift_apply (x : L) : lift i (f.comp i) p x = f x := congr($(comp_lift i f p) x)

variable (M) in
/-- If `i : K →+* L` is a homomorphisms of characteristic `p` rings, such that
`i` is `p`-radical, and `M` is a perfect ring of characteristic `p`,
then `K →+* M` is one-to-one correspondence to
`L →+* M`, given by `PerfectRing.lift`. This is a generalization to `PerfectClosure.lift`. -/
def liftEquiv : (K →+* M) ≃ (L →+* M) where
  toFun j := lift i j p
  invFun f := f.comp i
  left_inv f := lift_comp i f p
  right_inv f := comp_lift i f p

theorem liftEquiv_apply : liftEquiv M i p j = lift i j p := rfl

theorem liftEquiv_symm_apply : (liftEquiv M i p).symm f = f.comp i := rfl

theorem liftEquiv_id_apply : liftEquiv M (RingHom.id K) p j = j :=
  lift_id j p

@[simp]
theorem liftEquiv_id : liftEquiv M (RingHom.id K) p = Equiv.refl _ :=
  Equiv.ext (liftEquiv_id_apply · p)

section comp

variable [ExpChar N p] [PerfectRing N p] [IsPRadical j p]

@[simp]
theorem lift_comp_lift : (lift j k p).comp (lift i j p) = lift i k p :=
  IsPRadical.injective_comp_of_perfect _ i p (by ext; simp)

@[simp]
theorem lift_comp_lift_apply (x : L) : lift j k p (lift i j p x) = lift i k p x :=
  congr($(lift_comp_lift i j k p) x)

theorem lift_comp_lift_apply_eq_self [PerfectRing L p] (x : L) :
    lift j i p (lift i j p x) = x := by
  rw [lift_comp_lift_apply, lift_self_apply]

theorem lift_comp_lift_eq_id [PerfectRing L p] :
    (lift j i p).comp (lift i j p) = RingHom.id L :=
  RingHom.ext (lift_comp_lift_apply_eq_self i j p)

end comp

section liftEquiv_comp

variable [ExpChar N p] [IsPRadical g p] [IsPRadical (g.comp i) p]

@[simp]
theorem lift_lift : lift g (lift i j p) p = lift (g.comp i) j p := by
  refine IsPRadical.injective_comp_of_perfect _ (g.comp i) p ?_
  simp_rw [← RingHom.comp_assoc _ _ (lift g _ p), lift_comp]

theorem lift_lift_apply (x : N) : lift g (lift i j p) p x = lift (g.comp i) j p x :=
  congr($(lift_lift i j g p) x)

@[simp]
theorem liftEquiv_comp_apply :
    liftEquiv M g p (liftEquiv M i p j) = liftEquiv M (g.comp i) p j := lift_lift i j g p

@[simp]
theorem liftEquiv_trans :
    (liftEquiv M i p).trans (liftEquiv M g p) = liftEquiv M (g.comp i) p :=
  Equiv.ext (liftEquiv_comp_apply i · g p)

end liftEquiv_comp

end PerfectRing

namespace IsPerfectClosure

variable [ExpChar K p] [ExpChar L p] [PerfectRing L p] [IsPerfectClosure i p] [PerfectRing M p]
  [IsPerfectClosure j p]

/-- If `L` and `M` are both perfect closures of `K`, then there is a ring isomorphism `L ≃+* M`.
This is similar to `IsAlgClosure.equiv` and `IsSepClosure.equiv`. -/
def equiv : L ≃+* M where
  __ := PerfectRing.lift i j p
  invFun := PerfectRing.liftAux j i p
  left_inv := PerfectRing.lift_comp_lift_apply_eq_self i j p
  right_inv := PerfectRing.lift_comp_lift_apply_eq_self j i p

theorem equiv_toRingHom : (equiv i j p).toRingHom = PerfectRing.lift i j p := rfl

@[simp]
theorem equiv_symm : (equiv i j p).symm = equiv j i p := rfl

theorem equiv_symm_toRingHom :
    (equiv i j p).symm.toRingHom = PerfectRing.lift j i p := rfl

theorem equiv_apply (x : L) (n : ℕ) (y : K) (h : i y = x ^ p ^ n) :
    equiv i j p x = (iterateFrobeniusEquiv M p n).symm (j y) :=
  PerfectRing.liftAux_apply i j p _ _ _ h

theorem equiv_symm_apply (x : M) (n : ℕ) (y : K) (h : j y = x ^ p ^ n) :
    (equiv i j p).symm x = (iterateFrobeniusEquiv L p n).symm (i y) := by
  rw [equiv_symm, equiv_apply j i p _ _ _ h]

theorem equiv_self_apply (x : L) : equiv i i p x = x :=
  PerfectRing.liftAux_self_apply i p x

@[simp]
theorem equiv_self : equiv i i p = RingEquiv.refl L :=
  RingEquiv.ext (equiv_self_apply i p)

@[simp]
theorem equiv_comp_apply (x : K) : equiv i j p (i x) = j x :=
  PerfectRing.lift_comp_apply i j p x

@[simp]
theorem equiv_comp : RingHom.comp (equiv i j p) i = j :=
  RingHom.ext (equiv_comp_apply i j p)

section comp

variable [ExpChar N p] [PerfectRing N p] [IsPerfectClosure k p]

@[simp]
theorem equiv_comp_equiv_apply (x : L) :
    equiv j k p (equiv i j p x) = equiv i k p x :=
  PerfectRing.lift_comp_lift_apply i j k p x

@[simp]
theorem equiv_comp_equiv : (equiv i j p).trans (equiv j k p) = equiv i k p :=
  RingEquiv.ext (equiv_comp_equiv_apply i j k p)

theorem equiv_comp_equiv_apply_eq_self (x : L) :
    equiv j i p (equiv i j p x) = x := by
  rw [equiv_comp_equiv_apply, equiv_self_apply]

theorem equiv_comp_equiv_eq_id :
    (equiv i j p).trans (equiv j i p) = RingEquiv.refl L :=
  RingEquiv.ext (equiv_comp_equiv_apply_eq_self i j p)

end comp

end IsPerfectClosure

end CommRing

namespace PerfectClosure

variable [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p]
variable (K)

/-- The absolute perfect closure `PerfectClosure` is a `p`-radical extension over the base ring.
In particular, it is a perfect closure of the base ring, that is,
`IsPerfectClosure (PerfectClosure.of K p) p`. -/
instance isPRadical : IsPRadical (PerfectClosure.of K p) p where
  pow_mem' x := PerfectClosure.induction_on x fun x ↦ ⟨x.1, x.2, by
    rw [← iterate_frobenius, iterate_frobenius_mk K p x.1 x.2]⟩
  ker_le' x h := by
    rw [RingHom.mem_ker, of_apply, zero_def, mk_eq_iff] at h
    obtain ⟨n, h⟩ := h
    simp_rw [zero_add, ← coe_iterateFrobenius, map_zero] at h
    exact mem_pNilradical.2 ⟨n, h⟩

end PerfectClosure

section Field

variable [Field K] [Field L] [Algebra K L] (p : ℕ) [ExpChar K p]
variable (K L)

/-- If `L / K` is a `p`-radical field extension, then it is purely inseparable. -/
theorem IsPRadical.isPurelyInseparable [IsPRadical (algebraMap K L) p] :
    IsPurelyInseparable K L :=
  (isPurelyInseparable_iff_pow_mem K p).2 (IsPRadical.pow_mem (algebraMap K L) p)

/-- If `L / K` is a purely inseparable field extension, then it is `p`-radical. In particular, if
`L` is perfect, then the (relative) perfect closure `perfectClosure K L` is a perfect closure
of `K`, that is, `IsPerfectClosure (algebraMap K (perfectClosure K L)) p`. -/
instance IsPurelyInseparable.isPRadical [IsPurelyInseparable K L] :
    IsPRadical (algebraMap K L) p where
  pow_mem' := (isPurelyInseparable_iff_pow_mem K p).1 ‹_›
  ker_le' := (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap K L).injective ▸ bot_le

end Field

end IsPerfectClosure
