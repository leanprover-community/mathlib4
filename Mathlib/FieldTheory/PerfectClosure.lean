/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Perfect

/-!

# The perfect closure of a characteristic `p` ring

## Main definitions

- `PerfectClosure`: the perfect closure of a characteristic `p` ring, which is the smallest
  extension that makes frobenius surjective.

- `PerfectClosure.mk K p (n, x)`: for `n : ℕ` and `x : K` this is `x ^ (p ^ -n)` viewed as
  an element of `PerfectClosure K p`. Every element of `PerfectClosure K p` is of this form
  (`PerfectClosure.mk_surjective`).

- `PerfectClosure.of`: the structure map from `K` to `PerfectClosure K p`.

- `PerfectClosure.lift`: given a ring `K` of characteristic `p` and a perfect ring `L` of the same
  characteristic, any homomorphism `K →+* L` can be lifted to `PerfectClosure K p`.

## Main results

- `PerfectClosure.induction_on`: to prove a result for all elements of the perfect closure, one only
  needs to prove it for all elements of the form `x ^ (p ^ -n)`.

- `PerfectClosure.mk_mul_mk`, `PerfectClosure.one_def`, `PerfectClosure.mk_add_mk`,
  `PerfectClosure.neg_mk`, `PerfectClosure.zero_def`, `PerfectClosure.mk_zero_zero`,
  `PerfectClosure.mk_zero`, `PerfectClosure.mk_inv`, `PerfectClosure.mk_pow`:
  how to do multiplication, addition, etc. on elements of form `x ^ (p ^ -n)`.

- `PerfectClosure.mk_eq_iff`: when does `x ^ (p ^ -n)` equal.

- `PerfectClosure.eq_iff`: same as `PerfectClosure.mk_eq_iff` but with additional assumption that
  `K` being reduced, hence gives a simpler criterion.

- `PerfectClosure.instPerfectRing`: `PerfectClosure K p` is a perfect ring.

## Tags

perfect ring, perfect closure

-/

universe u v

open Function

section

variable (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- `PerfectClosure.R` is the relation `(n, x) ∼ (n + 1, x ^ p)` for `n : ℕ` and `x : K`.
`PerfectClosure K p` is the quotient by this relation. -/
@[mk_iff]
inductive PerfectClosure.R : ℕ × K → ℕ × K → Prop
  | intro : ∀ n x, PerfectClosure.R (n, x) (n + 1, frobenius K p x)

/-- The perfect closure is the smallest extension that makes frobenius surjective. -/
def PerfectClosure : Type u :=
  Quot (PerfectClosure.R K p)

end

namespace PerfectClosure

variable (K : Type u)

section Ring

variable [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- `PerfectClosure.mk K p (n, x)` for `n : ℕ` and `x : K` is an element of `PerfectClosure K p`,
viewed as `x ^ (p ^ -n)`. Every element of `PerfectClosure K p` is of this form
(`PerfectClosure.mk_surjective`). -/
def mk (x : ℕ × K) : PerfectClosure K p :=
  Quot.mk (R K p) x

theorem mk_surjective : Function.Surjective (mk K p) := Quot.mk_surjective

@[simp] theorem mk_succ_pow (m : ℕ) (x : K) : mk K p ⟨m + 1, x ^ p⟩ = mk K p ⟨m, x⟩ :=
  Eq.symm <| Quot.sound (R.intro m x)

@[simp]
theorem quot_mk_eq_mk (x : ℕ × K) : (Quot.mk (R K p) x : PerfectClosure K p) = mk K p x :=
  rfl

variable {K p}

/-- Lift a function `ℕ × K → L` to a function on `PerfectClosure K p`. -/
def liftOn {L : Type*} (x : PerfectClosure K p) (f : ℕ × K → L)
    (hf : ∀ x y, R K p x y → f x = f y) : L :=
  Quot.liftOn x f hf

@[simp]
theorem liftOn_mk {L : Sort _} (f : ℕ × K → L) (hf : ∀ x y, R K p x y → f x = f y) (x : ℕ × K) :
    (mk K p x).liftOn f hf = f x :=
  rfl

@[elab_as_elim]
theorem induction_on (x : PerfectClosure K p) {q : PerfectClosure K p → Prop}
    (h : ∀ x, q (mk K p x)) : q x :=
  Quot.inductionOn x h

variable (K p)

private theorem mul_aux_left (x1 x2 y : ℕ × K) (H : R K p x1 x2) :
    mk K p (x1.1 + y.1, (frobenius K p)^[y.1] x1.2 * (frobenius K p)^[x1.1] y.2) =
      mk K p (x2.1 + y.1, (frobenius K p)^[y.1] x2.2 * (frobenius K p)^[x2.1] y.2) :=
  match x1, x2, H with
  | _, _, R.intro n x =>
    Quot.sound <| by
      rw [← iterate_succ_apply, iterate_succ_apply', iterate_succ_apply', ← frobenius_mul,
        Nat.succ_add]
      apply R.intro

private theorem mul_aux_right (x y1 y2 : ℕ × K) (H : R K p y1 y2) :
    mk K p (x.1 + y1.1, (frobenius K p)^[y1.1] x.2 * (frobenius K p)^[x.1] y1.2) =
      mk K p (x.1 + y2.1, (frobenius K p)^[y2.1] x.2 * (frobenius K p)^[x.1] y2.2) :=
  match y1, y2, H with
  | _, _, R.intro n y =>
    Quot.sound <| by
      rw [← iterate_succ_apply, iterate_succ_apply', iterate_succ_apply', ← frobenius_mul]
      apply R.intro

instance instMul : Mul (PerfectClosure K p) :=
  ⟨Quot.lift
      (fun x : ℕ × K =>
        Quot.lift
          (fun y : ℕ × K =>
            mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 * (frobenius K p)^[x.1] y.2))
          (mul_aux_right K p x))
      fun x1 x2 (H : R K p x1 x2) =>
      funext fun e => Quot.inductionOn e fun y => mul_aux_left K p x1 x2 y H⟩

@[simp]
theorem mk_mul_mk (x y : ℕ × K) :
    mk K p x * mk K p y =
      mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 * (frobenius K p)^[x.1] y.2) :=
  rfl

instance instCommMonoid : CommMonoid (PerfectClosure K p) :=
  { (inferInstance : Mul (PerfectClosure K p)) with
    mul_assoc := fun e f g =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
          Quot.inductionOn g fun ⟨s, z⟩ => by
            apply congr_arg (Quot.mk _)
            simp only [mul_assoc, iterate_map_mul, ← iterate_add_apply,
              add_comm, add_left_comm]
    one := mk K p (0, 1)
    one_mul := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
        congr_arg (Quot.mk _) <| by
          simp only [iterate_map_one, iterate_zero_apply, one_mul, zero_add]
    mul_one := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
        congr_arg (Quot.mk _) <| by
          simp only [iterate_map_one, iterate_zero_apply, mul_one, add_zero]
    mul_comm := fun e f =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
          congr_arg (Quot.mk _) <| by simp only [add_comm, mul_comm] }

theorem one_def : (1 : PerfectClosure K p) = mk K p (0, 1) :=
  rfl

instance instInhabited : Inhabited (PerfectClosure K p) :=
  ⟨1⟩

private theorem add_aux_left (x1 x2 y : ℕ × K) (H : R K p x1 x2) :
    mk K p (x1.1 + y.1, (frobenius K p)^[y.1] x1.2 + (frobenius K p)^[x1.1] y.2) =
      mk K p (x2.1 + y.1, (frobenius K p)^[y.1] x2.2 + (frobenius K p)^[x2.1] y.2) :=
  match x1, x2, H with
  | _, _, R.intro n x =>
    Quot.sound <| by
      rw [← iterate_succ_apply, iterate_succ_apply', iterate_succ_apply', ← frobenius_add,
        Nat.succ_add]
      apply R.intro

private theorem add_aux_right (x y1 y2 : ℕ × K) (H : R K p y1 y2) :
    mk K p (x.1 + y1.1, (frobenius K p)^[y1.1] x.2 + (frobenius K p)^[x.1] y1.2) =
      mk K p (x.1 + y2.1, (frobenius K p)^[y2.1] x.2 + (frobenius K p)^[x.1] y2.2) :=
  match y1, y2, H with
  | _, _, R.intro n y =>
    Quot.sound <| by
      rw [← iterate_succ_apply, iterate_succ_apply', iterate_succ_apply', ← frobenius_add]
      apply R.intro

instance instAdd : Add (PerfectClosure K p) :=
  ⟨Quot.lift
      (fun x : ℕ × K =>
        Quot.lift
          (fun y : ℕ × K =>
            mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 + (frobenius K p)^[x.1] y.2))
          (add_aux_right K p x))
      fun x1 x2 (H : R K p x1 x2) =>
      funext fun e => Quot.inductionOn e fun y => add_aux_left K p x1 x2 y H⟩

@[simp]
theorem mk_add_mk (x y : ℕ × K) :
    mk K p x + mk K p y =
      mk K p (x.1 + y.1, (frobenius K p)^[y.1] x.2 + (frobenius K p)^[x.1] y.2) :=
  rfl

instance instNeg : Neg (PerfectClosure K p) :=
  ⟨Quot.lift (fun x : ℕ × K => mk K p (x.1, -x.2)) fun x y (H : R K p x y) =>
      match x, y, H with
      | _, _, R.intro n x => Quot.sound <| by rw [← frobenius_neg]; apply R.intro⟩

@[simp]
theorem neg_mk (x : ℕ × K) : -mk K p x = mk K p (x.1, -x.2) :=
  rfl

instance instZero : Zero (PerfectClosure K p) :=
  ⟨mk K p (0, 0)⟩

theorem zero_def : (0 : PerfectClosure K p) = mk K p (0, 0) :=
  rfl

/-- Prior to https://github.com/leanprover-community/mathlib4/pull/15862, this lemma was called `mk_zero_zero`.
See `mk_zero_right` for the lemma used to be called `mk_zero`. -/
@[simp]
theorem mk_zero : mk K p 0 = 0 :=
  rfl

@[simp]
theorem mk_zero_right (n : ℕ) : mk K p (n, 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    apply (Quot.sound _).symm
    have := R.intro (p := p) n (0 : K)
    rwa [frobenius_zero K p] at this

theorem R.sound (m n : ℕ) (x y : K) (H : (frobenius K p)^[m] x = y) :
    mk K p (n, x) = mk K p (m + n, y) := by
  subst H
  induction m with
  | zero => simp only [zero_add, iterate_zero_apply]
  | succ m ih =>
    rw [ih, Nat.succ_add, iterate_succ']
    apply Quot.sound
    apply R.intro

instance instAddCommGroup : AddCommGroup (PerfectClosure K p) :=
  { (inferInstance : Add (PerfectClosure K p)),
    (inferInstance : Neg (PerfectClosure K p)) with
    add_assoc := fun e f g =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
          Quot.inductionOn g fun ⟨s, z⟩ => by
            apply congr_arg (Quot.mk _)
            simp only [iterate_map_add, ← iterate_add_apply, add_assoc, add_comm s _]
    zero_add := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
        congr_arg (Quot.mk _) <| by
          simp only [iterate_map_zero, iterate_zero_apply, zero_add]
    add_zero := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ =>
        congr_arg (Quot.mk _) <| by
          simp only [iterate_map_zero, iterate_zero_apply, add_zero]
    sub_eq_add_neg := fun _ _ => rfl
    neg_add_cancel := fun e =>
      Quot.inductionOn e fun ⟨n, x⟩ => by
        simp only [quot_mk_eq_mk, neg_mk, mk_add_mk, iterate_map_neg, neg_add_cancel, mk_zero_right]
    add_comm := fun e f =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ => congr_arg (Quot.mk _) <| by simp only [add_comm]
    nsmul := nsmulRec
    zsmul := zsmulRec }

instance instCommRing : CommRing (PerfectClosure K p) :=
  { instAddCommGroup K p, AddMonoidWithOne.unary,
    (inferInstance : CommMonoid (PerfectClosure K p)) with
    zero_mul := fun a => by
      refine Quot.inductionOn a fun ⟨m, x⟩ => ?_
      rw [zero_def, quot_mk_eq_mk, mk_mul_mk]
      simp only [zero_add, iterate_zero, id_eq, iterate_map_zero, zero_mul, mk_zero_right]
    mul_zero := fun a => by
      refine Quot.inductionOn a fun ⟨m, x⟩ => ?_
      rw [zero_def, quot_mk_eq_mk, mk_mul_mk]
      simp only [iterate_zero, id_eq, iterate_map_zero, mul_zero, mk_zero_right]
    left_distrib := fun e f g =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
          Quot.inductionOn g fun ⟨s, z⟩ => by
            simp only [quot_mk_eq_mk, mk_add_mk, mk_mul_mk, add_comm, add_left_comm]
            apply R.sound
            simp only [iterate_map_mul, iterate_map_add, ← iterate_add_apply,
              mul_add, add_comm, add_left_comm]
    right_distrib := fun e f g =>
      Quot.inductionOn e fun ⟨m, x⟩ =>
        Quot.inductionOn f fun ⟨n, y⟩ =>
          Quot.inductionOn g fun ⟨s, z⟩ => by
            simp only [quot_mk_eq_mk, mk_add_mk, mk_mul_mk, add_assoc, add_comm _ s,
              add_left_comm _ s]
            apply R.sound
            simp only [iterate_map_mul, iterate_map_add, ← iterate_add_apply,
              add_mul, add_comm, add_left_comm] }

theorem mk_eq_iff (x y : ℕ × K) :
    mk K p x = mk K p y ↔ ∃ z, (frobenius K p)^[y.1 + z] x.2 = (frobenius K p)^[x.1 + z] y.2 := by
  constructor
  · intro H
    replace H := Quot.eqvGen_exact H
    induction H with
    | rel x y H => obtain ⟨n, x⟩ := H; exact ⟨0, rfl⟩
    | refl H => exact ⟨0, rfl⟩
    | symm x y H ih => obtain ⟨w, ih⟩ := ih; exact ⟨w, ih.symm⟩
    | trans x y z H1 H2 ih1 ih2 =>
      obtain ⟨z1, ih1⟩ := ih1
      obtain ⟨z2, ih2⟩ := ih2
      exists z2 + (y.1 + z1)
      rw [← add_assoc, iterate_add_apply, ih1]
      rw [← iterate_add_apply, add_comm, iterate_add_apply, ih2]
      rw [← iterate_add_apply]
      simp only [add_comm, add_left_comm]
  intro H
  obtain ⟨m, x⟩ := x
  obtain ⟨n, y⟩ := y
  obtain ⟨z, H⟩ := H; dsimp only at H
  rw [R.sound K p (n + z) m x _ rfl, R.sound K p (m + z) n y _ rfl, H]
  rw [add_assoc, add_comm, add_comm z]

@[simp]
theorem mk_pow (x : ℕ × K) (n : ℕ) : mk K p x ^ n = mk K p (x.1, x.2 ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, one_def, mk_eq_iff]
    exact ⟨0, by simp_rw [← coe_iterateFrobenius, map_one]⟩
  | succ n ih =>
    rw [pow_succ, pow_succ, ih, mk_mul_mk, mk_eq_iff]
    exact ⟨0, by simp_rw [iterate_frobenius, add_zero, mul_pow, ← pow_mul,
      ← pow_add, mul_assoc, ← pow_add]⟩

theorem natCast (n x : ℕ) : (x : PerfectClosure K p) = mk K p (n, x) := by
  induction n with
  | zero =>
    induction x with
    | zero => simp
    | succ x ih => simp [Nat.cast_succ, ih, one_def]
  | succ n ih =>
    rw [ih]; apply Quot.sound
    suffices R K p (n, (x : K)) (Nat.succ n, frobenius K p (x : K)) by
      rwa [frobenius_natCast K p x] at this
    apply R.intro

theorem intCast (x : ℤ) : (x : PerfectClosure K p) = mk K p (0, x) := by
  cases x <;> simp [natCast K p 0]

theorem natCast_eq_iff (x y : ℕ) : (x : PerfectClosure K p) = y ↔ (x : K) = y := by
  constructor <;> intro H
  · rw [natCast K p 0, natCast K p 0, mk_eq_iff] at H
    obtain ⟨z, H⟩ := H
    simpa only [zero_add, iterate_fixed (frobenius_natCast K p _)] using H
  rw [natCast K p 0, natCast K p 0, H]

instance instCharP : CharP (PerfectClosure K p) p := by
  constructor; intro x; rw [← CharP.cast_eq_zero_iff K]
  rw [← Nat.cast_zero, natCast_eq_iff, Nat.cast_zero]

theorem frobenius_mk (x : ℕ × K) :
    (frobenius (PerfectClosure K p) p : PerfectClosure K p → PerfectClosure K p) (mk K p x) =
      mk _ _ (x.1, x.2 ^ p) := by
  simp only [frobenius_def]
  exact mk_pow K p x p

/-- Embedding of `K` into `PerfectClosure K p` -/
def of : K →+* PerfectClosure K p where
  toFun x := mk _ _ (0, x)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem of_apply (x : K) : of K p x = mk _ _ (0, x) :=
  rfl

instance instReduced : IsReduced (PerfectClosure K p) where
  eq_zero x := induction_on x fun x ⟨n, h⟩ ↦ by
    replace h : mk K p x ^ p ^ n = 0 := by
      rw [← Nat.sub_add_cancel ((n.lt_pow_self (Fact.out : p.Prime).one_lt).le),
        pow_add, h, mul_zero]
    simp only [zero_def, mk_pow, mk_eq_iff, zero_add, ← coe_iterateFrobenius, map_zero] at h ⊢
    obtain ⟨m, h⟩ := h
    exact ⟨n + m, by simpa only [iterateFrobenius_def, pow_add, pow_mul] using h⟩

instance instPerfectRing : PerfectRing (PerfectClosure K p) p where
  bijective_frobenius := by
    let f : PerfectClosure K p → PerfectClosure K p := fun e ↦
      liftOn e (fun x => mk K p (x.1 + 1, x.2)) fun x y H =>
      match x, y, H with
      | _, _, R.intro n x => Quot.sound (R.intro _ _)
    refine bijective_iff_has_inverse.mpr ⟨f, fun e ↦ induction_on e fun ⟨n, x⟩ ↦ ?_,
      fun e ↦ induction_on e fun ⟨n, x⟩ ↦ ?_⟩ <;>
      simp only [f, liftOn_mk, frobenius_mk, mk_succ_pow]

@[simp]
theorem iterate_frobenius_mk (n : ℕ) (x : K) :
    (frobenius (PerfectClosure K p) p)^[n] (mk K p ⟨n, x⟩) = of K p x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, ← ih, frobenius_mk, mk_succ_pow]

/-- Given a ring `K` of characteristic `p` and a perfect ring `L` of the same characteristic,
any homomorphism `K →+* L` can be lifted to `PerfectClosure K p`. -/
noncomputable def lift (L : Type v) [CommSemiring L] [CharP L p] [PerfectRing L p] :
    (K →+* L) ≃ (PerfectClosure K p →+* L) where
  toFun f :=
    { toFun := by
        refine fun e => liftOn e (fun x => (frobeniusEquiv L p).symm^[x.1] (f x.2)) ?_
        rintro - - ⟨n, x⟩
        simp [f.map_frobenius]
      map_one' := f.map_one
      map_zero' := f.map_zero
      map_mul' := by
        rintro ⟨n, x⟩ ⟨m, y⟩
        simp only [quot_mk_eq_mk, liftOn_mk, f.map_iterate_frobenius, mk_mul_mk, map_mul,
          iterate_map_mul]
        have := LeftInverse.iterate (frobeniusEquiv_symm_apply_frobenius L p)
        rw [iterate_add_apply, this _ _, add_comm, iterate_add_apply, this _ _]
      map_add' := by
        rintro ⟨n, x⟩ ⟨m, y⟩
        simp only [quot_mk_eq_mk, liftOn_mk, f.map_iterate_frobenius, mk_add_mk, map_add,
          iterate_map_add]
        have := LeftInverse.iterate (frobeniusEquiv_symm_apply_frobenius L p)
        rw [iterate_add_apply, this _ _, add_comm n, iterate_add_apply, this _ _] }
  invFun f := f.comp (of K p)
  right_inv f := by
    ext ⟨n, x⟩
    simp only [quot_mk_eq_mk, RingHom.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      liftOn_mk]
    apply (injective_frobenius L p).iterate n
    rw [← f.map_iterate_frobenius, iterate_frobenius_mk,
      RightInverse.iterate (frobenius_apply_frobeniusEquiv_symm L p) n]

end Ring

theorem eq_iff [CommRing K] [IsReduced K] (p : ℕ) [Fact p.Prime] [CharP K p] (x y : ℕ × K) :
    mk K p x = mk K p y ↔ (frobenius K p)^[y.1] x.2 = (frobenius K p)^[x.1] y.2 :=
  (mk_eq_iff K p x y).trans
    ⟨fun ⟨z, H⟩ => (frobenius_inj K p).iterate z <| by simpa only [add_comm, iterate_add] using H,
      fun H => ⟨0, H⟩⟩

instance [CommRing K] [IsReduced K] (p : ℕ) [Fact p.Prime] [CharP K p] [Nontrivial K] :
    Nontrivial (PerfectClosure K p) where
  exists_pair_ne := ⟨0, 1, fun H => zero_ne_one ((eq_iff _ _ _ _).1 H)⟩

section Field

variable [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

instance instInv : Inv (PerfectClosure K p) :=
  ⟨Quot.lift (fun x : ℕ × K => Quot.mk (R K p) (x.1, x.2⁻¹)) fun x y (H : R K p x y) =>
      match x, y, H with
      | _, _, R.intro n x =>
        Quot.sound <| by
          simp only [frobenius_def]
          rw [← inv_pow]
          apply R.intro⟩

@[simp]
theorem mk_inv (x : ℕ × K) : (mk K p x)⁻¹ = mk K p (x.1, x.2⁻¹) :=
  rfl

instance instDivisionRing : DivisionRing (PerfectClosure K p) where
  mul_inv_cancel e := induction_on e fun ⟨m, x⟩ H ↦ by
    have := mt (eq_iff _ _ _ _).2 H
    rw [mk_inv, mk_mul_mk]
    refine (eq_iff K p _ _).2 ?_
    simp only [iterate_map_one, iterate_map_zero, iterate_zero_apply, ← iterate_map_mul] at this ⊢
    rw [mul_inv_cancel₀ this, iterate_map_one]
  inv_zero := congr_arg (Quot.mk (R K p)) (by rw [inv_zero])
  nnqsmul := _
  nnqsmul_def := fun _ _  => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

instance instField : Field (PerfectClosure K p) :=
  { (inferInstance : DivisionRing (PerfectClosure K p)),
    (inferInstance : CommRing (PerfectClosure K p)) with }

instance instPerfectField : PerfectField (PerfectClosure K p) := PerfectRing.toPerfectField _ p

end Field

end PerfectClosure
