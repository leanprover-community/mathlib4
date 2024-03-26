import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring.RingNF


@[ext]
structure F4 where
  x0 : ZMod 2
  x1 : ZMod 2

namespace F4
section
instance : Zero F4 := ⟨0,0⟩

instance : Add F4 := ⟨fun a b ↦ ⟨a.x0 + b.x0,a.x1 + b.x1⟩⟩

instance : Neg F4 := ⟨fun a ↦ a⟩ -- elements are mod 2, and -1=1, so it's id.

instance : One F4 := ⟨1,1⟩

instance : Mul F4 := ⟨fun a b ↦
  ⟨(a.x0 * b.x0) + (a.x0 + a.x1) * (b.x0 + b.x1),
  (a.x1 * b.x1) + (a.x0 + a.x1) * (b.x0 + b.x1)⟩
⟩
instance : Inv F4 := ⟨fun a ↦ ⟨a.x1,a.x0⟩⟩
private theorem elem_def (a : F4) : ∃x y : ZMod 2, a = ⟨x, y⟩ := by
  use a.x0
  use a.x1


private theorem zero_def' : (0 : F4) = ⟨0,0⟩ :=
  rfl

private theorem add_def (a b :F4) : a + b = ⟨a.x0 + b.x0, a.x1 + b.x1⟩ :=
  rfl

private theorem neg_def (a:F4) : -a = a := rfl

private theorem one_def' : (1 : F4) = ⟨1,1⟩ := rfl

private theorem mul_def (a b : F4) : a * b = ⟨(a.x0 * b.x0) + (a.x0 + a.x1) * (b.x0 + b.x1),
  (a.x1 * b.x1) + (a.x0 + a.x1) * (b.x0 + b.x1)⟩ := rfl

private theorem inv_def (a : F4) : a⁻¹ = ⟨a.x1,a.x0⟩ := rfl

private def h1: (4:ZMod 2) = (0:ZMod 2) := rfl

private def h2: (2:ZMod 2) = (0:ZMod 2) := rfl

private def h3: (3:ZMod 2) = (1:ZMod 2) := rfl

instance : AddCommGroup F4 where
  add_assoc := by simp_rw [add_def,add_assoc,forall_const]
  zero_add := by simp_rw [zero_def',add_def,zero_add,forall_const]
  add_zero := by simp_rw [zero_def',add_def,add_zero,forall_const]
  add_comm := by simp_rw [add_def,add_comm,forall_const]
  add_left_neg := by simp_rw [neg_def,add_def,zero_def']; ring_nf; simp_rw [h2,mul_zero,forall_const]

instance : CommRing F4 where
  add_left_neg := by simp_rw [neg_def,add_def,zero_def']; ring_nf; simp_rw [h2,mul_zero,forall_const]
  left_distrib := by simp_rw [mul_def,add_def]; ring_nf; simp only [forall_const]
  right_distrib := by simp_rw [mul_def,add_def]; ring_nf; simp only [forall_const]
  zero_mul := by simp_rw [mul_def,zero_def',zero_mul,zero_add,zero_mul,forall_const]
  mul_zero := by simp_rw [mul_def,zero_def',mul_zero,zero_add,mul_zero,forall_const]
  mul_assoc := fun a b c => by simp_rw [mul_def]; ext <;> ring_nf <;> rw [h1,h2]
  one_mul := by simp_rw [mul_def,one_def']; ring_nf; simp_rw [h3,h2]; ring_nf; simp_rw [forall_const]
  mul_one := by simp_rw [mul_def,one_def']; ring_nf; simp_rw [h3,h2]; ring_nf; simp_rw [forall_const]
  mul_comm := by simp_rw [mul_def]; ring_nf; simp_rw [forall_const]

instance : Field F4 where
  exists_pair_ne := ⟨0,1,
    by simp_rw [ne_eq,F4.ext_iff,zero_def',one_def',and_self];exact Fin.zero_ne_one⟩
  mul_inv_cancel := by
    simp_rw [mul_def,inv_def,zero_def',one_def',ne_eq,F4.ext_iff]
    intro ⟨a0,a1⟩ ha
    ring_nf
    simp only [not_and] at ha
    suffices hsemifinal : a0 * a1 * 3 + a0 ^ 2 + a1 ^ 2 = 1 by
      apply And.intro hsemifinal hsemifinal
    match a0 with
      | 1 => simp only [one_mul, one_pow,h3,ZMod.pow_card]
             ring_nf
             rw [h2]
             ring_nf
      | 0 => match a1 with
              | 1 => simp only [mul_one,zero_mul,zero_add,one_pow]
                     ring_nf
              | 0 => contradiction
  inv_zero := rfl

instance: DecidableEq F4 := fun ⟨a1,a2⟩ => fun
    ⟨b1,b2⟩ =>
      if h1: a1 = b1
      then
        if h2: a2 = b2 then
          isTrue (by
            ext
            . exact h1
            . exact h2)
        else
          isFalse (by
            by_contra hab
            obtain ⟨h1',h2'⟩ := hab
            trivial)
      else
        isFalse (by
        by_contra hab
        obtain ⟨h1',h2'⟩ := hab
        trivial)
end

notation "ω" => (⟨1,0⟩:F4)

-- @[simp]
-- lemma omega_def : ⟨1,0⟩ = ω := rfl

-- @[simp]
-- lemma omega_inverse : ⟨0,1⟩ = ω⁻¹ := rfl

-- @[simp]
-- lemma one_def : ⟨1,1⟩ = (1:F4) := rfl

-- @[simp]
-- lemma zero_def : ⟨0,0⟩ = (0:F4) := rfl


instance : Repr F4 where
  reprPrec := fun
    | .mk x0 x1 => Function.const ℕ (
      if x0 = 0 ∧ x1 = 0 then
        "0"
      else if x0 = 1 ∧ x1 = 0 then
        "ω"
      else if x0 = 0 ∧ x1 = 1 then
        "ω⁻¹"
      else
        "1"
    )

@[simp]
lemma two_eq_zero : (2:F4) = 0 := rfl

lemma cases (x:F4) : x = 0 ∨ x = 1 ∨ x = ω ∨ x = ω⁻¹ := by
  obtain ⟨x1,x2⟩ := x
  obtain ⟨n1,hn1⟩ := x1
  obtain ⟨n2,hn2⟩ := x2
  rcases n1
  . simp only [Nat.zero_eq, Fin.zero_eta, mk.injEq, zero_ne_one, false_and, false_or]
    rcases n2
    . left
      simp only [Nat.zero_eq, Fin.zero_eta]
      rw [zero_def']
    rename_i n2
    rcases n2
    . simp only [Nat.zero_eq, Nat.reduceSucc, Fin.mk_one]
      right
      right
      rw [inv_def]
    contradiction
  rename_i n1
  rcases n1
  . simp only [Nat.zero_eq, Nat.reduceSucc, Fin.mk_one, mk.injEq, true_and]
    right
    rcases n2
    . simp only [Nat.zero_eq, Fin.zero_eta, true_or, or_true]
    rename_i n2
    rcases n2
    . simp only [Nat.zero_eq, Nat.reduceSucc, Fin.mk_one, one_ne_zero, false_or]
      left
      rw [one_def']
    contradiction
  contradiction


instance : Fintype F4 where
  elems := {
    val := {0,1,ω,ω⁻¹}
    nodup := by
      simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons, zero_ne_one,
        Multiset.mem_singleton, zero_eq_inv, or_self, false_or, one_eq_inv,
        Multiset.nodup_singleton, and_true]
      decide
  }
  complete := fun f => by
    obtain h|h|h|h := f.cases <;> rw [h]
    . simp only [Multiset.insert_eq_cons, Finset.mk_cons, Finset.cons_eq_insert, Finset.mem_insert,
        zero_ne_one, Finset.mem_mk, Multiset.mem_singleton, zero_eq_inv, or_self, false_or, true_or]
    . simp only [Multiset.insert_eq_cons, Finset.mk_cons, Finset.cons_eq_insert, Finset.mem_insert,
      one_ne_zero, Finset.mem_mk, Multiset.mem_singleton, one_eq_inv, true_or, or_true]
    . simp only [Multiset.insert_eq_cons, Finset.mk_cons, Finset.cons_eq_insert, Finset.mem_insert,
      Finset.mem_mk, Multiset.mem_singleton, true_or, or_true]
    . simp only [Multiset.insert_eq_cons, Finset.mk_cons, Finset.cons_eq_insert, Finset.mem_insert,
      inv_eq_zero, inv_eq_one, Finset.mem_mk, Multiset.mem_singleton, or_true]

def naturalEquiv : Fin 4 ≃ F4 where
  toFun := ![0,1,ω,ω⁻¹]
  invFun := fun x => if x = 0 then 0 else if x = 1 then 1 else if x = ω then 2 else 3
  left_inv := fun ⟨i,_⟩ =>
    by
    simp only
    rcases i
    . simp only [Nat.zero_eq, Fin.zero_eta, Matrix.cons_val_zero, ↓reduceIte]
    rename_i i
    rcases i
    . decide
    rename_i i
    rcases i
    . decide
    rename_i i
    rcases i
    . decide
    contradiction
  right_inv :=fun y => by obtain h|h|h|h := y.cases <;> rw [h] <;> decide

@[simp]
lemma square_eq_inv (x:F4): x^2 = x⁻¹ := by
  obtain h|h|h|h := x.cases <;> rw [h] <;> rfl

@[simp]
lemma neg_eq_self (x:F4) : -x = x := by
  obtain h|h|h|h := x.cases <;> rw [h] <;> rfl

@[simp]
lemma add_self (x : F4) : x + x = 0 := by
  obtain h|h|h|h := x.cases <;> rw [h] <;> rfl

lemma omega_ne_zero : ω ≠ 0 := by
  rw [zero_def']
  simp only [ne_eq, mk.injEq, one_ne_zero, and_true, not_false_eq_true]

lemma omega_inv_ne_zero : ω⁻¹ ≠ 0 := by
  rw [zero_def',inv_def]
  simp only [ne_eq, mk.injEq, one_ne_zero, and_false, not_false_eq_true]

@[simp]
lemma omega_add_omega_inv : ω + ω⁻¹ = 1 := rfl

def embed_Z2 : ZMod 2 →+* F4 where
  toFun := fun x => ⟨x,x⟩
  map_one' := rfl
  map_mul' := fun x y => by
    simp only
    rw [mul_def]
    simp only [CharTwo.add_self_eq_zero, mul_zero, add_zero]
  map_zero' := rfl
  map_add' := fun x y => by
    simp only
    rw [add_def]


lemma embed_Z2.inj : (⇑embed_Z2).Injective := fun x y h => by
  simp_rw [embed_Z2] at h
  simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, mk.injEq, and_self] at h
  exact h

instance : Algebra (ZMod 2) F4 := {
  embed_Z2 with
  smul := fun b z => embed_Z2 b * z
  commutes' := fun r x => by exact mul_comm (embed_Z2 r) x
  smul_def' := fun r x => rfl
}
