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

private theorem zero_def : (0 : F4) = ⟨0,0⟩ :=
  rfl

private theorem add_def (a b :F4) : a + b = ⟨a.x0 + b.x0, a.x1 + b.x1⟩ :=
  rfl

private theorem neg_def (a:F4) : -a = a := rfl

private theorem one_def : (1 : F4) = ⟨1,1⟩ := rfl

private theorem mul_def (a b : F4) : a * b = ⟨(a.x0 * b.x0) + (a.x0 + a.x1) * (b.x0 + b.x1),
  (a.x1 * b.x1) + (a.x0 + a.x1) * (b.x0 + b.x1)⟩ := rfl

private theorem inv_def (a : F4) : a⁻¹ = ⟨a.x1,a.x0⟩ := rfl

private def h1: (4:ZMod 2) = (0:ZMod 2) := rfl

private def h2: (2:ZMod 2) = (0:ZMod 2) := rfl

private def h3: (3:ZMod 2) = (1:ZMod 2) := rfl

instance : AddCommGroup F4 where
  add_assoc := by simp_rw [add_def,add_assoc,forall_const]
  zero_add := by simp_rw [zero_def,add_def,zero_add,forall_const]
  add_zero := by simp_rw [zero_def,add_def,add_zero,forall_const]
  add_comm := by simp_rw [add_def,add_comm,forall_const]
  add_left_neg := by simp_rw [neg_def,add_def,zero_def]; ring_nf; simp_rw [h2,mul_zero,forall_const]

instance : CommRing F4 where
  add_left_neg := by simp_rw [neg_def,add_def,zero_def]; ring_nf; simp_rw [h2,mul_zero,forall_const]
  left_distrib := by simp_rw [mul_def,add_def]; ring_nf; simp only [forall_const]
  right_distrib := by simp_rw [mul_def,add_def]; ring_nf; simp only [forall_const]
  zero_mul := by simp_rw [mul_def,zero_def,zero_mul,zero_add,zero_mul,forall_const]
  mul_zero := by simp_rw [mul_def,zero_def,mul_zero,zero_add,mul_zero,forall_const]
  mul_assoc := fun a b c => by simp_rw [mul_def]; ext <;> ring_nf <;> rw [h1,h2]
  one_mul := by simp_rw [mul_def,one_def]; ring_nf; simp_rw [h3,h2]; ring_nf; simp_rw [forall_const]
  mul_one := by simp_rw [mul_def,one_def]; ring_nf; simp_rw [h3,h2]; ring_nf; simp_rw [forall_const]
  mul_comm := by simp_rw [mul_def]; ring_nf; simp_rw [forall_const]

instance : Field F4 where
  exists_pair_ne := ⟨0,1,
    by simp_rw [ne_eq,F4.ext_iff,zero_def,one_def,and_self];exact Fin.zero_ne_one⟩
  mul_inv_cancel := by
    simp_rw [mul_def,inv_def,zero_def,one_def,ne_eq,F4.ext_iff]
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

private def temp : F4 := ⟨1,0⟩
def ω : F4 := temp -- no creating your own values
end

@[simp]
lemma omega_square_omega_inverse : ω^2=ω⁻¹ := rfl

@[simp]
lemma omega_cube_one : ω^3 = 1 := rfl

@[simp]
lemma omega_add_omega_inverse : ω + ω⁻¹ = 1 := rfl

@[simp]
lemma omega_add_one : ω + 1 = ω⁻¹ := rfl

@[simp]
lemma omega_add_omega : ω + ω = 0 := rfl
