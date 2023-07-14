import Mathlib
--.Algebra.QuadraticDiscriminant
-- import Mathlib.Data.Int


namespace PellAlg

/-- An (a,b,c) triple, used for defining a quadratic.-/
structure Triple : Type where
  a : ℤ
  b : ℤ
  c : ℤ
deriving Repr

/-- The floor of the positive root of the triple. -/
def fpr (t : Triple) : ℤ := (-t.b + (discrim t.a t.b t.c).sqrt) / (2 * t.a)

/-- The quadratic form defined by the triple, and its fpr-translation. -/
def qf (t : Triple) (x : ℝ) := t.a * x * x + t.b * x + t.c

def qf_fpr_translate (t : Triple) (w : ℝ) := qf t (fpr t + w)

lemma root_iff_translate_root (t : Triple) (z : ℝ) :
  qf t z = 0 ↔ qf_fpr_translate t (z - fpr t) = 0 := by rw [qf_fpr_translate, add_sub_cancel'_right]

/-- The Brouckner transform. -/
def brouckner (t : Triple) : Triple :=
  { a := -(t.a * (fpr t) * (fpr t) + t.b * (fpr t) + t.c),
    b := -(2 * t.a * (fpr t) + t.b),
    c := -t.a }

/-- Iterating the Brouckner transform on triples until a becomes 1. -/
def iterate_brouckner (t : Triple) (l : List (Triple × ℤ)) : (n : ℕ) → List (Triple × ℤ)
  | 0     => l
  | n + 1 =>
    let t := brouckner t
    if t.a = 1 then
      (t, fpr t) :: l
    else
      iterate_brouckner t ((t, fpr t) :: l) n

-- Example
#eval iterate_brouckner ⟨1,0, (-19)⟩ [] 20

/-- Swap a and c in a triple. -/
def swapac (t : Triple) : Triple := {a := t.c, b := t.b, c := t.a}

/-- Swapping twice gives the original triple. -/
lemma swapac_twice (t : Triple) : t = swapac (swapac t) := by simp [swapac]

/-- The inverse of a root is a root of the quadratic with a and c swapped. -/
lemma swapac_root (t: Triple) (z : ℝ) (hz : z ≠ 0) :
  qf t z = 0 ↔ qf (swapac t) (1 / z) = 0 := by
    simp_rw [qf, swapac]
    field_simp
    have : t.c * z + t.b * (z * z) + t.a * (z * z * z) = (qf t z) * z := by
      rw [qf]; ring
    rw [this, qf]
    simp [mul_ne_zero_iff, hz]

/-- The swapped Brouckner transform is the negation of the fpr-translation. -/
lemma neg_qf_fpr_translate_eq_brouckner (t : Triple) (w : ℝ) :
  -qf_fpr_translate t w = qf (swapac (brouckner t)) w := by
  rw [swapac, brouckner, qf_fpr_translate, qf, qf]
  simp only [Int.cast_add, Int.cast_neg, Int.cast_mul]
  ring

/-- Relates root of original form to root of Brouckner transform. -/
theorem brouckner_root (t: Triple) (z : ℝ) (hz : z ≠ fpr t) :
  qf t z = 0 ↔ qf (brouckner t) (1 / (z - fpr t)) = 0 := by
  rw [swapac_twice (brouckner t), ← swapac_root _ _ (sub_ne_zero.mpr hz),
  ←neg_qf_fpr_translate_eq_brouckner, neg_eq_zero,←root_iff_translate_root]

/- Harald wrote:
First, I will show: if a z² + b z + c = 0 has
a negative root z_- and
a positive root z_+>1,
and a>0, c<0, then
a' z² + b' z + c' has a root in (-1,0) and a root>1, and a'>0, and c'<0.
That c'<0 is trivial (because c' = - a). Since a>0, we see that a z² + b z + c is <0 for z in (z_-,z_+); since m is both < z_+ and >= 1 > z_-, we see that a m² + b m + c < 0, and so a'>0.-/

structure Roots (t : Triple) : Type where
  x1 : ℝ
  x2 : ℝ
  h1 : qf t x1 = 0
  h2 : qf t x2 = 0

/-- Computes the roots of `brouckner t` given the roots of `t`, provided that `t` has no integer
roots. -/

noncomputable def brouckner_roots (t : Triple) (r : Roots t)
(hne1 : r.x1 ≠ fpr t) (hne2 : r.x2 ≠ fpr t) : Roots (brouckner t) :=
  {x1 := 1 / (r.x2 - fpr t),
   x2 := 1 / (r.x1 - fpr t),
   h1 := ((brouckner_root t r.x2) hne2).mp r.h2,
   h2 := ((brouckner_root t r.x1) hne1).mp r.h1}

lemma discrim_ge_zero_of_root (ha : a ≠ 0) (h : ∃x, a * x * x + b * x + c = 0) [NeZero (2 : K)] :
  0 ≤ discrim a b c := by
  obtain ⟨x, hx⟩ := h
  rw [quadratic_eq_zero_iff_discrim_eq_sq] at hx
  rw [hx]
  positivity
  assumption

example (a b c : ℤ) (h : a + b = 0) : a = -b := by exact (add_eq_zero_iff_eq_neg.mp h)
lemma lem1 (T : Triple) (z : ℝ) (hz1 : qf T z = 0) (hz2 : 1 < z) (ha : T.a > 0) (hc : T.c < 0) :
  0 < z * (T.a * z + T.b) := by
  -- have h : 0 = 0 * z := by exact?
-- apply mul_lt_mul_of_pos_left

lemma lem2 (T : Triple) (z : ℝ) (hz1 : qf T z = 0) (hz2 : 1 < z) (ha : T.a > 0) (hc : T.c < 0)
  (t : ℝ) (ht1 : t < z) (ht2 : 1 ≤ t) : (qf T t < 0) := by
  rw [←hz1, qf, qf]
  simp only [add_lt_add_iff_right]
  rw [← add_mul, ← add_mul]
  apply mul_lt_mul
  simp only [add_lt_add_iff_right]
  apply mul_lt_mul'
  trivial
  assumption
  exact le_trans zero_le_one ht2
  norm_cast
  exact ht1.le
  exact lt_of_lt_of_le zero_lt_one ht2
  apply le_of_lt
  apply lem1 T z hz1 hz2 ha hc

lemma discrim_bound (T: Triple) (z : ℝ) (hz : qf T z = 0) :
  (discrim T.a T.b T.c ≤ (2 * T.a * z + T.b) ^ 2) := by
  rw [Real.rpow_two, add_sq, discrim]
  ring_nf
  simp only [Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.int_cast_ofNat, tsub_le_iff_right]
  rw [add_assoc,add_comm, add_assoc]
  simp only [le_add_iff_nonneg_right]
  apply le_of_eq
  calc
    0 = 4 * T.a * qf T z := by rw [hz, mul_zero]
    _ = 4 * T.a * (T.a * z * z + T.b * z + T.c) := by rw [qf]
    _ = ↑T.a * ↑T.c * 4 + (↑T.a * z * ↑T.b * 4 + ↑T.a ^ 2 * z ^ 2 * 4) := by
      rw[Real.rpow_two, Real.rpow_two]; ring_nf
  simp only [Real.rpow_two]

lemma le_of_le_sq (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (H : x * x ≤ y * y) : x ≤ y :=
  (mul_self_le_mul_self_iff hx hy).mpr H

lemma square_sqrt_le_self_of_nonneg (x : ℤ) (hx : 0 ≤ x) : x.sqrt * x.sqrt ≤ x := by
  rw [Int.sqrt]
  obtain ⟨n, hn⟩ := Int.NonNeg.elim hx
  simp only [sub_zero] at hn
  rw [hn]
  simp only [Int.toNat_ofNat]
  norm_cast
  exact Nat.sqrt_le n


lemma fpr_le_pos_root (T : Triple) (r : Roots T) (h : r.x1 ≤ r.x2) (ha : 0 < T.a) :
  (fpr T) ≤ r.x2 := by
  have key : (discrim T.a T.b T.c).sqrt ≤ 2 * T.a * r.x2 + T.b
  apply le_of_le_sq
  norm_cast; apply Int.sqrt_nonneg
  sorry
  norm_num
  rw [←Int.cast_mul]
  apply le_trans
  · apply ((@Int.cast_le ℝ _ _ _ _).mpr (square_sqrt_le_self_of_nonneg (discrim T.a T.b T.c) ?_))
    sorry
  · rw [← sq]
    have := discrim_bound T r.x2 ?_
    rw [← Real.rpow_two]
    exact this
    sorry
  rw [fpr]

lemma brouckner_root_signs (t : Triple) (r : Roots t) (h1 : r.x1 < 0) (h2 : r.x2 > 1)
  (h3 : 0 < t.a) (h4 : t.c < 0)  : 0 < (brouckner t).a := by
  have ne1 : r.x1 ≠ fpr t := by sorry
  have ne2 : r.x2 ≠ fpr t := by sorry
  have br : Roots (brouckner t) := brouckner_roots t r ne1 ne2;


    done

end PellAlg

/- Floris notes from 12 July
fun (a,b,c,D) ↦
conditions: sign(a) = - sign(c), a ≠ 0, D = b^2 - 4ac

m = ⌊ (-b + √D) / (2a) ⌋


return (-(am^2+bm+c),-(2am+b),-a,m)
Pell:
x^2 - Ny^2 = 1
* equivalently, elt in ℤ√N with norm 1
* find fundamental solution η
* really fundamental solution: also generated everything with norm = ±1
* all solutions are in the form ±η^k

example: N = 19 -> 170^2 - 19*39^2 = 1

want to find x^2-19y^2=1
x>y
suppose we know `m = ⌊x / y⌋`
Let (x', y') := (y, x - my) (cf Euclidean algorithm)
(x,y) := (y'+mx',x')
If ax^2+bxy+cy^2=1
then

all steps but the first one are reversible
Book :
* A. Weil: number theory an approach through history from hammurapi to legendre

-/

/-
1 compute x and y and that they are a solution
2 show that a > 0 and c < 0 in intermdiate steps
3-ε: claim: if brouckner a b c D = (a',b',c',m) then
    brouckner (-c) (-b) (-a) D = (a,b,c,?)
3 from 3-ε show reversibility of all steps but first one
4 show that there are finitely many options for a,b,c
  with b^2-4ac=D and a>0,c<0 (at most √D * (√D)ᵉ for some small `e>0`)
5 from 2,3,4 show termination
6 the x,y we get in step 1 are a *fundamental* solution
  to do: show that brouckner is monotone w.r.t. some order
-/

-- #reduce (54 : ℤ).sqrt
-- example : (50 : ℕ).sqrt = 7 := by norm_num
-- example : (123456789 : ℕ).sqrt = 11111 := by norm_num
-- example : (2340276615670 ^ 2 : ℕ).sqrt = 2340276615670 := by
--   norm_num
