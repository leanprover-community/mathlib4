import Mathlib

namespace PellAlg

/-- An (a,b,c) triple, used for defining a quadratic.-/
structure Triple : Type where
  a : ℤ
  b : ℤ
  c : ℤ
deriving Repr

/-- The floor of the positive root of the triple. -/
def fpr (t : Triple) : ℤ := (-t.b + (discrim t.a t.b t.c).toNat.sqrt) / (2 * t.a)

/-- The quadratic form defined by the triple, and its fpr-translation. -/
def qf (t : Triple) (x : ℝ) := t.a * x * x + t.b * x + t.c

def qf_fpr_translate (t : Triple) (w : ℝ) := qf t (fpr t + w)

lemma qf_fpr_translate_root (t : Triple) (z : ℝ) (hz : qf t z = 0) :
  qf_fpr_translate t (z - fpr t) = 0 := by rw [qf_fpr_translate, add_sub_cancel'_right]; exact hz

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
-- #eval iterate_brouckner ⟨1,0, (-19)⟩ [] 20

/-- Swap a and c in a triple. -/
def swapac (t : Triple) : Triple := {a := t.c, b := t.b, c := t.a}

/-- Swapping twice gives the original triple. -/
lemma swapac_twice (t : Triple) : t = swapac (swapac t) := by simp [swapac]

/-- The inverse of a root is a root of the quadratic with a and c swapped. -/
lemma swapac_root (t: Triple) (z : ℝ) (hz : qf t z = 0) (hz' : z ≠ 0) :
  qf (swapac t) (1 / z) = 0 := by
  simp_rw [qf, swapac]
  rw [← zero_div (z * z), eq_div_iff (mul_ne_zero hz' hz')]
  simp only [add_mul]
  have : t.c * (1 / z) * (1 / z) * (z * z) + t.b * (1 / z) * (z * z) + t.a * (z * z) = qf t z :=
    by rw[qf]; field_simp; ring
  rwa [this]

/-- The swapped Brouckner transform is the negation of the fpr-translation. -/
lemma neg_qf_fpr_translate_eq_brouckner (t : Triple) (w : ℝ) :
  -qf_fpr_translate t w = qf (swapac (brouckner t)) w := by
  rw [swapac, brouckner, qf_fpr_translate, qf, qf]
  simp only [Int.cast_add, Int.cast_neg, Int.cast_mul]
  ring

/-- First key fact: from a non-integer root, we can obtain a root of the Brouckner transform. -/
theorem brouckner_root (t: Triple) (z : ℝ) (hz : qf t z = 0) (hz' : z ≠ fpr t) :
  qf (brouckner t) (1 / (z - fpr t)) = 0 := by
  rw [swapac_twice (brouckner t)]
  have h2 : -qf_fpr_translate t (z - fpr t) = 0 := by rw[qf_fpr_translate_root _ _ hz, neg_zero]
  rw [neg_qf_fpr_translate_eq_brouckner] at h2
  apply swapac_root _ _ h2 (sub_ne_zero.mpr hz')

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
