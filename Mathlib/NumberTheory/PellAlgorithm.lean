
import Mathlib


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

structure Coefficients : Type where
  a : ℤ
  b : ℤ
  c : ℤ
  D : ℤ := b^2 - 4*a*c
  hD : D = b^2 - 4*a*c := by rfl
deriving Repr

def quad_form (f : Coefficients) (t : ℝ) : ℝ :=
  f.a * t * t + f.b * t + f.c

structure Roots (f : Coefficients) : Type where
  xp : ℝ
  xm : ℝ
  hxp : quad_form f xp = 0
  hxm : quad_form f xm = 0
  hle : xm < xp

def brouckner (f : Coefficients) : Coefficients × ℤ :=
  let m := (-f.b + f.D.sqrt) / (2 * f.a)
  ({a := -(f.a*m^2+f.b*m+f.c),
    b := -(2*f.a*m+f.b),
    c:= -f.a,
    D := f.D,
    hD := by rw [f.hD]; ring},
    m)

theorem roots_stay (f : Coefficients) (r : Roots f) (hxm : r.xm < 0) (hxp : r.xp > 1)
(r' : Roots (brouckner f).fst) :
  -1 < r'.xm ∧ r.xm < 0 ∧ r.xp > 1 := by sorry

def iterate_brouckner (f : Coefficients) (l : List (Coefficients × ℤ)) :
    (n : ℕ) → List (Coefficients × ℤ)
  | 0     => l
  | n + 1 =>
    let (f, m) := brouckner f
    if f.a = 1 then
      (f,m)::l
    else
      iterate_brouckner f ((f,m)::l) n



-- theorem bouckner_preserves_sign (f : Coefficients) (ha : 0 < f.a) (hc : f.c < 0) :
--   0 < (brouckner f).fst.a ∧ (brouckner f).fst.c < 0 := by
--     constructor
--     · simp [brouckner]
--       let m := (-f.b + f.D.sqrt) / (2 * f.a)
--       have : f.a * m^2 + f.b * m + f.c < 0 := by sorry
--       simp at this; linarith
--     · simp [brouckner, f.hD]; ring_nf; assumption

#eval iterate_brouckner ⟨1,0, (-19), (4 * 19), by norm_num⟩ [] 20

-- example : let (a',b',c',m) := brouckner a b c D;
--   brouckner (-c') (-b') (-a') D = (-c,-b,-a,sorry) := by
--   simp [brouckner]
--   constructor
--   field_simp


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
example : (50 : ℕ).sqrt = 7 := by norm_num
example : (123456789 : ℕ).sqrt = 11111 := by norm_num
example : (2340276615670 ^ 2 : ℕ).sqrt = 2340276615670 := by
  norm_num
