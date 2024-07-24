/-
Copyright (c) 2022 Dhruv Bhatia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Bhatia, Robert Y. Lewis, Mario Carneiro
-/
import Mathlib.Tactic.Polyrith

/-!

Each call to `polyrith` makes a call to the SageCell web API at
<https://sagecell.sagemath.org/>. To avoid making many API calls from CI,
we only test this communication in a few tests.

A full test suite is provided at the bottom of the file.

-/

/-!
## Set up testing infrastructure
-/

-- section tactic
-- open polyrith tactic
-- /--
-- For testing purposes, this behaves like `tactic.polyrith`, but takes an extra argument
-- representing the expected output from a call to Sage.
-- Allows for testing without actually making API calls.
-- -/
-- meta def tactic.test_polyrith (only_on : bool) (hyps : list pexpr)
--   (sage_out : json) (expected_args : list string) (expected_out : string) :
--   tactic unit := do
--   (eq_names, m, R, args) ← create_args only_on hyps,
--   guard (args = expected_args) <|>
--     fail!"expected arguments to Sage: {expected_args}\nbut produced: {args}",
--   out ← to_string <$> process_output eq_names m R sage_out,
--   guard (out = expected_out) <|>
--     fail!"expected final output: {expected_out}\nbut produced: {out}"

-- meta def format_string_list (input : list string) : format :=
-- "[" ++ (format.join <| (input.map (λ s, ("\"" : format) ++ format.of_string s ++ "\"")).intersperse ("," ++ format.line)) ++ "]"

-- setup_tactic_parser

-- meta def tactic.interactive.test_polyrith (restr : parse (tk "only")?)
--   (hyps : parse pexpr_list?)
--   (sage_out : string) (expected_args : list string) (expected_out : string) : tactic unit := do
--   some sage_out ← return <| json.parse sage_out,
--   tactic.test_polyrith restr.is_some (hyps.get_or_else []) sage_out expected_args expected_out

-- meta def tactic.interactive.test_sage_output (restr : parse (tk "only")?)
--   (hyps : parse pexpr_list?) (expected_out : string) : tactic unit := do
--   expected_json ← json.parse expected_out,
--   sleep 10, -- otherwise can lead to weird errors when actively editing code with polyrith calls
--   (eq_names, m, R, args) ← create_args restr.is_some (hyps.get_or_else []),
--   sage_out ← sage_output args,
--   guard (sage_out = expected_json) <|>
--     fail!"Expected output from Sage: {expected_out}\nbut produced: {sage_out}"

-- /--
-- A convenience function. Given a working test, prints the code for a call to `test_sage_output`.
-- -/
-- meta def tactic.interactive.create_sage_output_test (restr : parse (tk "only")?)
--   (hyps : parse pexpr_list?) : tactic unit := do
--   let hyps := (hyps.get_or_else []),
--   sleep 10, -- otherwise can lead to weird errors when actively editing code with polyrith calls
--   (eq_names, m, R, args) ← create_args restr.is_some hyps,
--   sage_out ← to_string <$> sage_output args,
--   let sage_out := sage_out.fold "" (λ s c, s ++ (if c = '"' then "\\\"" else to_string c)),
--   let onl := if restr.is_some then "only " else "",
--   let hyps := if hyps = [] then "" else to_string hyps,
--   trace!"test_sage_output {onl}{hyps} \"{sage_out}\""

-- /--
-- A convenience function. Given a working test, prints the code for a call to `test_polyrith`.
-- -/
-- meta def tactic.interactive.create_polyrith_test (restr : parse (tk "only")?)
--   (hyps : parse pexpr_list?) : tactic unit := do
--   let hyps := (hyps.get_or_else []),
--   sleep 10, -- otherwise can lead to weird errors when actively editing code with polyrith calls
--   (eq_names, m, R, args) ← create_args restr.is_some hyps,
--   sage_out ← sage_output args,
--   out ← to_string <$> process_output eq_names m R sage_out,
--   let out := out.fold "" (λ s c, s ++ (if c = '"' then "\\\"" else to_string c)),
--   let sage_out := (to_string sage_out).fold ""
--     (λ s c, s ++ (if c = '"' then "\\\"" else to_string c)),
--   let argstring := format_string_list args,
--   let onl := if restr.is_some then "only " else "",
--   let hyps := if hyps = [] then "" else to_string hyps,
--   let trf := format.nest 2 <| format!"test_polyrith {onl}{hyps} \n\"{sage_out}\"\n{argstring}\n\"{out}\"",
--   trace!"Try this: {trf}"


-- end tactic

-- /-!
-- ## SageCell communication tests
-- -/

-- example (x y : ℚ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
--     x*y = -2*y + 1 := by
--   test_sage_output "{\"data\":[\"(poly.const 1/1)\",\"(poly.const -2/1)\"],\"success\":true}"
--   linear_combination h1 - 2 * h2

-- example (w x y z : ℝ) (h1 : x + 2.1*y + 2*z = 2) (h2 : x + 8*z + 5*w = -6.5)
--     (h3 : x + y + 5*z + 5*w = 3) :
--   x + 2.2*y + 2*z - 5*w = -8.5 := by
--   test_sage_output "{\"data\":[\"(poly.const 2/1)\",\"(poly.const 1/1)\",\"(poly.const -2/1)\"],\"success\":true}"
--   linear_combination 2 * h1 + h2 - 2 * h3



-- /-! ### Standard Cases over ℤ, ℚ, and ℝ -/

-- example (x y : ℤ) (h1 : 3*x + 2*y = 10) :
--   3*x + 2*y = 10 :=
-- by test_polyrith
--   "{\"data\":[\"(poly.const 1/1)\"],\"success\":true}"
--   ["ff",
--   "int",
--   "2",
--   "[(((3 * var0) + (2 * var1)) - 10)]",
--   "(((3 * var0) + (2 * var1)) - 10)"]
--   "linear_combination h1"

-- example (x y : ℚ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
--   x*y = -2*y + 1 :=
-- by test_polyrith
--   "{\"data\":[\"(poly.const 1/1)\",\"(poly.const -2/1)\"],\"success\":true}"
--   ["ff",
--   "rat",
--   "2",
--   "[(((var0 * var1) + (2 * var0)) - 1), (var0 - var1)]",
--   "((var0 * var1) - ((-2 * var1) + 1))"]
--   "linear_combination h1 - 2 * h2"

-- example (x y : ℝ) (h1 : x + 2 = -3) (h2 : y = 10) :
--   -y + 2*x + 4 = -16 :=
-- by test_polyrith
--   "{\"data\":[\"(poly.const 2/1)\",\"(poly.const -1/1)\"],\"success\":true}"
--   ["ff",
--   "real",
--   "2",
--   "[((var1 + 2) - -3), (var0 - 10)]",
--   "(((-var0 + (2 * var1)) + 4) - -16)"]
--   "linear_combination 2 * h1 - h2"

-- example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
--     (hc : x + 2*y + z = 2) :
--   -3*x - 3*y - 4*z = 2 :=
-- by test_polyrith
--   "{\"data\":[\"(poly.const 1/1)\",\"(poly.const -1/1)\",\"(poly.const -2/1)\"],\"success\":true}"
--   ["ff",
--   "real",
--   "3",
--   "[(((var0 + (2 * var1)) - var2) - 4), ((((2 * var0) + var1) + var2) - -2), (((var0 + (2 * var1)) + var2) - 2)]",
--   "((((-3 * var0) - (3 * var1)) - (4 * var2)) - 2)"]
--   "linear_combination ha - hb - 2 * hc"

-- example (w x y z : ℝ) (h1 : x + 2.1*y + 2*z = 2) (h2 : x + 8*z + 5*w = -6.5)
--     (h3 : x + y + 5*z + 5*w = 3) :
--   x + 2.2*y + 2*z - 5*w = -8.5 :=
-- by test_polyrith
--   "{\"data\":[\"(poly.const 2/1)\",\"(poly.const 1/1)\",\"(poly.const -2/1)\"],\"success\":true}"
--   ["ff",
--   "real",
--   "4",
--   "[(((var0 + (21/10 * var1)) + (2 * var2)) - 2), (((var0 + (8 * var2)) + (5 * var3)) - -13/2), ((((var0 + var1) + (5 * var2)) + (5 * var3)) - 3)]",
--   "((((var0 + (11/5 * var1)) + (2 * var2)) - (5 * var3)) - -17/2)"]
--   "linear_combination 2 * h1 + h2 - 2 * h3"

-- example (a b c d : ℚ) (h1 : a = 4) (h2 : 3 = b) (h3 : c*3 = d) (h4 : -d = a) :
--   2*a - 3 + 9*c + 3*d = 8 - b + 3*d - 3*a :=
-- by test_polyrith
--   "{\"data\":[\"(poly.const 2/1)\",\"(poly.const -1/1)\",\"(poly.const 3/1)\",\"(poly.const -3/1)\"],\"success\":true}"
--   ["ff",
--   "rat",
--   "4",
--   "[(var0 - 4), (3 - var3), ((var1 * 3) - var2), (-var2 - var0)]",
--   "(((((2 * var0) - 3) + (9 * var1)) + (3 * var2)) - (((8 - var3) + (3 * var2)) - (3 * var0)))"]
--   "linear_combination 2 * h1 - h2 + 3 * h3 - 3 * h4"

-- /-! ### Case with ambiguous identifiers-/

-- example («def evil» y : ℤ) (h1 : 3*«def evil» + 2*y = 10) :
--   3*«def evil» + 2*y = 10 :=
-- by test_polyrith
--   "{\"data\":[\"(poly.const 1/1)\"],\"success\":true}"
--   ["ff",
--   "int",
--   "2",
--   "[(((3 * var0) + (2 * var1)) - 10)]",
--   "(((3 * var0) + (2 * var1)) - 10)"]
--   "linear_combination h1"

-- example («¥» y : ℤ) (h1 : 3*«¥» + 2*y = 10) :
--   «¥» * (3*«¥» + 2*y) = 10 * «¥» :=
-- by test_polyrith
--   "{\"data\":[\"(poly.var 0)\"],\"success\":true}"
--   ["ff",
--   "int",
--   "2",
--   "[(((3 * var0) + (2 * var1)) - 10)]",
--   "((var0 * ((3 * var0) + (2 * var1))) - (10 * var0))"]
--   "linear_combination «¥» * h1"

-- /-! ### Cases with arbitrary coefficients -/

-- example (a b : ℤ) (h : a = b) :
--   a * a = a * b :=
-- by test_polyrith
--   "{\"data\":[\"(poly.var 0)\"],\"success\":true}"
--   ["ff",
--   "int",
--   "2",
--   "[(var0 - var1)]",
--   "((var0 * var0) - (var0 * var1))"]
--   "linear_combination a * h"

-- example (a b c : ℤ) (h : a = b) :
--   a * c = b * c :=
-- by test_polyrith
--   "{\"data\":[\"(poly.var 1)\"],\"success\":true}"
--   ["ff",
--   "int",
--   "3",
--   "[(var0 - var2)]",
--   "((var0 * var1) - (var2 * var1))"]
--   "linear_combination c * h"

-- example (a b c : ℤ) (h1 : a = b) (h2 : b = 1) :
--   c * a + b = c * b + 1 :=
-- by test_polyrith
--   "{\"data\":[\"(poly.var 0)\",\"(poly.const 1/1)\"],\"success\":true}"
--   ["ff",
--   "int",
--   "3",
--   "[(var1 - var2), (var2 - 1)]",
--   "(((var0 * var1) + var2) - ((var0 * var2) + 1))"]
--   "linear_combination c * h1 + h2"

-- example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
--   x*x*y + y*x*y + 6*x = 3*x*y + 14 :=
-- by test_polyrith
--   "{\"data\":[\"(poly.mul (poly.var 0) (poly.var 1))\",\"(poly.const 2/1)\"],\"success\":true}"
--   ["ff",
--   "rat",
--   "2",
--   "[((var0 + var1) - 3), ((3 * var0) - 7)]",
--   "(((((var0 * var0) * var1) + ((var1 * var0) * var1)) + (6 * var0)) - (((3 * var0) * var1) + 14))"]
--   "linear_combination x * y * h1 + 2 * h2"

-- example (x y z w : ℚ) (hzw : z = w) : x*z + 2*y*z = x*w + 2*y*w := by
--   test_polyrith
--   "{\"data\":[\"(poly.add (poly.var 0) (poly.mul (poly.const 2/1) (poly.var 2)))\"],\"success\":true}"
--   ["ff",
--   "rat",
--   "4",
--   "[(var1 - var3)]",
--   "(((var0 * var1) + ((2 * var2) * var1)) - ((var0 * var3) + ((2 * var2) * var3)))"]
--   "linear_combination (x + 2 * y) * hzw"

-- /-! ### Cases with non-hypothesis inputs/input restrictions -/

-- example (a b : ℝ) (ha : 2*a = 4) (hab : 2*b = a - b) (hignore : 3 = a + b) :
--   b = 2 / 3 := by
--   test_polyrith only [ha, hab]
--   "{\"data\":[\"(poly.const 1/6)\",\"(poly.const 1/3)\"],\"success\":true}"
--   ["ff",
--   "real",
--   "2",
--   "[((2 * var1) - 4), ((2 * var0) - (var1 - var0))]",
--   "(var0 - 2/3)"]
--   "linear_combination ha / 6 + hab / 3"

-- constant term : ∀ a b : ℚ, a + b = 0

-- example (a b c d : ℚ) (h : a + b = 0) (h2 : b + c = 0) : a + b + c + d = 0 := by
--   test_polyrith only [term c d, h]
--   "{\"data\":[\"(poly.const 1/1)\",\"(poly.const 1/1)\"],\"success\":true}"
--   ["ff",
--   "rat",
--   "4",
--   "[((var2 + var3) - 0), ((var0 + var1) - 0)]",
--   "((((var0 + var1) + var2) + var3) - 0)"]
--   "linear_combination term c d + h"

-- constants (qc : ℚ) (hqc : qc = 2*qc)

-- example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc := by
--   test_polyrith [h a b, hqc]
--   "{\"data\":[\"(poly.const 3/1)\",\"(poly.const 1/1)\"],\"success\":true}"
--   ["ff",
--   "rat",
--   "3",
--   "[(var0 - var2), (var1 - (2 * var1))]",
--   "(((3 * var0) + var1) - ((3 * var2) + (2 * var1)))"]
--   "linear_combination 3 * h a b + hqc"

-- constant bad (q : ℚ) : q = 0

-- example (a b : ℚ) : a + b^3 = 0 := by
--   test_polyrith [bad a, bad (b^2)]
--   "{\"data\":[\"(poly.const 1/1)\",\"(poly.var 1)\"],\"success\":true}"
--   ["ff",
--   "rat",
--   "2",
--   "[(var0 - 0), ((var1 ^ 2) - 0)]",
--   "((var0 + (var1 ^ 3)) - 0)"]
--   "linear_combination bad a + b * bad (b ^ 2)"

-- /-! ### Case over arbitrary field/ring -/

-- example {α} [h : CommRing α] {a b c d e f : α} (h1 : a*d = b*c) (h2 : c*f = e*d) :
--   c * (a*f - b*e) = 0 := by
--   test_polyrith
--   "{\"data\":[\"(poly.var 4)\",\"(poly.var 1)\"],\"success\":true}"
--   ["ff",
--   "α",
--   "6",
--   "[((var1 * var5) - (var3 * var0)), ((var0 * var2) - (var4 * var5))]",
--   "((var0 * ((var1 * var2) - (var3 * var4))) - 0)"]
--   "linear_combination e * h1 + a * h2"

-- example {K : Type*} [Field K] [Invertible 2] [Invertible 3]
--   {ω p q r s t x : K} (hp_nonzero : p ≠ 0) (hr : r ^ 2 = q ^ 2 + p ^ 3) (hs3 : s ^ 3 = q + r)
--   (ht : t * s = p) (x : K) (H : 1 + ω + ω ^ 2 = 0) :
--   x ^ 3 + 3 * p * x - 2 * q =
--     (x - (s - t)) * (x - (s * ω - t * ω ^ 2)) * (x - (s * ω ^ 2 - t * ω)) := by
--   have hs_nonzero : s ≠ 0 := by
--     contrapose! hp_nonzero with hs_nonzero
--     test_polyrith
--   "{\"data\":[\"(poly.const 0/1)\",\"(poly.const 0/1)\",\"(poly.const -1/1)\",\"(poly.const 0/1)\",\"(poly.var 4)\"],\"success\":true}"
--   ["ff",
--   "K",
--   "6",
--   "[((var1 ^ 2) - ((var2 ^ 2) + (var0 ^ 3))), ((var3 ^ 3) - (var2 + var1)), ((var4 * var3) - var0), (((1 + var5) + (var5 ^ 2)) - 0), (var3 - 0)]",
--   "(var0 - 0)"]
--   "linear_combination -ht + t * hs_nonzero"}
--   have H' : 2 * q = s ^ 3 - t ^ 3 := by
--     rw [← mul_left_inj' (pow_ne_zero 3 hs_nonzero)]
--     test_polyrith
--   "{\"data\":[\"(poly.const -1/1)\",\"(poly.sub (poly.add (poly.neg (poly.pow (poly.var 1) 3)) (poly.var 0)) (poly.var 3))\",\"(poly.add (poly.add (poly.mul (poly.pow (poly.var 1) 2) (poly.pow (poly.var 2) 2)) (poly.mul (poly.mul (poly.var 1) (poly.var 2)) (poly.var 4))) (poly.pow (poly.var 4) 2))\",\"(poly.const 0/1)\"],\"success\":true}"
--   ["ff",
--   "K",
--   "6",
--   "[((var3 ^ 2) - ((var0 ^ 2) + (var4 ^ 3))), ((var1 ^ 3) - (var0 + var3)), ((var2 * var1) - var4), (((1 + var5) + (var5 ^ 2)) - 0)]",
--   "(((2 * var0) * (var1 ^ 3)) - (((var1 ^ 3) - (var2 ^ 3)) * (var1 ^ 3)))"]
--   "linear_combination -hr + (-s ^ 3 + q - r) * hs3 + (s ^ 2 * t ^ 2 + s * t * p + p ^ 2) * ht"}
--   test_polyrith
--   "{\"data\":[\"(poly.const 0/1)\",\"(poly.const 0/1)\",\"(poly.add (poly.add (poly.sub (poly.add (poly.add (poly.sub (poly.add (poly.sub (poly.mul (poly.var 0) (poly.pow (poly.var 5) 4)) (poly.mul (poly.var 3) (poly.pow (poly.var 5) 4))) (poly.mul (poly.var 4) (poly.pow (poly.var 5) 4))) (poly.mul (poly.var 3) (poly.pow (poly.var 5) 3))) (poly.mul (poly.var 4) (poly.pow (poly.var 5) 3))) (poly.mul (poly.mul (poly.const 3/1) (poly.var 0)) (poly.pow (poly.var 5) 2))) (poly.mul (poly.var 3) (poly.pow (poly.var 5) 2))) (poly.mul (poly.var 4) (poly.pow (poly.var 5) 2))) (poly.mul (poly.mul (poly.const 2/1) (poly.var 0)) (poly.var 5)))\",\"(poly.add (poly.sub (poly.add (poly.sub (poly.sub (poly.add (poly.add (poly.sub (poly.add (poly.sub (poly.sub (poly.add (poly.neg (poly.mul (poly.mul (poly.var 0) (poly.pow (poly.var 3) 2)) (poly.var 5))) (poly.mul (poly.pow (poly.var 3) 3) (poly.var 5))) (poly.mul (poly.mul (poly.var 0) (poly.pow (poly.var 4) 2)) (poly.var 5))) (poly.mul (poly.pow (poly.var 4) 3) (poly.var 5))) (poly.mul (poly.mul (poly.var 0) (poly.var 1)) (poly.pow (poly.var 5) 2))) (poly.mul (poly.mul (poly.var 1) (poly.var 3)) (poly.pow (poly.var 5) 2))) (poly.mul (poly.mul (poly.var 1) (poly.var 4)) (poly.pow (poly.var 5) 2))) (poly.mul (poly.pow (poly.var 0) 2) (poly.var 3))) (poly.pow (poly.var 3) 3)) (poly.mul (poly.pow (poly.var 0) 2) (poly.var 4))) (poly.pow (poly.var 4) 3)) (poly.mul (poly.mul (poly.var 0) (poly.var 1)) (poly.var 5))) (poly.mul (poly.mul (poly.const 3/1) (poly.var 0)) (poly.var 1)))\",\"(poly.const -1/1)\"],\"success\":true}"
--   ["ff",
--   "K",
--   "7",
--   "[((var6 ^ 2) - ((var2 ^ 2) + (var1 ^ 3))), ((var3 ^ 3) - (var2 + var6)), ((var4 * var3) - var1), (((1 + var5) + (var5 ^ 2)) - 0), ((2 * var2) - ((var3 ^ 3) - (var4 ^ 3)))]",
--   "((((var0 ^ 3) + ((3 * var1) * var0)) - (2 * var2)) - (((var0 - (var3 - var4)) * (var0 - ((var3 * var5) - (var4 * (var5 ^ 2))))) * (var0 - ((var3 * (var5 ^ 2)) - (var4 * var5)))))"]
--   "linear_combination (x * ω ^ 4 - s * ω ^ 4 + t * ω ^ 4 - s * ω ^ 3 + t * ω ^ 3 + 3 * x * ω ^ 2 - s * ω ^ 2 +
--       t * ω ^ 2 +
--     2 * x * ω) * ht + (-(x * s ^ 2 * ω) + s ^ 3 * ω - x * t ^ 2 * ω - t ^ 3 * ω + x * p * ω ^ 2 - p * s * ω ^ 2 +
--                 p * t * ω ^ 2 +
--               x ^ 2 * s -
--             s ^ 3 -
--           x ^ 2 * t +
--         t ^ 3 -
--       x * p * ω +
--     3 * x * p) * H - H'"


-- /-! ## Degenerate cases -/

-- example {K : Type*} [Field K] [CharZero K] {s : K} (hs : 3 * s + 1 = 4) : s = 1 := by
--   test_polyrith
--   "{\"data\":[\"(poly.const 1/3)\"],\"success\":true}"
--   ["ff",
--   "K",
--   "1",
--   "[(((3 * var0) + 1) - 4)]",
--   "(var0 - 1)"]
--   "linear_combination hs / 3"

-- example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by
--   test_polyrith
--   "{\"data\":[\"(poly.const 1/1)\"],\"success\":true}"
--   ["ff",
--   "int",
--   "1",
--   "[((var0 + 4) - 2)]",
--   "(var0 - -2)"]
--   "linear_combination h1"

-- example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := by
--   test_polyrith
--   "{\"data\":[\"(poly.const 1/3)\"],\"success\":true}"
--   ["ff",
--   "rat",
--   "1",
--   "[(((3 * var0) + 1) - 4)]",
--   "(var0 - 1)"]
--   "linear_combination h1 / 3"

-- example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 := by
--   test_polyrith
--   "{\"data\":[\"(poly.const 1/1)\"],\"success\":true}"
--   ["ff",
--   "int",
--   "1",
--   "[(((2 * var0) + 3) - var0)]",
--   "(var0 - -3)"]
--   "linear_combination h1"

-- example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 := by
--   test_polyrith
--   "{\"data\":[\"(poly.const 1/1)\"],\"success\":true}"
--   ["ff",
--   "rat",
--   "1",
--   "[(((4 * var0) + 1) - ((3 * var0) - 2))]",
--   "(var0 - -3)"]
--   "linear_combination h1"

-- example (z : ℤ) (h1 : z + 1 = 2) (h2 : z + 2 = 2) : (1 : ℤ) = 2 := by
--   test_polyrith
--   "{\"data\":[\"(poly.const 1/1)\",\"(poly.const -1/1)\"],\"success\":true}"
--   ["ff",
--   "int",
--   "1",
--   "[((var0 + 1) - 2), ((var0 + 2) - 2)]",
--   "(1 - 2)"]
--   "linear_combination h1 - h2"

-- example {R} [CommRing R] (x : R) (h2 : (2 : R) = 0) : x + x = 0 := by
--   test_polyrith
--   "{\"data\":[\"(poly.var 0)\"],\"success\":true}"
--   ["ff",
--   "R",
--   "1",
--   "[(2 - 0)]",
--   "((var0 + var0) - 0)"]
--   "linear_combination x * h2"

-- example {R} [CommRing R] (_x : R) (h : (2 : R) = 4) : (0 : R) = 2 := by
--   test_polyrith
--   "{\"data\":[\"(poly.const 1/1)\"],\"success\":true}"
--   ["ff",
--   "R",
--   "0",
--   "[(2 - 4)]",
--   "(0 - 2)"]
--   "linear_combination h"

-- We comment the following tests so that we don't overwhelm the SageCell API.

/-

/-! ### Standard Cases over ℤ, ℚ, and ℝ -/

example (x y : ℤ) (h1 : 3*x + 2*y = 10) : 3*x + 2*y = 10 := by
  polyrith

example (x y : ℚ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  polyrith

-- example (x y : ℝ) (h1 : x + 2 = -3) (h2 : y = 10) :
--   -y + 2*x + 4 = -16 := by
--   polyrith

-- example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
--     (hc : x + 2*y + z = 2) :
--    -3*x - 3*y - 4*z = 2 := by
--  polyrith

-- example (w x y z : ℝ) (h1 : x + 2.1*y + 2*z = 2) (h2 : x + 8*z + 5*w = -6.5)
--     (h3 : x + y + 5*z + 5*w = 3) :
--    x + 2.2*y + 2*z - 5*w = -8.5 := by
--  polyrith

example (a b c d : ℚ) (h1 : a = 4) (h2 : 3 = b) (h3 : c*3 = d) (h4 : -d = a) :
    2*a - 3 + 9*c + 3*d = 8 - b + 3*d - 3*a := by
  polyrith

/-! ### Case with ambiguous identifiers-/
-- set_option trace.Meta.Tactic.polyrith true
example («def evil» y : ℤ) (h1 : 3*«def evil» + 2*y = 10) :
    3*«def evil» + 2*y = 10 := by
  polyrith

example («¥» y : ℤ) (h1 : 3*«¥» + 2*y = 10) :
    «¥» * (3*«¥» + 2*y) = 10 * «¥» := by
  polyrith

/-! ### Cases with arbitrary coefficients -/

example (a b : ℤ) (h : a = b) : a * a = a * b := by
  polyrith

example (a b c : ℤ) (h : a = b) : a * c = b * c := by
  polyrith

example (a b c : ℤ) (h1 : a = b) (h2 : b = 1) :
    c * a + b = c * b + 1 := by
  polyrith

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
    x*x*y + y*x*y + 6*x = 3*x*y + 14 :=
  polyrith

example (x y z w : ℚ) (hzw : z = w) : x*z + 2*y*z = x*w + 2*y*w := by
  polyrith


/-! ### Cases with non-hypothesis inputs/input restrictions -/

-- example (a b : ℝ) (ha : 2*a = 4) (hab : 2*b = a - b) (hignore : 3 = a + b) :
--   b = 2 / 3 :=
-- by polyrith only [ha, hab]

axiom term : ∀ a b : ℚ, a + b = 0

example (a b c d : ℚ) (h : a + b = 0) (h2 : b + c = 0) : a + b + c + d = 0 := by
  polyrith only [term c d, h]

axiom qc : ℚ
axiom hqc : qc = 2*qc

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc := by
  polyrith [h a b, hqc]

axiom bad (q : ℚ) : q = 0

example (a b : ℚ) : a + b^3 = 0 := by
  polyrith [bad a, bad (b^2)]

/-! ### Case over arbitrary field/ring -/

example {α} [h : CommRing α] {a b c d e f : α} (h1 : a*d = b*c) (h2 : c*f = e*d) :
    c * (a*f - b*e) = 0 := by
  polyrith

-- example {K : Type*} [Field K] [Invertible 2] [Invertible 3]
--   {ω p q r s t x : K} (hp_nonzero : p ≠ 0) (hr : r ^ 2 = q ^ 2 + p ^ 3) (hs3 : s ^ 3 = q + r)
--   (ht : t * s = p) (x : K) (H : 1 + ω + ω ^ 2 = 0) :
--   x ^ 3 + 3 * p * x - 2 * q =
--     (x - (s - t)) * (x - (s * ω - t * ω ^ 2)) * (x - (s * ω ^ 2 - t * ω)) := by
--   have hs_nonzero : s ≠ 0 := by
--     contrapose! hp_nonzero with hs_nonzero
--     polyrith
--   have H' : 2 * q = s ^ 3 - t ^ 3 := by
--     rw [← mul_left_inj' (pow_ne_zero 3 hs_nonzero)]
--     polyrith
--   polyrith

/-

### Examples with exponent

-/

example (x y z : ℚ) (h : x = y) (h2 : x * y = 0) : x + y*z = 0 := by
  polyrith

example (K : Type)
    [Field K]
    [CharZero K]
    {x y z : K}
    (h₂ : y ^ 3 + x * (3 * z ^ 2) = 0)
    (h₁ : x ^ 3 + z * (3 * y ^ 2) = 0)
    (h₀ : y * (3 * x ^ 2) + z ^ 3 = 0)
    (h : x ^ 3 * y + y ^ 3 * z + z ^ 3 * x = 0) :
    x = 0 := by
  polyrith

/-!
### With trace enabled
Here, the tactic will trace the command that gets sent to sage,
and so the tactic will not prove the goal. `linear_combination`
is called manually to prevent errors.
-/

set_option trace.Meta.Tactic.polyrith true

-- example (x y : ℝ) (h1 : x + 2 = -3) (h2 : y = 10) : -y + 2*x + 4 = -16 := by
--   polyrith
--   linear_combination 2 * h1 - h2

example (a b c : ℤ) (h1 : a = b) (h2 : b = 1) : c * a + b = c * b + 1 := by
  polyrith
  linear_combination c * h1 + h2

example (a b c d : ℚ) (h : a + b = 0) (h2 : b + c = 0) : a + b + c + d = 0 := by
  polyrith only [term c d, h]
  linear_combination term c d + h

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc := by
  polyrith [h a b, hqc]
  linear_combination 3 * h a b + hqc
-/


-- the following can be uncommented to regenerate the tests above.

/-


/-! ### Standard Cases over ℤ, ℚ, and ℝ -/

example (x y : ℤ) (h1 : 3*x + 2*y = 10) :
    3*x + 2*y = 10 := by
  create_polyrith_test

example (x y : ℚ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
    x*y = -2*y + 1 := by
  create_polyrith_test

example (x y : ℝ) (h1 : x + 2 = -3) (h2 : y = 10) : -y + 2*x + 4 = -16 := by
  create_polyrith_test

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
    -3*x - 3*y - 4*z = 2 := by
  create_polyrith_test

example (w x y z : ℝ) (h1 : x + 2.1*y + 2*z = 2) (h2 : x + 8*z + 5*w = -6.5)
    (h3 : x + y + 5*z + 5*w = 3) :
    x + 2.2*y + 2*z - 5*w = -8.5 := by
  create_polyrith_test

example (a b c d : ℚ) (h1 : a = 4) (h2 : 3 = b) (h3 : c*3 = d) (h4 : -d = a) :
    2*a - 3 + 9*c + 3*d = 8 - b + 3*d - 3*a := by
  create_polyrith_test

/-! ### Case with ambiguous identifiers-/

example («def evil» y : ℤ) (h1 : 3*«def evil» + 2*y = 10) :
    3*«def evil» + 2*y = 10 := by
  create_polyrith_test

example («¥» y : ℤ) (h1 : 3*«¥» + 2*y = 10) :
    «¥» * (3*«¥» + 2*y) = 10 * «¥» := by
  create_polyrith_test

/-! ### Cases with arbitrary coefficients -/

example (a b : ℤ) (h : a = b) : a * a = a * b := by
  create_polyrith_test

example (a b c : ℤ) (h : a = b) : a * c = b * c := by
  create_polyrith_test

example (a b c : ℤ) (h1 : a = b) (h2 : b = 1) : c * a + b = c * b + 1 := by
  create_polyrith_test

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
    x*x*y + y*x*y + 6*x = 3*x*y + 14 := by
  create_polyrith_test

example (x y z w : ℚ) (hzw : z = w) : x*z + 2*y*z = x*w + 2*y*w := by
  create_polyrith_test

/-! ### Cases with non-hypothesis inputs/input restrictions -/

example (a b : ℝ) (ha : 2*a = 4) (hab : 2*b = a - b) (hignore : 3 = a + b) :
    b = 2 / 3 := by
  create_polyrith_test only [ha, hab]

constant term : ∀ a b : ℚ, a + b = 0

example (a b c d : ℚ) (h : a + b = 0) (h2 : b + c = 0) : a + b + c + d = 0 := by
  create_polyrith_test only [term c d, h]

constants (qc : ℚ) (hqc : qc = 2*qc)

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc := by
  create_polyrith_test [h a b, hqc]

constant bad (q : ℚ) : q = 0

example (a b : ℚ) : a + b^3 = 0 := by create_polyrith_test [bad a, bad (b^2)]

/-! ### Case over arbitrary field/ring -/

example {α} [h : CommRing α] {a b c d e f : α} (h1 : a*d = b*c) (h2 : c*f = e*d) :
    c * (a*f - b*e) = 0 := by
  create_polyrith_test

example {K : Type*} [Field K] [Invertible 2] [Invertible 3]
  {ω p q r s t x : K} (hp_nonzero : p ≠ 0) (hr : r ^ 2 = q ^ 2 + p ^ 3) (hs3 : s ^ 3 = q + r)
  (ht : t * s = p) (x : K) (H : 1 + ω + ω ^ 2 = 0) :
  x ^ 3 + 3 * p * x - 2 * q =
    (x - (s - t)) * (x - (s * ω - t * ω ^ 2)) * (x - (s * ω ^ 2 - t * ω)) := by
  have hs_nonzero : s ≠ 0 := by
    contrapose! hp_nonzero with hs_nonzero
    create_polyrith_test
  have H' : 2 * q = s ^ 3 - t ^ 3 := by
    rw [← mul_left_inj' (pow_ne_zero 3 hs_nonzero)]
    create_polyrith_test
  create_polyrith_test


/-! ## Degenerate cases -/

example {K : Type*} [Field K] [CharZero K] {s : K} (hs : 3 * s + 1 = 4) : s = 1 := by
  create_polyrith_test

example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := by
  create_polyrith_test

example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := by
  create_polyrith_test

example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 := by
  create_polyrith_test

example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 := by
  create_polyrith_test

example (z : ℤ) (h1 : z + 1 = 2) (h2 : z + 2 = 2) : (1 : ℤ) = 2 := by
  create_polyrith_test

-/

-- example (a b : ℤ) (h : a + b = 4) : a + b = 0 := by
--   fail_if_success polyrith
--   -- polyrith failed to retrieve a solution from Sage!
--   -- ValueError: polynomial is not in the ideal
--   sorry

-- example (a : ℕ) : a = 0 := by
--   have := True.intro
--   polyrith -- polyrith did not find any relevant hypotheses and the goal is not provable by ring

-- example (y a : ℤ) (k : ℕ) (h : a ^ k = 0) : a ^ k * y = 0 := by
--   polyrith
