import Mathlib.Tactic.Linarith

open Mathlib.Meta.NormNum
open Mathlib.Tactic.Ring

set_option linter.all false
set_option linter.style.setOption false
set_option linter.style.longLine false


-- set_option trace.Meta.isDefEq true in
set_option trace.profiler.threshold 1 in
set_option trace.profiler true in
set_option trace.linarith true in
set_option trace.linarith.detail true in
set_option trace.Meta.synthInstance.answer true in
set_option maxHeartbeats 0 in

theorem linear_combination_with_10_terms
    (a b c d e f g h i j : Int)
    (h0: -e + g + -h + i = 0)
    (h1: b + -d + -e + f + g + i = 0)
    (h2: -b + j = 0)
    (h3: c + d + -f + -i = 0)
    (h4: b + c + e + -g + -h + i + j = 0)
    (h5: -a + b + d + f + -h + -i = 0)
    (h6: a + d + e + -g + -h = 0)
    (h7: -a + d + -f + -h + j = 0)
    (h8: a + -d + e + f + g + h + -i + j = 0)
    (h9: -a + b + c + -e + -f + h + j = 0)
    : -2*a + b + 2*c + d + -3*f + -g + 3*h + -3*i = 0 := by
    nlinarith
