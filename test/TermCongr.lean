import Mathlib.Tactic.TermCongr
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring

namespace Tests

-- set_option trace.Elab.congr true

example {α β : Sort _} (f : α → β) (x y : α) (h : x = y) :
  congr_arg f h = congr(f $h) := rfl

example {α : Sort _} {β : α → Sort _} (f g : (x : α) → β x) (h : f = g) (x : α) :
  congr_fun h x = congr($h x) := rfl

example (x y : Nat) (h : x = y) : True := by
  have : 1 + x = _ := congr(_ + $h)
  guard_hyp this : 1 + x = 1 + y
  trivial

example [Decidable p] (x y : Nat) (h : x = y) : True := by
  have := congr(if p then 1 else $h)
  guard_hyp this :ₛ (if p then 1 else x) = (if p then 1 else y)
  trivial

example (x y z w : Nat) (h : x = y) (h' : z = w) : 1 + x * z^2 = 1 + y * w^2 := by
  refine congr(1 + $(?_) * $(?_)^2)
  · exact h
  · exact h'

example (x y z w : Nat) (h : x = y) (h' : z = w) : 1 + x * z^2 = 1 + y * w^2 := by
  refine congr(1 + $(?foo) * $(?bar)^2)
  case foo => exact h
  case bar => exact h'

example (p q : Prop) (h : p = q) : p ↔ q := congr($h)

example (p q : Prop) (h : p = q) : p ↔ q := by
  refine congr($(?_))
  guard_target = p ↔ q
  exact congr($h)

example (p q : Prop) (h : p = q) : Nonempty p = Nonempty q := congr(Nonempty $h)

example (p q : Prop) (h : p ↔ q) : Nonempty p = Nonempty q := congr(Nonempty $h)

example (p q : Prop) (h : p ↔ q) : Nonempty p ↔ Nonempty q := Iff.of_eq <| congr(Nonempty $h)

example (p q : Prop) (h : p ↔ q) : Nonempty p ↔ Nonempty q := congr(Nonempty $h)

example [Fintype α] [Fintype β] (h : α = β) : Fintype.card α = Fintype.card β :=
  congr(Fintype.card $h)

example (s t : Set α) [Fintype s] [Fintype t] (h : s = t) : Fintype.card s = Fintype.card t :=
  congr(Fintype.card $h)

example (x y : ℤ) (h1 : 3*x + 2*y = 10) (h2 : 2*x + 5*y = 3) :
    11*y = -11 := by
  have := congr(-2*$h1 + 3*$h2)
  guard_hyp this : -2*(3*x + 2*y) + 3*(2*x + 5*y) = -2*10 + 3*3
  ring_nf at this ⊢
  exact this

example (a b c d : ℚ) (h1 : a = 4) (h2 : 3 = b) (h3 : c*3 = d) (h4 : -d = a) :
    2*a - 3 + 9*c + 3*d = 8 - b + 3*d - 3*a := by
  have := congr(2*$h1 -1*$h2 +3*$h3 -3*$h4)
  guard_hyp this : 2*a - 1*3 + 3*(c*3) -3*(-d) = 2*4 - 1*b + 3*d - 3*a
  ring_nf at this ⊢
  exact this

example (a b c d e f : Nat) (hab : a = b) (hcd : c = d) (hef : e = f) : True := by
  have := congr(1 + $hab + $hcd * $hef)
  guard_hyp this : 1 + a + c * e = 1 + b + d * f
  trivial

example (f g : Nat → Nat) (h : ∀ n, f n = g n) :
    (fun n => 1 + f n) = (fun n => 1 + g n) :=
  congr(fun n => 1 + $(h n))

example (f g : Nat → Nat) (h : ∀ n, f n = g n) :
    (fun n => 1 + f n) = (fun n => 1 + g n) := by
  refine congr(fun n => 1 + $(?_))
  guard_target = f n = g n
  apply h

structure Foo where
  (x y : Nat)

example (s : Foo) (h : 1 = 2) : True := by
  have := congr(({s with x := $h} : Foo))
  guard_hyp this : ({ x := 1, y := s.y } : Foo) = { x := 2, y := s.y }
  trivial
