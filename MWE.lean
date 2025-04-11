import Batteries

def Blah.Meow.foo (x : ℕ) : ℕ := sorry

theorem mwe (p : ℕ)
    (h : 1 + Blah.Meow.foo p ≤ p + 1) : Blah.Meow.foo p ≤ p := by
  simpa [add_comm] using h -- error

def Blah.foo (x : ℕ) : ℕ := sorry

theorem mwe' (p : ℕ)
    (h : 1 + Blah.foo p ≤ p + 1) : Blah.foo p ≤ p := by
  simpa [add_comm] using h -- OK
