module

import Mathlib.Init

public section

structure Foo where _mkInternal :: x : Nat

-- We can use internal constructors in the module we defined them in
def e : Foo := ⟨4⟩
