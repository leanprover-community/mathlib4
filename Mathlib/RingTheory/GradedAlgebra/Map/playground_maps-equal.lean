import Mathlib

section mapsEqual
universe u
variable (A A' B B': Type u) (f : A → B) (g : A' → B) (h : A → B') (k : A' → B') (hA : A = A') (hB : B = B')

example (h' : g ∘ (cast hA) = f) (hf : f.Surjective) : g.Surjective := by
  subst hA h'
  exact hf

example (h' : h = (cast hB) ∘ f) (hf : f.Surjective) : h.Surjective := by
  subst hB h'
  exact hf

example (h' : k ∘ (cast hA) = (cast hB) ∘ f) (hf : f.Surjective) : k.Surjective := by
  subst hA hB
  change k = f at h'
  simpa [h'] using hf

end mapsEqual
