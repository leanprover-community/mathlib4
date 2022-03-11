/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: E.W.Ayers
-/

namespace Sum

def map (f : A → B) (g : S → T) : (A ⊕ S) → (B ⊕ T)
  | (Sum.inl a) => Sum.inl $ f a
  | (Sum.inr s) => Sum.inr $ g s

/-- Non-dependent version of `Sum.rec`. -/
def elim : (A → C) → (B → C) → (A ⊕ B) → C
  | l, _, (Sum.inl a) => l a
  | _, r, (Sum.inr b) => r b

def swap : A ⊕ B → B ⊕ A
  | Sum.inl a => Sum.inr a
  | Sum.inr b => Sum.inl b

def Double (A : Type u) := A ⊕ A

def codelta {A} : A ⊕ A → A
  | (Sum.inl a) => a
  | (Sum.inr a) => a

instance : Monad (Sum A) where
  map f := Sum.map id f
  pure := Sum.inr
  bind a f :=
    match a with
    | Sum.inl a => Sum.inl a
    | Sum.inr b => f b

end Sum
