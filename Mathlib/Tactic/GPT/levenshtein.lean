/- Levenshtein Distance -/
import Init.Data.Array

def iota (n : Nat) : Array Nat :=
  ((List.iota n).reverse.map $ λ n => n-1).toArray

def lev' (s₀ : String) (s₁ : String) : Nat :=
  let v₀ := iota (s₁.length + 1);
  let v₁ := Array.mkArray (s₁.length + 1) 0;

  let ⟨v₀, _⟩ : Array Nat × Array Nat :=
    s₀.toList.enum.foldl (λ ⟨v₀, v₁⟩ ⟨i, c₀⟩ =>
      let v₁ := v₁.set! 0 (i + 1);

      let ⟨v₀, v₁⟩ : Array Nat × Array Nat :=
        s₁.toList.enum.foldl (λ ⟨v₀, v₁⟩ ⟨j, c₁⟩ =>
          let delCost := (v₀.get! (j + 1)) + 1;
          let insCost := (v₁.get! j) + 1;
          let subCost :=
            if c₀ = c₁ then v₀.get! j
            else (v₀.get! j) + 1;
          let v₁ := v₁.set! (j + 1) (Nat.min (Nat.min delCost insCost) subCost);
          ⟨v₀, v₁⟩)
        ⟨v₀, v₁⟩;

      ⟨v₁, v₀⟩)
    ⟨v₀, v₁⟩;

  v₀.get! s₁.length

def lev (s₀ : String) (s₁ : String) : Nat :=
  if s₀.length ≤ s₁.length then lev' s₀ s₁
  else lev' s₁ s₀

def main : IO Unit := do
  IO.println (lev "sitting" "kitten")
