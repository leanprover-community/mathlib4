import Std
import Mathlib.Init.Data.Nat.Notation

axiom T0 : Type
axiom F (A B : Type) (f : A → B) : Type
axiom F' (A B : Type) (f : A → B) : B → F A B f
axiom G (n : ℕ) (B : Type) : Type
axiom G' (n : ℕ) (B : Type) : B → B
axiom H : ℕ → ℕ
axiom H_le (n : ℕ) : H n ≤ n

noncomputable def system : ℕ → (A : Type) × (ℕ → (B : Type) × (B → A))
  | 0 => ⟨T0, fun _ => ⟨_, id⟩⟩
  | n+1 =>
    let ⟨A, fs⟩ := system n
    let ⟨B, g⟩ := fs (H n)
    let f1 := F' B A (g ∘ G' n B)
    ⟨F B A (g ∘ G' n B), fun m =>
      if m ≤ n then
        let ⟨C, k⟩ := fs m; ⟨C, f1 ∘ k⟩
      else
        ⟨_, id⟩⟩

def A (n : ℕ) : Type := (system n).1

theorem system_eq {m n} (h : m ≤ n) : ((system n).2 m).1 = A m := by
  match n with
  | 0 => cases h; rfl
  | n+1 =>
    simp [system]; split <;> simp <;> rename_i h'
    · apply system_eq h'
    · cases (Nat.le_or_eq_of_le_succ h).resolve_left h'
      rfl

noncomputable def f (n : ℕ) : A n → A (n + 1) := system_eq (Nat.le_succ _) ▸ ((system (n+1)).2 n).2

#check Eq.rec

theorem system_succ (n : ℕ) :
    ((system n).2 n).2.comp
      (system_eq (Nat.le_refl n) ▸ id) =
      id (α := A n) := by
  match n with
  | 0 => rfl
  | n+1 =>
    
    simp [system]

    done
