
example (a b : Nat) : HEq (a = b) (b = a) := by
  grind

section CC5
namespace LocalAxioms

axiom A : Type
axiom B : A → Type
axiom C : (a : A) → B a → Type
axiom D : (a : A) → (ba : B a) → C a ba → Type
axiom E : (a : A) → (ba : B a) → (cba : C a ba) → D a ba cba → Type
axiom F : (a : A) → (ba : B a) → (cba : C a ba) → (dcba : D a ba cba) → E a ba cba dcba → Type
axiom C_ss : ∀ a ba, Subsingleton (C a ba)
axiom a1 : A
axiom a2 : A
axiom a3 : A
axiom mk_B1 : (a : _) → B a
axiom mk_B2 : (a : _) → B a
axiom mk_C1 : {a : _} → (ba : _) → C a ba
axiom mk_C2 : {a : _} → (ba : _) → C a ba
axiom tr_B : {a : _} → B a → B a
axiom x : A → A
axiom y : A → A
axiom z : A → A
axiom f : {a : A} → {ba : B a} → (cba : C a ba) → D a ba cba
axiom f' : {a : A} → {ba : B a} → (cba : C a ba) → D a ba cba
axiom g : {a : A} → {ba : B a} → {cba : C a ba} → (dcba : D a ba cba) → E a ba cba dcba
axiom h : {a : A} → {ba : B a} → {cba : C a ba} → {dcba : D a ba cba} →
    (edcba : E a ba cba dcba) → F a ba cba dcba edcba

attribute [instance] C_ss

example : ∀ (a a' : A), HEq a a' → HEq (mk_B1 a) (mk_B1 a') := by
  grind

example : ∀ (a a' : A), HEq a a' → HEq (mk_B2 a) (mk_B2 a') := by
  grind

example : ∀ (a a' : A) (h : a = a') (b : B a), HEq (h ▸ b) b := by
  grind

example : HEq a1 (y a2) → HEq (mk_B1 a1) (mk_B1 (y a2)) := by
  grind

example : HEq a1 (x a2) → HEq a2 (y a1) → HEq (mk_B1 (x (y a1))) (mk_B1 (x (y (x a2)))) := by
  grind

example : HEq a1 (y a2) → HEq (mk_B1 a1) (mk_B2 (y a2)) →
    HEq (f (mk_C1 (mk_B2 a1))) (f (mk_C2 (mk_B1 (y a2)))) := by
  grind

example : HEq a1 (y a2) → HEq (tr_B (mk_B1 a1)) (mk_B2 (y a2)) →
    HEq (f (mk_C1 (mk_B2 a1))) (f (mk_C2 (tr_B (mk_B1 (y a2))))) := by
  grind

example : HEq a1 (y a2) → HEq (mk_B1 a1) (mk_B2 (y a2)) →
    HEq (g (f (mk_C1 (mk_B2 a1)))) (g (f (mk_C2 (mk_B1 (y a2))))) := by
  grind

example : HEq a1 (y a2) → HEq (tr_B (mk_B1 a1)) (mk_B2 (y a2)) →
    HEq (g (f (mk_C1 (mk_B2 a1)))) (g (f (mk_C2 (tr_B (mk_B1 (y a2)))))) := by
  grind

example : HEq a1 (y a2) → HEq a2 (z a3) → HEq a3 (x a1) → HEq (mk_B1 a1) (mk_B2 (y (z (x a1)))) →
          HEq (f (mk_C1 (mk_B2 (y (z (x a1)))))) (f' (mk_C2 (mk_B1 a1))) →
          HEq (g (f (mk_C1 (mk_B2 (y (z (x a1))))))) (g (f' (mk_C2 (mk_B1 a1)))) := by
  grind

example : HEq a1 (y a2) → HEq a2 (z a3) → HEq a3 (x a1) → HEq (mk_B1 a1) (mk_B2 (y (z (x a1)))) →
          HEq (f (mk_C1 (mk_B2 (y (z (x a1)))))) (f' (mk_C2 (mk_B1 a1))) →
          HEq (f' (mk_C1 (mk_B1 a1))) (f (mk_C2 (mk_B2 (y (z (x a1)))))) →
          HEq (g (f (mk_C1 (mk_B1 (y (z (x a1))))))) (g (f' (mk_C2 (mk_B2 a1)))) := by
  grind

example : HEq a1 (y a2) → HEq a2 (z a3) → HEq a3 (x a1) →
          HEq (tr_B (mk_B1 a1)) (mk_B2 (y (z (x a1)))) →
          HEq (f (mk_C1 (mk_B2 (y (z (x a1)))))) (f' (mk_C2 (tr_B (mk_B1 a1)))) →
          HEq (f' (mk_C1 (tr_B (mk_B1 a1)))) (f (mk_C2 (mk_B2 (y (z (x a1)))))) →
          HEq (g (f (mk_C1 (tr_B (mk_B1 (y (z (x a1)))))))) (g (f' (mk_C2 (mk_B2 a1)))) := by
  grind

end LocalAxioms
end CC5

section CC7

example (f g : {α : Type} → (a b : α) → {x : α // x ≠ b})
    (h : (b : Nat) → {x : Nat // x ≠ b}) (a b₁ b₂ : Nat) :
    h = f a → b₁ = b₂ → HEq (h b₁) (f a b₂) := by
  grind

example (f : Nat → Nat → Nat) (a b c d : Nat) :
        HEq c d → HEq (f a) (f b) → HEq (f a c) (f b d) := by
  grind

end CC7
