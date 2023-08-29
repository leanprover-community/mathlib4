/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Data.Sym.Sym2
import Mathlib.Logic.Relation

#align_import order.game_add from "leanprover-community/mathlib"@"fee218fb033b2fd390c447f8be27754bc9093be9"

/-!
# Game addition relation

This file defines, given relations `rα : α → α → Prop` and `rβ : β → β → Prop`, a relation
`Prod.GameAdd` on pairs, such that `GameAdd rα rβ x y` iff `x` can be reached from `y` by
decreasing either entry (with respect to `rα` and `rβ`). It is so called since it models the
subsequency relation on the addition of combinatorial games.

We also define `Sym2.GameAdd`, which is the unordered pair analog of `Prod.GameAdd`.

## Main definitions and results

- `Prod.GameAdd`: the game addition relation on ordered pairs.
- `WellFounded.prod_gameAdd`: formalizes induction on ordered pairs, where exactly one entry
  decreases at a time.

- `Sym2.GameAdd`: the game addition relation on unordered pairs.
- `WellFounded.sym2_gameAdd`: formalizes induction on unordered pairs, where exactly one entry
decreases at a time.
-/

set_option autoImplicit true


variable {α β : Type*} {rα : α → α → Prop} {rβ : β → β → Prop}

/-! ### `Prod.GameAdd` -/


namespace Prod

variable (rα rβ)

/-- `Prod.GameAdd rα rβ x y` means that `x` can be reached from `y` by decreasing either entry with
  respect to the relations `rα` and `rβ`.

  It is so called, as it models game addition within combinatorial game theory. If `rα a₁ a₂` means
  that `a₂ ⟶ a₁` is a valid move in game `α`, and `rβ b₁ b₂` means that `b₂ ⟶ b₁` is a valid move
  in game `β`, then `GameAdd rα rβ` specifies the valid moves in the juxtaposition of `α` and `β`:
  the player is free to choose one of the games and make a move in it, while leaving the other game
  unchanged.

  See `Sym2.GameAdd` for the unordered pair analog. -/

inductive GameAdd : α × β → α × β → Prop
  | fst {a₁ a₂ b} : rα a₁ a₂ → GameAdd (a₁, b) (a₂, b)
  | snd {a b₁ b₂} : rβ b₁ b₂ → GameAdd (a, b₁) (a, b₂)
#align prod.game_add Prod.GameAdd

theorem gameAdd_iff {rα rβ} {x y : α × β} :
    GameAdd rα rβ x y ↔ rα x.1 y.1 ∧ x.2 = y.2 ∨ rβ x.2 y.2 ∧ x.1 = y.1 := by
  constructor
  -- ⊢ GameAdd rα rβ x y → rα x.fst y.fst ∧ x.snd = y.snd ∨ rβ x.snd y.snd ∧ x.fst  …
  · rintro (@⟨a₁, a₂, b, h⟩ | @⟨a, b₁, b₂, h⟩)
    -- ⊢ rα (a₁, b).fst (a₂, b).fst ∧ (a₁, b).snd = (a₂, b).snd ∨ rβ (a₁, b).snd (a₂, …
    exacts [Or.inl ⟨h, rfl⟩, Or.inr ⟨h, rfl⟩]
    -- 🎉 no goals
  · revert x y
    -- ⊢ ∀ {x y : α × β}, rα x.fst y.fst ∧ x.snd = y.snd ∨ rβ x.snd y.snd ∧ x.fst = y …
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (⟨h, rfl : b₁ = b₂⟩ | ⟨h, rfl : a₁ = a₂⟩)
    -- ⊢ GameAdd rα rβ (a₁, b₁) (a₂, b₁)
    exacts [GameAdd.fst h, GameAdd.snd h]
    -- 🎉 no goals
#align prod.game_add_iff Prod.gameAdd_iff

theorem gameAdd_mk_iff {rα rβ} {a₁ a₂ : α} {b₁ b₂ : β} :
    GameAdd rα rβ (a₁, b₁) (a₂, b₂) ↔ rα a₁ a₂ ∧ b₁ = b₂ ∨ rβ b₁ b₂ ∧ a₁ = a₂ :=
  gameAdd_iff
#align prod.game_add_mk_iff Prod.gameAdd_mk_iff

@[simp]
theorem gameAdd_swap_swap : ∀ a b : α × β, GameAdd rβ rα a.swap b.swap ↔ GameAdd rα rβ a b :=
  fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ => by rw [Prod.swap, Prod.swap, gameAdd_mk_iff, gameAdd_mk_iff, or_comm]
                              -- 🎉 no goals
#align prod.game_add_swap_swap Prod.gameAdd_swap_swap

theorem gameAdd_swap_swap_mk (a₁ a₂ : α) (b₁ b₂ : β) :
    GameAdd rα rβ (a₁, b₁) (a₂, b₂) ↔ GameAdd rβ rα (b₁, a₁) (b₂, a₂) :=
  gameAdd_swap_swap rβ rα (b₁, a₁) (b₂, a₂)
#align prod.game_add_swap_swap_mk Prod.gameAdd_swap_swap_mk

/-- `Prod.GameAdd` is a subrelation of `Prod.Lex`. -/
theorem gameAdd_le_lex : GameAdd rα rβ ≤ Prod.Lex rα rβ := fun _ _ h =>
  h.rec (Prod.Lex.left _ _) (Prod.Lex.right _)
#align prod.game_add_le_lex Prod.gameAdd_le_lex

/-- `Prod.RProd` is a subrelation of the transitive closure of `Prod.GameAdd`. -/
theorem rprod_le_transGen_gameAdd : RProd rα rβ ≤ Relation.TransGen (GameAdd rα rβ)
  | _, _, h => h.rec (by
      intro _ _ _ _ hα hβ
      -- ⊢ Relation.TransGen (GameAdd rα rβ) (a₁✝, b₁✝) (a₂✝, b₂✝)
      exact Relation.TransGen.tail (Relation.TransGen.single $ GameAdd.fst hα) (GameAdd.snd hβ))
      -- 🎉 no goals
#align prod.rprod_le_trans_gen_game_add Prod.rprod_le_transGen_gameAdd

end Prod

/-- If `a` is accessible under `rα` and `b` is accessible under `rβ`, then `(a, b)` is
  accessible under `Prod.GameAdd rα rβ`. Notice that `Prod.lexAccessible` requires the
  stronger condition `∀ b, Acc rβ b`. -/
theorem Acc.prod_gameAdd (ha : Acc rα a) (hb : Acc rβ b) :
    Acc (Prod.GameAdd rα rβ) (a, b) := by
  induction' ha with a _ iha generalizing b
  -- ⊢ Acc (Prod.GameAdd rα rβ) (a, b)
  induction' hb with b hb ihb
  -- ⊢ Acc (Prod.GameAdd rα rβ) (a, b)
  refine' Acc.intro _ fun h => _
  -- ⊢ Prod.GameAdd rα rβ h (a, b) → Acc (Prod.GameAdd rα rβ) h
  rintro (⟨ra⟩ | ⟨rb⟩)
  -- ⊢ Acc (Prod.GameAdd rα rβ) (a₁✝, b)
  exacts [iha _ ra (Acc.intro b hb), ihb _ rb]
  -- 🎉 no goals
#align acc.prod_game_add Acc.prod_gameAdd

/-- The `Prod.GameAdd` relation on well-founded inputs is well-founded.

  In particular, the sum of two well-founded games is well-founded. -/
theorem WellFounded.prod_gameAdd (hα : WellFounded rα) (hβ : WellFounded rβ) :
    WellFounded (Prod.GameAdd rα rβ) :=
  ⟨fun ⟨a, b⟩ => (hα.apply a).prod_gameAdd (hβ.apply b)⟩
#align well_founded.prod_game_add WellFounded.prod_gameAdd

namespace Prod

/-- Recursion on the well-founded `Prod.GameAdd` relation.
  Note that it's strictly more general to recurse on the lexicographic order instead. -/
def GameAdd.fix {C : α → β → Sort*} (hα : WellFounded rα) (hβ : WellFounded rβ)
    (IH : ∀ a₁ b₁, (∀ a₂ b₂, GameAdd rα rβ (a₂, b₂) (a₁, b₁) → C a₂ b₂) → C a₁ b₁) (a : α) (b : β) :
    C a b :=
  @WellFounded.fix (α × β) (fun x => C x.1 x.2) _ (hα.prod_gameAdd hβ)
    (fun ⟨x₁, x₂⟩ IH' => IH x₁ x₂ fun a' b' => IH' ⟨a', b'⟩) ⟨a, b⟩
#align prod.game_add.fix Prod.GameAdd.fix

theorem GameAdd.fix_eq {C : α → β → Sort*} (hα : WellFounded rα) (hβ : WellFounded rβ)
    (IH : ∀ a₁ b₁, (∀ a₂ b₂, GameAdd rα rβ (a₂, b₂) (a₁, b₁) → C a₂ b₂) → C a₁ b₁) (a : α) (b : β) :
    GameAdd.fix hα hβ IH a b = IH a b fun a' b' _ => GameAdd.fix hα hβ IH a' b' :=
  WellFounded.fix_eq _ _ _
#align prod.game_add.fix_eq Prod.GameAdd.fix_eq

/-- Induction on the well-founded `Prod.GameAdd` relation.
  Note that it's strictly more general to induct on the lexicographic order instead. -/
theorem GameAdd.induction {C : α → β → Prop} :
    WellFounded rα →
      WellFounded rβ →
        (∀ a₁ b₁, (∀ a₂ b₂, GameAdd rα rβ (a₂, b₂) (a₁, b₁) → C a₂ b₂) → C a₁ b₁) → ∀ a b, C a b :=
  GameAdd.fix
#align prod.game_add.induction Prod.GameAdd.induction

end Prod

/-! ### `Sym2.GameAdd` -/

namespace Sym2

/-- `Sym2.GameAdd rα x y` means that `x` can be reached from `y` by decreasing either entry with
  respect to the relation `rα`.

  See `Prod.GameAdd` for the ordered pair analog. -/
def GameAdd (rα : α → α → Prop) : Sym2 α → Sym2 α → Prop :=
  Sym2.lift₂
    ⟨fun a₁ b₁ a₂ b₂ => Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂) ∨ Prod.GameAdd rα rα (b₁, a₁) (a₂, b₂),
      fun a₁ b₁ a₂ b₂ => by
        dsimp
        -- ⊢ (Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂) ∨ Prod.GameAdd rα rα (b₁, a₁) (a₂, b₂) …
        rw [Prod.gameAdd_swap_swap_mk _ _ b₁ b₂ a₁ a₂, Prod.gameAdd_swap_swap_mk _ _ a₁ b₂ b₁ a₂]
        -- ⊢ (Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂) ∨ Prod.GameAdd rα rα (b₁, a₁) (a₂, b₂) …
        simp [or_comm]⟩
        -- 🎉 no goals
#align sym2.game_add Sym2.GameAdd

theorem gameAdd_iff :
    ∀ {x y : α × α}, GameAdd rα ⟦x⟧ ⟦y⟧ ↔ Prod.GameAdd rα rα x y ∨ Prod.GameAdd rα rα x.swap y := by
  rintro ⟨_, _⟩ ⟨_, _⟩
  -- ⊢ GameAdd rα (Quotient.mk (Rel.setoid α) (fst✝¹, snd✝¹)) (Quotient.mk (Rel.set …
  rfl
  -- 🎉 no goals
#align sym2.game_add_iff Sym2.gameAdd_iff

theorem gameAdd_mk'_iff {a₁ a₂ b₁ b₂ : α} :
    GameAdd rα ⟦(a₁, b₁)⟧ ⟦(a₂, b₂)⟧ ↔
      Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂) ∨ Prod.GameAdd rα rα (b₁, a₁) (a₂, b₂) :=
  Iff.rfl
#align sym2.game_add_mk_iff Sym2.gameAdd_mk'_iff

theorem _root_.Prod.GameAdd.to_sym2 {a₁ a₂ b₁ b₂ : α} (h : Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂)) :
    Sym2.GameAdd rα ⟦(a₁, b₁)⟧ ⟦(a₂, b₂)⟧ :=
  gameAdd_mk'_iff.2 <| Or.inl <| h
#align prod.game_add.to_sym2 Prod.GameAdd.to_sym2

theorem GameAdd.fst {a₁ a₂ b : α} (h : rα a₁ a₂) : GameAdd rα ⟦(a₁, b)⟧ ⟦(a₂, b)⟧ :=
  (Prod.GameAdd.fst h).to_sym2
#align sym2.game_add.fst Sym2.GameAdd.fst

theorem GameAdd.snd {a b₁ b₂ : α} (h : rα b₁ b₂) : GameAdd rα ⟦(a, b₁)⟧ ⟦(a, b₂)⟧ :=
  (Prod.GameAdd.snd h).to_sym2
#align sym2.game_add.snd Sym2.GameAdd.snd

theorem GameAdd.fst_snd {a₁ a₂ b : α} (h : rα a₁ a₂) : GameAdd rα ⟦(a₁, b)⟧ ⟦(b, a₂)⟧ := by
  rw [Sym2.eq_swap]
  -- ⊢ GameAdd rα (Quotient.mk (Rel.setoid α) (b, a₁)) (Quotient.mk (Rel.setoid α)  …
  exact GameAdd.snd h
  -- 🎉 no goals
#align sym2.game_add.fst_snd Sym2.GameAdd.fst_snd

theorem GameAdd.snd_fst {a₁ a₂ b : α} (h : rα a₁ a₂) : GameAdd rα ⟦(b, a₁)⟧ ⟦(a₂, b)⟧ := by
  rw [Sym2.eq_swap]
  -- ⊢ GameAdd rα (Quotient.mk (Rel.setoid α) (a₁, b)) (Quotient.mk (Rel.setoid α)  …
  exact GameAdd.fst h
  -- 🎉 no goals
#align sym2.game_add.snd_fst Sym2.GameAdd.snd_fst

end Sym2

theorem Acc.sym2_gameAdd {a b} (ha : Acc rα a) (hb : Acc rα b) :
    Acc (Sym2.GameAdd rα) ⟦(a, b)⟧ := by
  induction' ha with a _ iha generalizing b
  -- ⊢ Acc (Sym2.GameAdd rα) (Quotient.mk (Sym2.Rel.setoid α) (a, b))
  induction' hb with b hb ihb
  -- ⊢ Acc (Sym2.GameAdd rα) (Quotient.mk (Sym2.Rel.setoid α) (a, b))
  refine' Acc.intro _ fun s => _
  -- ⊢ Sym2.GameAdd rα s (Quotient.mk (Sym2.Rel.setoid α) (a, b)) → Acc (Sym2.GameA …
  induction' s using Sym2.inductionOn with c d
  -- ⊢ Sym2.GameAdd rα (Quotient.mk (Sym2.Rel.setoid α) (c, d)) (Quotient.mk (Sym2. …
  rw [Sym2.GameAdd]
  -- ⊢ ↑Sym2.lift₂ { val := fun a₁ b₁ a₂ b₂ => Prod.GameAdd rα rα (a₁, b₁) (a₂, b₂) …
  dsimp
  -- ⊢ Prod.GameAdd rα rα (c, d) (a, b) ∨ Prod.GameAdd rα rα (d, c) (a, b) → Acc (↑ …
  rintro ((rc | rd) | (rd | rc))
  · exact iha c rc ⟨b, hb⟩
    -- 🎉 no goals
  · exact ihb d rd
    -- 🎉 no goals
  · rw [Sym2.eq_swap]
    -- ⊢ Acc (↑Sym2.lift₂ { val := fun a₁ b₁ a₂ b₂ => Prod.GameAdd rα rα (a₁, b₁) (a₂ …
    exact iha d rd ⟨b, hb⟩
    -- 🎉 no goals
  · rw [Sym2.eq_swap]
    -- ⊢ Acc (↑Sym2.lift₂ { val := fun a₁ b₁ a₂ b₂ => Prod.GameAdd rα rα (a₁, b₁) (a₂ …
    exact ihb c rc
    -- 🎉 no goals
#align acc.sym2_game_add Acc.sym2_gameAdd

/-- The `Sym2.GameAdd` relation on well-founded inputs is well-founded. -/
theorem WellFounded.sym2_gameAdd (h : WellFounded rα) : WellFounded (Sym2.GameAdd rα) :=
  ⟨fun i => Sym2.inductionOn i fun x y => (h.apply x).sym2_gameAdd (h.apply y)⟩
#align well_founded.sym2_game_add WellFounded.sym2_gameAdd

namespace Sym2

/-- Recursion on the well-founded `Sym2.GameAdd` relation. -/
def GameAdd.fix {C : α → α → Sort*} (hr : WellFounded rα)
    (IH : ∀ a₁ b₁, (∀ a₂ b₂, Sym2.GameAdd rα ⟦(a₂, b₂)⟧ ⟦(a₁, b₁)⟧ → C a₂ b₂) → C a₁ b₁) (a b : α) :
    C a b := by
  -- Porting note: this was refactored for #3414 (reenableeta), and could perhaps be cleaned up.
  have := hr.sym2_gameAdd
  -- ⊢ C a b
  dsimp only [GameAdd, lift₂, FunLike.coe, EquivLike.coe] at this
  -- ⊢ C a b
  exact @WellFounded.fix (α × α) (fun x => C x.1 x.2) _ this.of_quotient_lift₂
    (fun ⟨x₁, x₂⟩ IH' => IH x₁ x₂ fun a' b' => IH' ⟨a', b'⟩) (a, b)
#align sym2.game_add.fix Sym2.GameAdd.fix

theorem GameAdd.fix_eq {C : α → α → Sort*} (hr : WellFounded rα)
    (IH : ∀ a₁ b₁, (∀ a₂ b₂, Sym2.GameAdd rα ⟦(a₂, b₂)⟧ ⟦(a₁, b₁)⟧ → C a₂ b₂) → C a₁ b₁) (a b : α) :
    GameAdd.fix hr IH a b = IH a b fun a' b' _ => GameAdd.fix hr IH a' b' := by
  -- Porting note: this was refactored for #3414 (reenableeta), and could perhaps be cleaned up.
  dsimp [GameAdd.fix]
  -- ⊢ WellFounded.fix (_ : WellFounded fun a b => Prod.GameAdd rα rα (a.fst, a.snd …
  exact WellFounded.fix_eq _ _ _
  -- 🎉 no goals
#align sym2.game_add.fix_eq Sym2.GameAdd.fix_eq

/-- Induction on the well-founded `Sym2.GameAdd` relation. -/
theorem GameAdd.induction {C : α → α → Prop} :
    WellFounded rα →
      (∀ a₁ b₁, (∀ a₂ b₂, Sym2.GameAdd rα ⟦(a₂, b₂)⟧ ⟦(a₁, b₁)⟧ → C a₂ b₂) → C a₁ b₁) →
        ∀ a b, C a b :=
  GameAdd.fix
#align sym2.game_add.induction Sym2.GameAdd.induction

end Sym2
