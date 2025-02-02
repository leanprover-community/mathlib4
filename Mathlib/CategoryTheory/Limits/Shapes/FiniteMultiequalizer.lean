/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.FinCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.Tactic.DeriveFintype

/-!
# Finiteness instances on multi-spans
-/

namespace CategoryTheory.Limits

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] {fst snd : R → L}

namespace WalkingMulticospan

deriving instance Fintype for WalkingMulticospan

instance : FinCategory (WalkingMulticospan fst snd) where
  fintypeHom
    | .left a, .left b => ⟨if e : a = b then {eqToHom (e ▸ rfl)} else ∅, by rintro ⟨⟩; simp⟩
    | .left a, .right b => ⟨⟨(if e : fst b = a then {eqToHom (e ▸ rfl) ≫ Hom.fst b} else 0) +
        (if e : snd b = a then {eqToHom (e ▸ rfl) ≫ Hom.snd b} else 0), by
        split_ifs with h₁ h₂
        · simp only [Multiset.singleton_add, Multiset.nodup_cons, Multiset.mem_singleton,
            Multiset.nodup_singleton, and_true]
          let f : ((left a : WalkingMulticospan fst snd) ⟶ right b) → Prop
            | .fst a => True
            | .snd a => False
          apply ne_of_apply_ne f
          conv_lhs => tactic => subst h₁; simp only [eqToHom_refl, Category.id_comp, f]
          conv_rhs => tactic => subst h₂; simp only [eqToHom_refl, Category.id_comp, f]
          simp
        all_goals simp⟩, by rintro ⟨⟩ <;> simp⟩
    | .right a, .left b => ⟨∅, by rintro ⟨⟩⟩
    | .right a, .right b => ⟨if e : a = b then {eqToHom (e ▸ rfl)} else ∅, by rintro ⟨⟩; simp⟩

end WalkingMulticospan

namespace WalkingMultispan

deriving instance Fintype for WalkingMultispan

instance : FinCategory (WalkingMultispan fst snd) where
  fintypeHom
    | .left a, .left b => ⟨if e : a = b then {eqToHom (e ▸ rfl)} else ∅, by rintro ⟨⟩; simp⟩
    | .left a, .right b => ⟨⟨(if e : fst a = b then {Hom.fst a ≫ eqToHom (e ▸ rfl)} else 0) +
        (if e : snd a = b then {Hom.snd a ≫ eqToHom (e ▸ rfl)} else 0), by
        split_ifs with h₁ h₂
        · simp only [Multiset.singleton_add, Multiset.nodup_cons, Multiset.mem_singleton,
            Multiset.nodup_singleton, and_true]
          let f : ((left a : WalkingMultispan fst snd) ⟶ right b) → Prop
            | .fst a => True
            | .snd a => False
          apply ne_of_apply_ne f
          conv_lhs => tactic => subst h₁; simp only [eqToHom_refl, Category.id_comp, f]
          conv_rhs => tactic => subst h₂; simp only [eqToHom_refl, Category.id_comp, f]
          simp
        all_goals simp⟩, by rintro ⟨⟩ <;> simp⟩
    | .right a, .left b => ⟨∅, by rintro ⟨⟩⟩
    | .right a, .right b => ⟨if e : a = b then {eqToHom (e ▸ rfl)} else ∅, by rintro ⟨⟩; simp⟩

end WalkingMultispan

end CategoryTheory.Limits
