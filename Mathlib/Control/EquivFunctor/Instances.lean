/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Control.EquivFunctor

#align_import control.equiv_functor.instances from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# `EquivFunctor` instances

We derive some `EquivFunctor` instances, to enable `equiv_rw` to rewrite under these functions.
-/


open Equiv

instance EquivFunctorUnique : EquivFunctor Unique where
  map e := Equiv.uniqueCongr e
  map_refl' α := by simp
                    -- 🎉 no goals
  map_trans' := by simp
                   -- 🎉 no goals
#align equiv_functor_unique EquivFunctorUnique

instance EquivFunctorPerm : EquivFunctor Perm where
  map e p := (e.symm.trans p).trans e
  map_refl' α := by ext; simp
                    -- ⊢ ↑((fun {α β} e p => (e.symm.trans p).trans e) (Equiv.refl α) x✝¹) x✝ = ↑(id  …
                         -- 🎉 no goals
  map_trans' _ _ := by ext; simp
                       -- ⊢ ↑((fun {α β} e p => (e.symm.trans p).trans e) (x✝³.trans x✝²) x✝¹) x✝ = ↑((( …
                            -- 🎉 no goals
#align equiv_functor_perm EquivFunctorPerm

-- There is a classical instance of `LawfulFunctor Finset` available,
-- but we provide this computable alternative separately.
instance EquivFunctorFinset : EquivFunctor Finset where
  map e s := s.map e.toEmbedding
  map_refl' α := by ext; simp
                    -- ⊢ a✝ ∈ (fun {α β} e s => Finset.map (Equiv.toEmbedding e) s) (Equiv.refl α) x✝ …
                         -- 🎉 no goals
  map_trans' k h := by
    ext _ a; simp; constructor <;> intro h'
    -- ⊢ a ∈ (fun {α β} e s => Finset.map (Equiv.toEmbedding e) s) (k.trans h) x✝ ↔ a …
             -- ⊢ (∃ a_1, a_1 ∈ x✝ ∧ ↑h (↑k a_1) = a) ↔ ↑k.symm (↑h.symm a) ∈ x✝
                   -- ⊢ (∃ a_1, a_1 ∈ x✝ ∧ ↑h (↑k a_1) = a) → ↑k.symm (↑h.symm a) ∈ x✝
                                   -- ⊢ ↑k.symm (↑h.symm a) ∈ x✝
                                   -- ⊢ ∃ a_1, a_1 ∈ x✝ ∧ ↑h (↑k a_1) = a
    · let ⟨a, ha₁, ha₂⟩ := h'
      -- ⊢ ↑k.symm (↑h.symm a✝) ∈ x✝
      rw [← ha₂]; simp; apply ha₁
      -- ⊢ ↑k.symm (↑h.symm (↑h (↑k a))) ∈ x✝
                  -- ⊢ a ∈ x✝
                        -- 🎉 no goals
    · exists (Equiv.symm k) ((Equiv.symm h) a)
      -- ⊢ ↑k.symm (↑h.symm a) ∈ x✝ ∧ ↑h (↑k (↑k.symm (↑h.symm a))) = a
      simp [h']
      -- 🎉 no goals
#align equiv_functor_finset EquivFunctorFinset

instance EquivFunctorFintype : EquivFunctor Fintype where
  map e s := Fintype.ofBijective e e.bijective
  map_refl' α := by ext; simp
                    -- ⊢ (fun {α β} e s => Fintype.ofBijective ↑e (_ : Function.Bijective ↑e)) (Equiv …
                         -- 🎉 no goals
  map_trans' := by simp
                   -- 🎉 no goals
#align equiv_functor_fintype EquivFunctorFintype
