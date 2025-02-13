/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Basic
/-! # Epi-mono factorisation in the simplex category presented by generators and relations

This file aims to establish that there is a nice epi-mono factorisation in `SimplexCategoryGenRel`.
More precisely, we introduce two (inductively-defined) morphism property `P_δ` and `P_σ` that
single out morphisms that are compositions of `δ i` (resp. `σ i`).

We only define these, and prove various lemmas to help reasoning about them.

## TODOs
 - Prove that every morphism factors as a `P_σ` followed by a `P_δ`.

-/

namespace SimplexCategoryGenRel
open CategoryTheory

section EpiMono

/-- `δ i` is a split monomorphism thanks to the simplicial identities. -/
def SplitMonoδ {n : ℕ} {i : Fin (n + 2)} : SplitMono (δ i) where
  retraction := by
    induction i using Fin.lastCases with
    | last => exact σ n
    | cast i => exact σ i
  id := by
    cases i using Fin.lastCases
    · simp only [Fin.natCast_eq_last, Fin.lastCases_last]
      exact δ_comp_σ_succ
    · simp only [Fin.natCast_eq_last, Fin.lastCases_castSucc]
      exact δ_comp_σ_self

instance {n : ℕ} {i : Fin (n + 2)} : IsSplitMono (δ i) := .mk' SplitMonoδ

/-- `δ i` is a split epimorphism thanks to the simplicial identities. -/
def SplitEpiσ {n : ℕ} {i : Fin (n + 1)} : SplitEpi (σ i) where
  section_ := δ i.castSucc
  id := δ_comp_σ_self

instance {n : ℕ} {i : Fin (n + 1)} : IsSplitEpi (σ i) := .mk' SplitEpiσ

/-- Auxiliary predicate to express that a morphism is purely a composition of `σ i`s. -/
inductive P_σ : MorphismProperty SimplexCategoryGenRel
  | σ {n : ℕ} (i : Fin (n + 1)) : P_σ <| σ i
  | id {n : ℕ} : P_σ <| 𝟙 (.mk n)
  | comp {n : ℕ} (i : Fin (n + 1)) {a : SimplexCategoryGenRel} (g : a ⟶ .mk (n + 1))
    (hg: P_σ g) : P_σ <| g ≫ σ i

/-- A version of `P_σ` where composition is taken on the right instead. It is equivalent to `P_σ`
(see `P_σ_eq_P_σ'`). -/
inductive P_σ' : MorphismProperty SimplexCategoryGenRel
  | σ {n : ℕ} (i : Fin (n + 1)) : P_σ' <| σ i
  | id {n : ℕ} : P_σ' <| 𝟙 (.mk n)
  | comp {n : ℕ} (i : Fin (n + 1)) {a : SimplexCategoryGenRel} (g :.mk n ⟶ a)
    (hg: P_σ' g) : P_σ' <| σ i ≫ g

/-- Auxiliary predicate to express that a morphism is purely a composition of `δ i`s. -/
inductive P_δ : MorphismProperty SimplexCategoryGenRel
  | δ {n : ℕ} (i : Fin (n + 2)) : P_δ <| δ i
  | id {n : ℕ} : P_δ <| 𝟙 (.mk n)
  | comp {n : ℕ} (i : Fin (n + 2)) {a : SimplexCategoryGenRel} (g : a ⟶ .mk n )
    (hg: P_δ g) : P_δ <| g ≫ δ i

/-- A version of `P_δ` where composition is taken on the right instead. It is equivalent to `P_δ`
(see `P_σ_eq_P_δ'`). -/
inductive P_δ' : MorphismProperty SimplexCategoryGenRel
  | δ {n : ℕ} (i : Fin (n + 2)) : P_δ' <| δ i
  | id {n : ℕ} : P_δ' <| 𝟙 (.mk n)
  | comp {a : SimplexCategoryGenRel} {n : ℕ} (i : Fin (n + 2)) (g : .mk (n + 1) ⟶ a)
    (hg: P_δ' g) : P_δ' <| δ i ≫ g

lemma P_σ_eqToHom {x y : SimplexCategoryGenRel} (h : x = y) : P_σ <| eqToHom h := by
  subst h
  rw [eqToHom_refl]
  exact P_σ.id

lemma P_δ_eqToHom {x y : SimplexCategoryGenRel} (h : x = y) : P_δ <| eqToHom h := by
  subst h
  rw [eqToHom_refl]
  exact P_δ.id

lemma P_δ_comp {x y z : SimplexCategoryGenRel} (f : x ⟶ y) (g : y ⟶ z) :
    P_δ f → P_δ g → P_δ (f ≫ g) := by
  intro hf hg
  induction hg with
  | δ i => exact P_δ.comp _ f hf
  | id => rwa [Category.comp_id]
  | comp i b _ h => specialize h f hf
                    rw [← Category.assoc]
                    exact P_δ.comp i (f ≫ b) h

lemma P_σ_comp {x y z : SimplexCategoryGenRel} (f : x ⟶ y) (g : y ⟶ z) :
    P_σ f → P_σ g → P_σ (f ≫ g) := by
  intro hf hg
  induction hg with
  | σ i => exact P_σ.comp _ f hf
  | id => rwa [Category.comp_id]
  | comp i b _ h => specialize h f hf
                    rw [← Category.assoc]
                    exact P_σ.comp i (f ≫ b) h

lemma P_σ'_comp {x y z : SimplexCategoryGenRel} (f : x ⟶ y) (g : y ⟶ z) :
    P_σ' f → P_σ' g → P_σ' (f ≫ g) := by
  intro hf hg
  induction hf with
  | σ i => exact P_σ'.comp _ g hg
  | id => rwa [Category.id_comp]
  | comp i b _ h => specialize h g hg
                    rw [Category.assoc]
                    exact P_σ'.comp i (b ≫ g) h

lemma P_δ'_comp {x y z : SimplexCategoryGenRel} (f : x ⟶ y) (g : y ⟶ z) :
    P_δ' f → P_δ' g → P_δ' (f ≫ g) := by
  intro hf hg
  induction hf with
  | δ i => exact P_δ'.comp _ g hg
  | id => rwa [Category.id_comp]
  | comp i b _ h => specialize h g hg
                    rw [Category.assoc]
                    exact P_δ'.comp i (b ≫ g) h

/-- The property `P_σ` is equivalent to `P_σ'`. -/
lemma P_σ_eq_P_σ' : P_σ = P_σ' := by
  apply le_antisymm <;> intro x y f h
  · induction h with
    | σ i => exact P_σ'.σ i
    | id => exact P_σ'.id
    | comp i f h h' => exact P_σ'_comp _ _ h' (P_σ'.σ _)
  · induction h with
    | σ i => exact P_σ.σ i
    | id => exact P_σ.id
    | comp i f h h' => exact P_σ_comp _ _ (P_σ.σ _) h'

/-- The property `P_δ` is equivalent to `P_δ'`. -/
lemma P_δ_eq_P_δ' : P_δ = P_δ' := by
  apply le_antisymm <;> intro x y f h
  · induction h with
    | δ i => exact P_δ'.δ i
    | id => exact P_δ'.id
    | comp i f h h' => exact P_δ'_comp _ _ h' (P_δ'.δ _)
  · induction h with
    | δ i => exact P_δ.δ i
    | id => exact P_δ.id
    | comp i f h h' => exact P_δ_comp _ _ (P_δ.δ _) h'

/-- All `P_σ` are split epis as composition of such. -/
lemma isSplitEpi_P_σ {x y : SimplexCategoryGenRel} {e : x ⟶ y} (he : P_σ e) : IsSplitEpi e := by
  induction he <;> infer_instance

/-- All `P_δ` are split monos as composition of such. -/
lemma isSplitMono_P_δ {x y : SimplexCategoryGenRel} {m : x ⟶ y} (hm : P_δ m) :
    IsSplitMono m := by
  induction hm <;> infer_instance

lemma isSplitEpi_P_σ_toSimplexCategory {x y : SimplexCategoryGenRel} {e : x ⟶ y} (he : P_σ e)
    : IsSplitEpi <| toSimplexCategory.map e := by
  constructor
  constructor
  apply SplitEpi.map
  exact isSplitEpi_P_σ he |>.exists_splitEpi.some

lemma isSplitMono_P_δ_toSimplexCategory {x y : SimplexCategoryGenRel} {m : x ⟶ y} (hm : P_δ m)
    : IsSplitMono <| toSimplexCategory.map m := by
  constructor
  constructor
  apply SplitMono.map
  exact isSplitMono_P_δ hm |>.exists_splitMono.some

lemma eq_or_len_le_of_P_δ {x y : SimplexCategoryGenRel} {f : x ⟶ y} (h_δ : P_δ f) :
    (∃ h : x = y, f = eqToHom h) ∨ x.len < y.len := by
  induction h_δ with
  | δ i => right; simp
  | id => left; use rfl; simp
  | comp i u _ h' =>
    rcases h' with ⟨e, _⟩ | h'
    · right; rw [e]; exact Nat.lt_add_one _
    · right; exact Nat.lt_succ_of_lt h'

end EpiMono

end SimplexCategoryGenRel
