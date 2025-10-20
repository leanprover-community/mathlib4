/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Basic
/-! # Epi-mono factorization in the simplex category presented by generators and relations

This file aims to establish that there is a nice epi-mono factorization in `SimplexCategoryGenRel`.
More precisely, we introduce two morphism properties `P_δ` and `P_σ` that
single out morphisms that are compositions of `δ i` (resp. `σ i`).

The main result of this file is `exists_P_σ_P_δ_factorization`, which asserts that every
moprhism as a decomposition of a `P_σ` followed by a `P_δ`.

-/

namespace SimplexCategoryGenRel
open CategoryTheory

section EpiMono

/-- `δ i` is a split monomorphism thanks to the simplicial identities. -/
def splitMonoδ {n : ℕ} (i : Fin (n + 2)) : SplitMono (δ i) where
  retraction := by
    induction i using Fin.lastCases with
    | last => exact σ (Fin.last n)
    | cast i => exact σ i
  id := by
    cases i using Fin.lastCases
    · simp only [Fin.lastCases_last]
      exact δ_comp_σ_succ
    · simp only [Fin.lastCases_castSucc]
      exact δ_comp_σ_self

instance {n : ℕ} {i : Fin (n + 2)} : IsSplitMono (δ i) := .mk' <| splitMonoδ i

/-- `δ i` is a split epimorphism thanks to the simplicial identities. -/
def splitEpiσ {n : ℕ} (i : Fin (n + 1)) : SplitEpi (σ i) where
  section_ := δ i.castSucc
  id := δ_comp_σ_self

instance {n : ℕ} {i : Fin (n + 1)} : IsSplitEpi (σ i) := .mk' <| splitEpiσ i

/-- Auxiliary predicate to express that a morphism is purely a composition of `σ i`s. -/
abbrev P_σ := degeneracies.multiplicativeClosure

/-- Auxiliary predicate to express that a morphism is purely a composition of `δ i`s. -/
abbrev P_δ := faces.multiplicativeClosure

lemma P_σ.σ {n : ℕ} (i : Fin (n + 1)) : P_σ (σ i) := .of _ (.σ i)

lemma P_δ.δ {n : ℕ} (i : Fin (n + 2)) : P_δ (δ i) := .of _ (.δ i)

/-- All `P_σ` are split epis as composition of such. -/
lemma isSplitEpi_P_σ {x y : SimplexCategoryGenRel} {e : x ⟶ y} (he : P_σ e) : IsSplitEpi e := by
  induction he with
  | of x hx => cases hx; infer_instance
  | id => infer_instance
  | comp_of _ _ _ h => cases h; infer_instance

/-- All `P_δ` are split monos as composition of such. -/
lemma isSplitMono_P_δ {x y : SimplexCategoryGenRel} {m : x ⟶ y} (hm : P_δ m) :
    IsSplitMono m := by
  induction hm with
  | of x hx => cases hx; infer_instance
  | id => infer_instance
  | comp_of _ _ _ h => cases h; infer_instance

lemma isSplitEpi_toSimplexCategory_map_of_P_σ {x y : SimplexCategoryGenRel} {e : x ⟶ y}
    (he : P_σ e) : IsSplitEpi <| toSimplexCategory.map e := by
  constructor
  constructor
  apply SplitEpi.map
  exact isSplitEpi_P_σ he |>.exists_splitEpi.some

lemma isSplitMono_toSimplexCategory_map_of_P_δ {x y : SimplexCategoryGenRel} {m : x ⟶ y}
    (hm : P_δ m) : IsSplitMono <| toSimplexCategory.map m := by
  constructor
  constructor
  apply SplitMono.map
  exact isSplitMono_P_δ hm |>.exists_splitMono.some

lemma eq_or_len_le_of_P_δ {x y : SimplexCategoryGenRel} {f : x ⟶ y} (h_δ : P_δ f) :
    (∃ h : x = y, f = eqToHom h) ∨ x.len < y.len := by
  induction h_δ with
  | of _ hx => cases hx; right; simp
  | id => left; use rfl; simp
  | comp_of i u _ hg h' =>
    rcases h' with ⟨e, _⟩ | h' <;>
    apply Or.inr <;>
    cases hg
    · rw [e]
      exact Nat.lt_add_one _
    · exact Nat.lt_succ_of_lt h'

end EpiMono

section ExistenceOfFactorizations

/-- An auxiliary lemma to show that one can always use the simplicial identities to simplify a term
in the form `δ ≫ σ` into either an identity, or a term of the form `σ ≫ δ`. This is the crucial
special case to induct on to get an epi-mono factorization for all morphisms. -/
private lemma switch_δ_σ {n : ℕ} (i : Fin (n + 2)) (i' : Fin (n + 3)) :
    δ i' ≫ σ i = 𝟙 _ ∨ ∃ j j', δ i' ≫ σ i = σ j ≫ δ j' := by
  obtain h | rfl | h := lt_trichotomy i.castSucc i'
  · rw [Fin.castSucc_lt_iff_succ_le] at h
    obtain h | rfl := h.lt_or_eq
    · obtain ⟨i', rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
      rw [Fin.succ_lt_succ_iff] at h
      obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt h)
      exact Or.inr ⟨i, i', by rw [δ_comp_σ_of_gt h]⟩
    · exact Or.inl δ_comp_σ_succ
  · exact Or.inl δ_comp_σ_self
  · obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt h)
    rw [Fin.castSucc_lt_castSucc_iff] at h
    obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
    rw [← Fin.le_castSucc_iff] at h
    exact Or.inr ⟨i, i', by rw [δ_comp_σ_of_le h]⟩

/-- A low-dimensional special case of the previous -/
private lemma switch_δ_σ₀ (i : Fin 1) (i' : Fin 2) :
    δ i' ≫ σ i = 𝟙 _ := by
  fin_cases i; fin_cases i'
  · exact δ_comp_σ_self
  · exact δ_comp_σ_succ

private lemma factor_δ_σ {n : ℕ} (i : Fin (n + 1)) (i' : Fin (n + 2)) :
    ∃ (z : SimplexCategoryGenRel) (e : mk n ⟶ z) (m : z ⟶ mk n)
      (_ : P_σ e) (_ : P_δ m), δ i' ≫ σ i = e ≫ m := by
  cases n with
  | zero => exact ⟨_, _, _, P_σ.id_mem _, P_δ.id_mem _, by simp [switch_δ_σ₀]⟩
  | succ n =>
    obtain h | ⟨j, j', h⟩ := switch_δ_σ i i'
    · exact ⟨_, _, _, P_σ.id_mem _, P_δ.id_mem _, by simp [h]⟩
    · exact ⟨_, _, _, P_σ.σ _, P_δ.δ _, h⟩

/-- An auxiliary lemma that shows there exists a factorization as a P_δ followed by a P_σ for
morphisms of the form `P_δ ≫ σ`. -/
private lemma factor_P_δ_σ {n : ℕ} (i : Fin (n + 1)) {x : SimplexCategoryGenRel}
    (f : x ⟶ mk (n + 1)) (hf : P_δ f) : ∃ (z : SimplexCategoryGenRel) (e : x ⟶ z) (m : z ⟶ mk n)
      (_ : P_σ e) (_ : P_δ m), f ≫ σ i = e ≫ m := by
  induction n generalizing x with
  | zero => cases hf with
    | of _ h => cases h; exact factor_δ_σ _ _
    | id => exact ⟨_, _, _, P_σ.σ i, P_δ.id_mem _, by simp⟩
    | comp_of j f hf hg =>
      obtain ⟨k⟩ := hg
      obtain ⟨rfl, rfl⟩ | hf' := eq_or_len_le_of_P_δ hf
      · simpa using factor_δ_σ i k
      · simp at hf'
  | succ n hn =>
    cases hf with
    | of _ h => cases h; exact factor_δ_σ _ _
    | id n => exact ⟨_, _, _, P_σ.σ i, P_δ.id_mem _, by simp⟩
    | comp_of f g hf hg =>
      obtain ⟨k⟩ := hg
      obtain ⟨rfl, rfl⟩ | h' := eq_or_len_le_of_P_δ hf
      · simpa using factor_δ_σ i k
      · obtain h'' | ⟨j, j', h''⟩ := switch_δ_σ i k
        · exact ⟨_, _, _, P_σ.id_mem _, hf, by simp [h'']⟩
        · obtain ⟨z, e, m, he, hm, fac⟩ := hn j f hf
          exact ⟨z, e, m ≫ δ j', he, P_δ.comp_mem _ _ hm (P_δ.δ j'),
            by simp [h'', reassoc_of% fac]⟩

/-- Any morphism in `SimplexCategoryGenRel` can be decomposed as a `P_σ` followed by a `P_δ`. -/
theorem exists_P_σ_P_δ_factorization {x y : SimplexCategoryGenRel} (f : x ⟶ y) :
    ∃ (z : SimplexCategoryGenRel) (e : x ⟶ z) (m : z ⟶ y)
        (_ : P_σ e) (_ : P_δ m), f = e ≫ m := by
  induction f with
  | @id n => use (mk n), (𝟙 (mk n)), (𝟙 (mk n)), P_σ.id_mem _, P_δ.id_mem _; simp
  | @comp_δ n n' f j h =>
    obtain ⟨z, e, m, ⟨he, hm, rfl⟩⟩ := h
    exact ⟨z, e, m ≫ δ j, he, P_δ.comp_mem _ _ hm (P_δ.δ _), by simp⟩
  | @comp_σ n n' f j h =>
    obtain ⟨z, e, m, ⟨he, hm, rfl⟩⟩ := h
    cases hm with
    | of g hg =>
      rcases hg with ⟨i⟩
      obtain ⟨_, _, _, ⟨he₁, hm₁, h₁⟩⟩ := factor_δ_σ j i
      exact ⟨_, _, _, P_σ.comp_mem _ _ he he₁, hm₁,
        by simp [← h₁]⟩
    | @id n =>
      exact ⟨mk n', e ≫ σ j, 𝟙 _, P_σ.comp_mem _ _ he (P_σ.σ _), P_δ.id_mem _, by simp⟩
    | comp_of f g hf hg =>
      cases n' with
      | zero =>
        cases hg
        exact ⟨_, _, _, he, hf, by simp [switch_δ_σ₀]⟩
      | succ n =>
        rcases hg with ⟨i⟩
        obtain h' | ⟨j', j'', h'⟩ := switch_δ_σ j i
        · exact ⟨_, _, _, he, hf, by simp [h']⟩
        · obtain ⟨_, _, m₁, ⟨he₁, hm₁, h₁⟩⟩ := factor_P_δ_σ j' f hf
          exact ⟨_, _, m₁ ≫ δ j'', P_σ.comp_mem _ _ he he₁, P_δ.comp_mem _ _ hm₁ (P_δ.δ _),
            by simp [← reassoc_of% h₁, h']⟩

instance : MorphismProperty.HasFactorization P_σ P_δ where
  nonempty_mapFactorizationData f := by
    obtain ⟨z, e, m, he, hm, fac⟩ := exists_P_σ_P_δ_factorization f
    exact ⟨⟨z, e, m, fac.symm, he, hm⟩⟩

end ExistenceOfFactorizations

end SimplexCategoryGenRel
