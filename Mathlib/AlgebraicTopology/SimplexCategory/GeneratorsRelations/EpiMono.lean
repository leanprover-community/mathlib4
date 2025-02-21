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
    | last => exact σ n
    | cast i => exact σ i
  id := by
    cases i using Fin.lastCases
    · simp only [Fin.natCast_eq_last, Fin.lastCases_last]
      exact δ_comp_σ_succ
    · simp only [Fin.natCast_eq_last, Fin.lastCases_castSucc]
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
  obtain h'' | h'' | h'' : i'= i.castSucc ∨ i' < i.castSucc ∨ i.castSucc < i' := by
      simp only [lt_or_lt_iff_ne, ne_eq]
      tauto
  · subst h''
    rw [δ_comp_σ_self]
    simp
  · obtain ⟨h₁, h₂⟩ : i' ≠ Fin.last _ ∧ i ≠ 0 := by
      constructor
      · exact Fin.ne_last_of_lt h''
      · rw [Fin.lt_def, Fin.coe_castSucc] at h''
        apply Fin.ne_of_val_ne
        exact Nat.not_eq_zero_of_lt h''
    rw [← i'.castSucc_castPred h₁, ← i.succ_pred h₂]
    have H : i'.castPred h₁ ≤ (i.pred h₂).castSucc := by
      simp only [Fin.le_def, Fin.coe_castPred, Fin.coe_castSucc, Fin.coe_pred]
      rw [Fin.lt_def, Nat.lt_iff_add_one_le] at h''
      exact Nat.le_sub_one_of_lt h''
    rw [δ_comp_σ_of_le H]
    right
    use i.pred h₂, i'.castPred h₁
  · by_cases h : i.succ = i'
    · subst h
      rw [δ_comp_σ_succ]
      simp
    · obtain ⟨h₁, h₂⟩ : i ≠ Fin.last _ ∧ i' ≠ 0 := by
        constructor
        · by_cases h' : i' = Fin.last _
          · simp_all
          · rw [← Fin.val_eq_val] at h' h
            apply Fin.ne_of_val_ne
            rw [Fin.lt_def, Fin.coe_castSucc] at h''
            rcases i with ⟨i, hi⟩; rcases i' with ⟨i', hi'⟩
            intro hyp; subst hyp
            rw [Nat.lt_iff_add_one_le] at h'' hi'
            simp_all only [add_le_add_iff_right, Fin.val_last, Fin.succ_mk]
            rw [← one_add_one_eq_two] at hi'
            exact h (Nat.le_antisymm hi' h'').symm
        · exact Fin.ne_zero_of_lt h''
      rw [← i'.succ_pred h₂, ← i.castSucc_castPred h₁]
      have H : (i.castPred h₁).castSucc < i'.pred h₂ := by
        rcases (Nat.le_iff_lt_or_eq.mp h'') with h' | h'
        · simp only [Fin.lt_def, Fin.coe_castSucc, Nat.succ_eq_add_one, Fin.castSucc_castPred,
            Fin.coe_pred] at *
          exact Nat.lt_sub_of_add_lt h'
        · exfalso
          exact Fin.val_ne_of_ne h h'
      rw [δ_comp_σ_of_gt H]
      right
      use i.castPred h₁, i'.pred h₂

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
  | zero =>
    rw [switch_δ_σ₀]
    use mk 0, 𝟙 _, 𝟙 _, P_σ.id_mem _, P_δ.id_mem _
    simp
  | succ n =>
    obtain h | ⟨j, j', h⟩ := switch_δ_σ i i' <;> rw [h]
    · use mk (n + 1), 𝟙 _, 𝟙 _, P_σ.id_mem _, P_δ.id_mem _
      simp
    · use mk n, σ j, δ j', P_σ.σ _, P_δ.δ _

/-- An auxiliary lemma that shows there exists a factorization as a P_δ followed by a P_σ for
morphisms of the form `P_δ ≫ σ`. -/
private lemma factor_P_δ_σ {n : ℕ} (i : Fin (n + 1)) {x : SimplexCategoryGenRel}
    (f : x ⟶ mk (n + 1)) (hf : P_δ f) : ∃ (z : SimplexCategoryGenRel) (e : x ⟶ z) (m : z ⟶ mk n)
      (_ : P_σ e) (_ : P_δ m), f ≫ σ i = e ≫ m := by
  induction n using Nat.case_strong_induction_on generalizing x with
  | hz => cases hf with
    | of _ h => cases h; exact factor_δ_σ _ _
    | id  =>
      rw [Category.id_comp]
      use mk 0, σ i, 𝟙 _, P_σ.σ _, P_δ.id_mem _
      simp
    | comp_of j f hf hg =>
      cases hg
      obtain ⟨h', hf'⟩ | hf' := eq_or_len_le_of_P_δ hf
      · subst h'
        simp only [eqToHom_refl] at hf'
        subst hf'
        rw [Category.id_comp]
        exact factor_δ_σ _ _
      · simp at hf'
  | hi n h_rec =>
    cases hf with
    | of _ h => cases h; exact factor_δ_σ _ _
    | @id n =>
      rw [Category.id_comp]
      use mk (n + 1), σ i, 𝟙 _, P_σ.σ _, P_δ.id_mem _
      simp
    | comp_of f g hf hg =>
      obtain ⟨h', h''⟩ | h := eq_or_len_le_of_P_δ hf
      · subst h'
        cases hg
        rw [eqToHom_refl] at h''; subst h''
        rw [Category.id_comp]
        exact factor_δ_σ _ _
      · have hg' := hg
        rcases hg' with ⟨i'⟩
        obtain h' | ⟨j, j', h'⟩ := switch_δ_σ i i' <;> rw [Category.assoc, h']
        · rw [Category.comp_id]
          use x, 𝟙 x, f, P_σ.id_mem _, hf
          simp
        · rw [mk_len, Nat.lt_add_one_iff] at h
          obtain ⟨z, e, m₁, he, hm₁, h⟩ := h_rec n (Nat.le_refl _) j f hf
          rw [reassoc_of% h]
          use z, e, m₁ ≫ δ j', he, P_δ.comp_mem _ _ hm₁ (P_δ.δ _)

/-- Any morphism in `SimplexCategoryGenRel` can be decomposed as a `P_σ` followed by a `P_δ`. -/
theorem exists_P_σ_P_δ_factorization {x y : SimplexCategoryGenRel} (f : x ⟶ y) :
    ∃ (z : SimplexCategoryGenRel) (e : x ⟶ z) (m : z ⟶ y)
        (_ : P_σ e) (_ : P_δ m), f = e ≫ m := by
  induction f with
  | @id n => use (mk n), (𝟙 (mk n)), (𝟙 (mk n)), P_σ.id_mem _, P_δ.id_mem _; simp
  | @comp_δ n n' f j h =>
    obtain ⟨z, e, m, ⟨he, hm, h⟩⟩ := h
    rw [h, Category.assoc]
    use z, e, m ≫ δ j, he, P_δ.comp_mem _ _ hm (P_δ.δ _)
  | @comp_σ n n' f j h =>
    obtain ⟨z, e, m, ⟨he, hm, h⟩⟩ := h
    rw [h]
    cases hm with
    | of g hg =>
      cases hg
      rw [Category.assoc]
      obtain ⟨z₁, e₁, m₁, ⟨he₁, hm₁, h₁⟩⟩ := factor_δ_σ j _
      rw [h₁]
      use z₁, e ≫ e₁, m₁, P_σ.comp_mem _ _ he he₁, hm₁
      simp
    | @id n =>
      simp only [Category.comp_id]
      use mk n', e ≫ σ j, 𝟙 _, P_σ.comp_mem _ _ he (P_σ.σ _), P_δ.id_mem _
      simp
    | comp_of f g hf hg =>
      rw [Category.assoc, Category.assoc]
      cases n' with
      | zero =>
        cases hg
        rw [switch_δ_σ₀, Category.comp_id]
        use z, e, f, he, hf
      | succ n =>
        have hg' := hg
        rcases hg' with ⟨i⟩
        obtain h' | ⟨j', j'', h'⟩ := switch_δ_σ j i <;> rw [h']
        · rw [Category.comp_id]
          use z, e, f, he, hf
        · obtain ⟨z₁, e₁, m₁, ⟨he₁, hm₁, h₁⟩⟩ := factor_P_δ_σ j' f hf
          rw [reassoc_of% h₁]
          use z₁, e ≫ e₁, m₁ ≫ δ j'', P_σ.comp_mem _ _ he he₁, P_δ.comp_mem _ _ hm₁ (P_δ.δ _)
          simp

instance : MorphismProperty.HasFactorization P_σ P_δ where
  nonempty_mapFactorizationData f := by
    obtain ⟨z, e , m, he, hm, fac⟩ := exists_P_σ_P_δ_factorization f
    exact ⟨⟨z, e , m, fac.symm, he, hm⟩⟩

end ExistenceOfFactorizations

end SimplexCategoryGenRel
