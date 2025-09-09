/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# Degenerate simplices

Given a simplicial set `X` and `n : ℕ`, we define the sets `X.degenerate n`
and `X.nonDegenerate n` of degenerate or non-degenerate simplices of dimension `n`.

Any simplex `x : X _⦋n⦌` can be written in a unique way as `X.map f.op y`
for an epimorphism `f : ⦋n⦌ ⟶ ⦋m⦌` and a non-degenerate `m`-simplex `y`
(see lemmas `exists_nonDegenerate`, `unique_nonDegenerate_dim`,
`unique_nonDegenerate_simplex` and `unique_nonDegenerate_map`).

-/

universe u

open CategoryTheory Simplicial Limits Opposite

namespace SSet

variable (X : SSet.{u})

/-- An `n`-simplex of a simplicial set `X` is degenerate if it is in the range
of `X.map f.op` for some morphism `f : [n] ⟶ [m]` with `m < n`. -/
def degenerate (n : ℕ) : Set (X _⦋n⦌) :=
  setOf (fun x ↦ ∃ (m : ℕ) (_ : m < n) (f : ⦋n⦌ ⟶ ⦋m⦌),
    x ∈ Set.range (X.map f.op))

/-- The set of `n`-dimensional non-degenerate simplices in a simplicial
set `X` is the complement of `X.degenerate n`. -/
def nonDegenerate (n : ℕ) : Set (X _⦋n⦌) := (X.degenerate n)ᶜ

@[simp]
lemma degenerate_zero : X.degenerate 0 = ⊥ := by
  ext x
  simp only [Set.bot_eq_empty, Set.mem_empty_iff_false, iff_false]
  rintro ⟨m, hm, _⟩
  simp at hm

@[simp]
lemma nondegenerate_zero : X.nonDegenerate 0 = ⊤ := by
  simp [nonDegenerate]

variable {n : ℕ}

lemma mem_nonDegenerate_iff_notMem_degenerate (x : X _⦋n⦌) :
    x ∈ X.nonDegenerate n ↔ x ∉ X.degenerate n := Iff.rfl

@[deprecated (since := "2025-05-23")]
alias mem_nonDegenerate_iff_not_mem_degenerate := mem_nonDegenerate_iff_notMem_degenerate

lemma mem_degenerate_iff_notMem_nonDegenerate (x : X _⦋n⦌) :
    x ∈ X.degenerate n ↔ x ∉ X.nonDegenerate n := by
  simp [nonDegenerate]

@[deprecated (since := "2025-05-23")]
alias mem_degenerate_iff_not_mem_nonDegenerate := mem_degenerate_iff_notMem_nonDegenerate

lemma σ_mem_degenerate (i : Fin (n + 1)) (x : X _⦋n⦌) :
    X.σ i x ∈ X.degenerate (n + 1) :=
  ⟨n, by grind, SimplexCategory.σ i, Set.mem_range_self x⟩

lemma mem_degenerate_iff (x : X _⦋n⦌) :
    x ∈ X.degenerate n ↔ ∃ (m : ℕ) (_ : m < n) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f),
        x ∈ Set.range (X.map f.op) := by
  constructor
  · rintro ⟨m, hm, f, y, hy⟩
    rw [← image.fac f, op_comp] at hy
    have : _ ≤ m := SimplexCategory.len_le_of_mono (image.ι f)
    exact ⟨(image f).len, by grind, factorThruImage f, inferInstance, by aesop⟩
  · rintro ⟨m, hm, f, hf, hx⟩
    exact ⟨m, hm, f, hx⟩

lemma degenerate_eq_iUnion_range_σ :
    X.degenerate (n + 1) = ⋃ (i : Fin (n + 1)), Set.range (X.σ i) := by
  ext x
  constructor
  · intro hx
    rw [mem_degenerate_iff] at hx
    obtain ⟨m, hm, f, hf, y, rfl⟩ := hx
    obtain ⟨i, θ, rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective f (fun hf ↦ by
      rw [← SimplexCategory.mono_iff_injective] at hf
      have := SimplexCategory.le_of_mono f
      grind)
    aesop
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨i, y, rfl⟩ := hx
    apply σ_mem_degenerate

lemma exists_nonDegenerate (x : X _⦋n⦌) :
    ∃ (m : ℕ) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f)
      (y : X.nonDegenerate m), x = X.map f.op y := by
  induction n with
  | zero =>
      exact ⟨0, 𝟙 _, inferInstance, ⟨x, by simp⟩, by simp⟩
  | succ n hn =>
      by_cases hx : x ∈ X.nonDegenerate (n + 1)
      · exact ⟨n + 1, 𝟙 _, inferInstance, ⟨x, hx⟩, by simp⟩
      · simp only [← mem_degenerate_iff_notMem_nonDegenerate,
          degenerate_eq_iUnion_range_σ, Set.mem_iUnion, Set.mem_range] at hx
        obtain ⟨i, y, rfl⟩ := hx
        obtain ⟨m, f, hf, z, rfl⟩ := hn y
        exact ⟨_, SimplexCategory.σ i ≫ f, inferInstance, z, by simp; rfl⟩

lemma isIso_of_nonDegenerate (x : X.nonDegenerate n)
    {m : SimplexCategory} (f : ⦋n⦌ ⟶ m) [Epi f]
    (y : X.obj (op m)) (hy : X.map f.op y = x) :
    IsIso f := by
  obtain ⟨x, hx⟩ := x
  induction m using SimplexCategory.rec with | _ m
  rw [mem_nonDegenerate_iff_notMem_degenerate] at hx
  by_contra!
  refine hx ⟨_, not_le.1 (fun h ↦ this ?_), f, y, hy⟩
  rw [SimplexCategory.isIso_iff_of_epi]
  exact le_antisymm h (SimplexCategory.len_le_of_epi f)

namespace unique_nonDegenerate

/-!
Auxiliary definitions and lemmas for the lemmas
`unique_nonDegenerate_dim`, `unique_nonDegenerate_simplex` and
`unique_nonDegenerate_map` which assert the uniqueness of the
decomposition obtained in the lemma `exists_nonDegenerate`.
-/

section

variable {X} {x : X _⦋n⦌}
  {m₁ m₂ : ℕ} {f₁ : ⦋n⦌ ⟶ ⦋m₁⦌} (hf₁ : SplitEpi f₁)
  (y₁ : X.nonDegenerate m₁) (hy₁ : x = X.map f₁.op y₁)
  (f₂ : ⦋n⦌ ⟶ ⦋m₂⦌) (y₂ : X _⦋m₂⦌) (hy₂ : x = X.map f₂.op y₂)

/-- The composition of a section of `f₁` and `f₂`. It is proven below that it
is the identity, see `g_eq_id`. -/
private def g := hf₁.section_ ≫ f₂

variable {f₂ y₁ y₂}

include hf₁ hy₁ hy₂

private lemma map_g_op_y₂ : X.map (g hf₁ f₂).op y₂ = y₁ := by
  dsimp [g]
  rw [FunctorToTypes.map_comp_apply, ← hy₂, hy₁, ← FunctorToTypes.map_comp_apply, ← op_comp,
    SplitEpi.id, op_id, FunctorToTypes.map_id_apply]

private lemma isIso_factorThruImage_g :
    IsIso (factorThruImage (g hf₁ f₂)) := by
  have := map_g_op_y₂ hf₁ hy₁ hy₂
  rw [← image.fac (g hf₁ f₂), op_comp, FunctorToTypes.map_comp_apply] at this
  exact X.isIso_of_nonDegenerate y₁ (factorThruImage (g hf₁ f₂)) _ this

private lemma mono_g : Mono (g hf₁ f₂) := by
  have := isIso_factorThruImage_g hf₁ hy₁ hy₂
  rw [← image.fac (g hf₁ f₂)]
  infer_instance

private lemma le : m₁ ≤ m₂ :=
  have := isIso_factorThruImage_g hf₁ hy₁ hy₂
  SimplexCategory.len_le_of_mono
    (factorThruImage (g hf₁ f₂) ≫ image.ι _)

end

variable {X} in
private lemma g_eq_id {x : X _⦋n⦌} {m : ℕ} {f₁ : ⦋n⦌ ⟶ ⦋m⦌}
    {y₁ : X.nonDegenerate m} (hy₁ : x = X.map f₁.op y₁)
    {f₂ : ⦋n⦌ ⟶ ⦋m⦌} {y₂ : X _⦋m⦌} (hy₂ : x = X.map f₂.op y₂) (hf₁ : SplitEpi f₁) :
    g hf₁ f₂ = 𝟙 _ := by
  have := mono_g hf₁ hy₁ hy₂
  apply SimplexCategory.eq_id_of_mono

end unique_nonDegenerate

section

open unique_nonDegenerate

/-!
The following lemmas `unique_nonDegenerate_dim`, `unique_nonDegenerate_simplex` and
`unique_nonDegenerate_map` assert the uniqueness of the decomposition
obtained in the lemma `exists_nonDegenerate`.
-/

lemma unique_nonDegenerate_dim (x : X _⦋n⦌) {m₁ m₂ : ℕ}
    (f₁ : ⦋n⦌ ⟶ ⦋m₁⦌) [Epi f₁] (y₁ : X.nonDegenerate m₁) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ⦋n⦌ ⟶ ⦋m₂⦌) [Epi f₂] (y₂ : X.nonDegenerate m₂) (hy₂ : x = X.map f₂.op y₂) :
    m₁ = m₂ := by
  obtain ⟨⟨hf₁⟩⟩ := isSplitEpi_of_epi f₁
  obtain ⟨⟨hf₂⟩⟩ := isSplitEpi_of_epi f₂
  exact le_antisymm (le hf₁ hy₁ hy₂) (le hf₂ hy₂ hy₁)

lemma unique_nonDegenerate_simplex (x : X _⦋n⦌) {m : ℕ}
    (f₁ : ⦋n⦌ ⟶ ⦋m⦌) [Epi f₁] (y₁ : X.nonDegenerate m) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ⦋n⦌ ⟶ ⦋m⦌) (y₂ : X.nonDegenerate m) (hy₂ : x = X.map f₂.op y₂) :
    y₁ = y₂ := by
  obtain ⟨⟨hf₁⟩⟩ := isSplitEpi_of_epi f₁
  ext
  simpa [g_eq_id hy₁ hy₂ hf₁] using (map_g_op_y₂ hf₁ hy₁ hy₂).symm

lemma unique_nonDegenerate_map (x : X _⦋n⦌) {m : ℕ}
    (f₁ : ⦋n⦌ ⟶ ⦋m⦌) [Epi f₁] (y₁ : X.nonDegenerate m) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ⦋n⦌ ⟶ ⦋m⦌) (y₂ : X.nonDegenerate m) (hy₂ : x = X.map f₂.op y₂) :
    f₁ = f₂ := by
  ext x : 3
  suffices ∃ (hf₁ : SplitEpi f₁), hf₁.section_.toOrderHom (f₁.toOrderHom x) = x by
    obtain ⟨hf₁, hf₁'⟩ := this
    dsimp at hf₁'
    simpa [g, hf₁'] using (SimplexCategory.congr_toOrderHom_apply (g_eq_id hy₁ hy₂ hf₁)
      (f₁.toOrderHom x)).symm
  obtain ⟨⟨hf⟩⟩ := isSplitEpi_of_epi f₁
  let α (y : Fin (m + 1)) : Fin (n + 1) :=
    if y = f₁.toOrderHom x then x else hf.section_.toOrderHom y
  have hα₁ (y : Fin (m + 1)) : f₁.toOrderHom (α y) = y := by
    dsimp [α]
    split_ifs with hy
    · rw [hy]
    · apply SimplexCategory.congr_toOrderHom_apply hf.id
  have hα₂ : Monotone α := by
    rintro y₁ y₂ h
    by_contra! h'
    suffices y₂ ≤ y₁ by simp [show y₁ = y₂ by omega] at h'
    simpa only [hα₁] using f₁.toOrderHom.monotone h'.le
  exact ⟨{ section_ := SimplexCategory.Hom.mk ⟨α, hα₂⟩, id := by ext : 3; apply hα₁ },
    by simp [α]⟩

end

end SSet
