/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

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
lemma degenerate_zero : X.degenerate 0 = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨m, hm, _⟩
  simp at hm

@[simp]
lemma nondegenerate_zero : X.nonDegenerate 0 = Set.univ := by
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
  ⟨n, by cutsat, SimplexCategory.σ i, Set.mem_range_self x⟩

lemma mem_degenerate_iff (x : X _⦋n⦌) :
    x ∈ X.degenerate n ↔ ∃ (m : ℕ) (_ : m < n) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f),
        x ∈ Set.range (X.map f.op) := by
  constructor
  · rintro ⟨m, hm, f, y, hy⟩
    rw [← image.fac f, op_comp] at hy
    have : _ ≤ m := SimplexCategory.len_le_of_mono (image.ι f)
    exact ⟨(image f).len, by cutsat, factorThruImage f, inferInstance, by aesop⟩
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
      cutsat)
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

lemma mono_of_nonDegenerate (x : X.nonDegenerate n)
    {m : SimplexCategory} (f : ⦋n⦌ ⟶ m)
    (y : X.obj (op m)) (hy : X.map f.op y = x) :
    Mono f := by
  have := X.isIso_of_nonDegenerate x (factorThruImage f) (y := X.map (image.ι f).op y) (by
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, image.fac f, hy])
  rw [← image.fac f]
  infer_instance

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
    suffices y₂ ≤ y₁ by simp [show y₁ = y₂ by cutsat] at h'
    simpa only [hα₁] using f₁.toOrderHom.monotone h'.le
  exact ⟨{ section_ := SimplexCategory.Hom.mk ⟨α, hα₂⟩, id := by ext : 3; apply hα₁ },
    by simp [α]⟩

end

namespace Subcomplex

variable {X} (A : X.Subcomplex)

lemma mem_degenerate_iff {n : ℕ} (x : A.obj (op ⦋n⦌)) :
    x ∈ degenerate A n ↔ x.val ∈ X.degenerate n := by
  rw [SSet.mem_degenerate_iff, SSet.mem_degenerate_iff]
  constructor
  · rintro ⟨m, hm, f, _, y, rfl⟩
    exact ⟨m, hm, f, inferInstance, y.val, rfl⟩
  · obtain ⟨x, hx⟩ := x
    rintro ⟨m, hm, f, _, ⟨y, rfl⟩⟩
    refine ⟨m, hm, f, inferInstance, ⟨y, ?_⟩, rfl⟩
    have := isSplitEpi_of_epi f
    simpa [Set.mem_preimage, ← op_comp, ← FunctorToTypes.map_comp_apply,
      IsSplitEpi.id, op_id, FunctorToTypes.map_id_apply] using A.map (section_ f).op hx

lemma mem_nonDegenerate_iff {n : ℕ} (x : A.obj (op ⦋n⦌)) :
    x ∈ nonDegenerate A n ↔ x.val ∈ X.nonDegenerate n := by
  rw [mem_nonDegenerate_iff_notMem_degenerate,
    mem_nonDegenerate_iff_notMem_degenerate, mem_degenerate_iff]

lemma le_iff_contains_nonDegenerate (B : X.Subcomplex) :
    A ≤ B ↔ ∀ (n : ℕ) (x : X.nonDegenerate n), x.val ∈ A.obj _ → x.val ∈ B.obj _ := by
  constructor
  · aesop
  · rintro h ⟨n⟩ x hx
    induction n using SimplexCategory.rec with | _ n =>
    obtain ⟨m, f, _, ⟨a, ha⟩, ha'⟩ := exists_nonDegenerate A ⟨x, hx⟩
    simp only [Subpresheaf.toPresheaf_obj, Subtype.ext_iff,
      Subpresheaf.toPresheaf_map_coe] at ha'
    subst ha'
    rw [mem_nonDegenerate_iff] at ha
    exact B.map f.op (h _ ⟨_, ha⟩ a.prop)

lemma eq_top_iff_contains_nonDegenerate :
    A = ⊤ ↔ ∀ (n : ℕ), X.nonDegenerate n ⊆ A.obj _ := by
  simpa using le_iff_contains_nonDegenerate ⊤ A

lemma degenerate_eq_top_iff (n : ℕ) :
    degenerate A n = ⊤ ↔ (X.degenerate n ⊓ A.obj _) = A.obj _ := by
  constructor
  · intro h
    ext x
    simp only [Set.inf_eq_inter, Set.mem_inter_iff, and_iff_right_iff_imp]
    intro hx
    simp [← A.mem_degenerate_iff ⟨x, hx⟩, h, Set.top_eq_univ, Set.mem_univ]
  · intro h
    simp only [Set.inf_eq_inter, Set.inter_eq_right] at h
    ext x
    simpa [A.mem_degenerate_iff] using h x.prop

variable (X) in
lemma iSup_ofSimplex_nonDegenerate_eq_top :
    ⨆ (x : Σ (p : ℕ), X.nonDegenerate p), ofSimplex x.2.val = ⊤ := by
  rw [eq_top_iff_contains_nonDegenerate]
  intro n x hx
  simp only [Subpresheaf.iSup_obj, Set.mem_iUnion, Sigma.exists,
    Subtype.exists, exists_prop]
  exact ⟨n, x, hx, mem_ofSimplex_obj x⟩

end Subcomplex

section

variable {X} {Y : SSet.{u}}

lemma degenerate_app_apply {n : ℕ} {x : X _⦋n⦌} (hx : x ∈ X.degenerate n) (f : X ⟶ Y) :
    f.app _ x ∈ Y.degenerate n := by
  obtain ⟨m, hm, g, y, rfl⟩ := hx
  exact ⟨m, hm, g, f.app _ y, by rw [FunctorToTypes.naturality]⟩

lemma degenerate_le_preimage (f : X ⟶ Y) (n : ℕ) :
    X.degenerate n ⊆ (f.app _)⁻¹' (Y.degenerate n) :=
  fun _ hx ↦ degenerate_app_apply hx f

lemma image_degenerate_le (f : X ⟶ Y) (n : ℕ) :
    (f.app _)'' (X.degenerate n) ⊆ Y.degenerate n := by
  simpa using degenerate_le_preimage f n

lemma degenerate_iff_of_isIso (f : X ⟶ Y) [IsIso f] {n : ℕ} (x : X _⦋n⦌) :
    f.app _ x ∈ Y.degenerate n ↔ x ∈ X.degenerate n := by
  constructor
  · intro hy
    simpa [← FunctorToTypes.comp] using degenerate_app_apply hy (inv f)
  · exact fun hx ↦ degenerate_app_apply hx f

lemma nonDegenerate_iff_of_isIso (f : X ⟶ Y) [IsIso f] {n : ℕ} (x : X _⦋n⦌) :
    f.app _ x ∈ Y.nonDegenerate n ↔ x ∈ X.nonDegenerate n := by
  simp [mem_nonDegenerate_iff_notMem_degenerate,
    degenerate_iff_of_isIso]

attribute [local simp] nonDegenerate_iff_of_isIso in
/-- The bijection on nondegenerate simplices induced by an isomorphism
of simplicial sets. -/
@[simps]
def nonDegenerateEquivOfIso (e : X ≅ Y) {n : ℕ} :
    X.nonDegenerate n ≃ Y.nonDegenerate n where
  toFun := fun ⟨x, hx⟩ ↦ ⟨e.hom.app _ x, by aesop⟩
  invFun := fun ⟨y, hy⟩ ↦ ⟨e.inv.app _ y, by aesop⟩
  left_inv _ := by aesop
  right_inv _ := by aesop

end

variable {X} in
lemma degenerate_iff_of_mono {Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (x : X _⦋n⦌) :
    f.app _ x ∈ Y.degenerate n ↔ x ∈ X.degenerate n := by
  rw [← degenerate_iff_of_isIso (Subcomplex.toRange f) x,
    Subcomplex.mem_degenerate_iff]
  simp

variable {X} in
lemma nonDegenerate_iff_of_mono {Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (x : X _⦋n⦌) :
    f.app _ x ∈ Y.nonDegenerate n ↔ x ∈ X.nonDegenerate n := by
  simp [mem_nonDegenerate_iff_notMem_degenerate, degenerate_iff_of_mono]

end SSet
