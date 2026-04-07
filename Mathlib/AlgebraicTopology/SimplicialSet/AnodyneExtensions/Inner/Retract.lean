/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!

The first half of the proof of `007F`.

-/

universe w u

namespace SSet

open CategoryTheory Simplicial MonoidalCategory Limits Functor SimplexCategory

variable {n : ℕ} (i : Fin (n + 1))

-- [n] ⟶ [2] by j ↦
-- 0 if j < i
-- 1 if j = i
-- 2 if j > i
@[simp]
def s_aux : Fin (n + 1) →o Fin 3 where
  toFun j := if j < i then 0 else if j = i then 1 else 2
  monotone' _ := by grind

-- on vertices j maps to
-- (j, 0) if j < i
-- (j, 1) if j = i
-- (j, 2) if j > i
@[simp]
def s : Δ[n] ⟶ Δ[2] ⊗ Δ[n] :=
  CartesianMonoidalCategory.lift (stdSimplex.map (mkHom (s_aux i))) (𝟙 _)

@[simp]
def s_restricted :
    Λ[n, i].toSSet ⟶ Δ[2] ⊗ Λ[n, i] :=
  CartesianMonoidalCategory.lift (Λ[n, i].ι ≫ stdSimplex.map (mkHom (s_aux i))) (𝟙 _)

@[simp]
noncomputable
def horn_to_pushout :
    Λ[n, i].toSSet ⟶ (PushoutObjObj.ofHasPushout (curriedTensor SSet) Λ[2, 1].ι Λ[n, i].ι).pt :=
  s_restricted i ≫ pushout.inl _ _

@[simp]
def r_aux : Fin 3 × Fin (n + 1) →o Fin (n + 1) where
  toFun := fun ⟨k, j⟩ ↦ if (j < i ∧ k = 0) ∨ (j > i ∧ k = 2) then j else i
  monotone' := by
    intro ⟨k, j⟩ ⟨k', j'⟩ ⟨hk, hj⟩
    grind

@[simps]
def map_mk_from_prod {n m k : ℕ} (f : Fin (n + 1) × Fin (m + 1) →o Fin (k + 1)) :
    Δ[n] ⊗ Δ[m] ⟶ Δ[k] := by
  refine ⟨fun x ⟨c, d⟩ ↦
    ⟨mkHom ⟨fun a ↦ f ((stdSimplex.asOrderHom c) a, (stdSimplex.asOrderHom d) a), ?_⟩⟩, ?_⟩
  · intro j k hjk
    exact f.monotone ⟨OrderHom.monotone _ hjk, OrderHom.monotone _ hjk⟩
  · cat_disch

-- on vertices j k map to
-- j if (j < i) ∧ (k = 0)
-- j if (j > i) ∧ (k = 2)
-- i if (j = i) ∨ (k = 1)
@[simp]
def r : Δ[2] ⊗ Δ[n] ⟶ Δ[n] := map_mk_from_prod (r_aux i)

variable (h0 : 0 < i) (hn : i < Fin.last n)

#check Subcomplex.lift (r i)


-- r restricted along Λ[2, 1]
@[simp]
noncomputable
def r_restrict_horn_2 : (Λ[2, 1] : SSet) ⊗ Δ[n] ⟶ Λ[n, i] := by
  refine Subcomplex.lift (Λ[2, 1].ι ▷ Δ[n] ≫ r i) ?_
  rintro k _ ⟨⟨⟨x, hx⟩, y⟩, rfl⟩
  change _ ≠ _ at hx ⊢
  rw [Set.ne_univ_iff_exists_notMem] at hx ⊢
  obtain ⟨a, ha⟩ := hx
  fin_cases a
  · use 0
    simp [Fin.ne_of_lt h0]
    intro j h
    change (if _ < i ∧ _ = 0 ∨ i < _ ∧ _ = 2 then _ else i) = _ at h
    grind
  · grind
  · use Fin.last n
    simp [Fin.ne_of_gt hn]
    intro j h
    change (if _ < i ∧ _ = 0 ∨ i < _ ∧ _ = 2 then _ else i) = _ at h
    grind

-- r restricted along Λ[n, i].toSSet
@[simp]
noncomputable
def r_restrict_horn_n : Δ[2] ⊗ Λ[n, i] ⟶ Λ[n, i] := by
  refine Subcomplex.lift (Δ[2] ◁ Λ[n, i].ι ≫ r i) ?_
  rintro k _ ⟨⟨x, ⟨y, hy⟩⟩, rfl⟩
  change _ ≠ _ at hy ⊢
  rw [Set.ne_univ_iff_exists_notMem] at hy ⊢
  obtain ⟨a, ha⟩ := hy
  use a
  rintro ⟨l, h⟩
  ·
    sorry
  · grind

/-
where
  app k := by
    intro ⟨x, ⟨y, hy⟩⟩
    refine ⟨(Δ[2] ◁ Λ[n, i].ι ≫ r i).app k ⟨x, ⟨y, hy⟩⟩, ?_⟩
    change _ ≠ _ at hy ⊢
    rw [Set.ne_univ_iff_exists_notMem] at hy ⊢
    obtain ⟨a, ha⟩ := hy
    use a
    intro h
    simp at h ha
    obtain ⟨ha₁, ha₂⟩ := ha
    cases h
    · omega
    · next h =>
      obtain ⟨j, hj⟩ := h
      apply ha₂ j
      change (if _ < i ∧ _ = 0 ∨ i < _ ∧ _ = 2 then _ else i) = _ at hj
      aesop
-/

open stdSimplex SimplexCategory in
@[simp]
noncomputable
def pushout_to_horn : (PushoutObjObj.ofHasPushout (curriedTensor SSet) Λ[2, 1].ι Λ[n, i].ι).pt ⟶
    Λ[n, i] :=
  pushout.desc (r_restrict_horn_n i) (r_restrict_horn_2 i h0 hn) rfl

lemma r_aux_comp_s_aux_prod_id :
    OrderHom.comp (r_aux i) ((s_aux i).prod (OrderHom.id)) = OrderHom.id := by
  ext
  simp
  grind

lemma r_comp_s : s i ≫ r i = 𝟙 Δ[n] := by
  change stdSimplex.map (mkHom ((r_aux i).comp ((s_aux i).prod OrderHom.id))) = _
  rw [r_aux_comp_s_aux_prod_id]
  exact stdSimplex.map_id ⦋n⦌

lemma restricted_r_comp_s : horn_to_pushout i ≫ pushout_to_horn i h0 hn = 𝟙 Λ[n, i].toSSet := by
  ext
  simp
  cat_disch

attribute [local simp] PushoutObjObj.ofHasPushout_ι

set_option backward.isDefEq.respectTransparency false in
open CartesianMonoidalCategory in
noncomputable
instance hornRetract : RetractArrow Λ[n, i].ι
    (PushoutObjObj.ofHasPushout (curriedTensor SSet) Λ[2, 1].ι Λ[n, i].ι).ι where
  i := {
    left := lift (Λ[n, i].ι ≫ stdSimplex.map (mkHom (s_aux i))) (𝟙 _) ≫ pushout.inl _ _
    right := lift (stdSimplex.map (mkHom (s_aux i))) (𝟙 _)
  }
  r := {
    left := pushout_to_horn i h0 hn
    right := r i
    w := pushout.hom_ext (by cat_disch) (by cat_disch)
  }
  retract := Arrow.hom_ext _ _ (restricted_r_comp_s i h0 hn) (r_comp_s i)

end SSet
