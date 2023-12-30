/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Mathlib.AlgebraicTopology.ForMathlib
import Mathlib.AlgebraicTopology.Quasicategory

/-!
# Kan complexes and quasicategories

-/

universe v u

open CategoryTheory Simplicial Opposite

namespace SSet

def horn.face {n : ℕ} (i j : Fin (n+2)) (h : j ≠ i) : Λ[n+1, i] _[n] := by
  refine ⟨SimplexCategory.δ j, ?_⟩
  simpa only [unop_op, SimplexCategory.len_mk, asOrderHom, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe, Set.union_singleton, ne_eq,
    ← Set.univ_subset_iff, Set.subset_def, Set.mem_univ, Set.mem_insert_iff, Set.mem_range,
    Fin.succAboveEmb_apply, Fin.exists_succAbove_eq_iff, forall_true_left, not_forall, not_or,
    not_not, exists_eq_right]

open SimplicialObject SimplexCategory in
lemma quasicategory_of_filler (S : SSet)
    (H : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (σ₀ : Λ[n+2, i] ⟶ S) (_h0 : 0 < i) (_hn : i < Fin.last (n+2)),
      ∃ σ : S _[n+2], ∀ (j) (h : j ≠ i),
        S.δ j σ = σ₀.app _ (horn.face i j h)) :
    Quasicategory S where
  hornFilling' n i σ₀ h₀ hₙ := by
    obtain ⟨σ, h⟩ := H σ₀ h₀ hₙ
    use yonedaEquiv.symm σ
    apply NatTrans.ext; apply funext
    apply Opposite.rec
    apply SimplexCategory.rec
    intro m; ext f
    obtain ⟨j, hj₁, hj₂⟩ : ∃ j, ¬j = i ∧ ∀ (k : Fin (m+1)), f.1.toOrderHom k ≠ j
    · simpa [← Set.univ_subset_iff, Set.subset_def, asOrderHom, not_or] using f.2
    specialize h j hj₁
    obtain ⟨g, hg⟩ : ∃ g, f.1 = g ≫ SimplexCategory.δ j := by
      let g : ([m] : SimplexCategory) ⟶ [n+1] := f.1 ≫ SimplexCategory.σ (Fin.predAbove 0 j)
      use g
      apply Hom.ext
      ext k : 2
      specialize hj₂ k
      rw [Ne.def, Fin.ext_iff] at hj₂
      dsimp [SimplexCategory.δ, SimplexCategory.σ, Fin.succAbove, Fin.predAbove]
      split <;> rename_i h0j
      all_goals
      · split <;> rename_i hjk <;>
        simp only [Fin.lt_iff_val_lt_val, Fin.val_zero, Fin.coe_castSucc, Fin.coe_pred] at h0j hjk
        · simp only [Fin.coe_pred, Fin.succ_pred]
          symm
          apply dif_neg
          omega
        · simp only [Fin.coe_castLT, Fin.castSucc_castLT]
          symm
          apply dif_pos
          omega

    have H : f = (Λ[n+2, i].map g.op) (horn.face i j hj₁) := by
      apply Subtype.ext; exact hg
    have := σ₀.naturality g.op
    rw [Function.funext_iff] at this
    specialize this (horn.face i j hj₁)
    dsimp at this
    erw [H, this, ← h, NatTrans.comp_app]
    have := (S.map_comp (SimplexCategory.δ j).op g.op).symm
    rw [Function.funext_iff] at this
    apply this

section nerve

variable {C : Type} [inst : Category C]

-- TODO: move
/-- A constructor for `n`-simplices of the nerve of a category,
by specifying `n+1` objects and a morphism between each of the `n` pairs of adjecent objects. -/
noncomputable
def nerve.mk (n : ℕ)
    (obj : Fin (n+1) → C) (mor : ∀ (i : Fin n), obj i.castSucc ⟶ obj i.succ) :
    (nerve C).obj (op [n]) :=
  ComposableArrows.mkOfObjOfMapSucc obj mor

def nerve.δ_mor (n : ℕ)
    (obj : Fin (n+2) → C) (mor : ∀ (i : Fin (n+1)), obj i.castSucc ⟶ obj i.succ)
    (j : Fin (n+2)) (k : Fin n) :
    obj (Fin.succAbove j k.castSucc) ⟶ obj (Fin.succAbove j k.succ) :=
  if hkj : k.val + 1 < j.val
  then by
    refine eqToHom (congrArg _ ?_) ≫ mor k.castSucc ≫ eqToHom (congrArg _ ?_)
    · have : k.val < j.val := by linarith only [hkj]
      simp [Fin.succAbove, this]
    · ext; simp [Fin.succAbove, hkj]
  else if hkj' : k.val + 1 = j.val
  then by
    refine eqToHom (congrArg _ ?_) ≫ mor k.castSucc ≫ mor k.succ ≫ eqToHom (congrArg _ ?_)
    · simp [Fin.succAbove, hkj'.symm]
    · simp [Fin.succAbove, hkj'.symm]
  else by
    refine eqToHom (congrArg _ ?_) ≫ mor k.succ ≫ eqToHom (congrArg _ ?_)
    · have : ¬ k.val < j.val := by omega
      ext; simp [Fin.succAbove, this]
    · have : ¬ k.val + 1 < j.val := by omega
      ext; simp [Fin.succAbove, this]

lemma nerve.δ_mk (n : ℕ)
    (obj : Fin (n+2) → C) (mor : ∀ (i : Fin (n+1)), obj i.castSucc ⟶ obj i.succ)
    (j : Fin (n+2)) :
    (nerve C).δ j (nerve.mk (n+1) obj mor) =
      nerve.mk n (obj ∘ Fin.succAbove j) (nerve.δ_mor n obj mor j) :=
  ComposableArrows.ext (fun _ ↦ rfl) <| by
  dsimp [SimplicialObject.δ, mk, nerve, unop_op, Monotone.functor]
  simp only [Category.comp_id, Category.id_comp]
  intro i hi
  symm
  rw [← ComposableArrows.map'_def _ i (i+1) (by omega) (by omega),
      ComposableArrows.mkOfObjOfMapSucc_map_succ (hi := hi)]
  dsimp only [δ_mor]
  by_cases hij : i + 1 < j
  · simp only [hij, unop_op, SimplexCategory.len_mk, Fin.castSucc_mk, Fin.succ_mk, dite_true]
    have aux := (ComposableArrows.mkOfObjOfMapSucc obj mor).map'_def i (i+1) (by omega) (by omega)
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ obj mor i (by omega)] at aux
    have := (ComposableArrows.mkOfObjOfMapSucc obj mor).map_eqToHom
    rw [← this, ← this, aux, ← Functor.map_comp, ← Functor.map_comp]
    rfl
    · have : i < j.val := by linarith only [hij]
      simp [Fin.succAbove, this]
    · ext; simp [Fin.succAbove, hij]
  rw [dif_neg hij]
  by_cases hij' : i + 1 = j
  · simp only [hij', unop_op, SimplexCategory.len_mk, Fin.castSucc_mk, Fin.succ_mk, dite_true]
    have aux1 := (ComposableArrows.mkOfObjOfMapSucc obj mor).map'_def i (i+1) (by omega) (by omega)
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ obj mor i (by omega)] at aux1
    have aux2 := (ComposableArrows.mkOfObjOfMapSucc obj mor).map'_def (i+1) (i+2) (by omega) (by omega)
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ obj mor (i+1) (by omega)] at aux2
    have := (ComposableArrows.mkOfObjOfMapSucc obj mor).map_eqToHom
    rw [← this, ← this, aux1, aux2, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    rfl
    · simp [Fin.succAbove, hij'.symm]
    · simp [Fin.succAbove, hij'.symm]
  rw [dif_neg hij']
  · simp only [unop_op, SimplexCategory.len_mk, Fin.castSucc_mk, Fin.succ_mk, dite_true]
    have aux := (ComposableArrows.mkOfObjOfMapSucc obj mor).map'_def (i+1) (i+2) (by omega) (by omega)
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ obj mor (i+1) (by omega)] at aux
    have := (ComposableArrows.mkOfObjOfMapSucc obj mor).map_eqToHom
    rw [← this, ← this, aux, ← Functor.map_comp, ← Functor.map_comp]
    rfl
    · have : ¬ i < j.val := by omega
      ext; simp [Fin.succAbove, this]
    · have : ¬ i + 1 < j.val := by omega
      ext; simp [Fin.succAbove, this]

-- TODO: move
def nerve.source (f : (nerve C) _[1]) : C := f.obj (0 : Fin 2)

-- TODO: move
def nerve.target (f : (nerve C) _[1]) : C := f.obj (1 : Fin 2)

-- TODO: move
def nerve.arrow (f : (nerve C) _[1]) : source f ⟶ target f :=
  f.map' 0 1 zero_le_one le_rfl

-- TODO: move
open SimplexCategory in
lemma nerve.source_eq (f : (nerve C) _[1]) :
    source f = ((nerve C).map (δ (1 : Fin 2)).op f).obj (0 : Fin 1) := rfl

-- TODO: move
open SimplexCategory in
lemma nerve.target_eq (f : (nerve C) _[1]) :
    target f = ((nerve C).map (δ (0 : Fin 2)).op f).obj (0 : Fin 1) := rfl

open SimplexCategory in
def horn.vertex (n : ℕ) (i k : Fin (n+3)) : Λ[n+2, i] _[0] := by
  refine ⟨Hom.mk ⟨Function.const _ k, fun _ _ _ ↦ le_rfl⟩, ?_⟩
  suffices ∃ x, ¬x = i ∧ ¬k = x by
    simpa [← Set.univ_subset_iff, Set.subset_def, asOrderHom, not_or, Fin.forall_fin_one]
  by_cases hi0 : i = 0
  · by_cases hk1 : k = 1
    · use Fin.last (n+2)
      simp [hi0, hk1, Fin.ext_iff, @eq_comm _ (0:ℕ)]
    · use 1
      simp [hi0, hk1]
  · by_cases hk0 : k = 0
    · by_cases hi1 : i = 1
      · use Fin.last (n+2)
        simp [hi1, hk0, Fin.ext_iff, @eq_comm _ (0:ℕ)]
      · use 1
        simp [hi1, hk0, @eq_comm _ _ i]
    · use 0
      simp [hi0, hk0, @eq_comm _ _ i]

open SimplexCategory in
lemma nerve.horn_app_obj' (n : ℕ) (i : Fin (n+3)) (σ : Λ[n+2, i] ⟶ nerve C)
    (m : SimplexCategoryᵒᵖ) (f : Λ[n+2, i].obj m) (k : Fin (m.unop.len + 1)) :
    (σ.app m f).obj k = (σ.app (op [0]) (horn.vertex _ i (f.1.toOrderHom k))).obj 0 := by
  let φ : ([0] : SimplexCategory) ⟶ m.unop :=
    Hom.mk ⟨Function.const _ k, fun _ _ _ ↦ le_rfl⟩
  have := σ.naturality φ.op
  rw [Function.funext_iff] at this
  specialize this f
  exact (congrArg (fun F ↦ F.obj 0) this).symm

open Finset in
def horn.edge (n : ℕ) (i a b : Fin (n+1)) (hab : a ≤ b) (H : Finset.card {i, a, b} ≤ n) :
    Λ[n, i] _[1] := by
  refine ⟨SimplexCategory.Hom.mk ⟨![a, b], ?mono⟩, ?range⟩
  case mono =>
    rw [Fin.monotone_iff_le_succ]
    simp only [unop_op, SimplexCategory.len_mk, Fin.forall_fin_one]
    apply Fin.mk_le_mk.mpr hab
  case range =>
    suffices ∃ x, ¬i = x ∧ ¬a = x ∧ ¬b = x by
      simpa only [unop_op, SimplexCategory.len_mk, asOrderHom, SimplexCategory.Hom.toOrderHom_mk,
        Set.union_singleton, ne_eq, ← Set.univ_subset_iff, Set.subset_def, Set.mem_univ,
        Set.mem_insert_iff, @eq_comm _ _ i, Set.mem_range, forall_true_left, not_forall, not_or,
        not_exists, Fin.forall_fin_two]
    contrapose! H
    replace H : univ ⊆ {i, a, b} :=
      fun x _ ↦ by simpa [or_iff_not_imp_left, eq_comm] using H x
    replace H := card_le_card H
    rwa [card_fin] at H

def horn.primitiveEdge {n : ℕ} {i : Fin (n+1)}
    (h₀ : 0 < i) (hₙ : i < Fin.last n) (j : Fin n) :
    Λ[n, i] _[1] := by
  refine horn.edge n i j.castSucc j.succ ?_ ?_
  · simp only [← Fin.val_fin_le, Fin.coe_castSucc, Fin.val_succ, le_add_iff_nonneg_right, zero_le]
  simp only [← Fin.val_fin_lt, Fin.val_zero, Fin.val_last] at h₀ hₙ
  obtain rfl|hn : n = 2 ∨ 2 < n := by
    rw [eq_comm, or_comm, ← le_iff_lt_or_eq]; omega
  · revert i j; decide
  · exact le_trans (Finset.card_le_three i _ _) hn

def horn.edge₄ (n : ℕ) (i a b : Fin (n+1)) (hab : a ≤ b) (H : 3 ≤ n) :
    Λ[n, i] _[1] :=
  horn.edge n i a b hab <| (Finset.card_le_three i _ _).trans H

def horn.edge'' {n m : ℕ} {i : Fin (n+4)}
    (f : Λ[n+3, i] _[m]) (a b : Fin (m+1)) (h : a ≤ b) :
    Λ[n+3, i] _[1] :=
  edge₄ _ i (f.1.toOrderHom a) (f.1.toOrderHom b) (f.1.toOrderHom.monotone h) <| by
  simp only [le_add_iff_nonneg_left, zero_le]

def horn.edge' {n m : ℕ} {i : Fin (n+4)}
    (f : Λ[n+3, i] _[m]) (k : ℕ) (hk : k + 1 ≤ m) :
    Λ[n+3, i] _[1] :=
  edge'' f ⟨k, by omega⟩ ⟨k+1, by omega⟩ <| by simp [Fin.le_iff_val_le_val]

lemma morphism_heq {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (hX : X₁ = X₂) (hY : Y₁ = Y₂) (H : f₁ = eqToHom hX ≫ f₂ ≫ eqToHom hY.symm) :
    HEq f₁ f₂ := by
  subst hX hY
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at H
  exact heq_of_eq H

lemma nerve.arrow_app_congr (n : ℕ) (i : Fin (n+3)) (σ : Λ[n+2, i] ⟶ nerve C)
  (f g : Λ[n+2, i] _[1]) (h : f = g) :
  arrow (σ.app (op [1]) f) =
    eqToHom (by rw [h]) ≫
    arrow (σ.app (op [1]) g)
    ≫ eqToHom (by rw [h]) := by
  subst h; simp

open SimplexCategory in
lemma nerve.horn_app_map'' (n : ℕ) (i : Fin (n+4)) (σ : Λ[n+3, i] ⟶ nerve C)
    (m : ℕ) (f : Λ[n+3, i] _[m]) (a b : ℕ) (hab : a ≤ b) (hbm : b ≤ m) :
    (σ.app (op [m]) f).map' a b hab hbm =
      eqToHom (by rw [source, nerve.horn_app_obj', eq_comm, nerve.horn_app_obj']; rfl) ≫
      nerve.arrow (σ.app (op [1])
        (horn.edge'' f
          ⟨a, Nat.lt_add_one_iff.mpr <| hab.trans hbm⟩
          ⟨b, Nat.lt_add_one_iff.mpr <| hbm⟩
          <| Fin.mk_le_mk.mpr hab))
      ≫ eqToHom (by rw [target, nerve.horn_app_obj', eq_comm, nerve.horn_app_obj']; rfl) := by
  let φ : ([1] : SimplexCategory) ⟶ [m] :=
    Hom.mk ⟨![⟨a, by omega⟩, ⟨b, by omega⟩], ?mono⟩
  case mono =>
    rw [Fin.monotone_iff_le_succ]
    simpa [Fin.forall_fin_one, Fin.le_iff_val_le_val]
  have := σ.naturality φ.op
  rw [Function.funext_iff] at this
  specialize this f
  have := congr_arg_heq arrow this
  apply eq_of_heq
  refine this.symm.trans ?_; clear this; clear this
  apply morphism_heq
  case hX =>
    rw [source, nerve.horn_app_obj', types_comp, Function.comp_apply, nerve.horn_app_obj']
    rfl
  case hY =>
    rw [target, nerve.horn_app_obj', types_comp, Function.comp_apply, nerve.horn_app_obj']
    rfl
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, types_comp, Function.comp_apply]
  dsimp only [horn.edge', horn]
  simp only [ne_eq, smallCategory_comp, Hom.comp, len_mk, unop_op, Int.ofNat_eq_coe,
    Int.Nat.cast_ofNat_Int, id_eq, Fin.castSucc_zero, Matrix.cons_val_zero, eq_mpr_eq_cast,
    Quiver.Hom.unop_op, Hom.toOrderHom_mk]
  dsimp [OrderHom.comp]
  apply arrow_app_congr
  apply Subtype.ext
  apply Hom.ext
  ext j
  dsimp at j ⊢
  fin_cases j <;> rfl

open SimplexCategory in
lemma nerve.horn_app_map' (n : ℕ) (i : Fin (n+4)) (σ : Λ[n+3, i] ⟶ nerve C)
    (m : ℕ) (f : Λ[n+3, i] _[m]) (k : ℕ) (hk : k < m) :
    (σ.app (op [m]) f).map' k (k+1) (Nat.le_add_right k 1) hk =
      eqToHom (by rw [source, nerve.horn_app_obj', eq_comm, nerve.horn_app_obj']; rfl) ≫
      nerve.arrow (σ.app (op [1]) (horn.edge' f k hk))
      ≫ eqToHom (by rw [target, nerve.horn_app_obj', eq_comm, nerve.horn_app_obj']; rfl) := by
  apply horn_app_map''

open SimplexCategory in
/-- TODO: rename -/
def horn.triangle' {n : ℕ} (k : ℕ) (h : k + 1 < n) : Δ[n] _[2] := by
  refine Hom.mk ⟨![⟨k, by omega⟩, ⟨k+1, by omega⟩, ⟨k+2, by omega⟩], ?_⟩
  rw [Fin.monotone_iff_le_succ]
  simp only [unop_op, SimplexCategory.len_mk, Fin.forall_fin_two]
  dsimp
  simp only [Fin.le_iff_val_le_val, le_add_iff_nonneg_right, zero_le, Matrix.tail_cons,
    Matrix.head_cons, add_le_add_iff_left, true_and]
  decide

def horn.triangle {n : ℕ} (i : Fin (n+4))
    (h₀ : 0 < i) (hₙ : i < Fin.last (n+3))
    (k : ℕ) (h : k < n+2) : Λ[n+3, i] _[2] := by
  refine ⟨horn.triangle' k (by omega), ?_⟩
  simp only [unop_op, SimplexCategory.len_mk, asOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.const_coe_coe, Set.union_singleton, ne_eq, ← Set.univ_subset_iff, Set.subset_def,
    Set.mem_univ, Set.mem_insert_iff, Set.mem_range, Function.const_apply, exists_const,
    forall_true_left, not_forall, not_or, unop_op, not_exists, triangle',
    OrderHom.coe_mk, @eq_comm _ _ i]
  dsimp
  by_cases hk0 : k = 0
  · subst hk0
    use Fin.last (n+3)
    simp only [hₙ.ne, not_false_eq_true, Fin.zero_eta, zero_add, true_and]
    intro j
    fin_cases j <;> simp [Fin.ext_iff] <;> omega
  · use 0
    simp only [h₀.ne', not_false_eq_true, true_and]
    intro j
    fin_cases j <;> simp [Fin.ext_iff, hk0]

end nerve

namespace filler

variable {C : Type} [Category C]
variable {n : ℕ} {i : Fin (n+3)} (σ₀ : Λ[n+2, i] ⟶ nerve C)
variable (h₀ : 0 < i) (hₙ : i < Fin.last (n+2))

private
def obj : Fin (n+3) → C :=
  fun j ↦ (σ₀.app (op [0]) (horn.vertex n i j)).obj ⟨0, by simp⟩

private
def mor (j : Fin (n+2)) : obj σ₀ j.castSucc ⟶ obj σ₀ j.succ := by
  let e : Λ[n+2, i] _[1] := horn.primitiveEdge h₀ hₙ j
  let f := σ₀.app (op [1]) e
  let φ := nerve.arrow f
  have := fun (k : Fin 2) (e : Λ[n+2, i] _[1]) ↦
    congr_fun (σ₀.naturality (SimplexCategory.δ k).op) e
  dsimp only [types_comp, Function.comp] at this
  refine eqToHom ?_ ≫ φ ≫ eqToHom ?_
  · rw [nerve.source_eq, ← this]
    suffices : Λ[n+2, i].map (SimplexCategory.δ 1).op e = horn.vertex n i j.castSucc
    · rw [this]; rfl
    apply Subtype.ext
    apply SimplexCategory.Hom.ext'
    apply OrderHom.ext
    apply funext
    erw [Fin.forall_fin_one]
    rfl
  · rw [nerve.target_eq, ← this]
    suffices : Λ[n+2, i].map (SimplexCategory.δ 0).op e = horn.vertex n i j.succ
    · rw [this]; rfl
    apply Subtype.ext
    apply SimplexCategory.Hom.ext'
    apply OrderHom.ext
    apply funext
    erw [Fin.forall_fin_one]
    rfl

end filler

section

variable {C : Type} [Category C]
variable {n : ℕ} {i : Fin (n+3)} (σ₀ : Λ[n+2, i] ⟶ nerve C)
variable (h₀ : 0 < i) (hₙ : i < Fin.last (n+2))

noncomputable
def filler : (nerve C) _[n+2] :=
  nerve.mk _ (filler.obj σ₀) (filler.mor σ₀ h₀ hₙ)

open SimplexCategory in
lemma filler_spec_zero ⦃i : Fin 3⦄ (σ₀ : Λ[2, i] ⟶ nerve C)
    (h₀ : 0 < i) (hₙ : i < Fin.last 2) (j : Fin 3) (hj : j ≠ i) :
    (nerve C).δ j (filler σ₀ h₀ hₙ) = σ₀.app (op [1]) (horn.face i j hj) := by
  rw [filler, nerve.δ_mk]
  dsimp only [nerve.mk]
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · symm; apply nerve.horn_app_obj'
  · symm; apply nerve.horn_app_obj'
  dsimp only [ComposableArrows.hom]
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ 0 zero_lt_one]
  obtain rfl : i = 1 := by
    fin_cases i <;> simp at h₀ hₙ
    · rfl
    · exact (lt_irrefl _ hₙ).elim
  dsimp only [nerve.δ_mor]
  simp only [ne_eq, Fin.ext_iff, Fin.val_one, @eq_comm ℕ _ 1] at hj
  simp only [unop_op, SimplexCategory.len_mk, ComposableArrows.mkOfObjOfMapSucc_obj, Fin.zero_eta,
    Function.comp_apply, Fin.mk_one, zero_add, Nat.zero_eq, Fin.castSucc_zero, Fin.succ_zero_eq_one,
    hj, Fin.succ_one_eq_two, Fin.castSucc_one, dite_false, ComposableArrows.map']
  split <;> rename_i hj'
  · obtain rfl : j = 2 := by fin_cases j <;> simp at hj hj'; rfl
    rw [← eqToHom_comp_iff, ← comp_eqToHom_iff]
    swap; symm; apply nerve.horn_app_obj'
    swap; apply nerve.horn_app_obj'
    dsimp only [filler.mor]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    symm
    apply nerve.arrow_app_congr
    apply Subtype.ext
    apply Hom.ext
    ext b
    dsimp [horn.primitiveEdge, horn.edge, horn.face, δ, Fin.succAbove] at b ⊢
    fin_cases b <;> simp
  · obtain rfl : j = 0 := by fin_cases j <;> simp at hj hj'; rfl
    rw [← eqToHom_comp_iff, ← comp_eqToHom_iff]
    swap; symm; apply nerve.horn_app_obj'
    swap; apply nerve.horn_app_obj'
    dsimp only [filler.mor]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    symm
    apply nerve.arrow_app_congr
    apply Subtype.ext
    apply Hom.ext
    ext b
    dsimp [horn.primitiveEdge, horn.edge, horn.face, δ, Fin.succAbove] at b ⊢
    fin_cases b <;> simp

lemma nerve.arrow_app_congr' {n : ℕ} {i : Fin (n+4)} (σ : Λ[n+3, i] ⟶ nerve C)
  {f₁ f₂ f₃ g₁ g₂ g₃ : Λ[n+3, i] _[1]}
  {h₁ : f₁ = g₁} {h₂ : f₂ = g₂} {h₃ : f₃ = g₃} {hf₁} {hf₂} {hf₃} {hg₁} {hg₂} {hg₃}
  (H : arrow (σ.app (op [1]) f₁) =
    eqToHom hf₁
    ≫ arrow (σ.app (op [1]) f₂)
    ≫ eqToHom hf₂
    ≫ arrow (σ.app (op [1]) f₃)
    ≫ eqToHom hf₃) :
  arrow (σ.app (op [1]) g₁) =
    eqToHom hg₁
    ≫ arrow (σ.app (op [1]) g₂)
    ≫ eqToHom hg₂
    ≫ arrow (σ.app (op [1]) g₃)
    ≫ eqToHom hg₃ := by
  subst h₁ h₂ h₃
  exact H

open SimplexCategory in
lemma filler_spec_succ_aux
  ⦃i : Fin (n + 4)⦄ (σ₀ : horn (n + 3) i ⟶ nerve C) (h₀ : 0 < i)
  (hₙ : i < Fin.last (n + 3)) (j : Fin (n + 4)) (hj : j ≠ i) (k : ℕ) (hk : k < n + 2)
  (hkj : ¬k + 1 < ↑j) (hkj' : k + 1 = ↑j) (h2 : k < n + 2)
  (h3 :
    nerve.source (σ₀.app (op [1]) (horn.edge' (horn.face i j hj) k hk)) =
      nerve.source (σ₀.app (op [1]) (horn.primitiveEdge h₀ hₙ (Fin.castSucc { val := k, isLt := h2 }))))
  (h4 : Nat.succ k < Nat.succ (n + 2))
  (h5 :
    nerve.target (σ₀.app (op [1]) (horn.primitiveEdge h₀ hₙ (Fin.castSucc { val := k, isLt := h2 }))) =
      nerve.source (σ₀.app (op [1]) (horn.primitiveEdge h₀ hₙ (Fin.succ { val := k, isLt := h2 }))))
  (h6 :
    nerve.target (σ₀.app (op [1]) (horn.primitiveEdge h₀ hₙ (Fin.succ { val := k, isLt := h2 }))) =
      nerve.target (σ₀.app (op [1]) (horn.edge' (horn.face i j hj) k hk))) :
  eqToHom h3 ≫
      (nerve.arrow (σ₀.app (op [1]) (horn.primitiveEdge h₀ hₙ { val := k, isLt := _ })) ≫
          eqToHom h5 ≫ nerve.arrow (σ₀.app (op [1]) (horn.primitiveEdge h₀ hₙ { val := k + 1, isLt := h4 }))) ≫
        eqToHom h6 =
    nerve.arrow (σ₀.app (op [1]) (horn.edge' (horn.face i j hj) k hk)) := by
  obtain ⟨j, hj'⟩ := j
  dsimp only [Fin.eta] at *
  subst hkj'
  let F := σ₀.app (op [2]) (horn.triangle i h₀ hₙ k h2)
  have H := F.map'_comp 0 1 2 (by omega) (by omega) (by dsimp; omega)
  dsimp only at H
  have := nerve.horn_app_map' n i σ₀ _ (horn.triangle i h₀ hₙ k h2) 0 zero_lt_two
  rw [this] at H; clear this
  have := nerve.horn_app_map' n i σ₀ _ (horn.triangle i h₀ hₙ k h2) 1 one_lt_two
  rw [this] at H; clear this
  have := nerve.horn_app_map'' n i σ₀ _ (horn.triangle i h₀ hₙ k h2) 0 2 zero_le' le_rfl
  rw [this] at H; clear this
  rw [eqToHom_comp_iff, comp_eqToHom_iff] at H
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc] at H
  symm
  simp only [Category.assoc]
  apply nerve.arrow_app_congr' σ₀ H
  · apply Subtype.ext
    apply Hom.ext
    ext b
    dsimp [horn.triangle, horn.triangle', horn.face, horn.edge'', horn.edge', horn.edge₄, horn.edge,
      δ, Fin.succAbove] at b ⊢
    simp only [Matrix.cons_val_succ', Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons,
      lt_add_iff_pos_right, zero_lt_one, ite_true, lt_self_iff_false, ite_false]
  · apply Subtype.ext
    apply Hom.ext
    ext b
    dsimp [horn.primitiveEdge, horn.triangle, horn.triangle', horn.face, horn.edge'', horn.edge',
      horn.edge₄, horn.edge, δ, Fin.succAbove] at b ⊢
    simp only [Matrix.cons_val_succ', Fin.zero_eta, Matrix.cons_val_zero]
  · apply Subtype.ext
    apply Hom.ext
    ext b
    dsimp [horn.primitiveEdge, horn.triangle, horn.triangle', horn.face, horn.edge'', horn.edge',
      horn.edge₄, horn.edge, δ, Fin.succAbove] at b ⊢
    simp only [Matrix.cons_val_succ', Fin.zero_eta, Matrix.cons_val_zero]

open SimplexCategory in
lemma filler_spec_succ ⦃i : Fin (n + 4)⦄
    (σ₀ : Λ[n + 3, i] ⟶ nerve C) (h₀ : 0 < i) (hₙ : i < Fin.last (n + 3))
    (j : Fin (n + 4)) (hj : j ≠ i) :
    (nerve C).δ j (filler σ₀ h₀ hₙ) = σ₀.app (op [n + 2]) (horn.face i j hj) := by
  rw [filler, nerve.δ_mk]
  refine ComposableArrows.ext ?_ ?_
  · dsimp [nerve.mk]
    intro k
    symm
    apply nerve.horn_app_obj'
  intro k hk
  dsimp only [nerve.mk]
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ k (by omega)]
  dsimp only [nerve.δ_mor]
  split <;> rename_i hkj
  · rw [← eqToHom_comp_iff, ← comp_eqToHom_iff]
    swap; rw [eq_comm, nerve.horn_app_obj']; rfl
    swap; rw [nerve.horn_app_obj']; rfl
    have := nerve.horn_app_map' n i σ₀ _ (horn.face i j hj) k hk
    rw [this, ← eqToHom_comp_iff, ← comp_eqToHom_iff]
    swap; rw [nerve.target, nerve.horn_app_obj', eq_comm, nerve.horn_app_obj']; rfl
    swap; rw [nerve.source, nerve.horn_app_obj', eq_comm, nerve.horn_app_obj']; rfl
    dsimp only [filler.mor]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    symm
    apply nerve.arrow_app_congr
    apply Subtype.ext
    apply Hom.ext
    ext b
    dsimp [horn.primitiveEdge, horn.triangle, horn.triangle', horn.face, horn.edge'', horn.edge',
      horn.edge₄, horn.edge, δ, Fin.succAbove] at b ⊢
    have hkj' : k < j.val := by omega
    simp only [hkj', ite_true, hkj]
  split <;> rename_i hkj'
  · rw [← eqToHom_comp_iff, ← comp_eqToHom_iff]
    swap; rw [eq_comm, nerve.horn_app_obj']; rfl
    swap; rw [nerve.horn_app_obj']; rfl
    have := nerve.horn_app_map' n i σ₀ _ (horn.face i j hj) k hk
    rw [this, ← eqToHom_comp_iff, ← comp_eqToHom_iff]
    swap; rw [nerve.target, nerve.horn_app_obj', eq_comm, nerve.horn_app_obj']; rfl
    swap; rw [nerve.source, nerve.horn_app_obj', eq_comm, nerve.horn_app_obj']; rfl
    dsimp only [filler.mor]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    slice_lhs 2 4 => skip
    simp only [unop_op, len_mk, Int.ofNat_eq_coe, Int.Nat.cast_ofNat_Int, id_eq, Fin.castSucc_mk,
      Fin.succ_mk]
    apply filler_spec_succ_aux <;> assumption
  · rw [← eqToHom_comp_iff, ← comp_eqToHom_iff]
    swap; rw [eq_comm, nerve.horn_app_obj']; rfl
    swap; rw [nerve.horn_app_obj']; rfl
    have := nerve.horn_app_map' n i σ₀ _ (horn.face i j hj) k hk
    rw [this, ← eqToHom_comp_iff, ← comp_eqToHom_iff]
    swap; rw [nerve.target, nerve.horn_app_obj', eq_comm, nerve.horn_app_obj']; rfl
    swap; rw [nerve.source, nerve.horn_app_obj', eq_comm, nerve.horn_app_obj']; rfl
    dsimp only [filler.mor]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    symm
    apply nerve.arrow_app_congr
    apply Subtype.ext
    apply Hom.ext
    ext b
    dsimp [horn.primitiveEdge, horn.triangle, horn.triangle', horn.face, horn.edge'', horn.edge',
      horn.edge₄, horn.edge, δ, Fin.succAbove] at b ⊢
    have hkj'' : ¬ k < j.val := by omega
    simp only [hkj'', ite_false, hkj]

end

/-- The nerve of a category is a quasicategory.

[Kerodon, 0032] -/
instance (C : Type) [Category C] : Quasicategory (nerve C) := by
  apply quasicategory_of_filler
  intro n i σ₀ h₀ hₙ
  use filler σ₀ h₀ hₙ
  intro j hj
  cases n using Nat.casesAuxOn with
  | zero => apply filler_spec_zero
  | succ n => apply filler_spec_succ

end SSet
