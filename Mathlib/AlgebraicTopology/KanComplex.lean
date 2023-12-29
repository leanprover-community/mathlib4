/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.AlgebraicTopology.Nerve

/-!
# Kan complexes and quasicategories

-/

universe v u

open CategoryTheory CategoryTheory.Limits Opposite

open Simplicial

namespace CategoryTheory

namespace Functor

variable {C : Type*} [Category C] {D : Type*} [Category D]

lemma map_eqToHom (F : C ⥤ D) (X Y : C) (h : X = Y) :
    F.map (eqToHom h) = eqToHom (congrArg F.obj h) := by
  subst h
  simp only [eqToHom_refl, map_id]

end Functor

namespace ComposableArrows

variable {C : Type*} [inst : Category C] {n : ℕ}

private lemma arrow_ext_aux {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (hX : X₁ = X₂) (hY : Y₁ = Y₂) (H : mk₁ f₁ = mk₁ f₂) :
    f₁ = eqToHom hX ≫ f₂ ≫ eqToHom hY.symm := by
  subst hX hY
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  have := congr_arg_heq (fun f => f.map' 0 1) H
  exact eq_of_heq this

lemma arrow_ext {F G : ComposableArrows C n} (hn : n ≠ 0)
    (w : ∀ (i : ℕ) (hi : i < n), F.arrow i = G.arrow i) : F = G := by
  cases n using Nat.casesAuxOn
  · contradiction
  clear hn
  have obj : ∀ i, F.obj i = G.obj i := by
    intro i
    by_cases H : i = Fin.last _
    · subst H
      specialize w _ (Nat.lt_succ_self _)
      apply_fun (fun f ↦ f.obj 1) at w
      exact w
    · specialize w i ?lt
      case lt => contrapose! H; cases i; ext; linarith
      case neg =>
        apply_fun (fun f ↦ f.obj 0) at w
        exact w
  apply ext obj
  intro i hi
  specialize w i hi
  apply arrow_ext_aux _ _ _ (obj _) w

lemma map'_def (F : ComposableArrows C n)
    (i j : ℕ) (hij : i ≤ j := by linarith) (hjn : j ≤ n := by linarith) :
    F.map' i j = F.map (homOfLE (Fin.mk_le_mk.mpr hij)) := rfl

end ComposableArrows

end CategoryTheory

namespace SSet

/-- A *Kan complex* is a simplicial set `S` if it satisfies the following horn-filling condition:
for every `n : ℕ` and `0 ≤ i ≤ n`,
every map of simplicial sets `σ₀ : Λ[n, i] → S` can be extended to a map `σ : Δ[n] → S`. -/
class KanComplex (S : SSet) : Prop :=
  (hornFilling : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+1)⦄ (σ₀ : Λ[n, i] ⟶ S),
    ∃ σ : Δ[n] ⟶ S, σ₀ = hornInclusion n i ≫ σ)

/-- A *quasicategory* is a simplicial set `S` if it satisfies the following horn-filling condition:
for every `n : ℕ` and `0 < i < n`,
every map of simplicial sets `σ₀ : Λ[n, i] → S` can be extended to a map `σ : Δ[n] → S`.

[Kerodon, 003A] -/
class Quasicategory (S : SSet) : Prop :=
  (hornFilling' : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+3)⦄ (σ₀ : Λ[n+2, i] ⟶ S)
     (_h0 : 0 < i) (_hn : i < Fin.last (n+2)),
       ∃ σ : Δ[n+2] ⟶ S, σ₀ = hornInclusion (n+2) i ≫ σ)

lemma Quasicategory.hornFilling {S : SSet} [Quasicategory S] ⦃n : ℕ⦄ ⦃i : Fin (n+1)⦄
    (h0 : 0 < i) (hn : i < Fin.last n)
    (σ₀ : Λ[n, i] ⟶ S) : ∃ σ : Δ[n] ⟶ S, σ₀ = hornInclusion n i ≫ σ := by
  cases n using Nat.casesAuxOn with
  | zero => simp [Fin.lt_iff_val_lt_val] at hn
  | succ n =>
  cases n using Nat.casesAuxOn with
  | zero =>
    simp only [Fin.lt_iff_val_lt_val, Fin.val_zero, Fin.val_last, zero_add, Nat.lt_one_iff] at h0 hn
    simp [hn] at h0
  | succ n => exact Quasicategory.hornFilling' σ₀ h0 hn

/-- Every Kan complex is a quasicategory.

[Kerodon, 003C] -/
instance (S : SSet) [KanComplex S] : Quasicategory S where
  hornFilling' _ _ σ₀ _ _ := KanComplex.hornFilling σ₀

def horn.face {n : ℕ} (i j : Fin (n+1+1)) (h : j ≠ i) : Λ[n+1, i] _[n] := by
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
    -- let g_fun : Fin (m+1) → Fin (n+1) :=
    --   fun k ↦ if f.1.toOrderHom k ≤ j then f.1.toOrderHom k else f.1.toOrderHom k
    -- have g_mono : Monotone g_fun := sorry
    -- let g : ([m] : SimplexCategory) ⟶ [n] := .mk ⟨g_fun, g_mono⟩
    -- have hg : g ≫ SimplexCategory.δ j = f.1 := by
    --   ext k
    --   simp
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


-- TODO: move
instance fin_two_zero_le_one : ZeroLEOneClass (Fin 2) where
  zero_le_one := by decide

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
lemma nerve.horn_app_obj (n : ℕ) (i : Fin (n+3)) (σ : Λ[n+2, i] ⟶ nerve C)
    (m : SimplexCategoryᵒᵖ) (f : Λ[n+2, i].obj m) :
    σ.app m f = yonedaEquiv ((yonedaEquiv.symm f) ≫ σ) := by
  apply congrArg (σ.app m)
  apply Subtype.ext
  apply Hom.ext
  ext k
  rfl

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

def horn.edge {n : ℕ} {i : Fin (n+1)}
    (h₀ : 0 < i) (hₙ : i < Fin.last n) (j : Fin n) :
    Λ[n, i] _[1] := by
  refine ⟨SimplexCategory.Hom.mk ⟨![j.castSucc, j.succ], ?mono⟩, ?range⟩
  · rw [Fin.monotone_iff_le_succ]
    simp [Fin.forall_fin_one, Fin.le_iff_val_le_val]
  · suffices ∃ x, ¬x = i ∧ ¬Fin.castSucc j = x ∧ ¬Fin.succ j = x by
      simpa only [unop_op, SimplexCategory.len_mk, asOrderHom, SimplexCategory.Hom.toOrderHom_mk,
        OrderHom.const_coe_coe, Set.union_singleton, ne_eq, ← Set.univ_subset_iff, Set.subset_def,
        Set.mem_univ, Set.mem_insert_iff, Set.mem_range, Function.const_apply, exists_const,
        forall_true_left, not_forall, not_or, unop_op, not_exists, Fin.forall_fin_two]
    by_cases h : j.castSucc = 0
    · refine ⟨Fin.last n, ?_⟩
      cases n with
      | zero => simp only [Nat.zero_eq, Fin.last, Fin.zero_eta, Fin.not_lt_zero] at hₙ
      | succ n =>
        simp only [hₙ.ne', not_false_eq_true, h, (h₀.trans hₙ).ne, Fin.succ_eq_last_succ, true_and]
        simp only [Fin.lt_iff_val_lt_val, Fin.val_last, Fin.val_zero] at h₀ hₙ
        simp only [Fin.castSucc_eq_zero_iff] at h
        simp only [h, Fin.last, Fin.ext_iff, Fin.val_zero]
        linarith only [h₀, hₙ]
    · refine ⟨0, ?_⟩
      simp [h, h₀.ne, Fin.succ_ne_zero j]

def horn.edge' {n m : ℕ} {i : Fin (n+3)}
    -- (h₀ : 0 < i) (hₙ : i < Fin.last (n+2)) (j : Fin (n+2))
    (f : Λ[n+2, i] _[m]) (k : ℕ) (hk : k + 1 ≤ m) :
    Λ[n+2, i] _[1] := by
  refine ⟨SimplexCategory.Hom.mk ⟨?edge, ?mono⟩, ?range⟩
  case edge => exact ![f.1.toOrderHom ⟨k, by omega⟩, f.1.toOrderHom ⟨k+1, by omega⟩]
  case mono =>
    rw [Fin.monotone_iff_le_succ]
    simp only [unop_op, SimplexCategory.len_mk, Fin.forall_fin_one]
    apply f.1.toOrderHom.monotone
    simp [Fin.le_iff_val_le_val]
  case range =>
    simp only [unop_op, SimplexCategory.len_mk, asOrderHom, SimplexCategory.Hom.toOrderHom_mk,
        OrderHom.const_coe_coe, Set.union_singleton, ne_eq, ← Set.univ_subset_iff, Set.subset_def,
        Set.mem_univ, Set.mem_insert_iff, Set.mem_range, Function.const_apply, exists_const,
        forall_true_left, not_forall, not_or, unop_op, not_exists, Fin.forall_fin_two,
        OrderHom.coe_mk]
    dsimp
    sorry

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
lemma nerve.horn_app_map' (n : ℕ) (i : Fin (n+3)) (σ : Λ[n+2, i] ⟶ nerve C)
    (m : ℕ) (f : Λ[n+2, i] _[m]) (k : ℕ) (hk : k < m) :
    (σ.app (op [m]) f).map' k (k+1) (Nat.le_add_right k 1) hk =
      eqToHom (by rw [source, nerve.horn_app_obj', eq_comm, nerve.horn_app_obj']; rfl) ≫
      nerve.arrow (σ.app (op [1]) (horn.edge' f k hk))
      ≫ eqToHom (by rw [target, nerve.horn_app_obj', eq_comm, nerve.horn_app_obj']; rfl) := by
  let φ : ([1] : SimplexCategory) ⟶ [m] :=
    Hom.mk ⟨![⟨k, by omega⟩, ⟨k+1, by omega⟩], ?mono⟩
  case mono =>
    rw [Fin.monotone_iff_le_succ]
    simp [Fin.forall_fin_one, Fin.le_iff_val_le_val]
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

-- lemma nerve.horn_ext {n : ℕ} {i : Fin (n+1)}
--     (h₀ : 0 < i) (hₙ : i < Fin.last n)
--     (σ₀ σ₁ : Λ[n, i] ⟶ nerve C)
--     (h : ∀ j, σ₀.app (op [1]) (horn.edge h₀ hₙ j) = σ₁.app (op [1])  (horn.edge h₀ hₙ j)) :
--     σ₀ = σ₁ := by
--   apply NatTrans.ext; apply funext
--   apply Opposite.rec
--   apply SimplexCategory.rec
--   apply Nat.recAux
--   · sorry
--   intro m IH
--   ext f
--   apply ComposableArrows.arrow_ext
--   · simp
--   -- dsimp
--   intro j hj
--   let F := (σ₀.app { unop := [m + 1] } f).arrow j
--   have : F.obj 0 = F.obj 1 := by
--     dsimp [F, ComposableArrows.arrow]
--     show (σ₀.app { unop := [m + 1] } f).obj _ = (σ₀.app { unop := [m + 1] } f).obj _
--   -- simp only [SimplexCategory.len_mk] at hj
--   -- cases m using Nat.casesAuxOn with
--   -- | zero => simp at hj
--   -- | succ m =>
--   -- cases m using Nat.casesAuxOn with
--   -- | zero =>
--   --   simp only [zero_add, SimplexCategory.len_mk, Nat.lt_one_iff] at hj
--   --   subst j
--   --   specialize h f
--   --   dsimp
--   --   dsimp [horn] at f
--   --   sorry
--   -- | succ m =>
--   sorry

end nerve

/-- The nerve of a category is a quasicategory.

[Kerodon, 0032] -/
instance (C : Type) [Category C] : Quasicategory (nerve C) := by
  apply quasicategory_of_filler
  intro n i σ₀ h₀ hₙ
  let v : Fin (n+3) → Λ[n+2, i].obj (op [0]) :=
    fun j ↦ ⟨SimplexCategory.Hom.mk (OrderHom.const _ j), ?_⟩
  swap
  · simp only [unop_op, SimplexCategory.len_mk, asOrderHom, SimplexCategory.Hom.toOrderHom_mk,
      OrderHom.const_coe_coe, Set.union_singleton, ne_eq, ← Set.univ_subset_iff, Set.subset_def,
      Set.mem_univ, Set.mem_insert_iff, Set.mem_range, Function.const_apply, exists_const,
      forall_true_left, not_forall]
    by_cases h : j = 0
    · refine ⟨Fin.last (n+2), ?_⟩
      simp [h, hₙ.ne', (h₀.trans hₙ).ne]
    · refine ⟨0, ?_⟩
      simp [h, h₀.ne]
  let obj : Fin (n+3) → C := fun j ↦ (σ₀.app (op [0]) (v j)).obj ⟨0, by simp⟩
  let σ : (nerve C) _[n+2] := nerve.mk _ obj (fun j ↦ ?mor)
  use σ
  case mor =>
    let e : Λ[n+2, i].obj (op [1]) := horn.edge h₀ hₙ j
    let f := σ₀.app (op [1]) e
    let φ := nerve.arrow f
    -- let δ := fun (i : Fin 2) ↦ (nerve C).map (SimplexCategory.δ i).op
    have := fun (k : Fin 2) (e : Λ[n+2, i].obj (op [1])) ↦
      congr_fun (σ₀.naturality (SimplexCategory.δ k).op) e
    dsimp only [types_comp, Function.comp] at this
    refine eqToHom ?_ ≫ φ ≫ eqToHom ?_
    · rw [nerve.source_eq, ← this]
      suffices : Λ[n+2, i].map (SimplexCategory.δ 1).op e = v j.castSucc
      · rw [this]; rfl
      apply Subtype.ext
      apply SimplexCategory.Hom.ext'
      apply OrderHom.ext
      apply funext
      erw [Fin.forall_fin_one]
      rfl
    · rw [nerve.target_eq, ← this]
      suffices : Λ[n+2, i].map (SimplexCategory.δ 0).op e = v j.succ
      · rw [this]; rfl
      apply Subtype.ext
      apply SimplexCategory.Hom.ext'
      apply OrderHom.ext
      apply funext
      erw [Fin.forall_fin_one]
      rfl
  intro j hj
  rw [nerve.δ_mk]
  refine ComposableArrows.ext ?_ ?_
  · dsimp [nerve.mk]
    intro k
    symm
    apply nerve.horn_app_obj'
  intro k hk
  dsimp only [nerve.mk]
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ k (by omega)]
  apply eq_of_heq
  dsimp only [nerve.δ_mor]
  by_cases hkj : k + 1 < j.val
  · refine (heq_of_eq <| dif_pos hkj).trans ?_
    apply heq_of_eq
    rw [← eqToHom_comp_iff, ← comp_eqToHom_iff]
    swap; rw [eq_comm, nerve.horn_app_obj']; rfl
    swap; rw [nerve.horn_app_obj']; rfl
    have := nerve.horn_app_map' n i σ₀ _ (horn.face i j hj) k hk
    apply eq_of_heq
    refine HEq.trans ?_ (heq_of_eq this).symm
    apply heq_of_eq
    rw [← eqToHom_comp_iff, ← comp_eqToHom_iff]
    swap; rw [nerve.target, nerve.horn_app_obj', eq_comm, nerve.horn_app_obj']; rfl
    swap; rw [nerve.source, nerve.horn_app_obj', eq_comm, nerve.horn_app_obj']; rfl
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    symm
    -- apply nerve.arrow_app_congr
    sorry
  · refine (heq_of_eq <| dif_neg hkj).trans ?_
    sorry

  -- split <;> rename_i hkj
  -- apply ComposableArrows.arrow_ext
  -- · simp
  -- intro k hk
  -- refine ComposableArrows.ext₁ ?_ ?_ ?_
  -- · symm
  --   apply nerve.horn_app_obj'
  -- · symm
  --   apply nerve.horn_app_obj'
  -- dsimp only [SimplicialObject.δ]

  -- hornFilling n i σ₀ h₀ hₙ := by
  --   let v : Fin (n+1) → (horn n i).obj (op [0]) :=
  --     fun j ↦ ⟨SimplexCategory.Hom.mk (OrderHom.const _ j), ?_⟩
  --   swap
  --   · simp only [unop_op, SimplexCategory.len_mk, asOrderHom, SimplexCategory.Hom.toOrderHom_mk,
  --       OrderHom.const_coe_coe, Set.union_singleton, ne_eq, ← Set.univ_subset_iff, Set.subset_def,
  --       Set.mem_univ, Set.mem_insert_iff, Set.mem_range, Function.const_apply, exists_const,
  --       forall_true_left, not_forall]
  --     by_cases h : j = 0
  --     · refine ⟨Fin.last n, ?_⟩
  --       simp [h, hₙ.ne', (h₀.trans hₙ).ne]
  --     · refine ⟨0, ?_⟩
  --       simp [h, h₀.ne]
  --   let obj : Fin (n+1) → C := fun j ↦ (σ₀.app (op [0]) (v j)).obj ⟨0, by simp⟩
  --   let σ : Δ[n] ⟶ nerve C :=
  --     yonedaEquiv.symm <| nerve.mk n obj (fun j ↦ ?mor)
  --   use σ
  --   swap
  --   let e : (horn n i).obj (op [1]) := horn.edge h₀ hₙ j
  --   let f := σ₀.app (op [1]) e
  --   let φ := nerve.arrow f
  --   -- let δ := fun (i : Fin 2) ↦ (nerve C).map (SimplexCategory.δ i).op
  --   have := fun (k : Fin 2) (e : (horn n i).obj (op [1])) ↦
  --     congr_fun (σ₀.naturality (SimplexCategory.δ k).op) e
  --   dsimp only [types_comp, Function.comp] at this
  --   refine ?_ ≫ φ ≫ ?_
  --   · rw [nerve.source_eq, ← this]
  --     apply eqToHom
  --     suffices : (horn n i).map (SimplexCategory.δ 1).op e = v j.castSucc
  --     · rw [this]; rfl
  --     apply Subtype.ext
  --     apply SimplexCategory.Hom.ext'
  --     apply OrderHom.ext
  --     apply funext
  --     erw [Fin.forall_fin_one]
  --     rfl
  --   · rw [nerve.target_eq, ← this]
  --     apply eqToHom
  --     suffices : (horn n i).map (SimplexCategory.δ 0).op e = v j.succ
  --     · rw [this]; rfl
  --     apply Subtype.ext
  --     apply SimplexCategory.Hom.ext'
  --     apply OrderHom.ext
  --     apply funext
  --     erw [Fin.forall_fin_one]
  --     rfl
  --   apply nerve.horn_ext h₀ hₙ
  --   rw [NatTrans.comp_app]
  --   simp only [nerve_obj, unop_op, SimplexCategory.len_mk, ne_eq, Function.const_apply, id_eq,
  --     eq_mpr_eq_cast, Nat.zero_eq, Fin.zero_eta, Fin.castSucc_zero, Matrix.cons_val_zero,
  --     Fin.coe_castSucc, Fin.val_succ, OrderHom.coe_mk, Matrix.cons_val_one, Matrix.head_cons,
  --     eq_mp_eq_cast, Fin.val_zero, Nat.rawCast, Nat.cast_id, Int.ofNat_one, Int.rawCast,
  --     Int.cast_id, Int.ofNat_eq_coe, Int.ofNat_zero, Int.Nat.cast_ofNat_Int, cast_eq, Fin.val_last,
  --     nerve_map, Quiver.Hom.unop_op, SimplexCategory.toCat_map, ComposableArrows.whiskerLeft_obj]
  --   dsimp [hornInclusion]

end SSet
