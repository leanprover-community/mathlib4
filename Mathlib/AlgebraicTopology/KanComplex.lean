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

namespace CategoryTheory.ComposableArrows

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

end CategoryTheory.ComposableArrows

namespace SSet

/-- A *Kan complex* is a simplicial set `S` if it satisfies the following horn-filling condition:
for every `n : ℕ` and `0 ≤ i ≤ n`,
every map of simplicial sets `σ₀ : Λ[n, i] → S` can be extended to a map `σ : Δ[n] → S`. -/
class Kan_complex (S : SSet) : Prop :=
  (hornFilling : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+1)⦄ (σ₀ : Λ[n, i] ⟶ S),
    ∃ σ : Δ[n] ⟶ S, σ₀ = hornInclusion n i ≫ σ)

/-- A *quasicategory* is a simplicial set `S` if it satisfies the following horn-filling condition:
for every `n : ℕ` and `0 < i < n`,
every map of simplicial sets `σ₀ : Λ[n, i] → S` can be extended to a map `σ : Δ[n] → S`.

[Kerodon, 003A] -/
class quasicategory (S : SSet) : Prop :=
  (hornFilling : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+1)⦄ (σ₀ : Λ[n, i] ⟶ S) (_h0 : 0 < i) (_hn : i < Fin.last n),
    ∃ σ : Δ[n] ⟶ S, σ₀ = hornInclusion n i ≫ σ)

/-- Every Kan complex is a quasicategory.

[Kerodon, 003C] -/
instance (S : SSet) [Kan_complex S] : quasicategory S where
  hornFilling _ _ σ₀ _ _ := Kan_complex.hornFilling σ₀

def horn.face {n : ℕ} (i j : Fin (n+1+1)) (h : j ≠ i) : Λ[n+1, i] _[n] := by
  refine ⟨SimplexCategory.δ j, ?_⟩
  simpa only [unop_op, SimplexCategory.len_mk, asOrderHom, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe, Set.union_singleton, ne_eq, ←
    Set.univ_subset_iff, Set.subset_def, Set.mem_univ, Set.mem_insert_iff, Set.mem_range,
    Fin.succAboveEmb_apply, Fin.exists_succAbove_eq_iff, forall_true_left, not_forall, not_or,
    not_not, exists_eq_right]

open SimplicialObject in
lemma quasicategory_of_filler (S : SSet)
    (H : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n+1+1)⦄ (σ₀ : Λ[n+1, i] ⟶ S) (_h0 : 0 < i) (_hn : i < Fin.last (n+1)),
      ∃ σ : S _[n+1], ∀ (j) (h : j ≠ i),
        S.δ j σ = yonedaEquiv (yonedaEquiv.symm (horn.face i j h) ≫ σ₀)) :
    quasicategory S := by
  sorry

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

-- TODO: move
def nerve.source (f : (nerve C).obj (op [1])) : C := f.obj (0 : Fin 2)

-- TODO: move
def nerve.target (f : (nerve C).obj (op [1])) : C := f.obj (1 : Fin 2)

-- TODO: move
def nerve.arrow (f : (nerve C).obj (op [1])) : source f ⟶ target f :=
  f.map (homOfLE (X := Fin 2) zero_le_one)

-- TODO: move
open SimplexCategory in
lemma nerve.source_eq (f : (nerve C).obj (op [1])) :
    source f = ((nerve C).map (δ (1 : Fin 2)).op f).obj (0 : Fin 1) := rfl

-- TODO: move
open SimplexCategory in
lemma nerve.target_eq (f : (nerve C).obj (op [1])) :
    target f = ((nerve C).map (δ (0 : Fin 2)).op f).obj (0 : Fin 1) := rfl

def horn.edge {n : ℕ} {i : Fin (n+1)}
    (h₀ : 0 < i) (hₙ : i < Fin.last n) (j : Fin n) :
    Λ[n, i].obj (op [1]) := by
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

lemma nerve.horn_ext {n : ℕ} {i : Fin (n+1)}
    (h₀ : 0 < i) (hₙ : i < Fin.last n)
    (σ₀ σ₁ : Λ[n, i] ⟶ nerve C)
    (h : ∀ j, σ₀.app (op [1]) (horn.edge h₀ hₙ j) = σ₁.app (op [1])  (horn.edge h₀ hₙ j)) :
    σ₀ = σ₁ := by
  apply NatTrans.ext; apply funext
  apply Opposite.rec
  apply SimplexCategory.rec
  apply Nat.recAux
  · sorry
  intro m IH
  ext f
  apply ComposableArrows.arrow_ext
  · simp
  -- dsimp
  intro j hj
  let F := (σ₀.app { unop := [m + 1] } f).arrow j
  have : F.obj 0 = F.obj 1 := by
    dsimp [F, ComposableArrows.arrow]
    show (σ₀.app { unop := [m + 1] } f).obj _ = (σ₀.app { unop := [m + 1] } f).obj _
  -- simp only [SimplexCategory.len_mk] at hj
  -- cases m using Nat.casesAuxOn with
  -- | zero => simp at hj
  -- | succ m =>
  -- cases m using Nat.casesAuxOn with
  -- | zero =>
  --   simp only [zero_add, SimplexCategory.len_mk, Nat.lt_one_iff] at hj
  --   subst j
  --   specialize h f
  --   dsimp
  --   dsimp [horn] at f
  --   sorry
  -- | succ m =>
  sorry

end nerve

/-- The nerve of a category is a quasicategory.

[Kerodon, 0032] -/
instance (C : Type) [Category C] : quasicategory (nerve C) where
  hornFilling n i σ₀ h₀ hₙ := by
    let v : Fin (n+1) → (horn n i).obj (op [0]) :=
      fun j ↦ ⟨SimplexCategory.Hom.mk (OrderHom.const _ j), ?_⟩
    swap
    · simp only [unop_op, SimplexCategory.len_mk, asOrderHom, SimplexCategory.Hom.toOrderHom_mk,
        OrderHom.const_coe_coe, Set.union_singleton, ne_eq, ← Set.univ_subset_iff, Set.subset_def,
        Set.mem_univ, Set.mem_insert_iff, Set.mem_range, Function.const_apply, exists_const,
        forall_true_left, not_forall]
      by_cases h : j = 0
      · refine ⟨Fin.last n, ?_⟩
        simp [h, hₙ.ne', (h₀.trans hₙ).ne]
      · refine ⟨0, ?_⟩
        simp [h, h₀.ne]
    let obj : Fin (n+1) → C := fun j ↦ (σ₀.app (op [0]) (v j)).obj ⟨0, by simp⟩
    let σ : Δ[n] ⟶ nerve C :=
      yonedaEquiv.symm <| nerve.mk n obj (fun j ↦ ?mor)
    use σ
    swap
    let e : (horn n i).obj (op [1]) := horn.edge h₀ hₙ j
    let f := σ₀.app (op [1]) e
    let φ := nerve.arrow f
    -- let δ := fun (i : Fin 2) ↦ (nerve C).map (SimplexCategory.δ i).op
    have := fun (k : Fin 2) (e : (horn n i).obj (op [1])) ↦
      congr_fun (σ₀.naturality (SimplexCategory.δ k).op) e
    dsimp only [types_comp, Function.comp] at this
    refine ?_ ≫ φ ≫ ?_
    · rw [nerve.source_eq, ← this]
      apply eqToHom
      suffices : (horn n i).map (SimplexCategory.δ 1).op e = v j.castSucc
      · rw [this]; rfl
      apply Subtype.ext
      apply SimplexCategory.Hom.ext'
      apply OrderHom.ext
      apply funext
      erw [Fin.forall_fin_one]
      rfl
    · rw [nerve.target_eq, ← this]
      apply eqToHom
      suffices : (horn n i).map (SimplexCategory.δ 0).op e = v j.succ
      · rw [this]; rfl
      apply Subtype.ext
      apply SimplexCategory.Hom.ext'
      apply OrderHom.ext
      apply funext
      erw [Fin.forall_fin_one]
      rfl
    apply nerve.horn_ext h₀ hₙ
    rw [NatTrans.comp_app]
    simp only [nerve_obj, unop_op, SimplexCategory.len_mk, ne_eq, Function.const_apply, id_eq,
      eq_mpr_eq_cast, Nat.zero_eq, Fin.zero_eta, Fin.castSucc_zero, Matrix.cons_val_zero,
      Fin.coe_castSucc, Fin.val_succ, OrderHom.coe_mk, Matrix.cons_val_one, Matrix.head_cons,
      eq_mp_eq_cast, Fin.val_zero, Nat.rawCast, Nat.cast_id, Int.ofNat_one, Int.rawCast,
      Int.cast_id, Int.ofNat_eq_coe, Int.ofNat_zero, Int.Nat.cast_ofNat_Int, cast_eq, Fin.val_last,
      nerve_map, Quiver.Hom.unop_op, SimplexCategory.toCat_map, ComposableArrows.whiskerLeft_obj]
    dsimp [hornInclusion]

end SSet
