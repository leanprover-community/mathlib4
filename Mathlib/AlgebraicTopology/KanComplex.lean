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

lemma nerve.horn_ext {n : ℕ} {i : Fin (n+1)} (σ₀ σ₁ : Λ[n, i] ⟶ nerve C)
    (h : σ₀.app (op [1]) = σ₁.app (op [1])) : σ₀ = σ₁ := by
  apply NatTrans.ext; apply funext
  apply Opposite.rec
  apply SimplexCategory.rec
  intro m
  ext f
  apply ComposableArrows.ext
  intro j hj
  cases m using Nat.casesAuxOn with
  | zero => simp at hj
  | succ m =>
  cases m using Nat.casesAuxOn with
  | zero =>
    simp only [zero_add, SimplexCategory.len_mk, Nat.lt_one_iff] at hj
    subst j
    rw [Function.funext_iff] at h
    specialize h f
    dsimp
    sorry
  | succ m =>
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
    let e : (horn n i).obj (op [1]) :=
      ⟨SimplexCategory.Hom.mk ⟨![j.castSucc, j.succ], ?mono⟩, ?range⟩
    let f := σ₀.app (op [1]) e
    swap
    · rw [Fin.monotone_iff_le_succ]
      dsimp
      simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.le_iff_val_le_val, Fin.val_succ,
        Fin.forall_fin_one, Fin.castSucc_zero, Matrix.cons_val_zero, Fin.coe_castSucc,
        le_add_iff_nonneg_right, zero_le]
    swap
    · simp only [unop_op, SimplexCategory.len_mk, asOrderHom, SimplexCategory.Hom.toOrderHom_mk,
        OrderHom.const_coe_coe, Set.union_singleton, ne_eq, ← Set.univ_subset_iff, Set.subset_def,
        Set.mem_univ, Set.mem_insert_iff, Set.mem_range, Function.const_apply, exists_const,
        forall_true_left, not_forall, not_or, unop_op, not_exists, Fin.forall_fin_two]
      dsimp
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
    · let φ := nerve.arrow f
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
    apply nerve.horn_ext
    rw [NatTrans.comp_app]
    simp only [nerve_obj, unop_op, SimplexCategory.len_mk, ne_eq, Function.const_apply, id_eq,
      eq_mpr_eq_cast, Nat.zero_eq, Fin.zero_eta, Fin.castSucc_zero, Matrix.cons_val_zero,
      Fin.coe_castSucc, Fin.val_succ, OrderHom.coe_mk, Matrix.cons_val_one, Matrix.head_cons,
      eq_mp_eq_cast, Fin.val_zero, Nat.rawCast, Nat.cast_id, Int.ofNat_one, Int.rawCast,
      Int.cast_id, Int.ofNat_eq_coe, Int.ofNat_zero, Int.Nat.cast_ofNat_Int, cast_eq, Fin.val_last,
      nerve_map, Quiver.Hom.unop_op, SimplexCategory.toCat_map, ComposableArrows.whiskerLeft_obj]

end SSet
