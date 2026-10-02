/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# The fundamental groupoid of horns

In this file, we show that the morphisms `Λ[n, i] ⟶ Δ[n]` for `n ≠ 0`
induce equivalences of fundamental groupoids. This is proven by
showing that both the source and target fundamental groupoids are
equivalent to `Discrete PUnit`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial SimplicialObject.Truncated

namespace CategoryTheory

namespace Discrete

abbrev toPUnit (C : Type*) [Category C] : C ⥤ Discrete PUnit.{u + 1} :=
  (Functor.const _).obj (Discrete.mk .unit)

lemma isEquivalence_toPUnit {C : Type*} [Category C] (X₀ : C)
    (e : ∀ (X : C), X₀ ≅ X)
    (he : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (e X).hom ≫ f = (e Y).hom := by cat_disch) :
    (toPUnit.{u} C).IsEquivalence := by
  let h : C ≌ Discrete PUnit.{u + 1} :=
    { functor := toPUnit C
      inverse := Discrete.functor (fun _ ↦ X₀)
      unitIso := NatIso.ofComponents (fun X ↦ (e X).symm) (fun {X Y} f ↦ by
        simp [← cancel_epi (e X).hom, reassoc_of% he f])
      counitIso := Iso.refl _ }
  exact h.isEquivalence_functor

lemma isEquivalence_of_isEquivalence_toPUnit {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (hC : (toPUnit.{u} C).IsEquivalence := by infer_instance)
    (hD : (toPUnit.{u} D).IsEquivalence := by infer_instance) :
    F.IsEquivalence := by
  let e : F ⋙ toPUnit.{u} D ≅ toPUnit.{u} C := Iso.refl _
  have := Functor.isEquivalence_of_iso e.symm
  exact Functor.isEquivalence_of_comp_right _ (toPUnit.{u} D)

end Discrete

end CategoryTheory

namespace SSet

@[simp]
lemma stdSimplex.edge_zero {n : ℕ} (x y : (Δ[n] : SSet.{u}) _⦋0⦌) (e : Edge x y) :
    dsimp% e.edge 0 = obj₀Equiv x :=
  DFunLike.congr_fun e.src_eq 0

@[simp]
lemma stdSimplex.edge_one {n : ℕ} (x y : (Δ[n] : SSet.{u}) _⦋0⦌) (e : Edge x y) :
    dsimp% e.edge 1 = obj₀Equiv y :=
  DFunLike.congr_fun e.tgt_eq 0

instance {n : ℕ} (x y : (Δ[n] : SSet.{u}) _⦋0⦌) : Subsingleton (Edge x y) where
  allEq s t := by ext i : 2; fin_cases i <;> simp

instance horn.subsingleton_edge
    {n : ℕ} {A : (Δ[n] : SSet.{u}).Subcomplex} (x y : A.toSSet _⦋0⦌) :
    Subsingleton (Edge x y) where
  allEq s t := by
    have : s.map A.ι = t.map A.ι := by subsingleton
    ext : 1
    exact Subtype.ext_iff.2 (congr_arg Edge.edge this)

abbrev stdSimplex.edge' {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j := by grind) :
    Edge (obj₀Equiv.{u}.symm i) (obj₀Equiv.symm j) :=
  Edge.mk (stdSimplex.edge n i j hij)
    (by ext i : 1; fin_cases i; rfl) (by ext i : 1; fin_cases i; rfl)

abbrev stdSimplex.compStruct {n : ℕ} (i j k : Fin (n + 1)) (hij : i ≤ j := by grind)
    (hjk : j ≤ k := by grind) :
    Edge.CompStruct (edge'.{u} i j) (edge' j k) (edge' i k) :=
  Edge.CompStruct.mk (triangle i j k hij hjk)
    (by ext i : 1; fin_cases i <;> rfl)
    (by ext i : 1; fin_cases i <;> rfl)
    (by ext i : 1; fin_cases i <;> rfl)

lemma horn.card_le_of_edge {n : ℕ} {i a b : Fin (n + 3)}
    (e : Edge.{u} (X := Λ[n + 2, i]) ⟨stdSimplex.obj₀Equiv.symm a, by simp⟩
      ⟨stdSimplex.obj₀Equiv.symm b, by simp⟩) :
    Finset.card {i, a, b} ≤ n + 2 := by
  have := e.edge.prop
  sorry

open Finset in
def horn.edge' {n : ℕ} (i a b : Fin (n + 3)) (hab : a ≤ b := by grind)
    (h : #{i, a, b} ≤ n + 2 := by grind) :
    Edge.{u} (X := Λ[n + 2, i])
      ⟨stdSimplex.obj₀Equiv.symm a, by simp⟩
      ⟨stdSimplex.obj₀Equiv.symm b, by simp⟩ :=
  Edge.mk (horn.edge (n + 2) i a b hab h)
    (Subtype.ext_iff.2 (by ext i : 1; fin_cases i; rfl))
    (Subtype.ext_iff.2 (by ext i : 1; fin_cases i; rfl))

open Finset in
abbrev horn.compStruct {n : ℕ} (i a b c : Fin (n + 3)) (hab : a ≤ b := by grind)
    (hbc : b ≤ c := by grind) (h : #{i, a, b, c} ≤ n + 2) :
    Edge.CompStruct (horn.edge'.{u} i a b hab (by grind))
      (horn.edge' i b c hbc (by grind))
      (horn.edge' i a c (hab.trans hbc) (by grind)) := by
  sorry

namespace FundamentalGroupoid

lemma isEquivalence_toPUnit {X : SSet.{u}} (x₀ : X _⦋0⦌)
    (φ : ∀ (y : X _⦋0⦌), mk x₀ ⟶ mk y)
    (hφ : ∀ ⦃y z : X _⦋0⦌⦄ (e : Edge y z), φ y ≫ homMk e = φ z) :
    (Discrete.toPUnit.{u} (FundamentalGroupoid X)).IsEquivalence :=
  Discrete.isEquivalence_toPUnit (mk x₀) (fun x ↦ by
    induction x with | mk x
    exact asIso (φ x)) (fun x y f ↦ by
    induction f with
    | homMk _ => apply hφ
    | @inv x y f hf =>
      induction x with | mk x
      induction y with | mk y
      change φ x ≫ f = φ y at hf
      change φ y ≫ inv f = φ x
      simp [← hf]
    | @comp x y z f g hf hg =>
      induction x with | mk x
      induction y with | mk y
      induction z with | mk z
      change φ x ≫ f = φ y at hf
      change φ y ≫ g = φ z at hg
      change φ x ≫ f ≫ g = φ z
      simp [← hf, ← hg])

instance isEquivalence_toPUnit_stdSimplex (n : ℕ) :
    (Discrete.toPUnit.{u} (FundamentalGroupoid.{u} Δ[n])).IsEquivalence :=
  isEquivalence_toPUnit (stdSimplex.obj₀Equiv.symm 0)
    (fun x ↦ homMk ((stdSimplex.edge' 0 (x 0)).ofEq rfl
      (stdSimplex.obj₀Equiv.symm_apply_apply x))) (fun y z e ↦ by
        obtain ⟨y, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
        obtain ⟨z, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective z
        have hyz : y ≤ z := by
          convert! stdSimplex.monotone_apply e.edge (show 0 ≤ 1 by simp) <;> cat_disch
        obtain rfl : e = stdSimplex.edge' y z := by subsingleton
        exact homMk_comp (stdSimplex.compStruct 0 y z))

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
instance isEquivalence_toPUnit_horn {n : ℕ} (i : Fin (n + 1)) [NeZero n] :
    (Discrete.toPUnit.{u} (FundamentalGroupoid.{u} Λ[n, i])).IsEquivalence := by
  obtain _ | _ | n := n
  · exact (NeZero.ne 0 rfl).elim
  · sorry
  · let α (j : Fin (n + 3)) :
        mk.{u} (X := Λ[n + 2, i]) ⟨stdSimplex.obj₀Equiv.symm i, by simp⟩ ⟶
          mk ⟨stdSimplex.obj₀Equiv.symm j, by simp⟩ :=
      if hij : i ≤ j then
        homMk (horn.edge' _ _ _ hij (by grind))
      else
        inv (homMk (horn.edge' _ _ _ (by grind) (by grind)))
    let β (x : (Λ[n + 2, i] : SSet.{u}) _⦋0⦌) :
        mk.{u} (X := Λ[n + 2, i]) ⟨stdSimplex.obj₀Equiv.symm i, by simp⟩ ⟶ mk x :=
      α (x.val 0) ≫ eqToHom (by
        obtain ⟨x, _⟩ := x
        obtain ⟨x, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
        rfl)
    --have hα₀ : α i = 𝟙 _ := by
    --  simp [α, Subsingleton.elim (horn.edge' i i i (by simp) (by grind)) (.id _)]
    have hα₁ (j : Fin (n + 3)) (hij : i ≤ j := by grind) :
        α j = homMk (horn.edge' _ _ _ hij (by grind)) := dif_pos hij
    have hα₂ (j : Fin (n + 3)) (hij : j < i := by grind) :
        α j = inv (homMk (horn.edge' _ _ _ (by grind) (by grind))) := dif_neg (by grind)
    have hβ (j : Fin (n + 3)) : β _ = α j := Category.comp_id _
    refine isEquivalence_toPUnit ⟨stdSimplex.obj₀Equiv.symm i, by simp⟩
      β (fun y z e ↦ ?_)
    obtain ⟨y, _⟩ := y
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
    obtain ⟨z, _⟩ := z
    obtain ⟨k, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective z
    simp only [hβ]
    have hyz : j ≤ k := by
      have : e.edge.val 0 = j := DFunLike.congr_fun (Subtype.ext_iff.1 e.src_eq) 0
      have : e.edge.val 1 = k := DFunLike.congr_fun (Subtype.ext_iff.1 e.tgt_eq) 0
      convert! stdSimplex.monotone_apply e.edge.val (show 0 ≤ 1 by simp) <;> cat_disch
    obtain rfl | hyz := hyz.eq_or_lt
    · obtain rfl : e = .id _ := (horn.subsingleton_edge ..).elim ..
      rw [homMk_id, Category.comp_id]
    · have := horn.card_le_of_edge e
      obtain rfl : e = horn.edge' i j k := Subsingleton.elim _ _
      by_cases! hij : i ≤ j
      · rw [hα₁ j, hα₁ k]
        exact homMk_comp (horn.compStruct _ _ _ _ _ _ (by grind))
      · rw [hα₂ j hij, IsIso.inv_comp_eq]
        by_cases! hik : i ≤ k
        · rw [hα₁ k]
          exact (homMk_comp (horn.compStruct _ _ _ _ _ _ (by grind))).symm
        · rw [hα₂ k, IsIso.eq_comp_inv]
          exact homMk_comp (horn.compStruct _ _ _ _ _ _ (by grind))

instance {n : ℕ} (i : Fin (n + 1)) [NeZero n] :
    (mapFundamentalGroupoid.{u} Λ[n, i].ι).IsEquivalence :=
  Discrete.isEquivalence_of_isEquivalence_toPUnit.{u} _

end FundamentalGroupoid

end SSet
