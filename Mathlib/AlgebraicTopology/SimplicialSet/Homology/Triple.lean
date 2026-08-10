/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative

/-!
# The long exact sequence of a triple of simplicial sets


-/

@[expose] public section

universe w

open Simplicial CategoryTheory Limits Opposite

namespace SSetPair

variable {C : Type*} [Category* C] [Abelian C] [HasCoproducts.{w} C]
  {X Y Z : SSet.{w}} (i : X ⟶ Y) (j : Y ⟶ Z) (ij : X ⟶ Z)
  [Mono i] [Mono j] [Mono ij] (fac : i ≫ j = ij) (R : C)

abbrev tripleMap₁₂ : SSetPair.of i ⟶ SSetPair.of ij := homMk (𝟙 X) j

abbrev tripleMap₂₃ : SSetPair.of ij ⟶ SSetPair.of j := homMk i (𝟙 Z)

abbrev tripleMap₁₃ : SSetPair.of i ⟶ SSetPair.of j := homMk i j

@[reassoc (attr := simp)]
lemma tripleMap₁₂_comp_tripleMap₂₃ :
    tripleMap₁₂ i j ij fac ≫ tripleMap₂₃ i j ij fac = tripleMap₁₃ i j := by
  cat_disch

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma chainComplexMap_tripleMap₁₃ :
    chainComplexMap (tripleMap₁₃ i j ) R = 0 := by
  ext n
  rw [← cancel_epi (((SSetPair.of i).chainComplexπ R).f n)]
  cat_disch

@[reassoc (attr := simp)]
lemma chainComplexMap_tripleMap₁₂_chainComplexMap_tripleMap₂₃ :
    chainComplexMap (tripleMap₁₂ i j ij fac) R ≫
      chainComplexMap (tripleMap₂₃ i j ij fac) R = 0 := by
  rw [← chainComplexMap_comp, tripleMap₁₂_comp_tripleMap₂₃,
    chainComplexMap_tripleMap₁₃]

noncomputable abbrev tripleShortComplex : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk _ _ (chainComplexMap_tripleMap₁₂_chainComplexMap_tripleMap₂₃ i j ij fac R)

namespace splittingTripleShortComplexMapEval

end splittingTripleShortComplexMapEval

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open Classical in
@[no_expose]
noncomputable def splittingTripleShortComplexMapEval (n : ℕ) :
    ((tripleShortComplex i j ij fac R).map (HomologicalComplex.eval _ _ n)).Splitting := by
  let ρ (z : Z _⦋n⦌) : R ⟶ ((of i).chainComplex R).X n :=
    if hz : z ∈ Set.range (j.app _)
    then Y.ιChainComplex hz.choose ≫ ((of i).chainComplexπ R).f n
    else 0
  have ρ_eq_zero (z : Z _⦋n⦌) (hz : z ∉ Set.range (j.app _)) : ρ z = 0 :=
    dif_neg hz
  have hρ (y : Y _⦋n⦌) : ρ (j.app _ y) = Y.ιChainComplex y ≫ ((of i).chainComplexπ R).f n := by
    have hy : (Set.mem_range_self (f := j.app _) y).choose = y :=
      (mono_iff_injective (j.app (op ⦋n⦌))).1 inferInstance
        (Set.mem_range_self (f := j.app _) y).choose_spec
    dsimp [ρ]
    rw [dif_pos (by simp), hy]
  have hρ₀ (x : X _⦋n⦌) : ρ (ij.app _ x) = 0 := by simp [← fac, hρ]
  exact {
    r := chainComplexDesc _ ρ hρ₀
    s := chainComplexDesc' _ (fun z _ ↦ Z.ιChainComplex z ≫ ((of ij).chainComplexπ R).f n)
    f_r := chainComplex_hom_ext (fun y _ ↦ by simpa using! hρ y)
    s_g := chainComplex_hom_ext (fun z hz ↦ by
      rw [ι_chainComplexDesc'_assoc _ _ _ hz]
      cat_disch)
    id := chainComplex_hom_ext (fun z hz ↦ by
      dsimp
      simp only [Preadditive.comp_add, chainComplexπ_f_naturality_assoc, ι_chainComplexDesc_assoc,
        SSet.ι_chainComplexMap_f_assoc, NatTrans.id_app, Category.comp_id]
      by_cases hz' : z ∈ Set.range (j.app _)
      · obtain ⟨y, rfl⟩ := hz'
        change _ + Z.ιChainComplex (j.app _ y) ≫ _ = _
        simp [ι_chainComplexπ_f_eq_zero'_assoc j y (R := R), hρ]
        rfl
      · rw [ρ_eq_zero _ hz', ι_chainComplexDesc' _ _ _ hz']
        cat_disch) }

lemma shortExact_tripleShortComplex_map_eval (n : ℕ) :
    ((tripleShortComplex i j ij fac R).map (HomologicalComplex.eval _ _ n)).ShortExact :=
  (splittingTripleShortComplexMapEval i j ij fac R n).shortExact

instance (n : ℕ) : Mono ((tripleShortComplex i j ij fac R).f.f n) :=
  (shortExact_tripleShortComplex_map_eval i j ij fac R n).mono_f

instance (n : ℕ) : Epi ((tripleShortComplex i j ij fac R).g.f n) :=
  (shortExact_tripleShortComplex_map_eval i j ij fac R n).epi_g

instance : Mono (tripleShortComplex i j ij fac R).f :=
  HomologicalComplex.mono_of_mono_f _ inferInstance

instance : Epi (tripleShortComplex i j ij fac R).g :=
  HomologicalComplex.epi_of_epi_f _ inferInstance

lemma shortExact_tripleShortComplex :
    (tripleShortComplex i j ij fac R).ShortExact where
  exact := by
    rw [HomologicalComplex.exact_iff_degreewise_exact]
    intro n
    exact (shortExact_tripleShortComplex_map_eval i j ij fac R n).exact

end SSetPair
