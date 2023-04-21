/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.gamma_comp_n
! leanprover-community/mathlib commit 5f68029a863bdf76029fa0f7a519e6163c14152e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.DoldKan.FunctorGamma
import Mathbin.CategoryTheory.Idempotents.HomologicalComplex

/-! The counit isomorphism of the Dold-Kan equivalence

The purpose of this file is to construct natural isomorphisms
`N₁Γ₀ : Γ₀ ⋙ N₁ ≅ to_karoubi (chain_complex C ℕ)`
and `N₂Γ₂ : Γ₂ ⋙ N₂ ≅ 𝟭 (karoubi (chain_complex C ℕ))`.

-/


noncomputable section

open
  CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Idempotents Opposite SimplicialObject

open Simplicial

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C] [HasFiniteCoproducts C]

/-- The isomorphism  `(Γ₀.splitting K).nondeg_complex ≅ K` for all `K : chain_complex C ℕ`. -/
@[simps]
def Γ₀NondegComplexIso (K : ChainComplex C ℕ) : (Γ₀.splitting K).nondegComplex ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun n => Iso.refl _)
    (by
      rintro _ n (rfl : n + 1 = _)
      dsimp
      simp only [id_comp, comp_id, alternating_face_map_complex.obj_d_eq, preadditive.sum_comp,
        preadditive.comp_sum]
      rw [Fintype.sum_eq_single (0 : Fin (n + 2))]
      · simp only [Fin.val_zero, pow_zero, one_zsmul]
        erw [Γ₀.obj.map_mono_on_summand_id_assoc, Γ₀.obj.termwise.map_mono_δ₀,
          splitting.ι_π_summand_eq_id, comp_id]
      · intro i hi
        dsimp
        simp only [preadditive.zsmul_comp, preadditive.comp_zsmul, assoc]
        erw [Γ₀.obj.map_mono_on_summand_id_assoc, Γ₀.obj.termwise.map_mono_eq_zero, zero_comp,
          zsmul_zero]
        · intro h
          replace h := congr_arg SimplexCategory.len h
          change n + 1 = n at h
          linarith
        · simpa only [is_δ₀.iff] using hi)
#align algebraic_topology.dold_kan.Γ₀_nondeg_complex_iso AlgebraicTopology.DoldKan.Γ₀NondegComplexIso

/-- The natural isomorphism `(Γ₀.splitting K).nondeg_complex ≅ K` for `K : chain_complex C ℕ`. -/
def Γ₀'CompNondegComplexFunctor : Γ₀' ⋙ Split.nondegComplexFunctor ≅ 𝟭 (ChainComplex C ℕ) :=
  NatIso.ofComponents Γ₀NondegComplexIso fun X Y f =>
    by
    ext n
    dsimp
    simp only [comp_id, id_comp]
#align algebraic_topology.dold_kan.Γ₀'_comp_nondeg_complex_functor AlgebraicTopology.DoldKan.Γ₀'CompNondegComplexFunctor

/-- The natural isomorphism `Γ₀ ⋙ N₁ ≅ to_karoubi (chain_complex C ℕ)`. -/
def n₁Γ₀ : Γ₀ ⋙ N₁ ≅ toKaroubi (ChainComplex C ℕ) :=
  calc
    Γ₀ ⋙ N₁ ≅ Γ₀' ⋙ Split.forget C ⋙ N₁ := Functor.associator _ _ _
    _ ≅ Γ₀' ⋙ Split.nondegComplexFunctor ⋙ toKaroubi _ :=
      (isoWhiskerLeft Γ₀' Split.toKaroubiNondegComplexFunctorIsoN₁.symm)
    _ ≅ (Γ₀' ⋙ Split.nondegComplexFunctor) ⋙ toKaroubi _ := (Functor.associator _ _ _).symm
    _ ≅ 𝟭 _ ⋙ toKaroubi (ChainComplex C ℕ) := (isoWhiskerRight Γ₀'CompNondegComplexFunctor _)
    _ ≅ toKaroubi (ChainComplex C ℕ) := Functor.leftUnitor _
    
#align algebraic_topology.dold_kan.N₁Γ₀ AlgebraicTopology.DoldKan.n₁Γ₀

theorem n₁Γ₀_app (K : ChainComplex C ℕ) :
    n₁Γ₀.app K =
      (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.symm ≪≫
        (toKaroubi _).mapIso (Γ₀NondegComplexIso K) :=
  by
  ext1
  dsimp [N₁Γ₀]
  erw [id_comp, comp_id, comp_id]
  rfl
#align algebraic_topology.dold_kan.N₁Γ₀_app AlgebraicTopology.DoldKan.n₁Γ₀_app

theorem n₁Γ₀_hom_app (K : ChainComplex C ℕ) :
    n₁Γ₀.Hom.app K =
      (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.inv ≫
        (toKaroubi _).map (Γ₀NondegComplexIso K).Hom :=
  by
  change (N₁Γ₀.app K).Hom = _
  simpa only [N₁Γ₀_app]
#align algebraic_topology.dold_kan.N₁Γ₀_hom_app AlgebraicTopology.DoldKan.n₁Γ₀_hom_app

theorem n₁Γ₀_inv_app (K : ChainComplex C ℕ) :
    n₁Γ₀.inv.app K =
      (toKaroubi _).map (Γ₀NondegComplexIso K).inv ≫
        (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.Hom :=
  by
  change (N₁Γ₀.app K).inv = _
  simpa only [N₁Γ₀_app]
#align algebraic_topology.dold_kan.N₁Γ₀_inv_app AlgebraicTopology.DoldKan.n₁Γ₀_inv_app

@[simp]
theorem n₁Γ₀_hom_app_f_f (K : ChainComplex C ℕ) (n : ℕ) :
    (n₁Γ₀.Hom.app K).f.f n = (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.inv.f.f n :=
  by
  rw [N₁Γ₀_hom_app]
  apply comp_id
#align algebraic_topology.dold_kan.N₁Γ₀_hom_app_f_f AlgebraicTopology.DoldKan.n₁Γ₀_hom_app_f_f

@[simp]
theorem n₁Γ₀_inv_app_f_f (K : ChainComplex C ℕ) (n : ℕ) :
    (n₁Γ₀.inv.app K).f.f n = (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.Hom.f.f n :=
  by
  rw [N₁Γ₀_inv_app]
  apply id_comp
#align algebraic_topology.dold_kan.N₁Γ₀_inv_app_f_f AlgebraicTopology.DoldKan.n₁Γ₀_inv_app_f_f

theorem N₂Γ₂_toKaroubi : toKaroubi (ChainComplex C ℕ) ⋙ Γ₂ ⋙ N₂ = Γ₀ ⋙ N₁ :=
  by
  have h :=
    functor.congr_obj
      (functor_extension₂_comp_whiskering_left_to_karoubi (ChainComplex C ℕ) (simplicial_object C))
      Γ₀
  have h' :=
    functor.congr_obj
      (functor_extension₁_comp_whiskering_left_to_karoubi (simplicial_object C) (ChainComplex C ℕ))
      N₁
  dsimp [N₂, Γ₂, functor_extension₁] at h h'⊢
  rw [← functor.assoc, h, functor.assoc, h']
#align algebraic_topology.dold_kan.N₂Γ₂_to_karoubi AlgebraicTopology.DoldKan.N₂Γ₂_toKaroubi

/-- Compatibility isomorphism between `to_karoubi _ ⋙ Γ₂ ⋙ N₂` and `Γ₀ ⋙ N₁` which
are functors `chain_complex C ℕ ⥤ karoubi (chain_complex C ℕ)`. -/
@[simps]
def n₂Γ₂ToKaroubiIso : toKaroubi (ChainComplex C ℕ) ⋙ Γ₂ ⋙ N₂ ≅ Γ₀ ⋙ N₁ :=
  eqToIso N₂Γ₂_toKaroubi
#align algebraic_topology.dold_kan.N₂Γ₂_to_karoubi_iso AlgebraicTopology.DoldKan.n₂Γ₂ToKaroubiIso

/-- The counit isomorphism of the Dold-Kan equivalence for additive categories. -/
def n₂Γ₂ : Γ₂ ⋙ N₂ ≅ 𝟭 (Karoubi (ChainComplex C ℕ)) :=
  ((whiskeringLeft _ _ _).obj (toKaroubi (ChainComplex C ℕ))).preimageIso (n₂Γ₂ToKaroubiIso ≪≫ n₁Γ₀)
#align algebraic_topology.dold_kan.N₂Γ₂ AlgebraicTopology.DoldKan.n₂Γ₂

theorem n₂Γ₂_compatible_with_n₁Γ₀ (K : ChainComplex C ℕ) :
    n₂Γ₂.Hom.app ((toKaroubi _).obj K) = n₂Γ₂ToKaroubiIso.Hom.app K ≫ n₁Γ₀.Hom.app K :=
  congr_app
    (((whiskeringLeft _ _ (Karoubi (ChainComplex C ℕ))).obj
          (toKaroubi (ChainComplex C ℕ))).image_preimage
      (n₂Γ₂ToKaroubiIso.Hom ≫ n₁Γ₀.Hom : _ ⟶ toKaroubi _ ⋙ 𝟭 _))
    K
#align algebraic_topology.dold_kan.N₂Γ₂_compatible_with_N₁Γ₀ AlgebraicTopology.DoldKan.n₂Γ₂_compatible_with_n₁Γ₀

@[simp]
theorem n₂Γ₂_inv_app_f_f (X : Karoubi (ChainComplex C ℕ)) (n : ℕ) :
    (n₂Γ₂.inv.app X).f.f n =
      X.p.f n ≫ (Γ₀.splitting X.pt).ιSummand (Splitting.IndexSet.id (op [n])) :=
  by
  dsimp only [N₂Γ₂, functor.preimage_iso, iso.trans]
  simp only [whiskering_left_obj_preimage_app, N₂Γ₂_to_karoubi_iso_inv, functor.id_map,
    nat_trans.comp_app, eq_to_hom_app, functor.comp_map, assoc, karoubi.comp_f, karoubi.eq_to_hom_f,
    eq_to_hom_refl, comp_id, karoubi.comp_p_assoc, N₂_map_f_f, HomologicalComplex.comp_f,
    N₁Γ₀_inv_app_f_f, P_infty_on_Γ₀_splitting_summand_eq_self_assoc,
    splitting.to_karoubi_nondeg_complex_iso_N₁_hom_f_f, Γ₂_map_f_app, karoubi.decomp_id_p_f]
  dsimp [to_karoubi]
  rw [splitting.ι_desc]
  dsimp [splitting.index_set.id]
  rw [karoubi.homological_complex.p_idem_assoc]
#align algebraic_topology.dold_kan.N₂Γ₂_inv_app_f_f AlgebraicTopology.DoldKan.n₂Γ₂_inv_app_f_f

end DoldKan

end AlgebraicTopology

