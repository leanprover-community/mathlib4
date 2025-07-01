/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.DoldKan.FunctorGamma
import Mathlib.AlgebraicTopology.DoldKan.SplitSimplicialObject
import Mathlib.CategoryTheory.Idempotents.HomologicalComplex
import Mathlib.Tactic.SuppressCompilation

/-! The counit isomorphism of the Dold-Kan equivalence

The purpose of this file is to construct natural isomorphisms
`N₁Γ₀ : Γ₀ ⋙ N₁ ≅ toKaroubi (ChainComplex C ℕ)`
and `N₂Γ₂ : Γ₂ ⋙ N₂ ≅ 𝟭 (Karoubi (ChainComplex C ℕ))`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

suppress_compilation

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
  CategoryTheory.Idempotents Opposite SimplicialObject Simplicial

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category C] [Preadditive C] [HasFiniteCoproducts C]

/-- The isomorphism `(Γ₀.splitting K).nondegComplex ≅ K` for all `K : ChainComplex C ℕ`. -/
@[simps!]
def Γ₀NondegComplexIso (K : ChainComplex C ℕ) : (Γ₀.splitting K).nondegComplex ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by
      rintro _ n (rfl : n + 1 = _)
      dsimp
      simp only [id_comp, comp_id, AlternatingFaceMapComplex.obj_d_eq, Preadditive.sum_comp,
        Preadditive.comp_sum]
      rw [Fintype.sum_eq_single (0 : Fin (n + 2))]
      · simp only [Fin.val_zero, pow_zero, one_zsmul]
        rw [δ, Γ₀.Obj.mapMono_on_summand_id_assoc, Γ₀.Obj.Termwise.mapMono_δ₀,
          Splitting.cofan_inj_πSummand_eq_id]
        dsimp only [Γ₀.splitting, Splitting.summand.eq_1, Splitting.IndexSet.id_fst]
        rw [comp_id]
      · intro i hi
        dsimp
        simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, assoc]
        rw [δ, Γ₀.Obj.mapMono_on_summand_id_assoc, Γ₀.Obj.Termwise.mapMono_eq_zero, zero_comp,
          zsmul_zero]
        · intro h
          replace h := congr_arg SimplexCategory.len h
          change n + 1 = n at h
          omega
        · simpa only [Isδ₀.iff] using hi)

/-- The natural isomorphism `(Γ₀.splitting K).nondegComplex ≅ K` for `K : ChainComplex C ℕ`. -/
def Γ₀'CompNondegComplexFunctor : Γ₀' ⋙ Split.nondegComplexFunctor ≅ 𝟭 (ChainComplex C ℕ) :=
  NatIso.ofComponents Γ₀NondegComplexIso

/-- The natural isomorphism `Γ₀ ⋙ N₁ ≅ toKaroubi (ChainComplex C ℕ)`. -/
def N₁Γ₀ : Γ₀ ⋙ N₁ ≅ toKaroubi (ChainComplex C ℕ) :=
  calc
    Γ₀ ⋙ N₁ ≅ Γ₀' ⋙ Split.forget C ⋙ N₁ := Functor.associator _ _ _
    _ ≅ Γ₀' ⋙ Split.nondegComplexFunctor ⋙ toKaroubi _ :=
      (isoWhiskerLeft Γ₀' Split.toKaroubiNondegComplexFunctorIsoN₁.symm)
    _ ≅ (Γ₀' ⋙ Split.nondegComplexFunctor) ⋙ toKaroubi _ := (Functor.associator _ _ _).symm
    _ ≅ 𝟭 _ ⋙ toKaroubi (ChainComplex C ℕ) := isoWhiskerRight Γ₀'CompNondegComplexFunctor _
    _ ≅ toKaroubi (ChainComplex C ℕ) := Functor.leftUnitor _

theorem N₁Γ₀_app (K : ChainComplex C ℕ) :
    N₁Γ₀.app K = (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.symm ≪≫
      (toKaroubi _).mapIso (Γ₀NondegComplexIso K) := by
  ext1
  dsimp [N₁Γ₀]
  erw [id_comp, comp_id, comp_id]
  rfl

theorem N₁Γ₀_hom_app (K : ChainComplex C ℕ) :
    N₁Γ₀.hom.app K = (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.inv ≫
        (toKaroubi _).map (Γ₀NondegComplexIso K).hom := by
  change (N₁Γ₀.app K).hom = _
  simp only [N₁Γ₀_app]
  rfl

theorem N₁Γ₀_inv_app (K : ChainComplex C ℕ) :
    N₁Γ₀.inv.app K = (toKaroubi _).map (Γ₀NondegComplexIso K).inv ≫
        (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.hom := by
  change (N₁Γ₀.app K).inv = _
  simp only [N₁Γ₀_app]
  rfl

@[simp]
theorem N₁Γ₀_hom_app_f_f (K : ChainComplex C ℕ) (n : ℕ) :
    (N₁Γ₀.hom.app K).f.f n = (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.inv.f.f n := by
  rw [N₁Γ₀_hom_app]
  apply comp_id

@[simp]
theorem N₁Γ₀_inv_app_f_f (K : ChainComplex C ℕ) (n : ℕ) :
    (N₁Γ₀.inv.app K).f.f n = (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.hom.f.f n := by
  rw [N₁Γ₀_inv_app]
  apply id_comp

/-- Compatibility isomorphism between `toKaroubi _ ⋙ Γ₂ ⋙ N₂` and `Γ₀ ⋙ N₁` which
are functors `ChainComplex C ℕ ⥤ Karoubi (ChainComplex C ℕ)`. -/
def N₂Γ₂ToKaroubiIso : toKaroubi (ChainComplex C ℕ) ⋙ Γ₂ ⋙ N₂ ≅ Γ₀ ⋙ N₁ :=
  calc
    toKaroubi (ChainComplex C ℕ) ⋙ Γ₂ ⋙ N₂ ≅
      toKaroubi (ChainComplex C ℕ) ⋙ (Γ₂ ⋙ N₂) := (Functor.associator _ _ _).symm
    _ ≅ (Γ₀ ⋙ toKaroubi (SimplicialObject C)) ⋙ N₂ :=
        isoWhiskerRight ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app Γ₀) N₂
    _ ≅ Γ₀ ⋙ toKaroubi (SimplicialObject C) ⋙ N₂ := Functor.associator _ _ _
    _ ≅ Γ₀ ⋙ N₁ :=
      isoWhiskerLeft Γ₀ ((functorExtension₁CompWhiskeringLeftToKaroubiIso _ _).app N₁)

@[simp]
lemma N₂Γ₂ToKaroubiIso_hom_app (X : ChainComplex C ℕ) :
    (N₂Γ₂ToKaroubiIso.hom.app X).f = PInfty := by
  ext n
  dsimp [N₂Γ₂ToKaroubiIso]
  simp only [comp_id, assoc, PInfty_f_idem]
  conv_rhs =>
    rw [← PInfty_f_idem]
  congr 1
  apply (Γ₀.splitting X).hom_ext'
  intro A
  rw [Splitting.ι_desc_assoc, assoc]
  apply id_comp

@[simp]
lemma N₂Γ₂ToKaroubiIso_inv_app (X : ChainComplex C ℕ) :
    (N₂Γ₂ToKaroubiIso.inv.app X).f = PInfty := by
  ext n
  dsimp [N₂Γ₂ToKaroubiIso]
  simp only [comp_id, PInfty_f_idem_assoc, AlternatingFaceMapComplex.obj_X, Γ₀_obj_obj]
  convert comp_id _
  apply (Γ₀.splitting X).hom_ext'
  intro A
  rw [Splitting.ι_desc]
  erw [comp_id, id_comp]

/-- The counit isomorphism of the Dold-Kan equivalence for additive categories. -/
def N₂Γ₂ : Γ₂ ⋙ N₂ ≅ 𝟭 (Karoubi (ChainComplex C ℕ)) :=
  ((whiskeringLeft _ _ _).obj (toKaroubi (ChainComplex C ℕ))).preimageIso
      (N₂Γ₂ToKaroubiIso ≪≫ N₁Γ₀)

@[simp]
theorem N₂Γ₂_inv_app_f_f (X : Karoubi (ChainComplex C ℕ)) (n : ℕ) :
    (N₂Γ₂.inv.app X).f.f n =
      X.p.f n ≫ ((Γ₀.splitting X.X).cofan _).inj (Splitting.IndexSet.id (op ⦋n⦌)) := by
  dsimp [N₂Γ₂]
  simp only [whiskeringLeft_obj_preimage_app, NatTrans.comp_app, Functor.comp_map,
    Karoubi.comp_f, N₂Γ₂ToKaroubiIso_inv_app, HomologicalComplex.comp_f,
    N₁Γ₀_inv_app_f_f, toKaroubi_obj_X, Splitting.toKaroubiNondegComplexIsoN₁_hom_f_f,
    Γ₀.obj_obj, PInfty_on_Γ₀_splitting_summand_eq_self, N₂_map_f_f,
    Γ₂_map_f_app, unop_op, Karoubi.decompId_p_f, PInfty_f_idem_assoc,
    PInfty_on_Γ₀_splitting_summand_eq_self_assoc, Splitting.IndexSet.id_fst, SimplexCategory.len_mk,
    Splitting.ι_desc]
  apply Karoubi.HomologicalComplex.p_idem_assoc

lemma whiskerLeft_toKaroubi_N₂Γ₂_hom :
    whiskerLeft (toKaroubi (ChainComplex C ℕ)) N₂Γ₂.hom = N₂Γ₂ToKaroubiIso.hom ≫ N₁Γ₀.hom := by
  let e : _ ≅ toKaroubi (ChainComplex C ℕ) ⋙ 𝟭 _ := N₂Γ₂ToKaroubiIso ≪≫ N₁Γ₀
  have h := ((whiskeringLeft _ _ (Karoubi (ChainComplex C ℕ))).obj
    (toKaroubi (ChainComplex C ℕ))).map_preimage e.hom
  dsimp only [whiskeringLeft, N₂Γ₂, Functor.preimageIso] at h ⊢
  exact h

theorem N₂Γ₂_compatible_with_N₁Γ₀ (K : ChainComplex C ℕ) :
    N₂Γ₂.hom.app ((toKaroubi _).obj K) = N₂Γ₂ToKaroubiIso.hom.app K ≫ N₁Γ₀.hom.app K :=
  congr_app whiskerLeft_toKaroubi_N₂Γ₂_hom K

end DoldKan

end AlgebraicTopology
