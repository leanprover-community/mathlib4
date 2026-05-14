/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.GammaCompN
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.AlgebraicTopology.DoldKan.NReflectsIso
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-! # The unit isomorphism of the Dold-Kan equivalence

In order to construct the unit isomorphism of the Dold-Kan equivalence,
we first construct natural transformations
`Γ₂N₁.natTrans : N₁ ⋙ Γ₂ ⟶ toKaroubi (SimplicialObject C)` and
`Γ₂N₂.natTrans : N₂ ⋙ Γ₂ ⟶ 𝟭 (SimplicialObject C)`.
It is then shown that `Γ₂N₂.natTrans` is an isomorphism by using
that it becomes an isomorphism after the application of the functor
`N₂ : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ)`
which reflects isomorphisms.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Idempotents
  SimplexCategory Opposite SimplicialObject Simplicial DoldKan

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C]

theorem PInfty_comp_map_mono_eq_zero (X : SimplicialObject C) {n : ℕ} {Δ' : SimplexCategory}
    (i : Δ' ⟶ ⦋n⦌) [hi : Mono i] (h₁ : Δ'.len ≠ n) (h₂ : ¬Isδ₀ i) :
    PInfty.f n ≫ X.map i.op = 0 := by
  induction Δ' using SimplexCategory.rec with | _ m
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt (len_lt_of_mono i fun h => by
        rw [← h] at h₁
        exact h₁ rfl)
  rcases k with _ | k
  · change n = m + 1 at hk
    subst hk
    obtain ⟨j, rfl⟩ := eq_δ_of_mono i
    rw [Isδ₀.iff] at h₂
    have h₃ : 1 ≤ (j : ℕ) := by
      by_contra h
      exact h₂ (by simpa only [Fin.ext_iff, not_le, Nat.lt_one_iff] using h)
    exact (HigherFacesVanish.of_P (m + 1) m).comp_δ_eq_zero j h₂ (by lia)
  · simp only [← add_assoc] at hk
    clear h₂ hi
    subst hk
    obtain ⟨j₁ : Fin (_ + 1), i, rfl⟩ :=
      eq_comp_δ_of_not_surjective i fun h => by
        rw [← SimplexCategory.epi_iff_surjective] at h
        grind [→ le_of_epi]
    obtain ⟨j₂, i, rfl⟩ :=
      eq_comp_δ_of_not_surjective i fun h => by
        rw [← SimplexCategory.epi_iff_surjective] at h
        grind [→ le_of_epi]
    by_cases hj₁ : j₁ = 0
    · subst hj₁
      rw [assoc, ← SimplexCategory.δ_comp_δ'' (Fin.zero_le _)]
      simp only [op_comp, X.map_comp, assoc, PInfty_f]
      erw [(HigherFacesVanish.of_P _ _).comp_δ_eq_zero_assoc _ j₂.succ_ne_zero, zero_comp]
      simp only [Fin.succ]
      lia
    · simp only [op_comp, X.map_comp, assoc, PInfty_f]
      erw [(HigherFacesVanish.of_P _ _).comp_δ_eq_zero_assoc _ hj₁, zero_comp]
      by_contra
      exact hj₁ (by simp only [Fin.ext_iff, Fin.val_zero]; lia)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem Γ₀_obj_termwise_mapMono_comp_PInfty (X : SimplicialObject C) {Δ Δ' : SimplexCategory}
    (i : Δ ⟶ Δ') [Mono i] :
    Γ₀.Obj.Termwise.mapMono (AlternatingFaceMapComplex.obj X) i ≫ PInfty.f Δ.len =
      PInfty.f Δ'.len ≫ X.map i.op := by
  induction Δ using SimplexCategory.rec with | _ n
  induction Δ' using SimplexCategory.rec with | _ n'
  dsimp
  -- We start with the case `i` is an identity
  by_cases h : n = n'
  · subst h
    simp only [SimplexCategory.eq_id_of_mono i, Γ₀.Obj.Termwise.mapMono_id, op_id, X.map_id]
    dsimp
    simp only [id_comp, comp_id]
  by_cases hi : Isδ₀ i
  -- The case `i = δ 0`
  · have h' : n' = n + 1 := hi.left
    subst h'
    simp only [Γ₀.Obj.Termwise.mapMono_δ₀' _ i hi]
    rw [← PInfty.comm _ n, AlternatingFaceMapComplex.obj_d_eq]
    simp only [Preadditive.comp_sum]
    rw [Finset.sum_eq_single (0 : Fin (n + 2))]
    rotate_left
    · intro b _ hb
      rw [Preadditive.comp_zsmul, SimplicialObject.δ,
        PInfty_comp_map_mono_eq_zero X (SimplexCategory.δ b) h
          (by
            rw [Isδ₀.iff]
            exact hb),
        zsmul_zero]
    · simp only [Finset.mem_univ, not_true, IsEmpty.forall_iff]
    · simp only [hi.eq_δ₀, Fin.val_zero, pow_zero, one_zsmul]
      rfl
  -- The case `i ≠ δ 0`
  · rw [Γ₀.Obj.Termwise.mapMono_eq_zero _ i _ hi, zero_comp]
    swap
    · by_contra h'
      exact h (congr_arg SimplexCategory.len h'.symm)
    rw [PInfty_comp_map_mono_eq_zero]
    · exact h
    · assumption

variable [HasFiniteCoproducts C]

namespace Γ₂N₁

set_option backward.isDefEq.respectTransparency false in
/-- The natural transformation `N₁ ⋙ Γ₂ ⟶ toKaroubi (SimplicialObject C)`. -/
@[simps]
def natTrans : (N₁ : SimplicialObject C ⥤ _) ⋙ Γ₂ ⟶ toKaroubi _ where
  app X :=
    { f :=
        { app := fun Δ => (Γ₀.splitting K[X]).desc Δ fun A => PInfty.f A.1.unop.len ≫ X.map A.e.op
          naturality := fun Δ Δ' θ => by
            apply (Γ₀.splitting K[X]).hom_ext'
            intro A
            change _ ≫ (Γ₀.obj K[X]).map θ ≫ _ = _
            simp only [Splitting.ι_desc_assoc, assoc, Γ₀.Obj.map_on_summand'_assoc,
              Splitting.ι_desc]
            erw [Γ₀_obj_termwise_mapMono_comp_PInfty_assoc X (image.ι (θ.unop ≫ A.e))]
            dsimp only [toKaroubi]
            simp only [← X.map_comp]
            congr 2
            simp only [← op_comp]
            exact Quiver.Hom.unop_inj (A.fac_pull θ) }
      comm := by
        apply (Γ₀.splitting K[X]).hom_ext
        intro n
        dsimp [N₁]
        simp only [← Splitting.cofan_inj_id, Splitting.ι_desc, comp_id, Splitting.ι_desc_assoc,
          assoc, PInfty_f_idem_assoc] }
  naturality {X Y} f := by
    ext1
    apply (Γ₀.splitting K[X]).hom_ext
    intro n
    dsimp [N₁, toKaroubi]
    simp only [← Splitting.cofan_inj_id, Splitting.ι_desc, Splitting.ι_desc_assoc, assoc,
      PInfty_f_idem_assoc, PInfty_f_naturality_assoc,
      NatTrans.naturality, Splitting.IndexSet.id_fst, unop_op, len_mk]

end Γ₂N₁

/-- The compatibility isomorphism relating `N₂ ⋙ Γ₂` and `N₁ ⋙ Γ₂`. -/
@[simps! hom_app inv_app]
def Γ₂N₂ToKaroubiIso : toKaroubi (SimplicialObject C) ⋙ N₂ ⋙ Γ₂ ≅ N₁ ⋙ Γ₂ :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight toKaroubiCompN₂IsoN₁ Γ₂

namespace Γ₂N₂

/-- The natural transformation `N₂ ⋙ Γ₂ ⟶ 𝟭 (SimplicialObject C)`. -/
def natTrans : (N₂ : Karoubi (SimplicialObject C) ⥤ _) ⋙ Γ₂ ⟶ 𝟭 _ :=
  ((Functor.whiskeringLeft _ _ _).obj (toKaroubi (SimplicialObject C))).preimage
    (Γ₂N₂ToKaroubiIso.hom ≫ Γ₂N₁.natTrans)

set_option backward.isDefEq.respectTransparency false in
theorem natTrans_app_f_app (P : Karoubi (SimplicialObject C)) :
    Γ₂N₂.natTrans.app P =
      (N₂ ⋙ Γ₂).map P.decompId_i ≫
        (Γ₂N₂ToKaroubiIso.hom ≫ Γ₂N₁.natTrans).app P.X ≫ P.decompId_p := by
  dsimp only [natTrans]
  simp only [whiskeringLeft_obj_preimage_app, Functor.id_map]

end Γ₂N₂

set_option backward.isDefEq.respectTransparency false in
theorem compatibility_Γ₂N₁_Γ₂N₂_natTrans (X : SimplicialObject C) :
    Γ₂N₁.natTrans.app X =
      (Γ₂N₂ToKaroubiIso.app X).inv ≫
        Γ₂N₂.natTrans.app ((toKaroubi (SimplicialObject C)).obj X) := by
  rw [Γ₂N₂.natTrans_app_f_app]
  dsimp only [Karoubi.decompId_i_toKaroubi, Karoubi.decompId_p_toKaroubi, Functor.comp_map,
    NatTrans.comp_app]
  rw [N₂.map_id, Γ₂.map_id, Iso.app_inv]
  dsimp only [toKaroubi]
  erw [id_comp]
  rw [comp_id, Iso.inv_hom_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem identity_N₂_objectwise (P : Karoubi (SimplicialObject C)) :
    (N₂Γ₂.inv.app (N₂.obj P) : N₂.obj P ⟶ N₂.obj (Γ₂.obj (N₂.obj P))) ≫
    N₂.map (Γ₂N₂.natTrans.app P) = 𝟙 (N₂.obj P) := by
  ext n
  have eq₁ : (N₂Γ₂.inv.app (N₂.obj P)).f.f n = PInfty.f n ≫ P.p.app (op ⦋n⦌) ≫
      ((Γ₀.splitting (N₂.obj P).X).cofan _).inj (Splitting.IndexSet.id (op ⦋n⦌)) := by
    simp only [N₂Γ₂_inv_app_f_f, N₂_obj_p_f, assoc]
  have eq₂ : ((Γ₀.splitting (N₂.obj P).X).cofan _).inj (Splitting.IndexSet.id (op ⦋n⦌)) ≫
      (N₂.map (Γ₂N₂.natTrans.app P)).f.f n = PInfty.f n ≫ P.p.app (op ⦋n⦌) := by
    dsimp
    rw [PInfty_on_Γ₀_splitting_summand_eq_self_assoc, Γ₂N₂.natTrans_app_f_app]
    dsimp
    rw [Γ₂N₂ToKaroubiIso_hom_app, assoc, Splitting.ι_desc_assoc, assoc, assoc]
    dsimp [toKaroubi]
    rw [Splitting.ι_desc_assoc]
    simp [Splitting.IndexSet.e]
  simp only [Karoubi.comp_f, HomologicalComplex.comp_f, Karoubi.id_f, N₂_obj_p_f, assoc,
    eq₁, eq₂, PInfty_f_naturality_assoc, app_idem, PInfty_f_idem_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem identity_N₂ :
    (𝟙 (N₂ : Karoubi (SimplicialObject C) ⥤ _) ◫ N₂Γ₂.inv) ≫
    (Functor.associator _ _ _).inv ≫ Γ₂N₂.natTrans ◫ 𝟙 (@N₂ C _ _) = 𝟙 N₂ := by
  ext P : 2
  dsimp only [NatTrans.comp_app, NatTrans.hcomp_app, Functor.comp_map, Functor.associator,
    NatTrans.id_app, Functor.comp_obj]
  rw [Γ₂.map_id, N₂.map_id, comp_id, id_comp, id_comp, identity_N₂_objectwise P]

set_option backward.isDefEq.respectTransparency false in
instance : IsIso (Γ₂N₂.natTrans : (N₂ : Karoubi (SimplicialObject C) ⥤ _) ⋙ _ ⟶ _) := by
  have : ∀ P : Karoubi (SimplicialObject C), IsIso (Γ₂N₂.natTrans.app P) := by
    intro P
    have : IsIso (N₂.map (Γ₂N₂.natTrans.app P)) := by
      have h := identity_N₂_objectwise P
      dsimp only [Functor.id_obj, Functor.comp_obj] at h
      rw [hom_comp_eq_id] at h
      rw [h]
      infer_instance
    exact isIso_of_reflects_iso _ N₂
  apply NatIso.isIso_of_isIso_app

set_option backward.isDefEq.respectTransparency false in
instance : IsIso (Γ₂N₁.natTrans : (N₁ : SimplicialObject C ⥤ _) ⋙ _ ⟶ _) := by
  have : ∀ X : SimplicialObject C, IsIso (Γ₂N₁.natTrans.app X) := by
    intro X
    rw [compatibility_Γ₂N₁_Γ₂N₂_natTrans]
    infer_instance
  apply NatIso.isIso_of_isIso_app

/-- The unit isomorphism of the Dold-Kan equivalence. -/
@[simps! inv]
def Γ₂N₂ : 𝟭 _ ≅ (N₂ : Karoubi (SimplicialObject C) ⥤ _) ⋙ Γ₂ :=
  (asIso Γ₂N₂.natTrans).symm

/-- The natural isomorphism `toKaroubi (SimplicialObject C) ≅ N₁ ⋙ Γ₂`. -/
@[simps! inv]
def Γ₂N₁ : toKaroubi _ ≅ (N₁ : SimplicialObject C ⥤ _) ⋙ Γ₂ :=
  (asIso Γ₂N₁.natTrans).symm

end DoldKan

end AlgebraicTopology
