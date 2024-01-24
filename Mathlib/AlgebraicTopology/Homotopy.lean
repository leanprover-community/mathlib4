/-
Copyright (c) 2023 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/

import Mathlib.AlgebraicTopology.SimplicialObject
import Mathlib.AlgebraicTopology.Quasicategory
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # Homotopies in quasi-categories

A homotopy in a quasi-category is a 2-simplex such that the 0-edge is the identity.

We define homotopies and show that they form an equivelence relation.

-/

namespace SSet

open CategoryTheory Simplicial
open SimplexCategory Finset Opposite

class homotopy  {C : SSet} [Quasicategory C] (f g : C _[1]) (τ  : C _[2]) : Prop where
    prop_δ₂ : (C.map (δ 2).op) τ =f
    prop_δ₁ : (C.map (δ 1).op) τ =g
    prop_δ₀ : (C.map (δ 0).op) τ =(C.map (σ 0).op) ((C.map (δ 0).op) f)

/--Two 1-simplices are `homotopic` iff there exists a homotopy between them.-/
def homotopic {C : SSet} [Quasicategory C] (f g : C _[1]) : Prop := ∃ (σ : C _[2]), homotopy f g σ

namespace homotopy
/--Two 1-simplies which are homotopic have the same target.-/
lemma target {C : SSet} [Quasicategory C] (f g : C _[1]) (τ  : C _[2]) [homotopy f g τ ]:
    C.map (δ 0).op f = C.map (δ 0).op g := by
    rename_i homot
    rw [← homot.prop_δ₂,← homot.prop_δ₁]
    repeat rw [← (types_comp_apply (C.map _) (C.map _)),← C.map_comp,← op_comp]
    change C.map (δ 0 ≫ δ (Fin.succ 1)).op τ = C.map (δ 0 ≫ δ (Fin.succ 0)).op τ
    rw [δ_comp_δ (Fin.zero_le 0),δ_comp_δ (Fin.zero_le 1)]
    change C.map (δ 1 ≫ δ 0).op τ = C.map (δ 0 ≫ δ 0).op τ
    repeat rw [op_comp,C.map_comp,types_comp_apply]
    rw [homot.prop_δ₀ ]
    repeat rw [← (types_comp_apply (C.map _) (C.map _)),← C.map_comp,← op_comp]
    have hd : δ 1 ≫ σ (0: Fin 1)= δ 0 ≫ σ 0 := by
        ext
        simp_all only [len_mk, Hom.toOrderHom_mk, OrderHom.comp_coe, Function.comp_apply,
        Fin.coe_fin_one]
    rw [hd]

/--Two 1-simplies which are homotopic have the same source.-/
lemma source {C : SSet} [Quasicategory C] (f g : C _[1]) (τ  : C _[2]) [homotopy f g τ ]:
    C.map (δ 1).op f = C.map (δ 1).op g := by
    rename_i homot
    rw [← homot.prop_δ₂,← homot.prop_δ₁]
    repeat rw [← (types_comp_apply (C.map _) (C.map _)),← C.map_comp,← op_comp]
    change C.map (δ 1 ≫ δ (Fin.succ 1)).op τ = C.map (δ 1 ≫ δ 1).op τ
    rw [ δ_comp_δ]
    rfl
    rfl


instance {C :SSet} [Quasicategory C] (f : C _[1]) :
    homotopy f f (C.map (SimplexCategory.σ  1).op f) where
  prop_δ₂ := by
    rw [← (types_comp_apply (C.map (σ 1).op) (C.map (δ 2).op))]
    rw [← C.map_comp,← op_comp]
    rw [← Fin.succ_one_eq_two,δ_comp_σ_succ]
    rw [op_id,C.map_id,types_id_apply]
  prop_δ₁ := by
    rw [← (types_comp_apply (C.map _) (C.map _))]
    rw [← C.map_comp,← op_comp]
    rw [← Fin.castSucc_one,δ_comp_σ_self']
    rw [op_id,C.map_id,types_id_apply]
    rfl
  prop_δ₀ := by
    rw [← (types_comp_apply (C.map _) (C.map _)),← C.map_comp,← op_comp,← Fin.castSucc_zero,
     ← Fin.succ_zero_eq_one,δ_comp_σ_of_le,op_comp,C.map_comp,types_comp_apply]
    rfl
/--Any 1-simplies is homotopic to itself.-/
lemma refl  {C : SSet} [Quasicategory C] (f : C _[1]) : homotopic f f := by
   fconstructor
   exact  (C.map (SimplexCategory.σ  1).op f)
   infer_instance


/--If there exists a homotopy from `φ` to `φ'` and from `φ` to `φ''` then there exists a homotopy
 from `φ'` to `φ''`.-/
lemma trans' {C :SSet} [Quasicategory C] (φ φ' φ'' : C _[1]) (τ  τ' : C _[2])
    [homotopy φ φ' τ] [homotopy φ φ'' τ'] : homotopic φ' φ''  :=by
      rename_i qusi homot homot'
      let τ'':= C.map (σ  0≫ σ 0).op (C.map (δ 0).op φ)
      let face_map : Fin 3 → C _[2]
       | 0 => τ''
       | 1 => τ'
       | 2 => τ
      have hface : (i1 : Fin (3))→ (i2 : Fin (3)) → (i1< i2) →
    C.map (δ (Fin.predAbove 0 ((δ 1).toOrderHom i2))).op (face_map i1)
    =C.map (δ (Fin.predAbove (Fin.last (2)) ((δ 1).toOrderHom i1))).op (face_map i2) :=by
        intro i1 i2 i1_lt_i2
        fin_cases i1, i2
        any_goals rfl
        any_goals (rw [Fin.lt_def] at i1_lt_i2; simp at i1_lt_i2)
        ·  change C.map (δ 1).op τ''=C.map (δ 0).op τ'
           rw [homot'.prop_δ₀,← (types_comp_apply (C.map _) (C.map _))]
           rw [← C.map_comp,← op_comp,← Category.assoc,δ_comp_σ_succ']
           rfl
           rfl
        · change  C.map (δ 2).op τ'' =C.map (δ 0).op τ
          rw [homot.prop_δ₀]
          repeat rw [← (types_comp_apply (C.map _) (C.map _)),← C.map_comp,← op_comp]
          apply congrFun
          repeat apply congrArg
          congr
          ext
          simp_all only [OrderHom.comp_coe, Function.comp_apply, Fin.coe_fin_one]
        · change  C.map (δ 2).op τ' =C.map (δ 2).op  τ
          rw [homot.prop_δ₂,homot'.prop_δ₂]
      let three_horn := SSet.horn.homMk 1 face_map hface
      have h01 : (0:Fin 4) < (1:Fin 4):=Fin.one_pos
      have h0n: (1:Fin 4) < (Fin.last 3):=Fin.one_lt_last
      obtain ⟨lift,hlift⟩ := qusi.hornFilling h01 h0n three_horn
      let lift_simplex : C _[3] :=  lift.app (op [3])
         ((standardSimplex.objEquiv ([3]) (op [3])).invFun  (𝟙 ([3]:SimplexCategory)))
      have lift₂ : C.map (δ 2).op lift_simplex = τ' :=  horn.homMk_lift_face (1 : Fin 4) (1 : Fin 3)
          face_map hface lift hlift
      have lift₃ : C.map (δ 3).op lift_simplex = τ :=  horn.homMk_lift_face (1 : Fin 4) (2 : Fin 3)
               face_map hface lift hlift
      have lift₀ : C.map (δ 0).op lift_simplex = τ'' :=horn.homMk_lift_face (1 : Fin 4) (0 : Fin 3)
               face_map hface lift hlift
      use C.map (δ 1).op lift_simplex
      fconstructor
      all_goals rw [← (types_comp_apply (C.map _) (C.map _) ),← C.map_comp,← op_comp]
      all_goals rw [show δ (1 : Fin 4)= δ (Fin.castSucc 1) from rfl]
      · rw [← δ_comp_δ,op_comp,C.map_comp,types_comp_apply]
        change C.map (δ 1).op (C.map (δ 3).op lift_simplex) = φ'
        rw [lift₃]
        exact homot.prop_δ₁
        exact Nat.le_succ 1
      · rw [← δ_comp_δ,op_comp,C.map_comp,types_comp_apply]
        change C.map (δ 1).op (C.map (δ 2).op lift_simplex) = φ''
        rw [lift₂]
        exact homot'.prop_δ₁
        rfl
      · rw [congrArg δ Fin.castSucc_one,δ_comp_δ' (by {rw [Fin.lt_def];simp }),op_comp,C.map_comp,
           types_comp_apply, congrArg δ Fin.castSucc_zero,lift₀,(target φ φ' τ).symm ]
        repeat rw [← (types_comp_apply (C.map _) (C.map _)),← C.map_comp,← op_comp]
        apply congrFun
        repeat apply congrArg
        congr
        ext
        simp_all only [OrderHom.comp_coe, Function.comp_apply, Fin.coe_fin_one]

/--If there exists a homotopy from `φ` to `φ'` then there exists a homotopy
 from `φ'` to `φ`.-/
lemma symm {C :SSet} [Quasicategory C] (φ φ' : C _[1]) (τ   : C _[2])
    [homotopy φ φ' τ]:  homotopic φ' φ   := by
       obtain ⟨τ',homot'⟩:=refl φ
       exact trans' φ φ' φ τ τ'
/--If there exists a homotopy from `φ` to `φ'` and from `φ'` to `φ''` then there exists a homotopy
 from `φ` to `φ''`.-/
lemma trans {C :SSet} [Quasicategory C] (φ φ' φ'': C _[1]) (τ  τ' : C _[2])
    [homotopy φ φ' τ] [homotopy φ' φ'' τ']:  homotopic φ φ''   := by
          obtain ⟨τ'',homot''⟩:=symm φ φ' τ
          exact trans' φ' φ φ'' τ'' τ'

end homotopy
