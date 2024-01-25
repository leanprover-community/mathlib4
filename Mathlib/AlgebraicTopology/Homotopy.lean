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

## TODO
* define the homotopy category

-/

namespace Quasicategory

open CategoryTheory Simplicial
open SimplexCategory Finset Opposite
open SSet
/-- A homotopy is a 2-simplex τ satisfying certain conditions on its faces.  -/
class homotopy  {C : SSet} [Quasicategory C] (f g : C _[1]) (τ  : C _[2]) : Prop where
    prop_δ₂ : (C.map (δ 2).op) τ =f
    prop_δ₁ : (C.map (δ 1).op) τ =g
    prop_δ₀ : (C.map (δ 0).op) τ =(C.map (σ 0).op) ((C.map (δ 0).op) f)

/--Two 1-simplices are `homotopic` iff there exists a homotopy between them.-/
def homotopic {C : SSet} [Quasicategory C] (f g : C _[1]) : Prop := ∃ (σ : C _[2]), homotopy f g σ


instance {C :SSet} [Quasicategory C] (f : C _[1]) :
    homotopy f f (C.map (σ 1).op f) where
  prop_δ₂ := by
    rw [← (types_comp_apply (C.map (σ 1).op) (C.map (δ 2).op))]
    rw [← C.map_comp,← op_comp]
    rw [← Fin.succ_one_eq_two,δ_comp_σ_succ]
    rw [op_id,C.map_id,types_id_apply]
  prop_δ₁ := by
    rw [← (types_comp_apply (C.map _) (C.map _)),← C.map_comp,← op_comp]
    rw [δ_comp_σ_self',op_id,C.map_id]
    rfl
    rfl
  prop_δ₀ := by
    rw [← (types_comp_apply (C.map _) (C.map _)),← C.map_comp,← op_comp,← Fin.castSucc_zero,
     ← Fin.succ_zero_eq_one,δ_comp_σ_of_le,op_comp,C.map_comp,types_comp_apply]
    rfl

instance {C :SSet} [Quasicategory C] (X : C _[0]) : homotopy (C.map (σ 0).op X) (C.map (σ 0).op X)
   (C.map (σ  1≫ σ 0).op X):= by
    rw [op_comp,C.map_comp,types_comp_apply]
    infer_instance

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
      let τ'':= C.map (σ  1≫ σ 0).op (C.map (δ 0).op φ)
      have homot'':homotopy (C.map (σ 0).op (C.map (δ 0).op φ))
         (C.map (σ 0).op (C.map (δ 0).op φ))  τ'' := inferInstance
      let three_horn := SSet.horn.homMk₃₁ τ'' τ' τ (by rw [homot'.prop_δ₀,homot''.prop_δ₁])
          (by rw [homot.prop_δ₀,homot''.prop_δ₂]) (by rw [homot.prop_δ₂,homot'.prop_δ₂] )
      obtain ⟨l,hl⟩ := qusi.hornFilling (Fin.one_pos) (Fin.one_lt_last) three_horn
      let ls := l.app (op [3])  ((standardSimplex.objEquiv _ _).invFun  (𝟙 ([3]:SimplexCategory)))
      let ht:= SSet.horn.homMk₃₁_lift_face τ'' τ' τ (by rw [homot'.prop_δ₀,homot''.prop_δ₁])
       (by rw [homot.prop_δ₀,homot''.prop_δ₂]) (by rw [homot.prop_δ₂,homot'.prop_δ₂] ) l hl
        ( C.map (δ 1).op ls) (by rfl)
      use  C.map (δ 1).op ls
      fconstructor
      · rw [ht.right.right]
        exact prop_δ₁ φ
      · rw [ht.right.left]
        exact prop_δ₁ φ
      · rw [ht.left,homot''.prop_δ₀,homotopy.target φ φ' τ]
        apply congrArg
        repeat rw [← (types_comp_apply (C.map _) (C.map _)),← C.map_comp,← op_comp]
        apply congrFun
        apply congrArg
        congr
        rw [δ_comp_σ_self' (by rfl)]
        rfl

/--If there exists a homotopy from `φ` to `φ'` then there exists a homotopy
 from `φ'` to `φ`.-/
lemma symm {C :SSet} [Quasicategory C] (φ φ' : C _[1]) (τ   : C _[2])
    [homotopy φ φ' τ]:  homotopic φ' φ   := by
       obtain ⟨τ',homot'⟩:=refl φ
       exact trans' φ φ' φ τ τ'

lemma symm' {C :SSet} [Quasicategory C] (φ φ' : C _[1]) : homotopic φ' φ ↔ homotopic φ φ' := by
    apply Iff.intro
    · intro h
      obtain ⟨τ,hτ⟩ := h
      apply homotopy.symm φ' φ τ
    · intro h
      obtain ⟨τ,hτ⟩ := h
      apply homotopy.symm φ φ' τ
/--If there exists a homotopy from `φ` to `φ'` and from `φ'` to `φ''` then there exists a homotopy
 from `φ` to `φ''`.-/
lemma trans {C :SSet} [Quasicategory C] (φ φ' φ'': C _[1]) (τ  τ' : C _[2])
    [homotopy φ φ' τ] [homotopy φ' φ'' τ']:  homotopic φ φ''   := by
          obtain ⟨τ'',homot''⟩:=symm φ φ' τ
          exact trans' φ' φ φ'' τ'' τ'

end homotopy
open horn in
/--If φ and φ' are compositions of the same maps, then they are homotopic-/
lemma comp_homotopic {C :SSet} [Quasicategory C]  (τ τ' : C _[2])
    (h₀ : C.map (δ 0).op τ =  C.map (δ 0).op τ') (h₂ : C.map (δ 2).op τ =  C.map (δ 2).op τ') :
    homotopic (C.map (δ 1).op τ) (C.map (δ 1).op τ'):= by
      rename_i qusi
      let g := C.map (δ 0).op τ
      let τ'':= (C.map (σ 1).op g)
      have homot'': homotopy g g τ'' := inferInstance
      let three_horn :=  SSet.horn.homMk₃₁ τ'' τ' τ  (by {rw [homot''.prop_δ₁]; exact h₀})
           (homot''.prop_δ₂) (h₂.symm)
      obtain ⟨l,hl⟩ := qusi.hornFilling (Fin.one_pos) (Fin.one_lt_last) three_horn
      let ls :=  l.app (op [3]) ((standardSimplex.objEquiv _ _).invFun  (𝟙 ([3]:SimplexCategory)))
      let ht:= SSet.horn.homMk₃₁_lift_face τ'' τ' τ (by {rw [homot''.prop_δ₁]; exact h₀})
         (homot''.prop_δ₂) (h₂.symm) l hl (C.map (δ 1).op ls) (by rfl )
      use  C.map (δ 1).op ls
      fconstructor
      · rw [ht.right.right]
      · rw [ht.right.left]
      · rw [ht.left,homot''.prop_δ₀]
        unfold_let g
        repeat rw [← (types_comp_apply (C.map _) (C.map _)),← C.map_comp,← op_comp]
        apply congrFun
        apply congrArg
        apply congrArg
        rfl
section dual
/--We define the dual notion of a homotopy, in which the `δ 2` is the identity.
This dual notion of a homotopy naturally defines a homotopy in the opposite category.-/
class homotopy'  {C : SSet} [Quasicategory C] (f g : C _[1]) (τ  : C _[2]) : Prop where
    prop_δ₂ : (C.map (δ 2).op) τ =(C.map (σ 0).op) ((C.map (δ 1).op) f)
    prop_δ₁ : (C.map (δ 1).op) τ =g
    prop_δ₀ : (C.map (δ 0).op) τ =f

/--Two edges are homotopic' if there exists a homotopy' between them.-/
def homotopic' {C : SSet} [Quasicategory C] (f g : C _[1]) : Prop :=
    ∃ (τ  : C _[2]), homotopy'  f g τ

instance {C :SSet} [Quasicategory C] (f : C _[1]) :
    homotopy' f f (C.map (σ 0).op f) where
  prop_δ₂ := by
     repeat rw [← (types_comp_apply (C.map _) (C.map _)),← C.map_comp,← op_comp]
     rw [δ_comp_σ_of_gt' (by exact Fin.coe_sub_iff_lt.mp rfl)]
     rfl
  prop_δ₁ := by
    rw [← (types_comp_apply (C.map _) (C.map _)),← C.map_comp,← op_comp]
    rw [δ_comp_σ_succ',op_id,C.map_id]
    rfl
    rfl
  prop_δ₀ := by
    rw [← (types_comp_apply (C.map _) (C.map _)),← C.map_comp,← op_comp]
    rw [δ_comp_σ_self' (by rfl),op_id,C.map_id]
    rfl
/--Two edges are homotopic' iff they are homotopic.-/
lemma homotopic'_iff_homotopic_symm {C : SSet} [Quasicategory C] (f g : C _[1]) :
    homotopic' g f ↔ homotopic f g := by
      rename_i quasi
      apply Iff.intro
      · intro homoto'
        obtain ⟨τ₃,hτ₃⟩ := homoto'
        let τ₂:= (C.map (σ 0).op g)
        have hτ₂: homotopy' g g τ₂ := inferInstance
        let τ₀:= (C.map (σ 1).op g)
        have hτ₀: homotopy g g τ₀ := inferInstance
        let three_horn := horn.homMk₃₁ τ₀ τ₂ τ₃ (by rw [hτ₀.prop_δ₁,hτ₂.prop_δ₀])
          (by rw [hτ₀.prop_δ₂,hτ₃.prop_δ₀]) (by rw [hτ₂.prop_δ₂,hτ₃.prop_δ₂])
        obtain ⟨l,hl⟩ := quasi.hornFilling (Fin.one_pos) (Fin.one_lt_last) three_horn
        let ls :=  l.app (op [3]) ((standardSimplex.objEquiv _ _).invFun  (𝟙 ([3]:SimplexCategory)))
        let ht:= SSet.horn.homMk₃₁_lift_face τ₀ τ₂ τ₃ (by rw [hτ₀.prop_δ₁,hτ₂.prop_δ₀])
          (by rw [hτ₀.prop_δ₂,hτ₃.prop_δ₀]) (by rw [hτ₂.prop_δ₂,hτ₃.prop_δ₂])  l hl
          (C.map (δ 1).op ls) (by rfl)
        use  C.map (δ 1).op ls
        fconstructor
        · rw [ht.right.right,hτ₃.prop_δ₁]
        · rw [ht.right.left,hτ₂.prop_δ₁]
        · rw [ht.left,hτ₀.prop_δ₀]
          apply congrArg
          rw [← hτ₃.prop_δ₀,← hτ₃.prop_δ₁]
          repeat rw [← (types_comp_apply (C.map _) (C.map _)),← C.map_comp,← op_comp]
          rw [δ_comp_δ_self']
          rfl
          rfl
      · intro homoto
        obtain ⟨τ₀,hτ₀⟩ := homoto
        let τ₁:= (C.map (σ 1).op f)
        have hτ₁: homotopy f f τ₁ := inferInstance
        let τ₃:= (C.map (σ 0).op f)
        have hτ₃: homotopy' f f τ₃ := inferInstance
        let three_horn := horn.homMk₃₂ τ₀ τ₁ τ₃ (by rw [hτ₀.prop_δ₀,hτ₁.prop_δ₀])
            (by rw [hτ₀.prop_δ₂,hτ₃.prop_δ₀]) (by rw [hτ₁.prop_δ₂,hτ₃.prop_δ₁])
        have h02 : 0< (2:Fin 4):=by exact Fin.coe_sub_iff_lt.mp rfl
        obtain ⟨l,hl⟩ := quasi.hornFilling h02 (by exact Fin.coe_sub_iff_lt.mp rfl)  three_horn
        let ls :=  l.app (op [3]) ((standardSimplex.objEquiv _ _).invFun  (𝟙 ([3]:SimplexCategory)))
        let ht:= SSet.horn.homMk₃₂_lift_face τ₀ τ₁ τ₃ (by rw [hτ₀.prop_δ₀,hτ₁.prop_δ₀])
            (by rw [hτ₀.prop_δ₂,hτ₃.prop_δ₀]) (by rw [hτ₁.prop_δ₂,hτ₃.prop_δ₁])
              l hl (C.map (δ 2).op ls) (by rfl)
        use  C.map (δ 2).op ls
        fconstructor
        · rw [ht.right.right,hτ₃.prop_δ₂]
          apply congrArg
          exact homotopy.source f g τ₀
        · rw [ht.right.left,hτ₁.prop_δ₁]
        · rw [ht.left,hτ₀.prop_δ₁]

lemma homotopic'_iff_homotopic  {C : SSet} [Quasicategory C] (f g : C _[1]) :
    homotopic' f g ↔ homotopic f g  := by
      rw [homotopy.symm' g f ]
      exact homotopic'_iff_homotopic_symm g f

end dual
