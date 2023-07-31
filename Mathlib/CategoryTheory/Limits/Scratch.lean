import Mathlib.CategoryTheory.Limits.Presheaf

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

open Opposite

variable {C : Type u₁} [Category.{v₁} C] (A : Cᵒᵖ ⥤ Type v₁)

def F : CostructuredArrow yoneda A ⥤ C :=
  CostructuredArrow.proj _ _

def FF : CostructuredArrow yoneda A ⥤ Cᵒᵖ ⥤ Type v₁ :=
  CostructuredArrow.proj yoneda A ⋙ yoneda

def goal : coyoneda.obj (op A) ≅ (CostructuredArrow.proj yoneda A ⋙ yoneda).cocones :=
  NatIso.ofComponents
  (fun X => by
    refine' ⟨fun f => ⟨fun V => V.hom ≫ f, by aesop_cat⟩, _, _, _⟩
    · intro f
      refine' ⟨fun Y t => yonedaEquiv (f.app (CostructuredArrow.mk (yonedaEquiv.symm t))), _⟩
      · intros Y Z g
        ext x
        dsimp
        erw [yonedaEquiv_naturality]
        congr
        have fn := f.naturality
        dsimp at fn
        simp at fn
        dsimp at f
        let hq : CostructuredArrow.mk (yonedaEquiv.symm (A.map g x)) ⟶ CostructuredArrow.mk (yonedaEquiv.symm x) :=
          CostructuredArrow.homMk g.unop (by
            apply yonedaEquiv.injective
            rw [←yonedaEquiv_naturality]
            simp)
        have := fn hq
        exact this.symm
    · ext f
      dsimp at f
      dsimp
      ext X a
      dsimp
      erw [yonedaEquiv_apply (_ ≫ f)]
      simp
      apply congr_arg
      erw [yonedaEquiv_symm_app_apply]
      simp
    · ext f
      dsimp at f
      dsimp
      ext1
      ext1 Y
      dsimp
      have hf := f.naturality
      dsimp at hf
      ext Z b
      dsimp at b
      dsimp
      let hq : CostructuredArrow.mk (yonedaEquiv.symm (NatTrans.app Y.hom Z b)) ⟶ Y :=
        CostructuredArrow.homMk b (by
          dsimp
          apply yonedaEquiv.injective

          rw [←yonedaEquiv_naturality ]
          simp
          sorry)
      have := hf hq
      dsimp at this
      simp at this
      rw [←this ]

      erw [← yonedaEquiv_naturality]
      simp



    )
  (by aesop_cat)

end CategoryTheory.Limits
