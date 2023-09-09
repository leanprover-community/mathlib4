import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Shift.Pullback
import Mathlib.CategoryTheory.Shift.Opposite
import Mathlib.CategoryTheory.Preadditive.Opposite

namespace CategoryTheory

open Category Limits Preadditive

variable (C : Type*) [Category C]

def PretriangulatedOpposite [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] :=
  PullbackShift (OppositeShift C ℤ)
    (AddMonoidHom.mk' (fun n => -n) (fun a b => by dsimp; abel) : ℤ →+ ℤ)

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace PretriangulatedOpposite

instance : Category (PretriangulatedOpposite C) := by
  dsimp only [PretriangulatedOpposite]
  infer_instance

instance : HasZeroObject (PretriangulatedOpposite C) := by
  dsimp only [PretriangulatedOpposite]
  infer_instance

instance : Preadditive (PretriangulatedOpposite C) := by
  dsimp only [PretriangulatedOpposite]
  infer_instance

noncomputable instance : HasShift (PretriangulatedOpposite C) ℤ := by
  dsimp only [PretriangulatedOpposite]
  infer_instance

instance (n : ℤ) : (shiftFunctor (PretriangulatedOpposite C) n).Additive := by
  dsimp only [PretriangulatedOpposite]
  infer_instance

variable {C}

abbrev mk (X : C) : PretriangulatedOpposite C := Opposite.op X

abbrev homMk {X Y : C} (f : X ⟶ Y) : mk Y ⟶ mk X := Opposite.op f

variable (C)

def opFunctorShiftIso (a b : ℤ) (h : a + b = 0) :
    (shiftFunctor C a).op ≅ shiftFunctor (PretriangulatedOpposite C) b := by
  obtain rfl : a = -b := Iff.mp add_eq_zero_iff_eq_neg h
  rfl

noncomputable def opFunctorShiftCancelIso (n : ℤ) :
    (shiftFunctor C n).op ⋙ shiftFunctor (PretriangulatedOpposite C) n ≅ 𝟭 _ :=
  isoWhiskerLeft _ (opFunctorShiftIso C (-n) n n.add_left_neg).symm ≪≫
    NatIso.op (shiftFunctorCompIsoId C n (-n) n.add_right_neg).symm

noncomputable def opInverseShiftCancelIso (n : ℤ) :
  shiftFunctor (PretriangulatedOpposite C) n ⋙ (shiftFunctor C n).op ≅ 𝟭 _ :=
    isoWhiskerRight (opFunctorShiftIso C (-n) n n.add_left_neg).symm _ ≪≫
      NatIso.op (shiftFunctorCompIsoId C (-n) n n.add_left_neg).symm

variable {C}

lemma opInverseShiftCancelIso_hom_app_comp_opFunctorShiftCancelIso_inv_app (X : C) (n : ℤ) :
  ((opInverseShiftCancelIso C n).hom.app (PretriangulatedOpposite.mk (X⟦n⟧))).unop ≫
    ((opFunctorShiftCancelIso C n).inv.app (Opposite.op X)).unop⟦n⟧' = 𝟙 _:= by
  dsimp [opInverseShiftCancelIso, opFunctorShiftCancelIso, opFunctorShiftIso]
  rw [Functor.map_id, comp_id, comp_id, Quiver.Hom.unop_op,
    shift_shiftFunctorCompIsoId_add_neg_self_hom_app, Iso.inv_hom_id_app]
  rfl

lemma opFunctorShiftCancelIso_inv_app_comp_opInverseShiftCancelIso_hom_app
    (X : PretriangulatedOpposite C) (n : ℤ) :
  (opFunctorShiftCancelIso C n).inv.app ((shiftFunctor (PretriangulatedOpposite C) n).obj X) ≫
    (shiftFunctor (PretriangulatedOpposite C) n).map ((opInverseShiftCancelIso C n).hom.app X) = 𝟙 _ := by
  dsimp [opInverseShiftCancelIso, opFunctorShiftCancelIso, opFunctorShiftIso]
  simp only [comp_id, Functor.map_id, op_id, Functor.map_comp]
  erw [Functor.map_id]
  rw [id_comp]
  apply Quiver.Hom.unop_inj
  rw [unop_comp]
  change ((shiftFunctorCompIsoId C (-n) n n.add_left_neg).inv.app X.unop)⟦-n⟧' ≫
    (shiftFunctorCompIsoId C n (-n) n.add_right_neg).hom.app (X.unop⟦-n⟧) = 𝟙 _
  rw [shift_shiftFunctorCompIsoId_neg_add_self_inv_app, Iso.inv_hom_id_app]
  rfl

end PretriangulatedOpposite

namespace Pretriangulated

namespace TriangleOpEquivalence

open PretriangulatedOpposite

@[simps]
noncomputable def functor : (Triangle C)ᵒᵖ ⥤ Triangle (PretriangulatedOpposite C) where
  obj T := Triangle.mk (homMk T.unop.mor₂) (homMk T.unop.mor₁)
      (-((opFunctorShiftCancelIso C 1).app (Opposite.op T.unop.obj₁)).inv ≫
        (shiftFunctor (PretriangulatedOpposite C) (1 : ℤ)).map ((homMk T.unop.mor₃)))
  map {T₁ T₂} φ :=
    { hom₁ := homMk φ.unop.hom₃
      hom₂ := homMk φ.unop.hom₂
      hom₃ := homMk φ.unop.hom₁
      comm₁ := Opposite.unop_injective (φ.unop.comm₂.symm)
      comm₂ := Opposite.unop_injective (φ.unop.comm₁.symm)
      comm₃ := (by
        dsimp [homMk]
        simp only [neg_comp, Category.assoc, comp_neg]
        rw [← Functor.map_comp]
        erw [← @op_comp _ _ _ _ _ φ.unop.hom₃ T₁.unop.mor₃]
        erw [(opFunctorShiftCancelIso C 1).inv.naturality_assoc φ.unop.hom₁.op]
        dsimp
        rw [← Functor.map_comp]
        congr 3
        exact Opposite.unop_injective (φ.unop.comm₃.symm)) }

@[simps]
noncomputable def inverse : Triangle (PretriangulatedOpposite C) ⥤ (Triangle C)ᵒᵖ where
  obj T := Opposite.op
    (Triangle.mk T.mor₂.unop T.mor₁.unop (-((opInverseShiftCancelIso C 1).hom.app T.obj₁).unop ≫ T.mor₃.unop⟦(1 : ℤ)⟧'))
  map {T₁ T₂} φ := Quiver.Hom.op
    { hom₁ := φ.hom₃.unop
      hom₂ := φ.hom₂.unop
      hom₃ := φ.hom₁.unop
      comm₁ := Opposite.op_injective φ.comm₂.symm
      comm₂ := Opposite.op_injective φ.comm₁.symm
      comm₃ := by
        dsimp
        simp only [neg_comp, assoc, comp_neg, neg_inj, ← Functor.map_comp, ← unop_comp]
        rw [← φ.comm₃, unop_comp, Functor.map_comp, ← assoc, ← assoc]
        congr 1
        apply Opposite.op_injective
        exact (opInverseShiftCancelIso C 1).hom.naturality φ.hom₁ }

@[simps!]
noncomputable def unitIso : 𝟭 _ ≅ functor C ⋙ inverse C :=
  NatIso.ofComponents (fun T => Iso.op (by
    refine' Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) _ _ _
    · aesop_cat
    · aesop_cat
    · dsimp
      simp only [Functor.map_id, Category.comp_id, Category.id_comp]
      erw [Functor.map_neg]
      rw [comp_neg, neg_neg]
      dsimp [opEquiv]
      erw [Functor.map_comp]
      erw [← (NatIso.unop (opInverseShiftCancelIso C 1)).hom.naturality_assoc T.unop.mor₃]
      change T.unop.mor₃ ≫ _ ≫ _ = _
      dsimp
      erw [opInverseShiftCancelIso_hom_app_comp_opFunctorShiftCancelIso_inv_app, comp_id])) (by
        rintro ⟨T₁⟩ ⟨T₂⟩ f
        obtain ⟨f, rfl⟩ : ∃ (g : T₂ ⟶ T₁), f = Quiver.Hom.op g := ⟨f.unop, rfl⟩
        apply Opposite.unop_injective
        ext
        · change 𝟙 _ ≫ f.hom₁ = f.hom₁ ≫ 𝟙 _
          rw [id_comp, comp_id]
        · change 𝟙 _ ≫ f.hom₂ = f.hom₂ ≫ 𝟙 _
          rw [id_comp, comp_id]
        · change 𝟙 _ ≫ f.hom₃ = f.hom₃ ≫ 𝟙 _
          rw [id_comp, comp_id])

@[simps!]
noncomputable def counitIso : inverse C ⋙ functor C ≅ 𝟭 _ :=
  NatIso.ofComponents (fun T => by
    refine' Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) _ _ _
    · aesop_cat
    · aesop_cat
    · dsimp [homMk]
      simp only [Functor.map_id, comp_id, id_comp]
      change - (_ ≫ (shiftFunctor (PretriangulatedOpposite C) (1 : ℤ)).map (- ((T.mor₃.unop⟦(1 : ℤ)⟧').op ≫ _))) = _
      rw [Functor.map_neg, comp_neg, neg_neg, Functor.map_comp]
      erw [← (opFunctorShiftCancelIso C 1).inv.naturality_assoc T.mor₃]
      erw [opFunctorShiftCancelIso_inv_app_comp_opInverseShiftCancelIso_hom_app, comp_id]
      rfl) (by aesop_cat)

end TriangleOpEquivalence

noncomputable def triangleOpEquivalence :
    (Triangle C)ᵒᵖ ≌ Triangle (PretriangulatedOpposite C) where
  functor := TriangleOpEquivalence.functor C
  inverse := TriangleOpEquivalence.inverse C
  unitIso := TriangleOpEquivalence.unitIso C
  counitIso := TriangleOpEquivalence.counitIso C

end Pretriangulated

--instance : Pretriangulated (PretriangulatedOpposite C) := sorry
--
--instance [IsTriangulated C] : IsTriangulated (PretriangulatedOpposite C) := sorry

end CategoryTheory
