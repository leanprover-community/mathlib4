import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Shift.Pullback
import Mathlib.CategoryTheory.Shift.Opposite
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Triangulated.Functor

namespace CategoryTheory

open Category Limits Preadditive ZeroObject

variable (C : Type*) [Category C]

namespace Pretriangulated

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

lemma opFunctorShiftCancelIso_inv_app_op_unop_shift_op (X : C) (n : ℤ) :
  (((opFunctorShiftCancelIso C n).inv.app (Opposite.op X)).unop⟦n⟧').op =
    (opInverseShiftCancelIso C n).inv.app (PretriangulatedOpposite.mk (X⟦n⟧)) := by
  dsimp [opInverseShiftCancelIso, opFunctorShiftCancelIso, opFunctorShiftIso]
  simp only [comp_id, Quiver.Hom.unop_op]
  erw [Functor.map_id, comp_id, shift_shiftFunctorCompIsoId_add_neg_self_hom_app]

variable (C)

namespace TriangleOpEquivalence

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

@[simps]
noncomputable def triangleOpEquivalence :
    (Triangle C)ᵒᵖ ≌ Triangle (PretriangulatedOpposite C) where
  functor := TriangleOpEquivalence.functor C
  inverse := TriangleOpEquivalence.inverse C
  unitIso := TriangleOpEquivalence.unitIso C
  counitIso := TriangleOpEquivalence.counitIso C

def distinguishedTriangles : Set (Triangle (PretriangulatedOpposite C)) :=
  fun T => ((triangleOpEquivalence C).inverse.obj T).unop ∈ distTriang C

variable {C}

lemma mem_distinguishedOp_iff (T : Triangle (PretriangulatedOpposite C)) :
    T ∈ distinguishedTriangles C ↔ ((triangleOpEquivalence C).inverse.obj T).unop ∈ distTriang C :=
  by rfl

lemma mem_distinguishedOp_iff' (T : Triangle (PretriangulatedOpposite C)) :
    T ∈ distinguishedTriangles C ↔ ∃ (T' : Triangle C) (_ : T' ∈ distTriang C),
      Nonempty (T ≅ (triangleOpEquivalence C).functor.obj (Opposite.op T')) := by
  rw [mem_distinguishedOp_iff]
  constructor
  · intro hT
    exact ⟨_ ,hT, ⟨(triangleOpEquivalence C).counitIso.symm.app T⟩⟩
  · rintro ⟨T', hT', ⟨e⟩⟩
    refine' isomorphic_distinguished _ hT' _ _
    exact Iso.unop ((triangleOpEquivalence C).unitIso.app (Opposite.op T') ≪≫
      (triangleOpEquivalence C).inverse.mapIso e.symm)

lemma isomorphic_distinguished (T₁ : Triangle (PretriangulatedOpposite C))
    (hT₁ : T₁ ∈ distinguishedTriangles C) (T₂ : Triangle (PretriangulatedOpposite C))
    (e : T₂ ≅ T₁) :
    T₂ ∈ distinguishedTriangles C := by
  simp only [mem_distinguishedOp_iff] at hT₁ ⊢
  exact Pretriangulated.isomorphic_distinguished _ hT₁ _
    ((triangleOpEquivalence C).inverse.mapIso e).unop.symm

lemma contractibleTriangleIso (X : PretriangulatedOpposite C) :
    contractibleTriangle X ≅ (triangleOpEquivalence C).functor.obj
      (Opposite.op (contractibleTriangle X.unop).invRotate) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    { hom := 0
      inv := 0
      inv_hom_id := IsZero.eq_of_tgt (by
        rw [IsZero.iff_id_eq_zero]
        change (𝟙 ((0 : C)⟦(-1 : ℤ)⟧)).op = 0
        rw [← Functor.map_id, id_zero, Functor.map_zero, op_zero]) _ _ }
    (by aesop_cat) (by aesop_cat) (by aesop_cat)

lemma contractible_distinguished (X : PretriangulatedOpposite C) :
    contractibleTriangle X ∈ distinguishedTriangles C := by
  rw [mem_distinguishedOp_iff']
  exact ⟨_, inv_rot_of_dist_triangle _ (Pretriangulated.contractible_distinguished X.unop),
    ⟨contractibleTriangleIso X⟩⟩

noncomputable def rotateTriangleOpEquivalenceInverseObjRotateUnop
    (T : Triangle (PretriangulatedOpposite C)) :
    Triangle.rotate ((triangleOpEquivalence C).inverse.obj (Triangle.rotate T)).unop ≅
      ((triangleOpEquivalence C).inverse.obj T).unop := by
  refine' Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      ((opInverseShiftCancelIso C 1).symm.app T.obj₁).unop _ _ _
  · dsimp
    simp
  · dsimp
    rw [neg_comp, id_comp]
    erw [Functor.map_neg]
    dsimp
    rw [comp_neg, neg_comp, neg_neg]
    apply Quiver.Hom.op_inj
    simp only [op_comp, assoc]
    erw [(opInverseShiftCancelIso C 1).hom.naturality T.mor₁]
    dsimp
    rw [Iso.inv_hom_id_app_assoc]
  · dsimp
    simp only [Functor.map_id, comp_id, comp_neg, neg_inj, ← assoc, ← unop_comp,
      Iso.hom_inv_id_app, Functor.comp_obj, Functor.op_obj, unop_id, Opposite.unop_op, id_comp]

lemma rotate_distinguished_triangle (T : Triangle (PretriangulatedOpposite C)) :
    T ∈ distinguishedTriangles C ↔ T.rotate ∈ distinguishedTriangles C := by
  simp only [mem_distinguishedOp_iff, Pretriangulated.rotate_distinguished_triangle
    ((triangleOpEquivalence C).inverse.obj (T.rotate)).unop]
  exact distinguished_iff_of_iso (rotateTriangleOpEquivalenceInverseObjRotateUnop T).symm

lemma distinguished_cocone_triangle {X Y : PretriangulatedOpposite C} (f : X ⟶ Y) :
    ∃ (Z : PretriangulatedOpposite C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distinguishedTriangles C := by
  obtain ⟨Z, g, h, H⟩ := Pretriangulated.distinguished_cocone_triangle₁ f.unop
  simp only [mem_distinguishedOp_iff]
  refine' ⟨_, g.op, -(opFunctorShiftCancelIso C 1).inv.app (Opposite.op Z) ≫
    (shiftFunctor (PretriangulatedOpposite C) (1 : ℤ)).map h.op, _⟩
  dsimp
  convert H using 2
  rw [unop_neg, Functor.map_neg, comp_neg, neg_neg, unop_comp, Functor.map_comp]
  apply Quiver.Hom.op_inj
  simp only [op_comp]
  rw [← cancel_mono ((opInverseShiftCancelIso C 1).inv.app X) ]
  simp only [Opposite.op_unop, Quiver.Hom.op_unop, assoc]
  dsimp
  erw [Iso.hom_inv_id_app, comp_id]
  erw [(opInverseShiftCancelIso C 1).inv.naturality h.op]
  rw [opFunctorShiftCancelIso_inv_app_op_unop_shift_op]
  rfl

lemma complete_distinguished_triangle_morphism (T₁ T₂ : Triangle (PretriangulatedOpposite C))
    (hT₁ : T₁ ∈ distinguishedTriangles C) (hT₂ : T₂ ∈ distinguishedTriangles C)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  rw [mem_distinguishedOp_iff] at hT₁ hT₂
  obtain ⟨c, hc₁, hc₂⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁ _ _ hT₂ hT₁ b.unop
    a.unop (Quiver.Hom.op_inj comm.symm)
  dsimp at c hc₁ hc₂
  simp only [neg_comp, assoc, comp_neg, neg_inj] at hc₂
  refine' ⟨c.op, Quiver.Hom.unop_inj hc₁.symm, Quiver.Hom.unop_inj _⟩
  apply (shiftFunctor C (1 : ℤ)).map_injective
  rw [unop_comp, unop_comp, Functor.map_comp, Functor.map_comp, Quiver.Hom.unop_op,
      ← cancel_epi ((opInverseShiftCancelIso C 1).hom.app T₂.obj₁).unop, hc₂]
  apply Quiver.Hom.op_inj
  simp only [op_comp, Functor.id_obj, Opposite.op_unop, Functor.comp_obj, Functor.op_obj,
    Opposite.unop_op, Quiver.Hom.op_unop, assoc]
  congr 1
  exact (opInverseShiftCancelIso C 1).hom.naturality a

instance : Pretriangulated (PretriangulatedOpposite C) where
  distinguishedTriangles := distinguishedTriangles C
  isomorphic_distinguished := isomorphic_distinguished
  contractible_distinguished := contractible_distinguished
  distinguished_cocone_triangle := distinguished_cocone_triangle
  rotate_distinguished_triangle := rotate_distinguished_triangle
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism

--instance [IsTriangulated C] : IsTriangulated (PretriangulatedOpposite C) := sorry

end PretriangulatedOpposite

namespace Opposite
-- `open Pretriangulated.Opposite` to get these instances

variable (C : Type*) [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

noncomputable scoped instance : HasShift Cᵒᵖ ℤ :=
  (inferInstance : HasShift (PretriangulatedOpposite C) ℤ)

noncomputable scoped instance (n : ℤ) : (shiftFunctor Cᵒᵖ n).Additive :=
  (inferInstance : (shiftFunctor (PretriangulatedOpposite C) n).Additive)

scoped instance : Pretriangulated Cᵒᵖ :=
  (inferInstance : Pretriangulated (PretriangulatedOpposite C))

end Opposite

end Pretriangulated

end CategoryTheory
