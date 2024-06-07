import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.Tactic.Widget.CommDiag
import ProofWidgets.Component.Panel.GoalTypePanel
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import ProofWidgets.Component.Panel.SelectionPanel
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Limits.Fubini

universe u v u' v' u'' v''

open CategoryTheory Limits ProofWidgets

variable {C : Type u} {D : Type u'} {E : Type u''} [Category.{v, u} C] [Category.{v', u'} D]
  [Category.{v'', u''} E]

variable {X Y Z X' Y' Z' : C} [HasBinaryProduct X X'] [HasBinaryProduct Y X']
  [HasBinaryProduct Z X'] [HasBinaryProduct X Y'] [HasBinaryProduct Y Y']
  [HasBinaryProduct Z Y'] [HasBinaryProduct X Z'] [HasBinaryProduct Y Z']
  [HasBinaryProduct Z Z']

variable {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}

variable {F : C ⥤ D} [Limits.PreservesLimit (pair X X') F]
  [Limits.PreservesLimit (pair Y Y') F]

variable [HasBinaryProduct (F.obj X) (F.obj X')] [HasBinaryProduct (F.obj Y) (F.obj X')]
  [HasBinaryProduct (F.obj Z) (F.obj X')] [HasBinaryProduct (F.obj X) (F.obj Y')] [HasBinaryProduct (F.obj Y) (F.obj Y')]
  [HasBinaryProduct (F.obj Z) (F.obj Y')] [HasBinaryProduct (F.obj X) (F.obj Z')] [HasBinaryProduct (F.obj Y) (F.obj Z')]
  [HasBinaryProduct (F.obj Z) (F.obj Z')]

namespace CategoryTheory

namespace Functor

@[simp]
def precomp (F : E ⥤ C) : (C ⥤ D) ⥤ (E ⥤ D) where
  obj G := F ⋙ G
  map f := whiskerLeft F f

@[simp]
def postcomp (F : D ⥤ E) : (C ⥤ D) ⥤ (C ⥤ E) where
  obj G := G ⋙ F
  map f := whiskerRight f F

end Functor

namespace Limits

lemma prod_map_comp_left_id_right :
    prod.map (f ≫ g) (𝟙 X') = prod.map f (𝟙 X') ≫ prod.map g (𝟙 X') := by
  simp only [prod.map_map, Category.comp_id]

lemma prod_map_comp_right_id_left :
    prod.map (𝟙 X) (f' ≫ g') = prod.map (𝟙 X) f' ≫ prod.map (𝟙 X) g' := by
  simp only [prod.map_map, Category.comp_id]

@[simp]
lemma PreservesLimitPair.iso_inv :
    (PreservesLimitPair.iso F X X').inv = inv (prodComparison F X X') := by
  simp_rw [← PreservesLimitPair.iso_hom]; rw [IsIso.Iso.inv_hom]

variable [HasTerminal C] [HasTerminal D] [PreservesLimit (CategoryTheory.Functor.empty C) F]

@[simp]
lemma PreservesTerminal.iso_inv :
    (PreservesTerminal.iso F).inv = inv (terminalComparison F) := by
  simp_rw [← PreservesTerminal.iso_hom]; rw [IsIso.Iso.inv_hom]


lemma prod.associator_comp_prodComparison [HasBinaryProducts C] [HasBinaryProducts D] :
    prodComparison F (X ⨯ Y) Z ≫ prod.map (prodComparison F X Y) (𝟙 (F.obj Z))
    ≫ (prod.associator _ _ _).hom =
    F.map (prod.associator _ _ _).hom ≫ prodComparison F X (Y ⨯ Z) ≫ prod.map (𝟙 (F.obj X))
    (prodComparison F Y Z) := by
  with_panel_widgets [GoalTypePanel]
  ext <;> simp only [prod.associator_hom, prod.comp_lift, prod.map_fst_assoc, prodComparison_fst,
    prodComparison_snd, prod.map_snd, Category.comp_id, prodComparison_fst_assoc, limit.lift_π,
    BinaryFan.mk_pt, BinaryFan.π_app_left, BinaryFan.mk_fst, Category.assoc, prod.map_fst]
  · rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    simp only [limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_left, BinaryFan.mk_fst]
  · simp only [BinaryFan.π_app_right, BinaryFan.mk_snd, limit.lift_π, BinaryFan.mk_pt,
    BinaryFan.π_app_left, BinaryFan.mk_fst, prodComparison_snd_assoc]
    repeat' rw [← Functor.map_comp]
    congr 1
    simp only [limit.lift_π_assoc, BinaryFan.mk_pt, pair_obj_right, BinaryFan.π_app_right,
      BinaryFan.mk_snd, limit.lift_π, BinaryFan.π_app_left, BinaryFan.mk_fst]
  · simp only [BinaryFan.π_app_right, BinaryFan.mk_snd, limit.lift_π, BinaryFan.mk_pt,
    prodComparison_snd_assoc]
    repeat' rw [← F.map_comp]
    congr 1
    simp only [limit.lift_π_assoc, BinaryFan.mk_pt, pair_obj_right, BinaryFan.π_app_right,
      BinaryFan.mk_snd, limit.lift_π]

variable (F X Y Z)

lemma PreservesLimitsPair.iso.inv_comp_prod.associator [HasBinaryProducts C] [HasBinaryProducts D]
    [PreservesLimit (pair (X ⨯ Y) Z) F] [PreservesLimit (pair X Y) F]
    [PreservesLimit (pair Y Z) F] [PreservesLimit (pair X (Y ⨯ Z)) F] :
    prod.map (PreservesLimitPair.iso F X Y).inv (𝟙 (F.obj Z)) ≫
    (PreservesLimitPair.iso F (X ⨯ Y) Z).inv ≫ F.map (prod.associator _ _ _).hom =
    (prod.associator _ _ _).hom ≫ prod.map (𝟙 F.obj X) (PreservesLimitPair.iso F Y Z).inv ≫
    (PreservesLimitPair.iso F X (Y ⨯ Z)).inv := by
  refine Mono.right_cancellation (f := (PreservesLimitPair.iso F X (Y ⨯ Z)).hom) _ _ ?_
  refine Mono.right_cancellation (f := prod.map (𝟙 (F.obj X)) (PreservesLimitPair.iso F Y Z).hom)
    _ _ ?_
  conv_lhs => rw [Category.assoc, Category.assoc, Category.assoc]
              erw [← prod.associator_comp_prodComparison]
              rw [← PreservesLimitPair.iso_hom, ← PreservesLimitPair.iso_hom]
  slice_lhs 2 3 => rw [Iso.inv_hom_id]
  rw [Category.id_comp, ← Category.assoc, ← prod_map_comp_left_id_right, Iso.inv_hom_id,
    prod.map_id_id, Category.id_comp]
  slice_rhs 3 4 => rw [Iso.inv_hom_id]
  rw [Category.id_comp]; erw [← prod_map_comp_right_id_left]
  rw [Iso.inv_hom_id, prod.map_id_id, Category.comp_id]

variable {F X Y Z}

variable {h : X ⟶ Z} [HasBinaryProduct Y Z] [HasBinaryProduct X Y]
  [HasBinaryProduct (F.obj Y) (F.obj Z)]

lemma prodComparison_comp_lift :
    F.map (prod.lift f h) ≫ prodComparison F Y Z = prod.lift (F.map f) (F.map h) := by
  ext
  · simp only [Category.assoc, prodComparison_fst, limit.lift_π, BinaryFan.mk_pt,
    BinaryFan.π_app_left, BinaryFan.mk_fst]
    rw [← F.map_comp]; congr 1; simp only [limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_left,
      BinaryFan.mk_fst]
  · simp only [Category.assoc, prodComparison_snd, limit.lift_π, BinaryFan.mk_pt,
    BinaryFan.π_app_right, BinaryFan.mk_snd]
    rw [← F.map_comp]; congr 1; simp only [limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_right,
      BinaryFan.mk_snd]

variable [PreservesLimit (pair Y Z) F]

lemma PreservesLimitPair.iso.inv_comp_lift :
    prod.lift (F.map f) (F.map h) ≫ (PreservesLimitPair.iso F Y Z).inv = F.map (prod.lift f h) := by
  refine Mono.right_cancellation (f := (PreservesLimitPair.iso F Y Z).hom) _ _ ?_
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, PreservesLimitPair.iso_hom,
    prodComparison_comp_lift]

lemma default_comp_inv_terminalComparison :
    (default : F.obj X ⟶ ⊤_ D) ≫ inv (terminalComparison F) = F.map default := by
  simp only [IsIso.comp_inv_eq]
  convert Subsingleton.elim _ _
  infer_instance

variable {G : C ⥤ D}

variable [HasBinaryProduct (G.obj X) (G.obj Y)] [HasBinaryProduct (F.obj X) (F.obj Y)]

lemma prodComparison_natTrans (α : F ⟶ G) :
    prodComparison F X Y ≫ prod.map (α.app X) (α.app Y) =
    α.app (X ⨯ Y) ≫ prodComparison G X Y := by
  ext
  · rw [Category.assoc]; simp only [prod.map_fst, prodComparison_fst_assoc, NatTrans.naturality,
    Category.assoc, prodComparison_fst]
  · rw [Category.assoc]; simp only [prod.map_snd, prodComparison_snd_assoc, NatTrans.naturality,
    Category.assoc, prodComparison_snd]

lemma inv_prodComparison_natTrans [IsIso (prodComparison F X Y)] [IsIso (prodComparison G X Y)]
    (α : F ⟶ G) : inv (prodComparison F X Y) ≫ α.app (X ⨯ Y) =
    prod.map (α.app X) (α.app Y) ≫ inv (prodComparison G X Y) := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq, prodComparison_natTrans]


#exit

variable {J : Type*} [CategoryTheory.SmallCategory J] [HasBinaryProducts C]

example (F G : J ⥤ C) : Discrete WalkingPair ⥤ J ⥤ C := pair F G

example (F G : J ⥤ C) [HasLimit F] [HasLimit G] [HasLimitsOfShape J C]
    [HasLimitsOfShape (Discrete WalkingPair × J) C]
    [HasLimit (pair F G ⋙ lim)] [HasLimit (uncurry.obj (pair F G))]
    [HasLimitsOfShape (J × Discrete WalkingPair) C]
    : HasLimit (pair F G) := by
  have e₁ := limitFlipCompLimIsoLimitCompLim (pair F G)
  have e₂ := limitUncurryIsoLimitCompLim (pair F G)
  have f := HasLimit.isoOfEquivalence (G := uncurry.obj (pair F G))
    (F := (Prod.braiding _ _).functor ⋙ uncurry.obj (pair F G)) _ (Iso.refl _)
  have K := curry.obj ((Prod.braiding _ _).functor ⋙ uncurry.obj (pair F G))
  have g := limitIsoLimitCurryCompLim ((Prod.braiding _ _).functor ⋙ uncurry.obj (pair F G))
  have e₃ := limitUncurryIsoLimitCompLim (pair F G).flip




end Limits

end CategoryTheory

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace CommRingCat

#exit

section Coproduct

variable (A B : CommRingCat.{u})

/-- The explicit cocone with tensor products as the fibered product in `CommRingCat`. -/
def pushoutCocone : Limits.PushoutCocone f g := by
  letI := RingHom.toAlgebra f
  letI := RingHom.toAlgebra g
  fapply Limits.PushoutCocone.mk
  · show CommRingCat; exact CommRingCat.of (A ⊗[R] B)
  · show A ⟶ _; exact Algebra.TensorProduct.includeLeftRingHom
  · show B ⟶ _; exact Algebra.TensorProduct.includeRight.toRingHom
  · ext r
    trans algebraMap R (A ⊗[R] B) r
    · exact Algebra.TensorProduct.includeLeft.commutes (R := R) r
    · exact (Algebra.TensorProduct.includeRight.commutes (R := R) r).symm
set_option linter.uppercaseLean3 false in
#align CommRing.pushout_cocone CommRingCat.pushoutCocone

@[simp]
theorem pushoutCocone_inl :
    (pushoutCocone f g).inl = by
      letI := f.toAlgebra
      letI := g.toAlgebra
      exact Algebra.TensorProduct.includeLeftRingHom :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommRing.pushout_cocone_inl CommRingCat.pushoutCocone_inl

@[simp]
theorem pushoutCocone_inr :
    (pushoutCocone f g).inr = by
      letI := f.toAlgebra
      letI := g.toAlgebra
      exact Algebra.TensorProduct.includeRight.toRingHom :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommRing.pushout_cocone_inr CommRingCat.pushoutCocone_inr

@[simp]
theorem pushoutCocone_pt :
    (pushoutCocone f g).pt = by
      letI := f.toAlgebra
      letI := g.toAlgebra
      exact CommRingCat.of (A ⊗[R] B) :=
  rfl
set_option linter.uppercaseLean3 false in
#align CommRing.pushout_cocone_X CommRingCat.pushoutCocone_pt

/-- Verify that the `pushout_cocone` is indeed the colimit. -/
def pushoutCoconeIsColimit : Limits.IsColimit (pushoutCocone f g) :=
  Limits.PushoutCocone.isColimitAux' _ fun s => by
    letI := RingHom.toAlgebra f
    letI := RingHom.toAlgebra g
    letI := RingHom.toAlgebra (f ≫ s.inl)
    let f' : A →ₐ[R] s.pt :=
      { s.inl with
        commutes' := fun r => rfl }
    let g' : B →ₐ[R] s.pt :=
      { s.inr with
        commutes' := fun r => by
          change (g ≫ s.inr) r = (f ≫ s.inl) r
          congr 1
          exact
            (s.ι.naturality Limits.WalkingSpan.Hom.snd).trans
              (s.ι.naturality Limits.WalkingSpan.Hom.fst).symm }
    -- Porting note: Lean has forget why `A ⊗[R] B` makes sense
    letI : Algebra R A := f.toAlgebra
    letI : Algebra R B := g.toAlgebra
    letI : Algebra R (pushoutCocone f g).pt := show Algebra R (A ⊗[R] B) by infer_instance
    -- The factor map is a ⊗ b ↦ f(a) * g(b).
    use AlgHom.toRingHom (Algebra.TensorProduct.productMap f' g')
    simp only [pushoutCocone_inl, pushoutCocone_inr]
    constructor
    · ext x
      -- Porting note: Lean can't see through `forget` functor
      letI : Semiring ((forget CommRingCat).obj A) := A.str.toSemiring
      letI : Algebra R ((forget CommRingCat).obj A) := show Algebra R A by infer_instance
      exact Algebra.TensorProduct.productMap_left_apply _ _ x
    constructor
    · ext x
      -- Porting note: Lean can't see through `forget` functor
      letI : Semiring ((forget CommRingCat).obj B) := B.str.toSemiring
      letI : Algebra R ((forget CommRingCat).obj B) := show Algebra R B by infer_instance
      exact Algebra.TensorProduct.productMap_right_apply _ _ x
    intro h eq1 eq2
    let h' : A ⊗[R] B →ₐ[R] s.pt :=
      { h with
        commutes' := fun r => by
          change h (f r ⊗ₜ[R] 1) = s.inl (f r)
          rw [← eq1]
          simp only [pushoutCocone_pt, coe_of, AlgHom.toRingHom_eq_coe]
          rfl }
    suffices h' = Algebra.TensorProduct.productMap f' g' by
      ext x
      change h' x = Algebra.TensorProduct.productMap f' g' x
      rw [this]
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [f', g', ← eq1, pushoutCocone_pt, ← eq2, AlgHom.toRingHom_eq_coe,
      Algebra.TensorProduct.productMap_apply_tmul, AlgHom.coe_mk]
    change _ = h (a ⊗ₜ 1) * h (1 ⊗ₜ b)
    rw [← h.map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
set_option linter.uppercaseLean3 false in
#align CommRing.pushout_cocone_is_colimit CommRingCat.pushoutCoconeIsColimit

end Pushout
