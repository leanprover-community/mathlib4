/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Factorizations.CM5b
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.HomologicalComplexLimitsEventuallyConstant
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Factorization lemma

-/

@[expose] public section

open CategoryTheory Category Limits Preadditive ZeroObject

namespace CategoryTheory

variable {C : Type*} [Category C]

namespace Injective

lemma direct_factor {X I : C} {i : X ⟶ I} {p : I ⟶ X} (fac : i ≫ p = 𝟙 X) [Injective I] :
    Injective X where
  factors g f _ := ⟨Injective.factorThru (g ≫ i) f ≫ p,
    by rw [comp_factorThru_assoc, assoc, fac, comp_id]⟩

end Injective

end CategoryTheory

namespace CochainComplex

variable {C : Type*} [Category C] [Abelian C] (T : Pretriangulated.Triangle (CochainComplex C ℤ))
  [HasDerivedCategory C]
  (hT : DerivedCategory.Q.mapTriangle.obj T ∈ distTriang _)

open HomologicalComplex

lemma homologyMap_eq_zero_of_Q_map_eq_zero {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hf : DerivedCategory.Q.map f = 0) (n : ℤ) : homologyMap f n = 0 := by
  have eq := NatIso.naturality_2 (DerivedCategory.homologyFunctorFactors C n).symm f
  dsimp at eq
  rw [← eq, hf]
  simp only [Functor.map_zero, zero_comp, comp_zero]

noncomputable def homologyδOfDistinguished (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    T.obj₃.homology n₀ ⟶ T.obj₁.homology n₁ :=
  homologyMap T.mor₃ n₀ ≫
    ((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso 1 n₀ n₁ (by linarith)).hom.app T.obj₁

include hT in
lemma homologyMap_comp₁₂_eq_zero_of_distinguished (n : ℤ) :
    homologyMap T.mor₁ n ≫ homologyMap T.mor₂ n = 0 := by
  rw [← homologyMap_comp]
  apply homologyMap_eq_zero_of_Q_map_eq_zero
  rw [Functor.map_comp]
  exact Pretriangulated.comp_distTriang_mor_zero₁₂ _ hT

lemma homology_exact₂_of_distinguished (n : ℤ) :
    (ShortComplex.mk (homologyMap T.mor₁ n) (homologyMap T.mor₂ n)
      (homologyMap_comp₁₂_eq_zero_of_distinguished T hT n)).Exact := by
  let e := DerivedCategory.homologyFunctorFactors C n
  refine ShortComplex.exact_of_iso ?_ (DerivedCategory.HomologySequence.exact₂ _ hT n)
  exact ShortComplex.isoMk
    (e.app T.obj₁) (e.app T.obj₂) (e.app T.obj₃)
    (e.hom.naturality T.mor₁).symm (e.hom.naturality T.mor₂).symm

include hT in
lemma comp_homologyδOfDistinguished (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    homologyMap T.mor₂ n₀ ≫ homologyδOfDistinguished T n₀ n₁ h = 0 := by
  have hT' : DerivedCategory.Q.mapTriangle.obj T.rotate ∈ distTriang _ :=
    Pretriangulated.isomorphic_distinguished _ (Pretriangulated.rot_of_distTriang _ hT) _
      (DerivedCategory.Q.mapTriangleRotateIso.app T).symm
  have eq := homologyMap_comp₁₂_eq_zero_of_distinguished T.rotate hT' n₀
  dsimp at eq
  dsimp [homologyδOfDistinguished]
  rw [reassoc_of% eq, zero_comp]

lemma homology_exact₃_of_distinguished (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk (homologyMap T.mor₂ n₀) (homologyδOfDistinguished T n₀ n₁ h)
      (comp_homologyδOfDistinguished T hT n₀ n₁ h)).Exact := by
  have hT' : DerivedCategory.Q.mapTriangle.obj T.rotate ∈ distTriang _ :=
    Pretriangulated.isomorphic_distinguished _ (Pretriangulated.rot_of_distTriang _ hT) _
      (DerivedCategory.Q.mapTriangleRotateIso.app T).symm
  refine ShortComplex.exact_of_iso ?_ (homology_exact₂_of_distinguished _ hT' n₀)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso 1 n₀ n₁ (by linarith)).app T.obj₁) ?_ ?_
  · dsimp
    simp
  · dsimp [homologyδOfDistinguished]
    simp

omit [HasDerivedCategory C] in
lemma homologyMap_shift {K L : CochainComplex C ℤ} (f : K ⟶ L) (a n m : ℤ) (hm : a + n = m) :
    homologyMap (f⟦a⟧') n =
      ((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso a n m hm).hom.app K ≫ homologyMap f m ≫
      ((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso a n m hm).inv.app L := by
  erw [← NatTrans.naturality_assoc, Iso.hom_inv_id_app, comp_id]
  rfl

include hT in
lemma homologyδOfDistinguished_comp (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    homologyδOfDistinguished T n₀ n₁ h ≫ homologyMap T.mor₁ n₁ = 0 := by
  -- the proof most duplicates the proof of `homology_exact₁_of_distinguished` below
  -- it would be nicer to introduce an isomorphism in `Arrow₂`, and to deduce both
  -- this vanishing and the exactness
  have hT' : DerivedCategory.Q.mapTriangle.obj T.invRotate ∈ distTriang _ :=
    Pretriangulated.isomorphic_distinguished _ (Pretriangulated.inv_rot_of_distTriang _ hT) _
      (DerivedCategory.Q.mapTriangleInvRotateIso.app T).symm
  have eq := homologyMap_comp₁₂_eq_zero_of_distinguished T.invRotate hT' n₁
  dsimp at eq
  rw [homologyMap_neg, neg_comp, neg_eq_zero, homologyMap_comp, assoc,
    homologyMap_shift T.mor₃ (-1) n₁ n₀ (by linarith), assoc, assoc,
    IsIso.comp_left_eq_zero] at eq
  conv_lhs at eq =>
    congr
    · skip
    · rw [← assoc]
  dsimp only [homologyδOfDistinguished]
  rw [assoc]
  convert eq using 3
  rw [← cancel_epi (((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso (-1) n₁ n₀
    (by linarith)).hom.app (T.obj₁⟦(1 : ℤ)⟧)), Iso.hom_inv_id_app_assoc]
  rw [(homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso_hom_app_comp
      (-1 : ℤ) 1 0 (add_neg_cancel 1) n₁ n₀ n₁ (by linarith) (by linarith),
      Functor.shiftIso_zero_hom_app, ← Functor.map_comp]
  dsimp [shiftFunctorCompIsoId]
  rfl

lemma homology_exact₁_of_distinguished (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk (homologyδOfDistinguished T n₀ n₁ h) (homologyMap T.mor₁ n₁)
      (homologyδOfDistinguished_comp T hT n₀ n₁ h)).Exact := by
  have hT' : DerivedCategory.Q.mapTriangle.obj T.invRotate ∈ distTriang _ :=
    Pretriangulated.isomorphic_distinguished _ (Pretriangulated.inv_rot_of_distTriang _ hT) _
      (DerivedCategory.Q.mapTriangleInvRotateIso.app T).symm
  refine ShortComplex.exact_of_iso ?_ (homology_exact₂_of_distinguished _ hT' n₁)
  refine ShortComplex.isoMk
    (-((((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso (-1) n₁ n₀ (by linarith)).app T.obj₃)))
    (Iso.refl _) (Iso.refl _) ?_ ?_
  · dsimp [homologyδOfDistinguished]
    simp only [neg_comp, homologyMap_neg, comp_id, neg_inj]
    erw [← NatTrans.naturality_assoc]
    rw [homologyMap_comp]
    congr 1
    rw [(homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso_hom_app_comp
      (-1 : ℤ) 1 0 (add_neg_cancel 1) n₁ n₀ n₁ (by linarith) (by linarith),
      Functor.shiftIso_zero_hom_app, ← Functor.map_comp]
    dsimp [shiftFunctorCompIsoId]
    rfl
  · dsimp
    simp

end CochainComplex

namespace CochainComplex

open HomComplex

variable {C : Type*} [Category C] [Abelian C] {K L : CochainComplex C ℤ} (f : K ⟶ L)

noncomputable def mappingCocone := (mappingCone f)⟦(-1 : ℤ)⟧

namespace mappingCocone

-- not sure what are the best signs here
noncomputable def inl : Cochain K (mappingCocone f) 0 :=
  (mappingCone.inl f).rightShift (-1) 0 (zero_add _)
noncomputable def inr : Cocycle L (mappingCocone f) 1 :=
    (Cocycle.ofHom (mappingCone.inr _)).rightShift (-1) 1 (add_neg_cancel 1)
noncomputable def fst : (mappingCocone f) ⟶ K :=
  -((mappingCone.fst _).leftShift (-1) 0 (add_neg_cancel 1)).homOf
noncomputable def snd : Cochain (mappingCocone f) L (-1) :=
  (mappingCone.snd _).leftShift (-1) (-1) (zero_add _)

@[reassoc (attr := simp)]
lemma inr_fst (p q : ℤ) (hpq : p + 1 = q) : (inr f).1.v p q hpq ≫ (fst f).f q = 0 := by
    dsimp [inr, fst]
    rw [Cochain.rightShift_v _ (-1) 1 _ p q _ p (by linarith),
      Cochain.leftShift_v _ (-1) 0 _ q q _ p (by linarith)]
    simp

@[reassoc (attr := simp)]
lemma inl_snd (p q : ℤ) (hpq : p + (-1) = q) :
    (inl f).v p p (add_zero _) ≫ (snd f).v p q hpq = 0 := by
  dsimp [inl, snd]
  rw [Cochain.rightShift_v _ (-1) 0 _ p p _ q (by linarith),
    Cochain.leftShift_v _ (-1) (-1) _ p q _ q (by linarith)]
  simp

@[reassoc (attr := simp)]
lemma inr_snd (p q : ℤ) (hpq : p + 1 = q) :
    (inr f).1.v p q hpq ≫ (snd f).v q p (by linarith) = 𝟙 _ := by
  dsimp [inr, snd]
  rw [Cochain.rightShift_v _ (-1) 1 _ p q _ p (by linarith),
    Cochain.leftShift_v _ (-1) (-1) _ q p _ p (by linarith)]
  simp [show Int.negOnePow 2 = 1 by rfl]

@[reassoc (attr := simp)]
lemma inl_fst (p : ℤ) : (inl f).v p p (add_zero _) ≫ (fst f).f p = 𝟙 _ := by
  dsimp [inl, fst]
  have : ((1 : ℤ) + 1)/2 = 1 := rfl
  rw [Cochain.rightShift_v _ (-1) 0 _ p p _ (p-1) (by linarith),
    Cochain.leftShift_v _ (-1) 0 _ p p _ (p-1) (by linarith)]
  simp only [Int.reduceNeg, shiftFunctor_obj_X, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, mul_zero, Int.reduceSub, mul_neg, neg_mul,
    one_mul, neg_neg, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, EuclideanDomain.div_self,
    zero_add, Int.negOnePow_one, Iso.refl_hom, id_comp, Units.neg_smul, one_smul, assoc]
  erw [id_comp]
  simp

lemma id (p q : ℤ) (hpq : p + (-1) = q) : (fst f).f p ≫ (inl f).v p p (add_zero _) +
      (snd f).v p q hpq ≫ (inr f).1.v q p (by linarith) = 𝟙 _ := by
    dsimp [inl, inr, fst, snd]
    have : ((1 : ℤ) + 1) /2 = 1 := rfl
    rw [Cochain.rightShift_v _ (-1) 0 _ p p _ q (by linarith),
      Cochain.rightShift_v _ (-1) 1 _ q p _ q (by linarith),
      Cochain.leftShift_v _ (-1) 0 _ p p _ q (by linarith),
      Cochain.leftShift_v _ (-1) (-1) _ p q _ q (by linarith)]
    simp only [Int.reduceNeg, shiftFunctor_obj_X, mul_zero, Int.reduceSub, mul_neg, neg_mul,
      one_mul, neg_neg, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, EuclideanDomain.div_self,
      zero_add, Int.negOnePow_one, shiftFunctorObjXIso, Units.neg_smul, one_smul, assoc, mul_one,
      Int.reduceAdd, show Int.negOnePow 2 = 1 by rfl, Cochain.ofHom_v]
    rw [← comp_add]
    conv_lhs =>
      congr
      · skip
      · congr
        · rw [← assoc]
        · rw [← assoc]
    rw [← add_comp, mappingCone.id_X f q p (by linarith)]
    simp

noncomputable def triangleδ : L ⟶ (mappingCocone f)⟦(1 : ℤ)⟧ :=
  mappingCone.inr f ≫ (shiftEquiv (CochainComplex C ℤ) (1 : ℤ)).counitIso.inv.app _

@[simps!]
noncomputable def triangle : Pretriangulated.Triangle (CochainComplex C ℤ) :=
  Pretriangulated.Triangle.mk (fst f) f (triangleδ f)

noncomputable def triangleIso : triangle f ≅ (mappingCone.triangle f).invRotate := by
  refine Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · dsimp
    ext n
    have : ((1 : ℤ) + 1) / 2 = 1 := rfl
    dsimp [mappingCone.triangle]
    simp only [comp_id, Cochain.rightShift_neg, Cochain.neg_v,
      neg_comp, neg_neg, id_comp]
    rw [Cochain.leftShift_v _ (-1) 0 _ n n _ (n-1) (by linarith),
      Cochain.rightShift_v _ 1 0 _ _ _ _ n (by linarith)]
    simp only [Int.reduceNeg, shiftFunctor_obj_X, mul_zero, Int.reduceSub, mul_neg, neg_mul,
      one_mul, neg_neg, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, EuclideanDomain.div_self,
      zero_add, Int.negOnePow_one, shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom, id_comp, Units.neg_smul, one_smul, assoc]
    dsimp [shiftFunctorCompIsoId]
    rw [shiftFunctorAdd'_inv_app_f', shiftFunctorZero_hom_app_f]
    simp only [HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom, Iso.inv_hom_id, comp_id]
    rfl
  · dsimp
    simp only [comp_id, id_comp]
  · dsimp
    simp only [triangle, triangleδ, shiftEquiv'_inverse, shiftEquiv'_functor,
      shiftEquiv'_counitIso, Pretriangulated.Triangle.mk_obj₁, Pretriangulated.Triangle.mk_mor₃,
      CategoryTheory.Functor.map_id, comp_id, id_comp]
    rfl

variable [HasDerivedCategory C]

lemma Q_map_triangle_distinguished :
    DerivedCategory.Q.mapTriangle.obj (triangle f) ∈ distTriang _ := by
  refine Pretriangulated.isomorphic_distinguished _ ?_ _
    ((DerivedCategory.Q.mapTriangle.mapIso (triangleIso f)) ≪≫
      (DerivedCategory.Q.mapTriangleInvRotateIso.app (mappingCone.triangle f)).symm)
  refine Pretriangulated.inv_rot_of_distTriang _ ?_
  rw [DerivedCategory.mem_distTriang_iff]
  exact ⟨_, _, _, ⟨Iso.refl _⟩⟩

open HomologicalComplex

@[reassoc (attr := simp)]
lemma homologyMap_fst_comp (n : ℤ) : homologyMap (fst f) n ≫ homologyMap f n = 0 :=
  homologyMap_comp₁₂_eq_zero_of_distinguished _ (Q_map_triangle_distinguished f) n

noncomputable def homology_δ (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    L.homology n₀ ⟶ (mappingCocone f).homology n₁ :=
  homologyδOfDistinguished (triangle f) n₀ n₁ hn₁

@[reassoc (attr := simp)]
lemma homology_δ_comp (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    homology_δ f n₀ n₁ hn₁ ≫ homologyMap (fst f) n₁ = 0 :=
  homologyδOfDistinguished_comp _ (Q_map_triangle_distinguished f) n₀ n₁ hn₁

@[reassoc (attr := simp)]
lemma homology_comp_δ (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    homologyMap f n₀ ≫ homology_δ f n₀ n₁ hn₁ = 0 :=
  comp_homologyδOfDistinguished _ (Q_map_triangle_distinguished f) n₀ n₁ hn₁

lemma homology_exact₁ (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    (ShortComplex.mk (homology_δ f n₀ n₁ hn₁) (homologyMap (fst f) n₁) (by simp)).Exact :=
  homology_exact₁_of_distinguished _ (Q_map_triangle_distinguished f) n₀ n₁ hn₁

lemma homology_exact₂ (n : ℤ) :
    (ShortComplex.mk (homologyMap (fst f) n) (homologyMap f n) (by simp)).Exact :=
  homology_exact₂_of_distinguished _ (Q_map_triangle_distinguished f) n

lemma homology_exact₃ (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    (ShortComplex.mk (homologyMap f n₀) (homology_δ f n₀ n₁ hn₁) (by simp)).Exact :=
  homology_exact₃_of_distinguished _ (Q_map_triangle_distinguished f) n₀ n₁ hn₁

end mappingCocone

end CochainComplex

namespace CategoryTheory

variable {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y)

structure HomFactorization where
  I : C
  i : X ⟶ I
  p : I ⟶ Y
  fac : i ≫ p = f

variable {f}

namespace HomFactorization

/-- mk' -/
@[simps]
def mk' {I : C} {i : X ⟶ I} {p : I ⟶ Y} (fac : i ≫ p = f) : HomFactorization f :=
  { fac := fac, ..}

attribute [reassoc (attr := simp)] fac

variable (F₁ F₂ F₃ : HomFactorization f)

@[ext]
structure Hom where
  φ : F₁.I ⟶ F₂.I
  commi : F₁.i ≫ φ = F₂.i := by aesop_cat
  commp : φ ≫ F₂.p = F₁.p := by aesop_cat

attribute [reassoc (attr := simp)] Hom.commi Hom.commp

@[simps]
def Hom.id : Hom F₁ F₁ where
  φ := 𝟙 _

variable {F₁ F₂ F₃}

@[simps]
def Hom.comp (f : Hom F₁ F₂) (g : Hom F₂ F₃) : Hom F₁ F₃ where
  φ := f.φ ≫ g.φ

@[simps]
instance : Category (HomFactorization f) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[ext]
lemma hom_ext (f g : F₁ ⟶ F₂) (h : f.φ = g.φ) : f = g :=
  Hom.ext h

variable (f)

@[simps]
def forget : HomFactorization f ⥤ C where
  obj F := F.I
  map f := f.φ

end HomFactorization

end CategoryTheory

variable {C : Type*} [Category C] [Abelian C] [EnoughInjectives C]
  {K L : CochainComplex C ℤ} (f : K ⟶ L)

namespace CochainComplex

open HomologicalComplex HomComplex

namespace CM5aCof

variable {f}

structure IsCofFibFactorization (F : HomFactorization f) : Prop where
  hi : Mono F.i := by infer_instance
  hp : degreewiseEpiWithInjectiveKernel F.p

variable (f)

def CofFibFactorization := ObjectProperty.FullSubcategory (IsCofFibFactorization (f := f))

instance : Category (CofFibFactorization f) := by
  dsimp only [CofFibFactorization]
  infer_instance

namespace CofFibFactorization

def forget : CofFibFactorization f ⥤ HomFactorization f := ObjectProperty.ι _

variable {f}
variable (F : CofFibFactorization f)

instance : Mono (F.1.i) := F.2.hi

def IsIsoLE (n : ℤ) : Prop := ∀ (i : ℤ) (_ : i ≤ n), IsIso (F.1.p.f i)

class QuasiIsoLE (n : ℤ) : Prop where
  quasiIsoAt (i : ℤ) (_ : i ≤ n) : QuasiIsoAt (F.1.i) i

omit [EnoughInjectives C] in
lemma quasiIsoAt_of_quasiIsoLE (F : CofFibFactorization f)
    (n : ℤ) [F.QuasiIsoLE n] (i : ℤ) (hi : i ≤ n) : QuasiIsoAt (F.1.i) i :=
  QuasiIsoLE.quasiIsoAt i hi

@[simps]
def mk {I : CochainComplex C ℤ} {i : K ⟶ I} {p : I ⟶ L} (fac : i ≫ p = f)
  [hi : Mono i] (hp : degreewiseEpiWithInjectiveKernel p) :
    CofFibFactorization f where
  obj := HomFactorization.mk' fac
  property := ⟨hi, hp⟩

end CofFibFactorization

lemma step₁ [Mono f] (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
    (hf : ∀ (i : ℤ) (_ : i ≤ n₀), QuasiIsoAt f i) :
    ∃ (F : CofFibFactorization f) (_ : F.IsIsoLE n₀) (_ : F.QuasiIsoLE n₀),
      Mono (homologyMap F.1.i n₁) := by
  let S := ((single C (ComplexShape.up ℤ) n₁).obj (Injective.under (K.opcycles n₁)))
  let M := biprod S L
  let i₁ : K ⟶ S := ((toSingleEquiv _ _ n₀ n₁ (by subst hn₁; simp)).symm
    ⟨K.pOpcycles n₁ ≫ Injective.ι _,
      by rw [d_pOpcycles_assoc, zero_comp]⟩)
  let i : K ⟶ M := biprod.lift i₁ f
  let p : M ⟶ L := biprod.snd
  let σ : L ⟶ M := biprod.inr
  have σp : σ ≫ p = 𝟙 _ := by simp [σ, p]
  have hp : degreewiseEpiWithInjectiveKernel p := fun n => by
    rw [Abelian.epiWithInjectiveKernel_iff]
    refine ⟨S.X n,?_, (biprod.inl : _ ⟶ M).f n, ?_,
      ⟨(biprod.fst : M ⟶ _).f n, (biprod.inr : _ ⟶ M).f n, ?_, ?_, ?_⟩⟩
    · dsimp [S, single]
      by_cases h : n = n₁
      · rw [if_pos h]
        infer_instance
      · rw [if_neg h]
        infer_instance
    · rw [← comp_f, biprod.inl_snd, zero_f]
    · dsimp
      rw [← comp_f, biprod.inl_fst, id_f]
    · dsimp
      rw [← comp_f, biprod.inr_snd, id_f]
    · dsimp
      rw [← id_f, ← biprod.total, add_f_apply, comp_f, comp_f]
  have fac : i ≫ p = f := by simp [i, p]
  have hp' : ∀ (n : ℤ) (_ : n ≤ n₀), IsIso (p.f n) := fun n hn => by
    refine ⟨(biprod.inr : _ ⟶ M).f n, ?_, ?_⟩
    · rw [← cancel_mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).mapBiprod _ _).hom]
      ext
      · apply IsZero.eq_of_tgt
        dsimp [S, single]
        rw [if_neg (by linarith)]
        exact isZero_zero C
      · dsimp
        simp only [Category.assoc, biprod.lift_snd, Category.id_comp]
        rw [← comp_f, biprod.inr_snd, id_f, comp_id]
    · rw [← comp_f, biprod.inr_snd, id_f]
  have hp'' : ∀ (n : ℤ) (_ : n ≤ n₀), QuasiIsoAt p n := fun n hn => by
    obtain (hn | rfl) := hn.lt_or_eq
    · rw [quasiIsoAt_iff' _ (n-1) n (n+1) (by simp) (by simp)]
      let φ := (shortComplexFunctor' C (ComplexShape.up ℤ) (n - 1) n (n + 1)).map p
      have : IsIso φ.τ₁ := hp' _ (by linarith)
      have : IsIso φ.τ₂ := hp' _ (by linarith)
      have : IsIso φ.τ₃ := hp' _ (by linarith)
      apply ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ
    · rw [quasiIsoAt_iff_isIso_homologyMap]
      refine ⟨homologyMap σ n, ?_, ?_⟩
      · have : cyclesMap (biprod.inl : _ ⟶ M) n = 0 := by
          have : (biprod.inl : _ ⟶ M).f n = 0 := by
            apply IsZero.eq_of_src
            dsimp [S, single]
            rw [if_neg (by linarith)]
            exact Limits.isZero_zero C
          rw [← cancel_mono (M.iCycles n), zero_comp, cyclesMap_i, this, comp_zero]
        symm
        dsimp [p, σ]
        rw [← homologyMap_comp, ← homologyMap_id, ← sub_eq_zero, ← homologyMap_sub,
          ← biprod.total, add_sub_cancel_right, ← cancel_epi (M.homologyπ n),
          homologyπ_naturality, comp_zero, cyclesMap_comp, this, comp_zero, zero_comp]
      · rw [← homologyMap_comp, σp, homologyMap_id]
  have hi : ∀ (n : ℤ) (_ : n ≤ n₀), QuasiIsoAt i n := fun n hn => by
    have : QuasiIsoAt p n := hp'' n hn
    have : QuasiIsoAt (i ≫ p) n := by simpa only [fac] using hf n hn
    exact quasiIsoAt_of_comp_right i p n
  refine ⟨CofFibFactorization.mk fac hp, hp', ⟨hi⟩, mono_of_cancel_zero _ ?_⟩
  intro A₀ x₀ (hx₀ : x₀ ≫ homologyMap i n₁ = 0)
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ := surjective_up_to_refinements_of_epi (K.homologyπ n₁) x₀
  rw [← cancel_epi π₁, comp_zero, hx₁,
    K.comp_homologyπ_eq_zero_iff_up_to_refinements x₁ n₀ (by simp [hn₁])]
  replace hx₀ := π₁ ≫= hx₀
  rw [reassoc_of% hx₁, comp_zero, homologyπ_naturality, ← assoc,
    M.comp_homologyπ_eq_zero_iff_up_to_refinements (x₁ ≫ cyclesMap i n₁) n₀ (by simp [hn₁])] at hx₀
  have : Mono (opcyclesMap i₁ n₁) := by
    let α : Injective.under (K.opcycles n₁) ⟶ S.X n₁ :=
      (singleObjXSelf (ComplexShape.up ℤ) n₁ (Injective.under (K.opcycles n₁))).inv
    have := S.isIso_pOpcycles _ n₁ rfl rfl
    have : opcyclesMap i₁ n₁ = Injective.ι (K.opcycles n₁) ≫ α ≫ S.pOpcycles n₁ := by
      rw [← (cancel_epi (K.pOpcycles n₁)), p_opcyclesMap, ← assoc, ← assoc]
      simp [α, i₁, toSingleEquiv]
    rw [this]
    infer_instance
  have hx₁' : (x₁ ≫ K.iCycles n₁) ≫ K.pOpcycles n₁ = 0 := by
    obtain ⟨A₂, π₂, _, x₂, hx₂⟩ := hx₀
    replace hx₂ := hx₂ =≫ (M.iCycles n₁ ≫ M.pOpcycles n₁ ≫ opcyclesMap biprod.fst n₁)
    rw [assoc, assoc, assoc, cyclesMap_i_assoc, toCycles_i_assoc, d_pOpcycles_assoc,
      zero_comp, comp_zero, p_opcyclesMap, ← comp_f_assoc, biprod.lift_fst,
      ← p_opcyclesMap i₁ n₁] at hx₂
    rw [assoc, ← cancel_mono (opcyclesMap i₁ n₁), zero_comp, assoc, assoc,
      ← cancel_epi π₂, comp_zero, hx₂]
  rw [K.comp_pOpcycles_eq_zero_iff_up_to_refinements (x₁ ≫ K.iCycles n₁) n₀ (by simp [hn₁])] at hx₁'
  obtain ⟨A₃, π₃, _, x₃, hx₃⟩ := hx₁'
  refine ⟨A₃, π₃, inferInstance, x₃, ?_⟩
  rw [← cancel_mono (K.iCycles n₁), assoc, hx₃, assoc, toCycles_i]

def CofFibFactorizationQuasiIsoLE (n : ℤ) :=
  ObjectProperty.FullSubcategory (fun (F : CofFibFactorization f) => F.QuasiIsoLE n)

instance (n : ℤ) : Category (CofFibFactorizationQuasiIsoLE f n) := by
  dsimp only [CofFibFactorizationQuasiIsoLE]
  infer_instance

instance (n : ℤ) (F : CofFibFactorizationQuasiIsoLE f n) : F.1.QuasiIsoLE n := F.2

namespace Step₂

variable [Mono f] (n : ℤ) [Mono (homologyMap f n)]

@[simps]
noncomputable def homologyShortComplex : ShortComplex C :=
  ShortComplex.mk (homologyMap f n) (homologyMap (cokernel.π f) n)
    (by rw [← homologyMap_comp, cokernel.condition, homologyMap_zero])

omit [EnoughInjectives C] in
lemma shortExact : (ShortComplex.mk _ _ (cokernel.condition f)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)

omit [Mono (homologyMap f n)] [EnoughInjectives C] in
lemma homologyShortComplex_exact : (homologyShortComplex f n).Exact :=
  (shortExact f).homology_exact₂ n

instance mono_homologyShortComplex_f : Mono (homologyShortComplex f n).f := by
  dsimp
  infer_instance

noncomputable def I :=
  (single C (ComplexShape.up ℤ) n).obj (Injective.under (((cokernel f).truncGE n).X n))

omit [Mono (homologyMap f n)] [Mono f] in
lemma isZero_homology_I (q : ℤ) (hq : q ≠ n) : IsZero ((I f n).homology q) := by
  rw [← exactAt_iff_isZero_homology, exactAt_iff]
  apply ShortComplex.exact_of_isZero_X₂
  dsimp [I, single]
  rw [if_neg hq]
  exact Limits.isZero_zero C

instance (p : ℤ) : Injective ((I f n).X p) := by
  dsimp [I, single]
  split_ifs <;> infer_instance

/-- π' -/
noncomputable def π' : (cokernel f).truncGE n ⟶ I f n :=
  (toSingleEquiv _ _ (n-1) n (by simp)).symm ⟨Injective.ι _, by
    apply IsZero.eq_of_src
    exact isZero_of_isStrictlyGE _ n _ (by omega)⟩

instance : Mono ((π' f n).f n) := by
  simp only [π', toSingleEquiv, Equiv.coe_fn_symm_mk, mkHomToSingle_f, mono_comp_iff_of_mono]
  infer_instance

omit [Mono (homologyMap f n)] [Mono f] in
lemma mono_cyclesMap_π' : Mono (cyclesMap (π' f n) n) := by
  have : Mono (cyclesMap (π' f n) n ≫ (I f n).iCycles  n) := by
    rw [cyclesMap_i]
    infer_instance
  apply mono_of_mono _ ((I f n).iCycles n)

omit [Mono (homologyMap f n)] [Mono f] in
lemma mono_homologyMap_π' : Mono (homologyMap (π' f n) n) := by
  have := mono_cyclesMap_π' f n
  have := ((cokernel f).truncGE n).isIso_homologyπ (n-1) n (by simp)
    (IsZero.eq_of_src (isZero_of_isStrictlyGE _ n _ (by omega)) _ _)
  have := (I f n).isIso_homologyπ  (n-1) n (by simp) (by
      apply IsZero.eq_of_src
      dsimp [I, single]
      rw [if_neg (by linarith)]
      exact isZero_zero C)
  have : Mono ((truncGE (cokernel f) n).homologyπ n ≫ homologyMap (π' f n) n) := by
    rw [homologyπ_naturality (π' f n) n]
    infer_instance
  rw [← IsIso.inv_hom_id_assoc ((truncGE (cokernel f) n).homologyπ n) (homologyMap (π' f n) n)]
  infer_instance

noncomputable def α : L ⟶ I f n := cokernel.π f ≫ (cokernel f).πTruncGE n ≫ π' f n

omit [Mono (homologyMap f n)] [Mono f] in
@[reassoc (attr := simp)]
lemma f_α : f ≫ α f n = 0 := by simp [α]

omit [Mono (homologyMap f n)] [Mono f] in
@[reassoc (attr := simp)]
lemma f_α_f (i : ℤ) : f.f i ≫ (α f n).f i = 0 := by
  rw [← comp_f, f_α, zero_f]

omit [Mono (homologyMap f n)] [Mono f] in
@[simps]
noncomputable def homologyShortComplex' : ShortComplex C :=
  ShortComplex.mk (homologyMap f n) (homologyMap (α f n) n) (by
    rw [← homologyMap_comp, f_α, homologyMap_zero])

omit [Mono (homologyMap f n)] in
lemma homologyShortComplex'_exact : (homologyShortComplex' f n).Exact := by
  let φ : homologyShortComplex f n ⟶ homologyShortComplex' f n :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := homologyMap ((cokernel f).πTruncGE n ≫ π' f n) n
      comm₂₃ := by
        dsimp
        rw [id_comp, ← homologyMap_comp]
        rfl }
  have : IsIso φ.τ₁ := by infer_instance
  have : IsIso φ.τ₂ := by infer_instance
  have : Mono φ.τ₃ := by
    dsimp [φ]
    rw [homologyMap_comp]
    have := mono_homologyMap_π' f n
    infer_instance
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact homologyShortComplex_exact f n

instance mono_homologyShortComplex'_f : Mono (homologyShortComplex' f n).f := by
  dsimp
  infer_instance

/-- L' -/
noncomputable def L' := (mappingCone (α f n))⟦(-1 : ℤ)⟧

/-- i' -/
noncomputable def i' : Cocycle K (mappingCone (α f n)) (-1) :=
  mappingCone.liftCocycle (α f n) (Cocycle.ofHom f) 0 (neg_add_cancel 1) (by aesop_cat)

noncomputable def i : K ⟶ L' f n :=
  Cocycle.homOf ((i' f n).rightShift (-1) 0 (zero_add _))

noncomputable def p : L' f n ⟶ L := mappingCocone.fst _

omit [Mono (homologyMap f n)] [Mono f] in
lemma fac : i f n ≫ p f n = f := by
  ext q
  dsimp [i, p, mappingCocone.fst]
  have : ((1 : ℤ) + 1) / 2 = 1 := rfl
  rw [Cochain.rightShift_v _ (-1) 0 _ q q _ (q-1) (by linarith),
    Cochain.leftShift_v _ (-1) 0 _ q q _ (q-1) (by linarith)]
  simp only [Int.reduceNeg, shiftFunctor_obj_X, i', mappingCone.liftCocycle_coe, Cocycle.ofHom_coe,
    shiftFunctorObjXIso, XIsoOfEq_rfl, Iso.refl_inv, mul_zero, Int.reduceSub, mul_neg, neg_mul,
    one_mul, neg_neg, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, EuclideanDomain.div_self,
    zero_add, Int.negOnePow_one, Iso.refl_hom, id_comp, Units.neg_smul, one_smul, assoc]
  erw [id_comp]
  simp

instance : Mono (i f n) := mono_of_mono_fac (fac f n)

omit [Mono (homologyMap f n)] [Mono f] in
lemma isIso_p_f (q : ℤ) (hq : q ≤ n) : IsIso ((p f n).f q) := by
  refine ⟨(mappingCocone.inl _).v q q (add_zero _), ?_, by simp [p]⟩
  have : (mappingCocone.snd (α f n)).v q (q-1) (by linarith) = 0 := by
    apply IsZero.eq_of_tgt
    dsimp [I, single]
    rw [if_neg (by linarith)]
    exact Limits.isZero_zero C
  erw [← mappingCocone.id _ q (q - 1) (by linarith), left_eq_add, this, zero_comp]

@[simps]
noncomputable def cofFibFactorization : CofFibFactorization f where
  obj := HomFactorization.mk' (fac f n)
  property :=
    { hi := by
        dsimp
        infer_instance
      hp := fun q => by
        dsimp
        rw [Abelian.epiWithInjectiveKernel_iff]
        refine ⟨_, inferInstance, (mappingCocone.inr _).1.v (q-1) q (by omega),
          by simp [p], ⟨(mappingCocone.snd (α f n)).v q (q-1) (by linarith),
          (mappingCocone.inl (α f n)).v q q (add_zero _), by simp, by simp [p], ?_⟩⟩
        dsimp
        rw [add_comm, p, mappingCocone.id]
        rfl }

variable (hf : ∀ (i : ℤ) (_ : i ≤ n - 1), QuasiIsoAt f i)

omit [EnoughInjectives C] in
include hf in
lemma isGE_cokernel : (cokernel f).IsGE n := by
  rw [isGE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  apply ((shortExact f).homology_exact₃ i (i+1) (by simp)).isZero_X₂
  · apply ((shortExact f).homology_exact₂ i).epi_f_iff.1
    dsimp
    have := hf i (by linarith)
    infer_instance
  · apply ((shortExact f).homology_exact₁ i (i+1) (by simp)).mono_g_iff.1
    dsimp
    by_cases h : i + 1 ≤ n-1
    · have := hf (i+1) h
      infer_instance
    · obtain rfl : n = i + 1 := by linarith
      infer_instance

omit [EnoughInjectives C] in
include hf in
lemma quasiIso_truncGEπ : QuasiIso ((cokernel f).πTruncGE n) := by
  rw [quasiIso_πTruncGE_iff]
  exact isGE_cokernel f n hf

variable [HasDerivedCategory C]

omit [Mono (homologyMap f n)] [Mono f] in
lemma mono_homologyMap_p (q : ℤ) (hq : q ≤ n) : Mono (homologyMap (p f n) q) :=
  (mappingCocone.homology_exact₁ (α f n) (q-1) q (by linarith)).mono_g (by
    apply IsZero.eq_of_src
    apply isZero_homology_I
    linarith)

omit [Mono (homologyMap f n)] [Mono f] in
lemma epi_homologyMap_p (q : ℤ) (hq : q < n) : Epi (homologyMap (p f n) q) :=
  (mappingCocone.homology_exact₂ (α f n) q).epi_f (by
    apply IsZero.eq_of_tgt
    dsimp
    apply isZero_homology_I
    linarith)

omit [Mono (homologyMap f n)] [Mono f] in
lemma isIso_homologyMap_p (q : ℤ) (hq : q < n) : IsIso (homologyMap (p f n) q) := by
  have := mono_homologyMap_p f n q (by linarith)
  have := epi_homologyMap_p f n q hq
  apply isIso_of_mono_of_epi

omit [Mono (homologyMap f n)] [Mono f] in
include hf in
lemma isIso_homologyMap_i' (q : ℤ) (hq : q < n) : IsIso (homologyMap (i f n) q) := by
  have := isIso_homologyMap_p f n q hq
  have h : IsIso (homologyMap f q) := by
    simpa only [quasiIsoAt_iff_isIso_homologyMap] using (hf q (by linarith))
  rw [← fac f n, homologyMap_comp] at h
  exact IsIso.of_isIso_comp_right (homologyMap (i f n) q) (homologyMap (p f n) q)

/-- homologyShortComplex'' -/
@[simps]
noncomputable def homologyShortComplex'' : ShortComplex C :=
  ShortComplex.mk (homologyMap (p f n) n) (homologyMap (α f n) n)
    (mappingCocone.homologyMap_fst_comp _ _)

instance : Mono (homologyShortComplex'' f n).f :=
  mono_homologyMap_p f n n (by rfl)

omit [Mono (homologyMap f n)] [Mono f] in
lemma homologyShortComplex''_exact : (homologyShortComplex'' f n).Exact :=
  mappingCocone.homology_exact₂ (α f n) n

lemma isIso_homologyMap_i : IsIso (homologyMap (i f n) n) := by
  have h₁ := (homologyShortComplex'_exact f n).fIsKernel
  have h₂ := (homologyShortComplex''_exact f n).fIsKernel
  have : (homologyMap (i f n) n) = (IsLimit.conePointUniqueUpToIso h₁ h₂).hom := by
    rw [← cancel_mono (homologyShortComplex'' f n).f]
    have eq := IsLimit.conePointUniqueUpToIso_hom_comp h₁ h₂ WalkingParallelPair.zero
    dsimp at eq ⊢
    rw [eq, ← homologyMap_comp, fac]
  rw [this]
  infer_instance

include hf in
lemma quasiIsoLE_cofFibFactorization : (cofFibFactorization f n).QuasiIsoLE n := ⟨fun q hq => by
  dsimp
  rw [quasiIsoAt_iff_isIso_homologyMap]
  obtain hq | rfl := hq.lt_or_eq
  · exact isIso_homologyMap_i' f n hf q hq
  · exact isIso_homologyMap_i f q⟩

end Step₂

section

open Step₂

lemma step₂ [Mono f] (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
    (hf : ∀ (i : ℤ) (_ : i ≤ n₀), QuasiIsoAt f i)
    [Mono (homologyMap f n₁)] :
    ∃ (F : CofFibFactorization f) (_ : F.IsIsoLE n₁), F.QuasiIsoLE n₁ := by
  have : HasDerivedCategory C := MorphismProperty.HasLocalization.standard _
  obtain rfl : n₀ = n₁ - 1 := by linarith
  exact ⟨cofFibFactorization f n₁, isIso_p_f f n₁, quasiIsoLE_cofFibFactorization f n₁ hf⟩

end

lemma step₁₂ [Mono f] (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
    (hf : ∀ (i : ℤ) (_ : i ≤ n₀), QuasiIsoAt f i) :
    ∃ (F : CofFibFactorization f) (_ : F.IsIsoLE n₀), F.QuasiIsoLE n₁ := by
  obtain ⟨F₁, hF₁, hF₁', _⟩ := step₁ f n₀ n₁ hn₁ hf
  obtain ⟨F₂, hF₂, hF₂'⟩ := step₂ F₁.1.i n₀ n₁ hn₁ (F₁.quasiIsoAt_of_quasiIsoLE n₀)
  have fac : F₂.1.i ≫ F₂.1.p ≫ F₁.1.p = f := by
    rw [reassoc_of% F₂.1.fac, F₁.1.fac]
  refine ⟨CofFibFactorization.mk fac
    (MorphismProperty.comp_mem _ _ _ F₂.2.hp F₁.2.hp), ?_,
      ⟨F₂.quasiIsoAt_of_quasiIsoLE n₁⟩⟩
  · intro i hi
    have := hF₁ i hi
    have := hF₂ i (by linarith)
    dsimp
    infer_instance

/-- step' -/
lemma step' (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
    (F : CofFibFactorizationQuasiIsoLE f n₀) :
    ∃ (F' : CofFibFactorizationQuasiIsoLE f n₁) (f : F'.1 ⟶ F.1),
      ∀ (i : ℤ) (_ : i ≤ n₀), IsIso (f.hom.φ.f i) := by
  obtain ⟨F₁₂, h, _⟩ := step₁₂ F.1.1.i n₀ n₁ hn₁ (F.1.quasiIsoAt_of_quasiIsoLE n₀)
  have fac : F₁₂.obj.i ≫ F₁₂.obj.p ≫ F.1.1.p = f := by rw [F₁₂.1.fac_assoc, F.1.1.fac]
  exact ⟨⟨CofFibFactorization.mk fac (MorphismProperty.comp_mem _ _ _ F₁₂.2.hp F.1.2.hp),
    ⟨F₁₂.quasiIsoAt_of_quasiIsoLE n₁⟩⟩, ObjectProperty.homMk { φ := F₁₂.1.p }, h⟩

namespace CofFibFactorizationQuasiIsoLE

def zero [Mono f] (n : ℤ) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE (n + 1)] :
    CofFibFactorizationQuasiIsoLE f (n + (0 : ℕ)) where
  obj := CofFibFactorization.mk (comp_id _) (fun n => by
    rw [Abelian.epiWithInjectiveKernel_iff]
    refine ⟨0, inferInstance, 0, ?_, ⟨0, 𝟙 _, ?_, ?_, ?_⟩⟩
    all_goals simp)
  property := ⟨by
    intro i hi
    simp only [Nat.cast_zero, add_zero] at hi
    dsimp
    rw [quasiIsoAt_iff_isIso_homologyMap]
    refine ⟨0, ?_, ?_⟩
    all_goals
      apply IsZero.eq_of_src
      rw [← exactAt_iff_isZero_homology, exactAt_iff]
      apply ShortComplex.exact_of_isZero_X₂
      apply isZero_of_isStrictlyGE _ (n + 1) i (by linarith)⟩

variable {f}

noncomputable def next {n₀ : ℤ} (F : CofFibFactorizationQuasiIsoLE f n₀)
    (n₁ : ℤ) (hn₁ : n₁ = n₀ + 1) :
    CofFibFactorizationQuasiIsoLE f n₁ :=
  (step' f _ _ hn₁ F).choose

noncomputable def fromNext {n₀ : ℤ} (F : CofFibFactorizationQuasiIsoLE f n₀)
    (n₁ : ℤ) (hn₁ : n₁ = n₀ + 1) : (F.next n₁ hn₁).1 ⟶ F.1 :=
  (step' f _ _ hn₁ F).choose_spec.choose

lemma isIso_fromNext_φ_f {n₀ : ℤ} (F : CofFibFactorizationQuasiIsoLE f n₀)
    (n₁ : ℤ) (hn₁ : n₁ = n₀ + 1) (i : ℤ) (hi : i ≤ n₀) :
    IsIso ((F.fromNext n₁ hn₁).hom.φ.f i) :=
  (step' f _ _ hn₁ F).choose_spec.choose_spec i hi

variable (f)

noncomputable def sequence [Mono f] (n₀ : ℤ) [K.IsStrictlyGE (n₀ + 1)] [L.IsStrictlyGE (n₀ + 1)] :
    ∀ (q : ℕ), CofFibFactorizationQuasiIsoLE f (n₀ + q)
  | 0 => zero f n₀
  | (q + 1) => (sequence n₀ q).next _ (by rw [Nat.cast_add, Nat.cast_one, add_assoc])

noncomputable def sequenceFromNext
    [Mono f] (n₀ : ℤ) [K.IsStrictlyGE (n₀ + 1)] [L.IsStrictlyGE (n₀ + 1)] (q : ℕ) :
    (sequence f n₀ (q + 1)).1 ⟶ (sequence f n₀ q).1 :=
  fromNext _ _ _

end CofFibFactorizationQuasiIsoLE

variable [Mono f] (n₀ : ℤ) [K.IsStrictlyGE (n₀ + 1)] [L.IsStrictlyGE (n₀ + 1)]

noncomputable def inverseSystem : ℕᵒᵖ ⥤ CofFibFactorization f :=
  (Functor.ofSequence (fun q => (CofFibFactorizationQuasiIsoLE.sequenceFromNext f n₀ q).op)).leftOp

noncomputable def inverseSystemI : ℕᵒᵖ ⥤ CochainComplex C ℤ :=
  inverseSystem f n₀ ⋙ CofFibFactorization.forget f ⋙ HomFactorization.forget f

lemma isIso_inverseSystemI_map_succ (n : ℕ) (q : ℤ) (hq : q ≤ n₀ + n) :
    IsIso (((inverseSystemI f n₀).map ((homOfLE (show n ≤ n + 1 by linarith)).op)).f q) := by
  dsimp only [inverseSystemI, inverseSystem]
  simp only [Functor.comp_obj, Functor.leftOp_obj, Opposite.unop_op, Functor.ofSequence_obj,
    HomFactorization.forget_obj, Functor.comp_map, Functor.leftOp_map, Quiver.Hom.unop_op,
    HomFactorization.forget_map, Functor.ofSequence_map_homOfLE_succ]
  change IsIso ((CofFibFactorizationQuasiIsoLE.sequenceFromNext f n₀ n).hom.1.f q)
  apply CofFibFactorizationQuasiIsoLE.isIso_fromNext_φ_f
  simpa only [Nat.add_eq, add_zero] using hq

/-- isIso_inverseSystemI_map' -/
lemma isIso_inverseSystemI_map' (n n' : ℕ) (h : n ≤ n')
    (q : ℤ) (hq : q ≤ n₀ + n) : IsIso (((inverseSystemI f n₀).map (homOfLE h).op).f q) := by
  suffices ∀ (k n n' : ℕ) (h : n + k = n') (q : ℤ) (_ : q ≤ n₀ + n),
      IsIso (((inverseSystemI f n₀).map (homOfLE (show n ≤ n' by linarith)).op).f q) by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact this k n _ rfl q hq
  intro k
  induction k with
  | zero =>
    intro n n' h
    obtain rfl : n = n' := by linarith
    intro q _
    have : homOfLE (show n ≤ n by rfl) = 𝟙 _ := rfl
    rw [this, op_id, (inverseSystemI f n₀).map_id, id_f]
    infer_instance
  | succ k hk =>
    intro n n'' h q hq
    let n' := n + k
    have := hk n n' rfl q hq
    rw [← homOfLE_comp (show n ≤ n' by omega) (show n' ≤ n'' by omega), op_comp,
      (inverseSystemI f n₀).map_comp, comp_f]
    obtain rfl : n'' = n' + 1 := by omega
    have := isIso_inverseSystemI_map_succ f n₀ n' q (by omega)
    infer_instance

lemma isIso_inverseSystemI_map {n n' : ℕ} (φ : Opposite.op n' ⟶ Opposite.op n)
    (q : ℤ) (hq : q ≤ n₀ + n) : IsIso (((inverseSystemI f n₀).map φ).f q) :=
  isIso_inverseSystemI_map' f n₀ n n' (leOfHom φ.unop) q hq

lemma isEventuallyConstantTo_inverseSystemI_comp_eval (q : ℤ) (n : ℕ) (hq : q ≤ n₀ + n) :
    (inverseSystemI f n₀ ⋙
      HomologicalComplex.eval _ _ q).IsEventuallyConstantTo (Opposite.op n) := by
  rintro ⟨n'⟩ φ
  exact isIso_inverseSystemI_map f n₀ φ q hq

instance (q : ℤ) :
    IsCofiltered.IsEventuallyConstant (inverseSystemI f n₀ ⋙ HomologicalComplex.eval _ _ q) where
  exists_isEventuallyConstantTo :=
    ⟨Opposite.op (q - n₀).toNat, isEventuallyConstantTo_inverseSystemI_comp_eval _ _ _ _
      (by linarith [Int.self_le_toNat (q - n₀)])⟩

example : HasLimit (inverseSystemI f n₀) := inferInstance

noncomputable def I := limit (inverseSystemI f n₀)

lemma isIso_π_f (n : ℕ) (q : ℤ) (hq : q ≤ n₀ + n) :
    IsIso ((limit.π (inverseSystemI f n₀) (Opposite.op n)).f q) := by
  apply isIso_limit_π_of_isEventuallyConstantTo
  exact isEventuallyConstantTo_inverseSystemI_comp_eval f n₀ q n hq

noncomputable def cone : Cone (inverseSystemI f n₀) where
  pt := K
  π :=
    { app := fun n => ((inverseSystem f n₀).obj n).1.i
      naturality := fun i j φ => by
        dsimp
        rw [id_comp]
        exact ((inverseSystem f n₀).map φ).hom.commi.symm }

noncomputable def i : K ⟶ I f n₀ := limit.lift (inverseSystemI f n₀) (cone f n₀)

noncomputable def p : I f n₀ ⟶ L :=
  limit.π _ (Opposite.op 0) ≫ ((inverseSystem f n₀).obj ((Opposite.op 0))).1.p

@[reassoc (attr := simp)]
lemma fac : i f n₀ ≫ p f n₀ = f := by simp [i, p, cone]

instance : Mono (i f n₀) := mono_of_mono_fac (fac f n₀)

/-- p' -/
noncomputable def p' (n : ℕ) : (inverseSystemI f n₀).obj (Opposite.op n) ⟶ L :=
  ((inverseSystem f n₀).obj (Opposite.op n)).1.p

@[simp]
lemma p'_zero : p' f n₀ 0 = 𝟙 _ := rfl

/-- `w_p'` -/
lemma w_p' (n n' : ℕ) (h : n ≤ n') :
    ((inverseSystemI f n₀).map (homOfLE h).op) ≫ p' f n₀ n = p' f n₀ n' :=
  ((inverseSystem f n₀).map (homOfLE h).op).hom.commp

/-- `π_comp_p'` -/
lemma π_comp_p' (n : ℕ) : limit.π _ (Opposite.op n) ≫ p' f n₀ n = p f n₀ := by
  dsimp [p]
  rw [← limit.w (inverseSystemI f n₀) (homOfLE (show 0 ≤ n by linarith)).op, assoc,
    (w_p' f n₀ 0 n _).symm]
  rfl

lemma isIso_p_f (q : ℤ) (hq : q ≤ n₀) : IsIso ((p f n₀).f q) := by
  rw [← π_comp_p' f n₀ 0, comp_f, p'_zero, id_f, comp_id]
  apply isIso_π_f
  rw [Nat.cast_zero, add_zero]
  exact hq

lemma degreewiseEpiWithInjectiveKernel_p :
    degreewiseEpiWithInjectiveKernel (CM5aCof.p f n₀) := fun q => by
  obtain ⟨n, hq⟩ : ∃ (n : ℕ), q ≤ n₀ + n :=
    ⟨Int.toNat (q - n₀), by linarith [Int.self_le_toNat (q - n₀)]⟩
  rw [← π_comp_p' f n₀ n, comp_f]
  refine MorphismProperty.comp_mem _ _ _ ?_ ?_
  · have := isIso_π_f f n₀ n q hq
    apply Abelian.epiWithInjectiveKernel_of_iso
  · exact ((inverseSystem f n₀).obj (Opposite.op n)).2.hp q


/-- i' -/
noncomputable def i' (n : ℕ) : K ⟶ (inverseSystemI f n₀).obj (Opposite.op n) :=
  ((inverseSystem f n₀).obj (Opposite.op n)).1.i

/-- quasiIsoAt_i' -/
lemma quasiIsoAt_i' (n : ℕ) (q : ℤ) (hq : q ≤ n₀ + n) : QuasiIsoAt (i' f n₀ n) q :=
  (CofFibFactorizationQuasiIsoLE.sequence f n₀ n).2.quasiIsoAt q hq

lemma quasiIsoAt_π_f (n : ℕ) (q : ℤ) (hq : q + 1 ≤ n₀ + n) :
    QuasiIsoAt (limit.π (inverseSystemI f n₀) (Opposite.op n)) q := by
  rw [quasiIsoAt_iff' _ (q-1) q (q + 1) (by simp) (by simp)]
  have := isIso_π_f f n₀ n (q-1) (by linarith)
  have := isIso_π_f f n₀ n q (by linarith)
  have := isIso_π_f f n₀ n (q+1) (by linarith)
  refine @ShortComplex.quasiIso_of_epi_of_isIso_of_mono _ _ _ _ _ _ _ _ ?_ ?_ ?_
  all_goals
    dsimp
    infer_instance

lemma i_π (n : ℕ) : i f n₀ ≫ (limit.π (inverseSystemI f n₀) (Opposite.op n)) = i' f n₀ n := by
  apply limit.lift_π

instance : QuasiIso (i f n₀) where
  quasiIsoAt q := by
    obtain ⟨n, hq⟩ : ∃ (n : ℕ), q + 1 ≤ n₀ + n :=
      ⟨Int.toNat (q + 1 - n₀), by linarith [Int.self_le_toNat (q + 1 - n₀)]⟩
    have := quasiIsoAt_π_f f n₀ n q hq
    rw [← quasiIsoAt_iff_comp_right _ (limit.π (inverseSystemI f n₀) (Opposite.op n)),
      i_π]
    exact quasiIsoAt_i' f n₀ n q  (by linarith)

example (n : ℤ) : n ≤ n.toNat := by exact Int.self_le_toNat n

end CM5aCof

section

lemma cm5a_cof (n : ℤ) [K.IsStrictlyGE n] [L.IsStrictlyGE n] [Mono f] :
    ∃ (L' : CochainComplex C ℤ) (_hL' : L'.IsStrictlyGE n) (i : K ⟶ L') (p : L' ⟶ L)
      (_hi : Mono i) (_hi' : QuasiIso i) (_hp : degreewiseEpiWithInjectiveKernel p), i ≫ p = f := by
  let n₀ := n - 1
  have : K.IsStrictlyGE (n₀ + 1) := K.isStrictlyGE_of_ge (n₀ + 1) n (by omega)
  have : L.IsStrictlyGE (n₀ + 1) := L.isStrictlyGE_of_ge (n₀ + 1) n (by omega)
  have : (CM5aCof.I f n₀).IsStrictlyGE n := by
    rw [isStrictlyGE_iff]
    intro q hq
    exact IsZero.of_iso (L.isZero_of_isStrictlyGE n q hq) (by
      have := CM5aCof.isIso_p_f f n₀ q (by omega)
      exact asIso ((CM5aCof.p f n₀).f q))
  exact ⟨_, inferInstance, CM5aCof.i f n₀, CM5aCof.p f n₀, inferInstance, inferInstance,
    CM5aCof.degreewiseEpiWithInjectiveKernel_p f n₀, CM5aCof.fac f n₀⟩

end

lemma cm5a (n : ℤ) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n] :
    ∃ (L' : CochainComplex C ℤ) (_hL' : L'.IsStrictlyGE n) (i : K ⟶ L') (p : L' ⟶ L)
      (_hi : Mono i) (_hi' : QuasiIso i) (_hp : degreewiseEpiWithInjectiveKernel p), i ≫ p = f := by
  have : K.IsStrictlyGE n := K.isStrictlyGE_of_ge n (n + 1) (by lia)
  obtain ⟨L', _, i₁, p₁, _, hp₁, _, rfl⟩ := cm5b f n
  obtain ⟨L'', _, i₂, p₂, _, _, hp₂, rfl⟩ := cm5a_cof i₁ n
  refine ⟨L'', inferInstance, i₂, p₂ ≫ p₁, inferInstance, inferInstance,
    MorphismProperty.comp_mem _ _ _ hp₂ hp₁, by simp⟩

variable (K)

/-- exists_injective_resolution' -/
lemma exists_injective_resolution' (n : ℤ) [K.IsStrictlyGE n] :
    ∃ (L : CochainComplex C ℤ) (i : K ⟶ L) (_hi : Mono i) (_hi' : QuasiIso i)
      (_ : ∀ (n : ℤ), Injective (L.X n)), L.IsStrictlyGE (n-1) := by
  have : K.IsStrictlyGE (n - 1 + 1) := by
    simp only [sub_add_cancel]
    infer_instance
  obtain ⟨L, hL, i, p, hi, hi', hp, _⟩ := cm5a (0 : K ⟶ 0) (n - 1)
  have hp₀ : p = 0 := (isZero_zero _).eq_of_tgt _ _
  refine ⟨L, i, hi, hi', fun n => Injective.of_iso ?_ ((hp n).2), hL⟩
  exact
    { hom := kernel.ι _
      inv := kernel.lift _ (𝟙 _) (by simp [hp₀])
      hom_inv_id := by rw [← cancel_mono (kernel.ι _), assoc, kernel.lift_ι, comp_id, id_comp]
      inv_hom_id := by simp }

lemma exists_injective_resolution (n : ℤ) [K.IsStrictlyGE n] :
    ∃ (L : CochainComplex C ℤ) (i : K ⟶ L) (_hi' : QuasiIso i)
      (_hL : ∀ (n : ℤ), Injective (L.X n)), L.IsStrictlyGE n := by
  have : HasDerivedCategory C := MorphismProperty.HasLocalization.standard _
  obtain ⟨L, i, _, _, hL, _⟩  := exists_injective_resolution' K n
  have : L.IsGE n := by
    have hK : K.IsGE n := inferInstance
    rw [← DerivedCategory.isGE_Q_obj_iff] at hK ⊢
    exact DerivedCategory.TStructure.t.isGE_of_iso (asIso (DerivedCategory.Q.map i)) n
  have : QuasiIso (L.πTruncGE n) := by
    rw [L.quasiIso_πTruncGE_iff n]
    infer_instance
  have : Injective (L.opcycles n) := by
    let S : ShortComplex C := ShortComplex.mk (L.d (n-1) n) (L.pOpcycles n) (by simp)
    have : Epi S.g := by dsimp; infer_instance
    have : Mono S.f := by
      let T := L.sc' (n-2) (n-1) n
      have hT : T.Exact := by
        rw [← L.exactAt_iff' (n-2) (n-1) n (by simp; linarith) (by simp),
          exactAt_iff_isZero_homology]
        exact L.isZero_of_isGE n (n-1) (by linarith)
      apply hT.mono_g
      apply IsZero.eq_of_src
      exact L.isZero_of_isStrictlyGE (n - 1) _
    have hS : S.ShortExact :=
      { exact := S.exact_of_g_is_cokernel (L.opcyclesIsCokernel (n-1) n (by simp)) }
    exact Injective.direct_factor (hS.splittingOfInjective).s_g
  -- note: this `i ≫ L.πTruncGE n` is a mono in degrees > n, but it may not be in degree n
  refine ⟨L.truncGE n, i ≫ L.πTruncGE n, inferInstance, ?_, inferInstance⟩
  intro q
  by_cases h : q < n
  · apply Injective.injective_of_isZero
    exact isZero_of_isStrictlyGE _ n _ h
  · simp only [not_lt] at h
    obtain (hq | rfl) := h.lt_or_eq
    · exact Injective.of_iso (L.truncGEXIso n q hq).symm (hL q)
    · exact Injective.of_iso (L.truncGEXIsoOpcycles n).symm inferInstance

section

variable (n : ℤ) [K.IsStrictlyGE n]

noncomputable def injectiveResolution : CochainComplex C ℤ :=
  (K.exists_injective_resolution n).choose

noncomputable def ιInjectiveResolution : K ⟶ K.injectiveResolution n :=
  (K.exists_injective_resolution n).choose_spec.choose

instance : QuasiIso (K.ιInjectiveResolution n) :=
  (K.exists_injective_resolution n).choose_spec.choose_spec.choose

instance (q : ℤ) : Injective ((K.injectiveResolution n).X q) :=
  (K.exists_injective_resolution n).choose_spec.choose_spec.choose_spec.choose q

instance : (K.injectiveResolution n).IsStrictlyGE n :=
  (K.exists_injective_resolution n).choose_spec.choose_spec.choose_spec.choose_spec

end

end CochainComplex
