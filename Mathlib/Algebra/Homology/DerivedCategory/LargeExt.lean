import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.CategoryTheory.Shift.ShiftedHom
import Mathlib.Data.Int.Units

universe w v u

section

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

instance : Neg (AddEquiv X Y) where
  neg e :=
    { toFun := fun x => -e x
      invFun := fun y => -e.symm y
      left_inv := fun x => by simp
      right_inv := fun y => by simp
      map_add' := fun x y => by
        dsimp
        rw [e.map_add]
        abel }

instance : SMul ℤˣ (AddEquiv X Y) where
  smul a e :=
    { toFun := fun x => a • e x
      invFun := fun y => a • e.symm y
      left_inv := fun x => by
        dsimp
        erw [map_zsmul, smul_smul]
        simp only [Int.units_mul_self, AddEquiv.symm_apply_apply, one_smul]
      right_inv := fun y => by
        dsimp
        erw [map_zsmul, smul_smul]
        simp only [Int.units_mul_self, AddEquiv.apply_symm_apply, one_smul]
      map_add' := fun x y => by
        dsimp
        rw [e.map_add, smul_add] }

lemma AddEquiv.neg_apply' (e : AddEquiv X Y) (x : X) :
    (-e) x = -e x := rfl

lemma AddEquiv.neg_symm_apply (e : AddEquiv X Y) (y : Y) :
    (-e).symm y = -e.symm y := rfl

end

open CategoryTheory Category Preadditive DerivedCategory Limits Pretriangulated

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasDerivedCategory.{w} C]

namespace CategoryTheory

namespace Abelian

variable (X Y Z : C) (n : ℕ)

structure LargeExt : Type w where
  hom : ShiftedHom ℤ ((singleFunctor _ 0).obj X) ((singleFunctor _ 0).obj Y) n

namespace LargeExt

variable {X Y Z n}

--lemma mk_hom
--    (f : ShiftedHom ℤ ((singleFunctor _ 0).obj X) ((singleFunctor _ 0).obj Y) n) :
--    (mk f).hom = f := rfl

lemma hom_injective (e₁ e₂ : LargeExt X Y n) (h : e₁.hom = e₂.hom) : e₁ = e₂ := by
  cases e₁
  cases e₂
  subst h
  rfl

lemma ext_iff (e₁ e₂ : LargeExt X Y n) : e₁ = e₂ ↔ e₁.hom = e₂.hom := by
  constructor
  · rintro rfl
    rfl
  · apply hom_injective

lemma mk_surjective (e : LargeExt X Y n) : ∃ (f : _), e = mk f := ⟨e.hom, rfl⟩

variable (X Y n)

@[simps]
def equiv :
    LargeExt X Y n ≃ ShiftedHom ℤ ((singleFunctor _ 0).obj X) ((singleFunctor _ 0).obj Y) n where
  toFun := hom
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : AddCommGroup (LargeExt X Y n) := Equiv.addCommGroup (equiv X Y n)

@[simps!]
def addEquiv :
    LargeExt X Y n ≃+ ShiftedHom ℤ ((singleFunctor _ 0).obj X) ((singleFunctor _ 0).obj Y) n where
  toEquiv := equiv X Y n
  map_add' _ _ := rfl

@[simp]
lemma add_hom (x y : LargeExt X Y n) : (x + y).hom = x.hom + y.hom := rfl

@[simp]
lemma sub_hom (x y : LargeExt X Y n) : (x - y).hom = x.hom - y.hom := rfl

@[simp]
lemma neg_hom (x : LargeExt X Y n) : (-x).hom = -x.hom := rfl

@[simp]
lemma zero_hom (X Y : C) (n : ℕ) : (0 : LargeExt X Y n).hom = 0 := rfl

@[simp]
lemma zsmul_hom (a : ℤ) (x : LargeExt X Y n) :
    (a • x).hom = a • x.hom := by
  let φ : LargeExt X Y n →+
      ((singleFunctor _ 0).obj X ⟶ ((singleFunctor _ 0).obj Y)⟦(n : ℤ)⟧) :=
    AddMonoidHom.mk' (fun e => e.hom) (by simp)
  apply φ.map_zsmul

variable {X Y}

noncomputable def ofHom (f : X ⟶ Y) : LargeExt X Y 0 :=
  mk (ShiftedHom.mk₀ ((singleFunctor _ 0).map f) ((0 : ℕ) : ℤ) rfl)

noncomputable def ofHomAddEquiv : (X ⟶ Y) ≃+ LargeExt X Y 0 where
  toFun f := ofHom f
  invFun g := (singleFunctor C 0).preimage (g.hom ≫
    (shiftFunctorZero' (DerivedCategory C) ((0 : ℕ) : ℤ) (by rfl)).hom.app _)
  left_inv f := by
    apply (singleFunctor C 0).map_injective
    simp only [Functor.image_preimage, ofHom, ShiftedHom.mk₀, assoc, Iso.inv_hom_id_app,
      Functor.id_obj, comp_id]
  right_inv g := by
    apply hom_injective
    dsimp only [ofHom, ShiftedHom.mk₀]
    simp only [Functor.image_preimage, assoc, Iso.hom_inv_id_app,
      comp_id]
  map_add' x y := by
    apply hom_injective
    simp [ofHom]

noncomputable instance : One (LargeExt X X 0) := ⟨ofHom (𝟙 _)⟩

@[simp]
lemma one_hom : (1 : LargeExt X X 0).hom = ShiftedHom.mk₀ (𝟙 _) ((0 : ℕ) : ℤ) rfl := by
  rw [← (singleFunctor C 0).map_id]
  rfl

variable (X)

@[simp]
lemma ofHom_id : ofHom (𝟙 X) = 1 := rfl

variable {X}

-- the signs are there for consistency with the composition
-- of Yoneda Ext, see Verdier, proposition III 3.2.5
noncomputable instance : HasGradedHMul (LargeExt Y Z) (LargeExt X Y) (LargeExt X Z) where
  γhmul' p q r h α β :=
    mk (((p * q : ℕ) : ℤ).negOnePow • β.hom •[show q + (p : ℤ) = r by
      rw [← h, Nat.cast_add, add_comm]] α.hom)

@[simp]
lemma γhmul_hom {p q n : ℕ} (α : LargeExt Y Z p) (β : LargeExt X Y q) (hpq : p + q = n) :
  (α •[hpq] β).hom =
    ((p * q : ℕ) : ℤ).negOnePow • β.hom •[by rw [← hpq, Nat.cast_add, add_comm]] α.hom := rfl

lemma γhmul_eq {p q n : ℕ} (α : LargeExt Y Z p) (β : LargeExt X Y q) (hpq : p + q = n) :
  (α •[hpq] β) = mk (((p * q : ℕ) : ℤ).negOnePow • β.hom •[show q + (p : ℤ) = n by
      rw [← hpq, Nat.cast_add, add_comm]] α.hom) := rfl

noncomputable example {p q n : ℕ} (α : LargeExt Y Z p) (β : LargeExt X Y q) (hpq : p + q = n) :
    LargeExt X Z n := α •[hpq] β

noncomputable example (f : LargeExt Y Z n) (g : X ⟶ Y) : LargeExt X Z n :=
  f •[add_zero n] (LargeExt.ofHom g)

lemma mk_zsmul (a : ℤ) (f : ShiftedHom ℤ ((singleFunctor _ 0).obj X) ((singleFunctor _ 0).obj Y) n) :
    mk (a • f) = a • mk f := rfl

@[simp]
lemma γhmul_add {p q n : ℕ} (α : LargeExt Y Z p) (β₁ β₂ : LargeExt X Y q) (hpq : p + q = n) :
    α •[hpq] (β₁ + β₂) = α •[hpq] β₁ + α •[hpq] β₂ := by
  apply hom_injective
  simp only [γhmul_hom, add_hom, ShiftedHom.add_γhmul, smul_add]

@[simp]
lemma add_γhmul {p q n : ℕ} (α₁ α₂ : LargeExt Y Z p) (β : LargeExt X Y q) (hpq : p + q = n) :
    (α₁ + α₂) •[hpq] β = α₁ •[hpq] β + α₂ •[hpq] β := by
  apply hom_injective
  simp only [γhmul_hom, add_hom, ShiftedHom.γhmul_add, smul_add]

@[simp]
lemma one_γhmul {n : ℕ} (β : LargeExt X Y n) :
    (1 : LargeExt Y Y 0) •[zero_add n] β = β := by
  apply hom_injective
  dsimp
  rw [one_hom]
  simp only [zero_mul, Int.negOnePow_zero, Int.ofNat_zero, one_smul]
  apply ShiftedHom.γhmul_one'

@[simp]
lemma γhmul_one {n : ℕ} (α : LargeExt X Y n) :
    α •[add_zero n] (1 : LargeExt X X 0)  = α := by
  apply hom_injective
  dsimp
  rw [one_hom]
  simp only [mul_zero, Int.negOnePow_zero, Int.ofNat_zero, one_smul]
  apply ShiftedHom.one_γhmul'

section

variable {R : Type*} [Ring R] [Linear R C]

noncomputable instance : Module R (LargeExt X Y n) := (equiv X Y n).module R

@[simp]
lemma smul_hom (a : R) (x : LargeExt X Y n) :
    (a • x).hom = a • x.hom := rfl

lemma smul_γhmul (a : R) {p q n : ℕ} (α : LargeExt Y Z p) (β : LargeExt X Y q) (hpq : p + q = n) :
    (a • α) •[hpq] β = a • (α •[hpq] β) := by
  apply hom_injective
  simp only [γhmul_hom, Nat.cast_mul, smul_hom, ShiftedHom.γhmul_smul, smul_smul]
  rw [smul_comm]

lemma units_smul_γhmul (a : Rˣ) {p q n : ℕ} (α : LargeExt Y Z p) (β : LargeExt X Y q) (hpq : p + q = n) :
    (a • α) •[hpq] β = a • (α •[hpq] β) :=
  smul_γhmul (a : R) α β hpq

lemma γhmul_smul {p q n : ℕ} (α : LargeExt Y Z p) (a : R) (β : LargeExt X Y q) (hpq : p + q = n) :
    α •[hpq] (a • β) = a • (α •[hpq] β) := by
  apply hom_injective
  simp only [γhmul_hom, Nat.cast_mul, smul_hom, ShiftedHom.smul_γhmul]
  rw [smul_comm]

lemma γhmul_units_smul {p q n : ℕ} (α : LargeExt Y Z p) (a : Rˣ) (β : LargeExt X Y q) (hpq : p + q = n) :
    α •[hpq] (a • β) = a • (α •[hpq] β) :=
  γhmul_smul α (a : R) β hpq

end

instance {X₁ X₂ X₃ X₄ : C} : IsAssocGradedHMul (LargeExt X₃ X₄)
    (LargeExt X₂ X₃) (LargeExt X₁ X₂) (LargeExt X₂ X₄) (LargeExt X₁ X₃)
    (LargeExt X₁ X₄) where
  γhmul_assoc p₁ p₂ p₃ α β γ p₁₂ p₂₃ p₁₂₃ h₁₂ h₂₃ h₁₂₃ := by
    apply hom_injective
    simp only [γhmul_hom, Nat.cast_mul, ShiftedHom.γhmul_units_smul, ShiftedHom.units_smul_γhmul, smul_smul,
      ← Int.negOnePow_add]
    congr 1
    · congr 1
      simp only [← h₁₂, ← h₂₃, Nat.cast_add, add_mul, mul_add]
      abel
    · symm
      apply IsAssocGradedHMul.γhmul_assoc

@[simp]
lemma ofHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    ofHom (f ≫ g) = ofHom g •[add_zero 0] ofHom f := by
  apply hom_injective
  dsimp [ofHom]
  simp only [Functor.map_comp, mul_zero, Int.negOnePow_zero, ShiftedHom.mk₀_comp, one_smul]

end LargeExt

@[simps]
noncomputable def LargeExtFunctor.obj (n : ℕ) (X : C) : C ⥤ Ab where
  obj := fun Y => AddCommGroupCat.of (LargeExt X Y n)
  map := fun f => AddCommGroupCat.ofHom (AddMonoidHom.mk'
    (fun β => (LargeExt.ofHom f) •[zero_add _] β)
    (fun β₁ β₂ => by dsimp ; simp))

@[simps]
noncomputable def LargeExtFunctor (n : ℕ) : Cᵒᵖ ⥤ C ⥤ Ab where
  obj X := LargeExtFunctor.obj n X.unop
  map {X₁ X₂} g :=
    { app := fun Y => AddCommGroupCat.ofHom (AddMonoidHom.mk'
        (fun α => (show LargeExt X₁.unop Y n from α) •[add_zero n] (LargeExt.ofHom g.unop))
        (fun _ _ => LargeExt.add_γhmul _ _ _ _)) }

section Linear

namespace LargeExt

variable {R : Type*} [Ring R] [Linear R C]

@[simps!]
noncomputable def leftSMul {Y Z : C} {p : ℕ} (α : LargeExt Y Z p)
    (X : C) (q : ℕ) (n : ℕ) (hpq : p + q = n) :
    LargeExt X Y q →+ LargeExt X Z n :=
  AddMonoidHom.mk' (fun β => α •[hpq] β) (by simp)

@[simps!]
noncomputable def rightSMul {X Y : C} {q : ℕ} (β : LargeExt X Y q)
    (Z : C) (p : ℕ) (n : ℕ) (hpq : p + q = n) :
    LargeExt Y Z p →+ LargeExt X Z n :=
  AddMonoidHom.mk' (fun α => α •[hpq] β) (by simp)

end LargeExt

end Linear

end Abelian

open Abelian

namespace ShortComplex

variable {S : ShortComplex C} (hS : S.ShortExact)

namespace ShortExact

noncomputable def singleδ : (singleFunctor C 0).obj S.X₃ ⟶
    ((singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧ :=
  (((SingleFunctors.evaluation _ _ 0).mapIso (singleFunctorsPostCompQIso C)).hom.app S.X₃) ≫
    triangleOfSESδ (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)) ≫
    (((SingleFunctors.evaluation _ _ 0).mapIso (singleFunctorsPostCompQIso C)).inv.app S.X₁)⟦(1 : ℤ)⟧'

@[simps!]
noncomputable def singleTriangle : Triangle (DerivedCategory C) :=
  Triangle.mk ((singleFunctor C 0).map S.f)
    ((singleFunctor C 0).map S.g) hS.singleδ

lemma singleTriangle_distinguished :
    hS.singleTriangle ∈ distTriang (DerivedCategory C) :=
  isomorphic_distinguished _ (triangleOfSES_distinguished (hS.map_of_exact
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0))) _ (by
    let e := (SingleFunctors.evaluation _ _ 0).mapIso (singleFunctorsPostCompQIso C)
    refine' Triangle.isoMk _ _ (e.app S.X₁) (e.app S.X₂) (e.app S.X₃) _ _ _
    · aesop_cat
    · aesop_cat
    · dsimp [singleδ, e]
      simp only [assoc, ← Functor.map_comp, SingleFunctors.inv_hom_id_hom_app,
        SingleFunctors.postComp_functor, Functor.comp_obj]
      erw [Functor.map_id, comp_id])

lemma eq_singleδ_iff_distinguished
    (α : (singleFunctor C 0).obj S.X₃ ⟶
      ((singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧) :
      α = hS.singleδ ↔
        Triangle.mk ((singleFunctor C 0).map S.f)
          ((singleFunctor C 0).map S.g) α ∈ distTriang (DerivedCategory C) := by
  constructor
  · rintro rfl
    apply singleTriangle_distinguished
  · intro h
    obtain ⟨φ, hφ₁, hφ₂⟩ := complete_distinguished_triangle_morphism _ _ h hS.singleTriangle_distinguished
      (𝟙 _) (𝟙 _) (by simp)
    obtain ⟨φ, rfl⟩ := (singleFunctor C 0).map_surjective φ
    obtain rfl : φ = 𝟙 _ := by
      have := hS.epi_g
      rw [← cancel_epi S.g]
      apply (singleFunctor C 0).map_injective
      simpa using hφ₁
    simpa using hφ₂

noncomputable def largeExtClass : LargeExt S.X₃ S.X₁ 1 :=
  LargeExt.mk hS.singleδ

lemma extClass_γhmul : hS.largeExtClass •[add_zero 1] (LargeExt.ofHom S.g) = 0 := by
  apply LargeExt.hom_injective
  dsimp [largeExtClass]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  erw [ShiftedHom.mk₀_γhmul]
  exact comp_distTriang_mor_zero₂₃ _ (hS.singleTriangle_distinguished)

lemma γhmul_extClass : (LargeExt.ofHom S.f) •[zero_add 1] hS.largeExtClass = 0 := by
  apply LargeExt.hom_injective
  dsimp [largeExtClass]
  have eq := comp_distTriang_mor_zero₃₁ _ (hS.singleTriangle_distinguished)
  rw [ShiftedHom.γhmul_eq]
  dsimp [LargeExt.ofHom, ShiftedHom.mk₀] at eq ⊢
  simp only [mul_one, Functor.map_comp, assoc, reassoc_of% eq, zero_comp, Nat.cast_zero,
    Int.negOnePow_zero, one_smul]

section

variable (A : C) (n n₀ n₁ : ℕ) (hn₁ : n₀ + 1 = n₁)
variable (S)

@[simp]
noncomputable def covariantLargeExtArrow₂₂ : Arrow₂ AddCommGroupCat :=
  Arrow₂.mk' (AddCommGroupCat.ofHom ((LargeExt.ofHom S.f).leftSMul A n n  (zero_add n)))
    (AddCommGroupCat.ofHom ((LargeExt.ofHom S.g).leftSMul A n n (zero_add n)))

variable {S}

/-lemma covariantLargeExtArrow₂₂Iso :
    covariantLargeExtArrow₂₂ S A n ≅ ((shortComplexOfDistTriangle (hS.singleTriangle⟦(n : ℤ)⟧)
      (Triangle.shift_distinguished _ hS.singleTriangle_distinguished _)).map
    (preadditiveCoyoneda.obj (Opposite.op ((singleFunctor C 0).obj A)))).arrow₂ :=
  AddCommGroupCat.arrow₂IsoMk ((-1 : Units ℤ)^n • LargeExt.addEquiv A S.X₁ n)
    (LargeExt.addEquiv A S.X₂ n) (LargeExt.addEquiv A S.X₃ n) (fun x₁ => by
      obtain ⟨x₁, rfl⟩ := (LargeExt.equiv _ _ _).symm.surjective x₁
      dsimp [LargeExt.addEquiv, LargeExt.equiv]
      dsimp only [FunLike.coe, ZeroHom.toFun, ModuleCat.ofHom, LinearMap.toAddMonoidHom, EquivLike.coe]
      dsimp [ZeroHom.toFun, LargeExt.leftSMul]
      simp
      sorry) sorry

lemma covariantLargeExtArrow₂₂_zero : (covariantLargeExtArrow₂₂ S A n).Zero :=
  Arrow₂.zero_of_arrow₂Iso (covariantLargeExtArrow₂₂Iso hS A n)

lemma covariant_largeExt_exact₂ :
    (ShortComplex.mk _ _ (covariantLargeExtArrow₂₂_zero hS A n)).Exact :=
  exact_of_arrow₂Iso (covariantLargeExtArrow₂₂Iso hS A n) (by apply Functor.map_distinguished_exact) -/

end

/- needs refactor as the signs have been changed...
lemma covariant_LargeExt_exact₁ {A : C} {n₁ : ℕ}
    (x₁ : LargeExt A S.X₁ n₁) (hx₁ : (LargeExt.ofHom S.f) •[zero_add n₁] x₁ = 0)
    (n₀ : ℕ) (h : 1 + n₀ = n₁) :
    ∃ (x₃ : LargeExt A S.X₃ n₀), x₁ = hS.extClass •[h] x₃ := by
  have h' : 1 + (n₀ : ℤ) = n₁ := by rw [← h, Nat.cast_add, Nat.cast_one]
  have h'' : (n₀ : ℤ) + 1 = n₁ := by rw [← h', add_comm 1]
  obtain ⟨y₃, hy₃⟩ := covariant_yoneda_exact₁ _
    (shift_distinguished _ hS.singleTriangle_distinguished n₀)
    (x₁.hom ≫ (shiftFunctorAdd' (DerivedCategory C) _ _ _ h'').hom.app _) (by
      simp only [LargeExt.ext_iff, LargeExt.γhmul_hom, newExt.ofHom,
        ShiftedHom.mk₀_γhmul, newExt.zero_hom] at hx₁
      dsimp [Triangle.shiftFunctor]
      simp only [assoc, Functor.map_zsmul, comp_zsmul]
      erw [← NatTrans.naturality, reassoc_of% hx₁, zero_comp, zsmul_zero])
  refine' ⟨CochainComplex.ε n₀ • newExt.mk y₃, _⟩
  apply newExt.hom_injective
  dsimp at hy₃
  simp only [newExt.γhmul_hom, extClass, ShiftedHom.γhmul_eq, newExt.zsmul_hom]
  rw [zsmul_comp, ← cancel_mono ((shiftFunctorAdd' (DerivedCategory C) _ _ _ h'').hom.app _), hy₃,
    comp_zsmul, zsmul_comp, assoc, assoc,
    shiftFunctorComm_eq _ _ _ _ h', Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rfl

lemma covariant_newExt_exact₂ {A : C} {n : ℕ}
    (x₂ : newExt A S.X₂ n) (hx₂ : (newExt.ofHom S.g) •[zero_add n] x₂ = 0) :
    ∃ (x₁ : newExt A S.X₁ n), x₂ = (newExt.ofHom S.f) •[zero_add n] x₁ := by
  obtain ⟨y₁, hy₁⟩ := covariant_yoneda_exact₂ _
    (shift_distinguished _ hS.singleTriangle_distinguished n) x₂.hom (by
      simp only [newExt.ext_iff, newExt.γhmul_hom, newExt.ofHom,
        ShiftedHom.mk₀_γhmul, newExt.zero_hom] at hx₂
      dsimp [Triangle.shiftFunctor]
      simp only [comp_zsmul, hx₂, zsmul_zero])
  refine' ⟨CochainComplex.ε n • newExt.mk y₁, _⟩
  apply newExt.hom_injective
  simp only [newExt.γhmul_hom, newExt.zsmul_hom,
    ShiftedHom.γhmul_zsmul, newExt.ofHom, ShiftedHom.mk₀_γhmul,
    hy₁, Triangle.shiftFunctor_obj, comp_zsmul, Triangle.mk_mor₁,
    singleTriangle_mor₁]

lemma covariant_newExt_exact₃ {A : C} {n₀ : ℕ}
    (x₃ : newExt A S.X₃ n₀) (n₁ : ℕ) (h : 1 + n₀ = n₁)
    (hx₃ : hS.extClass •[h] x₃ = 0) :
    ∃ (x₂ : newExt A S.X₂ n₀), x₃ = (newExt.ofHom S.g) •[zero_add n₀] x₂ := by
  obtain ⟨y₂, hy₂⟩ := covariant_yoneda_exact₃ _
    (shift_distinguished _ hS.singleTriangle_distinguished n₀) x₃.hom (by
      simp only [newExt.ext_iff, newExt.γhmul_hom, extClass,
        ShiftedHom.γhmul_eq, newExt.zero_hom, ← assoc] at hx₃
      rw [IsIso.comp_right_eq_zero] at hx₃
      dsimp [Triangle.shiftFunctor]
      simp only [comp_zsmul, reassoc_of% hx₃, zero_comp, zsmul_zero])
  refine' ⟨CochainComplex.ε n₀ • newExt.mk y₂, _⟩
  apply newExt.hom_injective
  simp only [newExt.γhmul_hom, newExt.zsmul_hom, newExt.ofHom, ShiftedHom.mk₀_γhmul,
    hy₂, Triangle.shiftFunctor_obj, Triangle.mk_mor₂, singleTriangle_mor₂,
    comp_zsmul]
  rw [zsmul_comp]

/- Note: the right multiplication with `hS.extClass` presumably corresponds to the connecting
homomorphism only up to a sign. -/

lemma contravariant_newExt_exact₁ {B : C} {n₀ : ℕ}
    (x₁ : newExt S.X₁ B n₀) (n₁ : ℕ) (h : n₀ + 1 = n₁)
    (hx₁ : x₁ •[h] hS.extClass = 0) :
    ∃ (x₂ : newExt S.X₂ B n₀), x₁ = x₂ •[add_zero n₀] (newExt.ofHom S.f) := by
  obtain ⟨x₂, hx₂⟩ := contravariant_yoneda_exact₂ _
    (inv_rot_of_dist_triangle _ hS.singleTriangle_distinguished) x₁.hom (by
      apply (shiftFunctor (DerivedCategory C) (1 : ℤ)).map_injective
      simp only [newExt.ext_iff, newExt.zero_hom, newExt.γhmul_hom, extClass,
        ShiftedHom.γhmul_eq] at hx₁
      rw [← assoc, IsIso.comp_right_eq_zero] at hx₁
      dsimp at hx₁ ⊢
      simp only [Functor.map_comp, Functor.map_neg, Functor.map_zero, neg_comp, assoc,
        neg_eq_zero, shift_neg_shift', IsIso.comp_left_eq_zero,
        shift_shiftFunctorCompIsoId_add_neg_self_hom_app, Iso.inv_hom_id_app_assoc, hx₁])
  refine' ⟨newExt.mk x₂, _⟩
  apply newExt.hom_injective
  simp only [newExt.γhmul_hom, newExt.ofHom, ShiftedHom.γhmul_mk₀, hx₂,
    Triangle.invRotate_mor₂, singleTriangle_mor₁]

lemma contravariant_newExt_exact₂ {B : C} {n : ℕ}
    (x₂ : newExt S.X₂ B n) (hx₂ : x₂ •[add_zero n] (newExt.ofHom S.f) = 0) :
    ∃ (x₃ : newExt S.X₃ B n), x₂ = x₃ •[add_zero n] (newExt.ofHom S.g) := by
  obtain ⟨y₃, hy₃⟩ := contravariant_yoneda_exact₂ _ hS.singleTriangle_distinguished x₂.hom (by
    simpa only [newExt.ext_iff, newExt.γhmul_hom, newExt.ofHom,
      ShiftedHom.γhmul_mk₀, newExt.zero_hom] using hx₂)
  refine' ⟨newExt.mk y₃, _⟩
  apply newExt.hom_injective
  dsimp at hy₃
  simp only [newExt.γhmul_hom, hy₃, newExt.ofHom, ShiftedHom.γhmul_mk₀]

lemma contravariant_newExt_exact₃ {B : C} {n₁ : ℕ}
    (x₃ : newExt S.X₃ B n₁) (hx₃ : x₃ •[add_zero n₁] (newExt.ofHom S.g) = 0)
    (n₀ : ℕ) (h : n₀ + 1 = n₁) :
    ∃ (x₁ : newExt S.X₁ B n₀), x₃ = x₁ •[h] hS.extClass := by
  have h' : (n₀ : ℤ) + 1 = n₁ := by rw [← h, Nat.cast_add, Nat.cast_one]
  obtain ⟨y₁, hy₁⟩ := contravariant_yoneda_exact₃ _ hS.singleTriangle_distinguished x₃.hom (by
    simpa only [newExt.ext_iff, newExt.γhmul_hom, newExt.ofHom,
      ShiftedHom.γhmul_mk₀, newExt.zero_hom] using hx₃)
  obtain ⟨x₁, rfl⟩ : ∃ (x₁ : (singleFunctor C 0).obj S.X₁ ⟶ ((singleFunctor C 0).obj B)⟦(n₀ : ℤ)⟧),
      y₁ = x₁⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' (DerivedCategory C) _ _ _ h').inv.app _ :=
    ⟨(shiftFunctor (DerivedCategory C) (1 : ℤ)).preimage
      (y₁ ≫ (shiftFunctorAdd' (DerivedCategory C) _ _ _ h').hom.app _), by simp⟩
  refine' ⟨newExt.mk x₁, _⟩
  apply newExt.hom_injective
  simp only [newExt.γhmul_hom, ShiftedHom.γhmul_eq, extClass]
  exact hy₁-/

end ShortExact

end ShortComplex

end CategoryTheory
