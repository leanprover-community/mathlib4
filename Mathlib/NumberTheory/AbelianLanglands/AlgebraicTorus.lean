import Mathlib.FieldTheory.Galois
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.Algebra.Category.GroupCat.Basic
import Mathlib.NumberTheory.AbelianLanglands.FGCommAlg
import Mathlib.Data.Polynomial.Laurent
import Mathlib.NumberTheory.AbelianLanglands.MvLaurentPolynomial
import Mathlib.CategoryTheory.Whiskering
import Mathlib.RingTheory.Algebraic
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.NumberTheory.AbelianLanglands.amibeinganidiot
open CategoryTheory
universe v u
set_option autoImplicit false
noncomputable section
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (σ : Type)

local notation:9000 R "[T;T⁻¹]" => LaurentPolynomial R
local notation:9000 R "["σ";"σ"⁻¹]" => MvLaurentPolynomial σ R

def AffineGroupScheme :=
FullSubcategory fun F : CommAlg.{u, u} R ⥤ GroupCat => (F ⋙ forget _).Corepresentable

instance : Category (AffineGroupScheme R) := by
  unfold AffineGroupScheme; infer_instance

instance (X : AffineGroupScheme R) : (X.1 ⋙ forget _).Corepresentable := X.2

namespace LaurentPolynomial
noncomputable def eval₂AlgHom (R : Type _) {S : Type _}
  [CommSemiring R] [Ring S] [Algebra R S] (x : S) (hx : IsUnit x) :
  R[T;T⁻¹] →ₐ[R] S :=
AddMonoidAlgebra.lift _ _ _ ((Units.coeHom S).comp (zpowersHom Sˣ $ IsUnit.unit hx))

@[simp] lemma eval₂AlgHom_C_mul_T {R S : Type _} [CommSemiring R] [Ring S]
  [Algebra R S] {x : S} {hx : IsUnit x} (n : ℤ) (r : R) :
    eval₂AlgHom R x hx (C r * T n) = r • ((IsUnit.unit hx ^ n : Sˣ) : S) := by
  rw [eval₂AlgHom, AddMonoidAlgebra.lift_apply, ←single_eq_C_mul_T, Finsupp.sum_single_index]
  { rfl }
  { rw [zero_smul] }

@[simp] lemma eval₂AlgHom_T {R S : Type _} [CommSemiring R] [Ring S]
  [Algebra R S] {x : S} {hx : IsUnit x} (n : ℤ) :
    eval₂AlgHom R x hx (T n) = IsUnit.unit hx ^ n := by
  rw [eval₂AlgHom, AddMonoidAlgebra.lift_apply, T, Finsupp.sum_single_index]
  { rw [one_smul]
    rfl }
  { rw [zero_smul] }

@[simps] noncomputable def algHomEquivUnits (R S : Type _)
  [CommSemiring R] [Ring S] [Algebra R S] :
    (R[T;T⁻¹] →ₐ[R] S) ≃ Sˣ where
  toFun := fun f => ((isUnit_T 1).map f).unit
  invFun := fun s => eval₂AlgHom R s (Units.isUnit s)
  left_inv := fun f => by ext; simp
  right_inv := fun f => by ext; simp

end LaurentPolynomial
section
open LaurentPolynomial

@[simps] def 𝔾ₘObj : CommAlg R ⥤ GroupCat where
  obj := fun A => GroupCat.of Aˣ
  map := fun f => Units.map f

/-instance : AddMonoid.FG ℤ :=
⟨{-1, 1}, sorry⟩ -- better things to do with my life.

instance : Algebra.FiniteType R R[T;T⁻¹] :=
AddMonoidAlgebra.finiteType_of_fg _ _

instance {σ : Type _} [Fintype σ] : AddMonoid.FG (σ →₀ ℤ) :=
sorry -- ffs
instance {σ : Type _} [Fintype σ] : Algebra.FiniteType R R[σ;σ⁻¹] :=
AddMonoidAlgebra.finiteType_of_fg _ _-/

noncomputable def 𝔾ₘObjCompForgetNatIso :
  𝔾ₘObj R ⋙ forget _ ≅ coyoneda.obj (Opposite.op (CommAlg.of R R[T;T⁻¹])) :=
NatIso.ofComponents (fun X => (algHomEquivUnits R X).symm.toIso) (by
  intro X Y (f : X →ₐ[R] Y)
  ext (x : Xˣ)
  dsimp
  rw [←AddMonoidAlgebra.algHom_ext_iff]
  intro i
  rw [single_eq_C_mul_T, map_one, one_mul]
  show _ = f _
  erw [algHomEquivUnits_symm_apply, algHomEquivUnits_symm_apply]
  dsimp
  rw [eval₂AlgHom_T, eval₂AlgHom_T]
  simp only [Units.coe_map, MonoidHom.coe_coe, IsUnit.unit_of_val_units, ←map_zpow])

@[simps] def 𝔾ₘ : AffineGroupScheme R where
  obj := 𝔾ₘObj R
  property := ⟨Opposite.op (CommAlg.of R R[T;T⁻¹]),
    (𝔾ₘObjCompForgetNatIso R).inv, by infer_instance⟩

end

@[simps] def splitTorusObj (σ : Type _) [Fintype σ] : CommAlg R ⥤ GroupCat where
  obj := fun A => GroupCat.of (σ → Aˣ)
  map := fun {X Y} f => MonoidHom.compLeft (Units.map (f : X →* Y)) σ

namespace MvLaurentPolynomial
open MvLaurentPolynomial
variable {σ}
noncomputable def eval₂AlgHom (R : Type _) {S : Type _}
  [CommSemiring R] [CommRing S] [Algebra R S] (x : σ → S) (hx : ∀ i : σ, IsUnit (x i)) :
  R[σ;σ⁻¹] →ₐ[R] S :=
AddMonoidAlgebra.lift _ _ _ ((Units.coeHom S).comp
  (AddMonoidHom.toMultiplicative''
    (Finsupp.liftAddHom (fun i => zmultiplesHom (Additive Sˣ) (hx i).unit))))

@[simp] lemma eval₂AlgHom_C_mul_T {R S : Type _} [CommSemiring R] [CommRing S]
  [Algebra R S] {x : σ → S} {hx : ∀ i : σ, IsUnit (x i)} (n : σ) (i : ℤ) (r : R) :
    eval₂AlgHom R x hx (C r * T n i) = r • ((IsUnit.unit (hx n) ^ i : Sˣ) : S) := by
sorry

@[simp] lemma eval₂AlgHom_T {R S : Type _} [CommSemiring R] [CommRing S]
  [Algebra R S] {x : σ → S} {hx : ∀ i : σ, IsUnit (x i)} (n : σ) (i : ℤ) :
    eval₂AlgHom R x hx (T n i) = IsUnit.unit (hx n) ^ i := by
  sorry

variable (σ)

@[simps] noncomputable def algHomEquivUnits (R S : Type _)
  [CommSemiring R] [CommRing S] [Algebra R S] :
    (R[σ;σ⁻¹] →ₐ[R] S) ≃ (σ → Sˣ) where
  toFun := fun f n => ((isUnit_T (n := n) 1).map f).unit
  invFun := fun s => eval₂AlgHom R (fun n => s n) (fun n => Units.isUnit (s n))
  left_inv := sorry
  right_inv := sorry

end MvLaurentPolynomial

def splitTorusObjCompForgetNatIso (σ : Type) [Fintype σ] :
  splitTorusObj R σ ⋙ forget _ ≅
    coyoneda.obj (Opposite.op (CommAlg.of R R[σ;σ⁻¹])) :=
NatIso.ofComponents (fun X => (MvLaurentPolynomial.algHomEquivUnits σ R X).symm.toIso) sorry

@[simps] def splitTorus (σ : Type) [Fintype σ] : AffineGroupScheme R where
  obj := splitTorusObj R σ
  property := ⟨Opposite.op (CommAlg.of R R[σ;σ⁻¹]),
    (splitTorusObjCompForgetNatIso R σ).inv, by infer_instance⟩

def rankOneSplitTorusIso (σ : Type) [Unique σ] :
  splitTorus R σ ≅ 𝔾ₘ R := sorry

open scoped TensorProduct

@[simp] def ffs2 (A B : Type u) [Ring A] [Algebra R A]
    [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B] :
    (S ⊗[R] A →ₐ[S] B) ≃ (A →ₐ[R] B) where
  toFun := fun f => (AlgHom.restrictScalars R f).comp Algebra.TensorProduct.includeRight
  invFun := fun f => Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId S B) f
  left_inv := fun f => by
    ext x
    refine' TensorProduct.induction_on x (by simp only [map_zero]) _ _
    · intro x y
      show algebraMap S B x * f (_ ⊗ₜ y) = f _
      rw [←Algebra.smul_def, ←map_smul]
      show f ((x * 1) ⊗ₜ[R] y) = _
      rw [mul_one]
    · intro x y hx hy
      rw [map_add, hx, hy, map_add]
  right_inv := fun f => by
    ext
    simp

def RestrictScalars.algebraOrig (A : Type u) [Ring A] [i : Algebra S A] :
  Algebra S (RestrictScalars R S A) := i

def toRestrictScalarsLeft (A B : Type u) [Ring A] [Algebra R A] [Algebra S A]
  [IsScalarTower R S A] [Ring B] [Algebra S B]
  (f : A →ₐ[S] B) : A →ₐ[R] RestrictScalars R S B :=
{   (RestrictScalars.ringEquiv _ _ _).symm.toRingHom.comp f.toRingHom with
  commutes' := fun r => by
    dsimp
    refine' (Equiv.symm_apply_eq _).2 _
    simp only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
      RestrictScalars.ringEquiv_algebraMap, ←f.commutes, ←IsScalarTower.algebraMap_apply] }

  @[simp] def ffs3 (A B : Type u) [Ring A] [Algebra R A]
    [CommRing B] [Algebra S B] :
    (S ⊗[R] A →ₐ[S] B) ≃ (A →ₐ[R] RestrictScalars R S B) where
  toFun := fun f => (toRestrictScalarsLeft _ _ _ _ _).comp Algebra.TensorProduct.includeRight
  invFun := fun f => by
    let i := RestrictScalars.algebraOrig R S B
    exact Algebra.TensorProduct.productLeftAlgHom (S := RestrictScalars R S B)
      (Algebra.ofId S (RestrictScalars R S B)) f
  left_inv := fun f => by
    ext x
    refine' TensorProduct.induction_on x (by simp only [map_zero]) _ _
    · intro x y
      show algebraMap S B x * f (_ ⊗ₜ y) = f _
      rw [←Algebra.smul_def, ←map_smul]
      show f ((x * 1) ⊗ₜ[R] y) = _
      rw [mul_one]
    · intro x y hx hy
      rw [map_add, hx, hy, map_add]
  right_inv := fun f => by
    ext
    simp

def baseChangeAux (A : CommAlg R) :
  CommAlg.restrictScalars R S ⋙ coyoneda.obj (Opposite.op A)
    ≅ coyoneda.obj (Opposite.op (CommAlg.of S (S ⊗[R] A))) :=
NatIso.ofComponents (fun B => by
  dsimp
  let i1 : Algebra R (RestrictScalars R S B) := by infer_instance
  let i2 : Module S (RestrictScalars R S B) := RestrictScalars.moduleOrig R S B
  let i3 : IsScalarTower R S (RestrictScalars R S B) := by infer_instance
  have := @ffs2 R S _ _ _ A B _ _ _ i1 _ i3
  ) _

def baseChange : AffineGroupScheme R ⥤ AffineGroupScheme S :=
FullSubcategory.lift _
  (fullSubcategoryInclusion _ ⋙ (whiskeringLeft _ _ _).obj (CommAlg.restrictScalars R S)) (by
    intro G
    constructor
    rcases G with ⟨G, X, f, hf⟩
    use Opposite.op (CommAlg.of S (TensorProduct R S X.unop))
    sorry)

def baseChangeCoreprXIso (X : AffineGroupScheme R) :
  (((baseChange R S).obj X).1 ⋙ forget _).coreprX
    ≅ CommAlg.of S (S ⊗[R] (X.1 ⋙ forget _).coreprX) := sorry

def baseChangeIso (X : AffineGroupScheme R) :
  ((baseChange R S).obj X).1 ⋙ forget _
    ≅ coyoneda.obj (Opposite.op (CommAlg.of S
    (S ⊗[R] (X.1 ⋙ forget _).coreprX))) :=
(Functor.coreprW _).symm ≪≫ Functor.mapIso _ (baseChangeCoreprXIso R S X).symm.op

-- idfk
def baseChangeObjMulEquiv (A : Type u) [CommRing A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] (X : AffineGroupScheme R) :
  ((baseChange R S).obj X).1.obj (CommAlg.of S A) ≃* X.1.obj (CommAlg.of R A) :=
(X.1.mapIso (restrictScalarsAlgEquiv R S A).toCommAlgIso).groupIsoToMulEquiv

variable {R}

-- idk, you have to type out the base change if you use this.
-- just put it in to stop myself accidentally writing CharGroup X instead of of the base change. idfk
class IsSplit (σ : outParam Type) [Fintype σ] (X : AffineGroupScheme R) : Prop where
  out : Nonempty (X ≅ splitTorus R σ)

def IsSplit.iso (σ : Type) [Fintype σ] (X : AffineGroupScheme R) [IsSplit σ X] :
    X ≅ splitTorus R σ :=
Classical.choice IsSplit.out

instance (σ : Type) [Fintype σ] (X : AffineGroupScheme R) [IsSplit σ X] (A : CommAlg R) :
  CommGroup (X.1.obj A) :=
{ mul_comm := sorry }

class SplitsOver (S : outParam (Type u)) [CommRing S] [Algebra R S] (σ : outParam Type)
    [Fintype σ] (X : AffineGroupScheme R) : Prop where
  out : Nonempty ((baseChange R S).obj X ≅ splitTorus S σ)

def SplitsOver.iso (σ : Type) [Fintype σ] (X : AffineGroupScheme R) [SplitsOver S σ X] :
    (baseChange R S).obj X ≅ splitTorus S σ :=
Classical.choice SplitsOver.out

instance (σ : Type) [Fintype σ] : IsSplit σ (splitTorus R σ) where
  out := ⟨Iso.refl _⟩

instance (S : Type u) [CommRing S] [Algebra R S] (σ : Type) [Fintype σ]
    (X : AffineGroupScheme R) [SplitsOver S σ X] : IsSplit σ ((baseChange R S).obj X) where
  out := ⟨SplitsOver.iso S σ X⟩

instance : IsSplit PUnit (𝔾ₘ R) where
  out := ⟨(rankOneSplitTorusIso R PUnit).symm⟩

def SplitsOver.appIso (σ : Type) [Fintype σ] (X : AffineGroupScheme R)
    [SplitsOver S σ X] (A : Type u) [CommRing A] [Algebra S A] :
    ((baseChange R S).obj X).1.obj (CommAlg.of S A) ≃* (σ → Aˣ) :=
  (((fullSubcategoryInclusion _).mapIso (SplitsOver.iso S σ X)).app (CommAlg.of S A)).groupIsoToMulEquiv

def SplitsOver.appIso' (σ : Type) [Fintype σ] (X : AffineGroupScheme R)
    [SplitsOver S σ X] (A : Type u) [CommRing A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] :
    X.1.obj (CommAlg.of R A) ≃* (σ → Aˣ) :=
(baseChangeObjMulEquiv R S A X).symm.trans (SplitsOver.appIso S σ X (CommAlg.of S A))

class IsAlgebraicTorus {F : Type u} (K : outParam (Type u)) [Field F] [Field K]
  [Algebra F K] [Fact (Algebra.IsAlgebraic F K)] (σ : outParam Type) [Fintype σ]
  (X : AffineGroupScheme F) extends SplitsOver K σ X

variable (X : AffineGroupScheme R)

instance (σ : Type) [Fintype σ] [IsSplit σ X] (A : CommAlg R) :
  CommGroup (X.1.obj A ⟶ (𝔾ₘ R).1.obj A) :=
@MonoidHom.commGroup (X.1.obj A) Aˣ _ _

def CharGroup (σ : Type) [Fintype σ] [IsSplit σ X] := X ⟶ 𝔾ₘ R

instance (σ : Type) [Fintype σ] [IsSplit σ X] :
  CommGroup (CharGroup X σ) := sorry

open CategoryTheory

instance (σ : Type) [Fintype σ] [IsSplit σ X] :
  AddCommGroup (Additive (CharGroup X σ)) :=
Additive.addCommGroup

instance (σ : Type) [Fintype σ] [IsSplit σ X] :
  Module ℤ (Additive (CharGroup X σ)) :=
by infer_instance

instance (σ : Type) [Fintype σ] [IsSplit σ X] :
  Module.Finite ℤ (Additive (CharGroup X σ)) := sorry

@[simps] def 𝔾ₘZPow (n : ℤ) : CharGroup (𝔾ₘ R) PUnit where
  app := fun A => GroupCat.ofHom (zpowGroupHom n)
  naturality := fun A B f => by ext; exact (map_zpow _ _ n).symm

open BigOperators

variable (R)

@[simps] def splitTorusZPow {σ : Type} [Fintype σ] (f : σ → ℤ) : CharGroup (splitTorus R σ) σ where
  app := fun A => GroupCat.ofHom (∏ i in @Fintype.elems σ _,
    (zpowGroupHom (f i)).comp (Pi.evalMonoidHom _ i))
  naturality := fun A B f => by
    ext x
    refine' Units.ext _
    dsimp
    rw [GroupCat.coe_comp, GroupCat.coe_comp]
    simp only [GroupCat.coe_of, GroupCat.ofHom, Function.comp_apply, MonoidHom.finset_prod_apply,
      MonoidHom.coe_comp, Pi.evalMonoidHom_apply, MonoidHom.compLeft_apply, zpowGroupHom_apply,
      Units.coe_prod, map_prod, map_zpow]

lemma splitTorusZPow_surjective (σ : Type) [Fintype σ] :
  Function.Surjective (splitTorusZPow R (σ := σ)) := sorry

def additiveCharGroupBasis (σ : Type) [Fintype σ] :
    Basis σ ℤ (Additive (CharGroup (splitTorus R σ) σ)) where
  repr := (LinearEquiv.ofBijective ({
    toFun := fun f => Additive.ofMul (splitTorusZPow R f.2)
    map_add' := sorry
    map_smul' := sorry
  }) sorry).symm

instance (σ : Type) [Fintype σ] : Module.Free ℤ (Additive (CharGroup (splitTorus R σ) σ)) := sorry

instance outparammy2 (σ : Type) [Fintype σ] [IsSplit σ X] :
  Module.Free ℤ (Additive (CharGroup X σ)) := sorry

variable {R σ}
variable [Fintype σ]
section
variable [IsSplit σ X]

@[simp] lemma charGroup_one_app (A : CommAlg R) : (1 : CharGroup X σ).app A = 1 := sorry

@[simp] lemma charGroup_mul_app (f g : CharGroup X σ) (A : CommAlg R) :
  (f * g).app A = (f.app A * g.app A) := sorry

@[simp] lemma charGroup_inv_app (f : CharGroup X σ) (A : CommAlg R) :
  (f⁻¹).app A = (f.app A)⁻¹ := sorry

@[simp] lemma charGroup_div_app (f g : CharGroup X σ) (A : CommAlg R) :
  (f / g).app A = f.app A / g.app A := sorry

@[simp] lemma charGroup_prod_app (s : Finset σ) (f : σ → CharGroup X σ) (A : CommAlg R) :
  (∏ i in s, f i).app A = ∏ i in s, (f i).app A := sorry

@[simp] lemma charGroup_zpow_app (f : CharGroup X σ) (n : ℤ) (A : CommAlg R) :
  (f ^ n).app A = (f.app A) ^ n := sorry

@[simps] def mulEquivCharGroupOfIso {X Y : AffineGroupScheme R} [IsSplit σ X]
  [IsSplit σ Y] (F : X ≅ Y) :
    CharGroup X σ ≃* CharGroup Y σ :=
{   F.homCongr (Iso.refl _) with
  map_mul' := fun f g => by
    refine' NatTrans.ext _ _ _
    ext A x
    dsimp
    simp only [Category.comp_id]
    erw [NatTrans.comp_app]
    simp only [charGroup_mul_app]
    rfl }

end
section
variable {X}

def charGroupx [IsSplit σ X] (F : CharGroup X σ) :
  (X.1 ⋙ forget _).coreprXˣ := F.app _ (X.1 ⋙ forget _).coreprx

variable {S}
variable [SplitsOver S σ X]

def charGroupx2 (F : CharGroup ((baseChange R S).obj X) σ) :
  (S ⊗[R] (X.1 ⋙ forget _).coreprX)ˣ :=
Units.map (AlgHom.toMonoidHom' (baseChangeCoreprXIso R S X).hom)
  (charGroupx F)

def charGroupxRepr (F : CharGroup ((baseChange R S).obj X) σ) :
  FreeAddMonoid (S × (X.1 ⋙ forget _).coreprX) :=
Quotient.out (s := (addConGen (TensorProduct.Eqv _ _ _)).toSetoid) (charGroupx2 F).1

def mkCharGroupxRepr (F : CharGroup ((baseChange R S).obj X) σ) :
  (addConGen (TensorProduct.Eqv _ _ _)).mk' (charGroupxRepr F) = (charGroupx2 F).1 :=
Quotient.out_eq (s := (addConGen (TensorProduct.Eqv _ _ _)).toSetoid) _

variable (g : S ≃ₐ[R] S) (F : CharGroup ((baseChange R S).obj X) σ)
set_option trace.profiler true

-- why so slow to elaborate :(
def charGroupGalx (g : S ≃ₐ[R] S) (F : CharGroup ((baseChange R S).obj X) σ) :
  (S ⊗[R] (X.1 ⋙ forget _).coreprX)ˣ :=
Units.map (Algebra.TensorProduct.map (g⁻¹ : S ≃ₐ[R] S).toAlgHom
  (AlgHom.id R (X.1 ⋙ forget _).coreprX)).toMonoidHom' (charGroupx2 F)
/-⟨(addConGen (TensorProduct.Eqv _ _ _)).mk' <|
  FreeAddMonoid.map (Prod.map (g⁻¹ : S ≃ₐ[R] S) (@id (X.1 ⋙ forget _).coreprX)) (charGroupxRepr F),
  sorry, sorry, sorry⟩-/

def charGroupGal (g : S ≃ₐ[R] S) (F : CharGroup ((baseChange R S).obj X) σ) :
  CharGroup ((baseChange R S).obj X) σ where
    app := fun A => {
      toFun := ((baseChangeIso R S X).hom ≫ (coyonedaEquiv (X := CommAlg.of S (S ⊗[R]
        (X.1 ⋙ forget _).coreprX))
        (F := (𝔾ₘ S).1 ⋙ forget _)).symm (charGroupGalx g F)).app A
      map_one' := by
        refine' Units.ext _
        dsimp
        simp only [baseChangeIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.op_hom,
          FunctorToTypes.comp, coyoneda_map_app, Opposite.unop_op, Quiver.Hom.unop_op,
          charGroupGalx, AlgEquiv.toAlgHom_eq_coe, charGroupx2, CommAlg.coe_of, charGroupx, 𝔾ₘ_obj,
          𝔾ₘObj_obj, GroupCat.coe_of, Units.coe_map]

      map_mul' := sorry }
    naturality := sorry

#exit
def pointsGal (g : S ≃ₐ[R] S) (f : ((baseChange R S).obj X).1.obj (CommAlg.of S S)) :
  ((baseChange R S).obj X).1.obj (CommAlg.of S S) :=
((baseChangeIso R S X).app (CommAlg.of S S)).inv
  ((ugh R S _ S).symm (g.toAlgHom.comp (ugh R S _ S
  (((baseChangeIso R S X).app (CommAlg.of S S)).hom f))))

theorem charGroupGalPoints (g : S ≃ₐ[R] S) (f : CharGroup ((baseChange R S).obj X) σ) :


end
