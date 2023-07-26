import Mathlib.FieldTheory.Galois
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.Algebra.Category.GroupCat.Basic
import Mathlib.NumberTheory.AbelianLanglands.FGCommAlg
import Mathlib.Data.Polynomial.Laurent
import Mathlib.NumberTheory.AbelianLanglands.MvLaurentPolynomial
import Mathlib.CategoryTheory.Whiskering
open CategoryTheory
universe v u
noncomputable section
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (σ : Type)

local notation:9000 R "[T;T⁻¹]" => LaurentPolynomial R
local notation:9000 R "["σ";"σ"⁻¹]" => MvLaurentPolynomial σ R

def AffineGroupScheme :=
FullSubcategory fun F : CommAlg.{u, u} R ⥤ GroupCat => (F ⋙ forget _).Corepresentable

instance : Category (AffineGroupScheme R) := by
  unfold AffineGroupScheme; infer_instance

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

def 𝔾ₘ : AffineGroupScheme R where
  obj := 𝔾ₘObj R
  property := ⟨Opposite.op (CommAlg.of R R[T;T⁻¹]),
    (𝔾ₘObjCompForgetNatIso R).inv, by infer_instance⟩

end

@[simps] def splitTorusObj (σ : Type _) [Fintype σ]  : CommAlg R ⥤ GroupCat where
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

def splitTorus (σ : Type) [Fintype σ] : AffineGroupScheme R where
  obj := splitTorusObj R σ
  property := ⟨Opposite.op (CommAlg.of R R[σ;σ⁻¹]),
    (splitTorusObjCompForgetNatIso R σ).inv, by infer_instance⟩

def baseChange : AffineGroupScheme R ⥤ AffineGroupScheme S :=
FullSubcategory.lift _
  (fullSubcategoryInclusion _ ⋙ (whiskeringLeft _ _ _).obj (CommAlg.restrictScalars R S)) (by
    intro G
    constructor
    rcases G with ⟨G, X, f, hf⟩
    use Opposite.op (CommAlg.of S (TensorProduct R S X.unop))
    sorry)

variable {R}

class SplitsOver (σ : Type) [Fintype σ] (X : AffineGroupScheme R) : Prop where
  out : Nonempty ((baseChange R S).obj X ≅ splitTorus S σ)

class AlgebraicTorus {F : Type u} (K : Type u) [Field F] [Field K]
    [Algebra F K] [IsAlgClosed K] (σ : Type) [Fintype σ]
    (X : AffineGroupScheme F) extends SplitsOver K σ X
