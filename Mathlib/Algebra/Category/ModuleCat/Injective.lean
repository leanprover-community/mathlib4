import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.LinearAlgebra.FinsuppVectorSpace
import Mathlib.Data.Finsupp.Basic
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.GroupTheory.Divisible
import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Algebra.Category.GroupCat.Injective

/-!
# The category of `R`-modules has enough injectives.
-/

universe v u

open CategoryTheory

open CategoryTheory.Limits

open LinearMap

open ModuleCat

open scoped Module

set_option maxHeartbeats 0

section ModuleHom

variable {R M A : Type _} [Ring R] [AddCommGroup M] [AddCommGroup A] [Module R M]

--how does this not exist yet?
instance ModuleHom₁ : Module R (A →+ M) where
  add_smul r s f := by ext x; simp [add_smul]
  zero_smul := by simp

def smul' (r : R) (f : R →+ A) : R →+ A where
  toFun := λ s => f (s*r)
  map_zero' := by simp
  map_add' := by simp [add_mul]

instance smul : SMul R (R →+ A) := ⟨smul'⟩

@[simp]
lemma smul_def (a b : R) (f : R →+ A) : (a • f) b = f (b*a) := rfl

instance ModuleHom₂ : Module R (R →+ A) where
  one_smul b := by ext; simp
  mul_smul a b f := by ext x; simp [mul_assoc]
  add_smul r s f := by ext x; simp [mul_add, map_add]
  zero_smul f := by ext x; simp
  smul_zero f := by ext x; simp
  smul_add a f g := by ext; simp [map_add]

end ModuleHom

#check Module.injective_iff_injective_object

namespace ModuleCat

-- universe stuff is very confusing, someone please help
variable (R : Type _) [Ring R] (M : ModuleCat.{_} R)

/-
Want to show R-mod has enough injectives. Let M be an R-Module
Let I(M) be a product of I₀ := Hom_Ab(M, ℚ ⧸ ℤ), indexed by Hom_R(M, I₀).
Then I is injective
There is a map e_M : M → I(M) which is injective
-/

-- ℚ ⧸ ℤ, in Ab:
#check Ab
def ι : ℤ →+ ℚ := Int.castAddHom ℚ

--There's no way I should have to do this manually, right?
def ZinQ : AddSubgroup ℚ where
carrier := Set.image ι ⊤
add_mem' := by rintro a b ⟨a, -, rfl⟩ ⟨b, -, rfl⟩; use a + b; simp
zero_mem' := by use 0; simp
neg_mem' := by rintro a ⟨a, -, rfl⟩; use -a; simp

-- ℚ ⧸ ℤ injective in Ab
#check QuotientAddGroup.divisibleBy
#check AddGroup.divisibleByIntOfDivisibleByNat
#check divisibleByIntOfCharZero
#check AddCommGroupCat.injective_of_divisible

instance DivisibleQ' : DivisibleBy ℚ ℕ := AddGroup.divisibleByNatOfDivisibleByInt ℚ
noncomputable instance DivisibleQmodZ' : DivisibleBy (ℚ ⧸ ZinQ) ℕ := QuotientAddGroup.divisibleBy _
noncomputable instance DivisibleQmodZ : DivisibleBy (ℚ ⧸ ZinQ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _


def QmodZ : Ab := ⟨ℚ ⧸ ZinQ, inferInstance⟩
instance injectiveQmodZ' : Injective (⟨ℚ ⧸ ZinQ, inferInstance⟩ : Ab) := inferInstance
instance injectiveQmodZ : Injective QmodZ := injectiveQmodZ'

--Proof that I₀ is injective
--need adjunction (Ab → Mod R)
instance ModuleHom₃ {A : Ab} : Module R $ (AddCommGroupCat.of R) ⟶ A := ModuleHom₂

#check forget₂ (ModuleCat R) Ab
def raise_obj (R : Type _) [Ring R] (A : Ab) : ModuleCat R := ⟨(AddCommGroupCat.of R) ⟶ A⟩
def raise_map (R : Type _) [Ring R] {A B : Type _} [AddCommGroup A] [AddCommGroup B]
  (f : A →+ B) : (R →+ A) →+[R] (R →+ B) where
    toFun g := AddMonoidHom.comp f g
    map_smul' m g := by ext; simp
    map_zero' := by simp
    map_add' g h := by ext; simp

def raise_map' {X Y : Ab} (f : X ⟶ Y) : (raise_obj R X) ⟶ (raise_obj R Y) where
  toFun g := AddMonoidHom.comp f g
  map_smul' m g := by aesop
  map_add' g h := sorry

def rightAdj : Ab ⥤ ModuleCat R where
  obj := raise_obj R
  map := raise_map' R

def core : Adjunction.CoreHomEquiv (forget₂ (ModuleCat R) Ab) (rightAdj R) := sorry

lemma adj : (forget₂ (ModuleCat R) Ab) ⊣ (rightAdj R) := Adjunction.mkOfHomEquiv (core R)

-- I₀ Hom_Ab(M, ℚ / ℤ), in R-Mod
def I₀ (R : Type _) [Ring R] : ModuleCat R := ⟨(AddCommGroupCat.of R) ⟶ QmodZ⟩
def I₀' : ModuleCat R := (rightAdj R).obj QmodZ
lemma I_def : (I₀ R) = (I₀' R).carrier := sorry

instance InjectiveI₀ : Injective (I₀' R) := Injective.injective_of_adjoint (adj R) QmodZ

--Proof that Π I₀ is injective:
def c : (M ⟶ (I₀' R)) → ModuleCat R := λ _ => (I₀' R)
instance c_Prod : HasProduct (c R M) := inferInstance
instance c_obj_insjective (f : M ⟶ (I₀' R)) : Injective ((c R M) f) := InjectiveI₀ R
example : Injective (∏ (c R M)) := inferInstance

#check Injective.instInjectivePiObj


--definition of the map M → I(M)
def f_ps (α : M ⟶ (I₀' R)) : M ⟶ I₀' R := sorry
def f_ps' (α : M ⟶ (I₀' R)) : M ⟶ (c R M f) := sorry

def f : M ⟶ ∏ (c R M) := sorry
instance f_mono : Mono (f R M) := sorry

#check Pi.lift

--injectivity of the map


instance moduleCat_enoughInjectives : EnoughInjectives (ModuleCat R) where
presentation M := ⟨{J := ∏ (c R M), f := f R M}⟩

end ModuleCat
