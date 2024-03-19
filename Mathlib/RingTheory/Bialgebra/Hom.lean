import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.Coalgebra.Hom

set_option autoImplicit true
open TensorProduct Bialgebra

universe u v w u₁ v₁

/-- hm -/
structure BialgHom (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A]
  [Semiring B] [Bialgebra R A] [Bialgebra R B] extends A →c[R] B where
  map_mul' : ∀ x y, toFun (x * y) = toFun x * toFun y
  map_one' : toFun 1 = 1
  commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r

attribute [coe] BialgHom.toCoalgHom

@[inherit_doc BialgHom]
infixr:25 " →b " => BialgHom _

@[inherit_doc]
notation:25 A " →b[" R "] " B => BialgHom R A B

/-- `BialgHomClass F R A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B`.  -/
class BialgHomClass (F : Type*) (R A B : outParam Type*)
    [CommSemiring R] [Semiring A] [Semiring B]
    [Bialgebra R A] [Bialgebra R B]
    [FunLike F A B] extends SemilinearMapClass F (RingHom.id R) A B,
       AlgHomClass F R A B, CoalgHomClass F R A B : Prop

-- Porting note: `dangerousInstance` linter has become smarter about `outParam`s
-- attribute [nolint dangerousInstance] BialgHomClass.toLinearMapClass

-- Porting note: simp can prove this
-- attribute [simp] BialgHomClass.commutes

namespace BialgHomClass

variable {R : Type*} {A : Type*} {B : Type*} [CommSemiring R]
  [Semiring A] [Semiring B] [Bialgebra R A] [Bialgebra R B] [FunLike F A B]

-- see Note [lower instance priority]
instance (priority := 100) linearMapClass [BialgHomClass F R A B] : LinearMapClass F R A B := by
  infer_instance

instance (priority := 100) algHomClass [BialgHomClass F R A B] : AlgHomClass F R A B := by
  infer_instance

instance (priority := 100) coalgHomClass [BialgHomClass F R A B] : CoalgHomClass F R A B := by
  infer_instance

-- Porting note: A new definition underlying a coercion `↑`.
/-- Turn an element of a type `F` satisfying `BialgHomClass F α β` into an actual
`BialgHom`. This is declared as the default coercion from `F` to `α →ₗ[R] β`. -/
@[coe]
def toBialgHom {F : Type*} [FunLike F A B] [BialgHomClass F R A B] (f : F) : A →b[R] B :=
  { LinearMapClass.linearMap f, AlgHomClass.toAlgHom f, CoalgHomClass.toCoalgHom f with }

instance coeTC {F : Type*} [FunLike F A B] [BialgHomClass F R A B] : CoeTC F (A →b[R] B) :=
  ⟨BialgHomClass.toBialgHom⟩

end BialgHomClass

namespace BialgHom

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

section Semiring

variable [CommSemiring R] [Semiring A] [Semiring B]
  [Semiring C] [Semiring D]

variable [Bialgebra R A] [Bialgebra R B] [Bialgebra R C] [Bialgebra R D]

instance funLike : FunLike (A →b[R] B) A B where
  coe f := f.toFun
  coe_injective' f g h := sorry

-- Porting note: This instance is moved.
instance bialgHomClass : BialgHomClass (A →b[R] B) R A B where
  map_zero := fun f => map_zero f.toLinearMap
  map_add := fun f => f.map_add'
  map_smulₛₗ := fun f => f.map_smul'
  map_one := fun f => f.map_one'
  map_mul := fun f => f.map_mul'
  commutes := fun f => f.commutes'
  counit_comp := fun f => f.counit_comp
  map_comp_comul := fun f => f.map_comp_comul

/-- See Note [custom simps projection] -/
def Simps.apply {R : Type u} {α : Type v} {β : Type w} [CommSemiring R]
    [Semiring α] [Semiring β] [Bialgebra R α] [Bialgebra R β] (f : α →c[R] β) : α → β := f

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [BialgHomClass F R A B] (f : F) :
    ⇑(f : A →b[R] B) = f :=
  rfl

@[simp]
theorem toFun_eq_coe (f : A →b[R] B) : f.toFun = f :=
  rfl

instance coeOutLinearMap : CoeOut (A →b[R] B) (A →ₗ[R] B) :=
  ⟨fun f => f.toCoalgHom.toLinearMap⟩

instance coeOutCoalgHom : CoeOut (A →b[R] B) (A →c[R] B) :=
  ⟨BialgHom.toCoalgHom⟩
-- Porting note: A new definition underlying a coercion `↑`.
@[coe]
def toAddMonoidHom' (f : A →b[R] B) : A →+ B := (f : A →ₗ[R] B)

instance coeOutAddMonoidHom : CoeOut (A →b[R] B) (A →+ B) :=
  ⟨BialgHom.toAddMonoidHom'⟩

@[simp]
theorem coe_mk {f : A →c[R] B} (h₀ h₁ h₂) :
    ((⟨f, h₀, h₁, h₂⟩ : A →b[R] B) : A → B) = f :=
  rfl

lemma commutes (f : A →b[R] B) (r : R) :
    f (algebraMap R A r) = algebraMap R B r := f.commutes' r

@[simps] def toAlgHom (f : A →b[R] B) : A →ₐ[R] B where
  toFun := f
  map_one' := map_one f
  map_mul' := map_mul f
  map_zero' := map_zero f
  map_add' := map_add f
  commutes' := commutes f

instance coeOutAlgHom : CoeOut (A →b[R] B) (A →ₐ[R] B) :=
  ⟨BialgHom.toAlgHom⟩

/-@[norm_cast]
theorem coe_mks {f : A → B} (h₁ h₂ h₃ h₄ ) : ⇑(⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A →b[R] B) = f :=
  rfl-/

/--- Porting note: This theorem is new.
@[simp, norm_cast]
theorem coe_linearMap_mk {f : A →ₗ[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A →b[R] B) : A →ₗ[R] B) = f :=
  rfl-/

-- make the coercion the simp-normal form
@[simp]
theorem toLinearMap_eq_coe (f : A →b[R] B) : f.toLinearMap = f :=
  rfl

@[simp, norm_cast]
theorem coe_toLinearMap (f : A →b[R] B) : ⇑(f : A →ₗ[R] B) = f :=
  rfl

@[simp, norm_cast]
theorem coe_toAlgHom (f : A →b[R] B) : ⇑(f : A →ₐ[R] B) = f :=
rfl

@[simp, norm_cast]
theorem coe_toCoalgHom (f : A →b[R] B) : ⇑(f : A →c[R] B) = f :=
rfl

@[simp, norm_cast]
theorem coe_toAddMonoidHom (f : A →b[R] B) : ⇑(f : A →+ B) = f :=
  rfl

variable (φ : A →b[R] B)

theorem coe_fn_injective : @Function.Injective (A →b[R] B) (A → B) (↑) :=
  DFunLike.coe_injective

theorem coe_fn_inj {φ₁ φ₂ : A →b[R] B} : (φ₁ : A → B) = φ₂ ↔ φ₁ = φ₂ :=
  DFunLike.coe_fn_eq

theorem coe_algHom_injective : Function.Injective ((↑) : (A →b[R] B) → A →ₐ[R] B) := fun φ₁ φ₂ H =>
  coe_fn_injective <| show ((φ₁ : A →ₐ[R] B) : A → B) = ((φ₂ : A →ₐ[R] B) : A → B) from
    congr_arg _ H

theorem coe_linearMap_injective : Function.Injective ((↑) : (A →b[R] B) → A →ₗ[R] B) := fun φ₁ φ₂ H =>
  coe_fn_injective <| show ((φ₁ : A →ₗ[R] B) : A → B) = ((φ₂ : A →ₗ[R] B) : A → B) from congr_arg _ H

theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (A →b[R] B) → A →+ B) :=
  LinearMap.toAddMonoidHom_injective.comp coe_linearMap_injective

protected theorem congr_fun {φ₁ φ₂ : A →b[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x :=
  DFunLike.congr_fun H x

protected theorem congr_arg (φ : A →b[R] B) {x y : A} (h : x = y) : φ x = φ y :=
  DFunLike.congr_arg φ h

@[ext]
theorem ext {φ₁ φ₂ : A →b[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
  DFunLike.ext _ _ H

theorem ext_iff {φ₁ φ₂ : A →b[R] B} : φ₁ = φ₂ ↔ ∀ x, φ₁ x = φ₂ x :=
  DFunLike.ext_iff

/-@[simp]
theorem mk_coe {f : A →b[R] B} (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A →b[R] B) = f :=
  ext fun _ => rfl-/

@[simp]
theorem counit_comp_apply (x : A) : Coalgebra.counit (φ x) = Coalgebra.counit (R := R) x :=
  LinearMap.congr_fun φ.counit_comp _

@[simp]
theorem map_comp_comul_apply (x : A) :
    TensorProduct.map φ.toLinearMap φ.toLinearMap (Coalgebra.comul x)
      = Coalgebra.comul (R := R) (φ x) :=
  LinearMap.congr_fun φ.map_comp_comul _

protected theorem map_add (r s : A) : φ (r + s) = φ r + φ s :=
  map_add _ _ _

protected theorem map_zero : φ 0 = 0 :=
  map_zero _

-- @[simp] -- Porting note: simp can prove this
protected theorem map_smul (r : R) (x : A) : φ (r • x) = r • φ x :=
  map_smul _ _ _

protected theorem map_mul (r s : A) : φ (r * s) = φ r * φ s :=
  map_mul _ _ _

protected theorem map_one : φ 1 = 1 :=
  map_one _

def mk' (f : A →c[R] B) (h1 : f 1 = 1)
    (hmul : (LinearMap.mul R A).compr₂ f = (LinearMap.mul R B).compl₁₂ f f)
    (hcomm : ∀ r, f (algebraMap R A r) = algebraMap R B r) :
    A →b[R] B :=
  { f with
    map_one' := h1
    map_mul' := LinearMap.ext_iff₂.1 hmul
    commutes' := hcomm }

@[simp]
theorem coe_mk' (f : A →c[R] B) (h1 : f 1 = 1)
    (hmul : (LinearMap.mul R A).compr₂ f = (LinearMap.mul R B).compl₁₂ f f)
    (hcomm : ∀ r, f (algebraMap R A r) = algebraMap R B r) : ⇑(mk' f h1 hmul hcomm) = f :=
  rfl

section

variable (R A)

/-- Identity map as an `BialgHom`. -/
protected def id : A →b[R] A :=
{ LinearMap.id, AlgHom.id _ _, CoalgHom.id _ _ with }

@[simp]
theorem coe_id : ⇑(BialgHom.id R A) = id :=
  rfl

@[simp]
theorem id_toLinearMap : (BialgHom.id R A : A →ₗ[R] A) = LinearMap.id :=
  rfl

end

theorem id_apply (p : A) : BialgHom.id R A p = p :=
  rfl

/-- Composition of algebra homeomorphisms. -/
def comp (φ₁ : B →b[R] C) (φ₂ : A →b[R] B) : A →b[R] C :=
  { φ₁.toLinearMap ∘ₗ φ₂.toLinearMap, φ₁.toAlgHom.comp φ₂.toAlgHom,
      φ₁.toCoalgHom.comp φ₂.toCoalgHom with }

@[simp]
theorem coe_comp (φ₁ : B →b[R] C) (φ₂ : A →b[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ :=
  rfl

theorem comp_apply (φ₁ : B →b[R] C) (φ₂ : A →b[R] B) (p : A) : φ₁.comp φ₂ p = φ₁ (φ₂ p) :=
  rfl

@[simp] theorem comp_toLinearMap (φ₁ : B →b[R] C) (φ₂ : A →b[R] B) :
    (φ₁.comp φ₂ : A →ₗ[R] C) = (φ₁ : B →ₗ[R] C) ∘ₗ ↑φ₂ :=
  rfl

@[simp]
theorem comp_id : φ.comp (BialgHom.id R A) = φ :=
  ext fun _x => rfl

@[simp]
theorem id_comp : (BialgHom.id R B).comp φ = φ :=
  ext fun _x => rfl

theorem comp_assoc (φ₁ : C →b[R] D) (φ₂ : B →b[R] C) (φ₃ : A →b[R] B) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
  ext fun _x => rfl

/-
/-- R-Alg ⥤ R-Mod -/
def toLinearMap : A →ₗ[R] B where
  toFun := φ
  map_add' := map_add _
  map_smul' := map_smul _-/

@[simp]
theorem toLinearMap_apply (p : A) : φ.toLinearMap p = φ p :=
  rfl
/-
theorem toLinearMap_injective :
    Function.Injective (toLinearMap : _ → A →ₗ[R] B) := fun _φ₁ _φ₂ h =>
  ext <| LinearMap.congr_fun h

@[simp]
theorem toLinearMap_id : toLinearMap (BialgHom.id R A) = LinearMap.id :=
  LinearMap.ext fun _ => rfl-/

/-
/-- Promote a `LinearMap` to an `BialgHom` by supplying proofs about the behavior on `1` and `*`. -/
@[simps]
def ofLinearMap (f : A →ₗ[R] B) (map_one : f 1 = 1) (map_mul : ∀ x y, f (x * y) = f x * f y) :
    A →b[R] B :=
  { f.toAddMonoidHom with
    toFun := f
    map_one' := map_one
    map_mul' := map_mul
    commutes' := fun c => by simp only [Bialgebra.algebraMap_eq_smul_one, f.map_smul, map_one] }
#align alg_hom.of_linear_map BialgHom.ofLinearMap-/
/-
@[simp]
theorem ofLinearMap_toLinearMap (map_one) (map_mul) :
    ofLinearMap φ.toLinearMap map_one map_mul = φ := by
  ext
  rfl

@[simp]
theorem toLinearMap_ofLinearMap (f : A →ₗ[R] B) (map_one) (map_mul) :
    toLinearMap (ofLinearMap f map_one map_mul) = f := by
  ext
  rfl
#align alg_hom.to_linear_map_of_linear_map BialgHom.toLinearMap_ofLinearMap

@[simp]
theorem ofLinearMap_id (map_one) (map_mul) :
    ofLinearMap LinearMap.id map_one map_mul = BialgHom.id R A :=
  ext fun _ => rfl
#align alg_hom.of_linear_map_id BialgHom.ofLinearMap_id
-/

theorem map_smul_of_tower {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A B R' R] (r : R')
    (x : A) : φ (r • x) = r • φ x :=
  φ.toLinearMap.map_smul_of_tower r x

/-theorem map_list_prod (s : List A) : φ s.prod = (s.map φ).prod :=
  φ.toLinearMap.map_list_prod s
#align alg_hom.map_list_prod BialgHom.map_list_prod-/

end Semiring
namespace Bialgebra

variable (R A)
variable [CommSemiring R] [Semiring A] [Algebra R A] [Bialgebra R A]

/-- The monoid of endomorphisms. -/
protected def End := A →b[R] A

namespace End

variable {R A}

instance : Monoid (Bialgebra.End R A) where
  mul := BialgHom.comp
  one := BialgHom.id R A
  mul_assoc _ _ _ := BialgHom.comp_assoc _ _ _
  mul_one := BialgHom.comp_id
  one_mul := BialgHom.id_comp

instance : Inhabited (Bialgebra.End R A) := ⟨1⟩

instance : FunLike (Bialgebra.End R A) A A :=
  inferInstanceAs (FunLike (A →b[R] A) A A)

instance : BialgHomClass (Bialgebra.End R A) R A A :=
  inferInstanceAs (BialgHomClass (A →b[R] A) R A A)

end End

@[simp]
theorem coe_one : ((1 : Bialgebra.End R A) : A → A) = id := rfl

@[simp]
theorem coe_mul (f g) : ((f * g : Bialgebra.End R A) : A → A) = f ∘ g := rfl

/-theorem algebraMap_eq_apply (f : A →b[R] B) {y : R} {x : A} (h : algebraMap R A y = x) :
    algebraMap R B y = f x :=
  h ▸ (f.commutes _).symm
#align alg_hom.algebra_map_eq_apply BialgHom.algebraMap_eq_apply-/

end Bialgebra
/-
section CommSemiring

variable [CommSemiring R] [CommSemiring A] [CommSemiring B]

variable [Bialgebra R A] [Bialgebra R B] (φ : A →b[R] B)

protected theorem map_multiset_prod (s : Multiset A) : φ s.prod = (s.map φ).prod :=
  map_multiset_prod _ _
#align alg_hom.map_multiset_prod BialgHom.map_multiset_prod

protected theorem map_prod {ι : Type*} (f : ι → A) (s : Finset ι) :
    φ (∏ x in s, f x) = ∏ x in s, φ (f x) :=
  map_prod _ _ _
#align alg_hom.map_prod BialgHom.map_prod

protected theorem map_finsupp_prod {α : Type*} [Zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A) :
    φ (f.prod g) = f.prod fun i a => φ (g i a) :=
  map_finsupp_prod _ _ _
#align alg_hom.map_finsupp_prod BialgHom.map_finsupp_prod

end CommSemiring
-/
section Ring

variable [CommSemiring R] [Ring A] [Ring B]

variable [Bialgebra R A] [Bialgebra R B] (φ : A →b[R] B)

protected theorem map_neg (x) : φ (-x) = -φ x :=
  map_neg _ _

protected theorem map_sub (x y) : φ (x - y) = φ x - φ y :=
  map_sub _ _ _

end Ring
end BialgHom
