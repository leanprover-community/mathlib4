import Mathlib.RingTheory.Coalgebra.Basic
set_option autoImplicit true
open TensorProduct Coalgebra

universe u v w u₁ v₁

/-- hm -/
structure CoalgHom (R : Type u) (A : Type v) (B : Type w) [CommSemiring R]
  [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [Coalgebra R A] [Coalgebra R B] extends A →ₗ[R] B where
  counit_comp : counit ∘ₗ toLinearMap = counit
  map_comp_comul : TensorProduct.map toLinearMap toLinearMap ∘ₗ comul = comul ∘ₗ toLinearMap

@[inherit_doc CoalgHom]
infixr:25 " →c " => CoalgHom _

@[inherit_doc]
notation:25 A " →c[" R "] " B => CoalgHom R A B

/-- `CoalgHomClass F R A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B`.  -/
class CoalgHomClass (F : Type*) (R A B : outParam Type*)
    [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
    [Coalgebra R A] [Coalgebra R B]
    [FunLike F A B] extends SemilinearMapClass F (RingHom.id R) A B : Prop where
  counit_comp : ∀ f : F, counit (R := R) (A := B) ∘ₗ LinearMapClass.linearMap f = counit (R := R) (A := A)
  map_comp_comul : ∀ f : F, TensorProduct.map (LinearMapClass.linearMap f) (LinearMapClass.linearMap f) ∘ₗ comul = comul ∘ₗ LinearMapClass.linearMap f

-- Porting note: `dangerousInstance` linter has become smarter about `outParam`s
-- attribute [nolint dangerousInstance] CoalgHomClass.toLinearMapClass

-- Porting note: simp can prove this
-- attribute [simp] CoalgHomClass.commutes

namespace CoalgHomClass

variable {R : Type*} {A : Type*} {B : Type*} [CommSemiring R]
  [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [Coalgebra R A] [Coalgebra R B] [FunLike F A B]

-- see Note [lower instance priority]
instance (priority := 100) linearMapClass [CoalgHomClass F R A B] : LinearMapClass F R A B := by
  infer_instance

-- Porting note: A new definition underlying a coercion `↑`.
/-- Turn an element of a type `F` satisfying `CoalgHomClass F α β` into an actual
`CoalgHom`. This is declared as the default coercion from `F` to `α →ₗ[R] β`. -/
@[coe]
def toCoalgHom {F : Type*} [FunLike F A B] [CoalgHomClass F R A B] (f : F) : A →c[R] B :=
  { LinearMapClass.linearMap f with
      toFun := f
      counit_comp := CoalgHomClass.counit_comp f
      map_comp_comul := CoalgHomClass.map_comp_comul f }

instance coeTC {F : Type*} [FunLike F A B] [CoalgHomClass F R A B] : CoeTC F (A →c[R] B) :=
  ⟨CoalgHomClass.toCoalgHom⟩

end CoalgHomClass

namespace CoalgHom

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

section AddCommMonoid

variable [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
  [AddCommMonoid C] [Module R C] [AddCommMonoid D] [Module R D]

variable [Coalgebra R A] [Coalgebra R B] [Coalgebra R C] [Coalgebra R D]


instance funLike : FunLike (A →c[R] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
    rcases g with ⟨⟨⟨_, _⟩, _⟩, _, _⟩
    congr

-- Porting note: This instance is moved.
instance coalgHomClass : CoalgHomClass (A →c[R] B) R A B where
  map_add := fun f => f.map_add'
  map_smulₛₗ := fun f => f.map_smul'
  counit_comp := fun f => f.counit_comp
  map_comp_comul := fun f => f.map_comp_comul

/-- See Note [custom simps projection] -/
def Simps.apply {R : Type u} {α : Type v} {β : Type w} [CommSemiring R]
    [AddCommMonoid α] [AddCommMonoid β]
    [Module R α] [Module R β] [Coalgebra R α] [Coalgebra R β] (f : α →c[R] β) : α → β := f

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [CoalgHomClass F R A B] (f : F) :
    ⇑(f : A →c[R] B) = f :=
  rfl

@[simp]
theorem toFun_eq_coe (f : A →c[R] B) : f.toFun = f :=
  rfl

attribute [coe] CoalgHom.toLinearMap

instance coeOutLinearMap : CoeOut (A →c[R] B) (A →ₗ[R] B) :=
  ⟨CoalgHom.toLinearMap⟩

-- Porting note: A new definition underlying a coercion `↑`.
@[coe]
def toAddMonoidHom' (f : A →c[R] B) : A →+ B := (f : A →ₗ[R] B)

instance coeOutAddMonoidHom : CoeOut (A →c[R] B) (A →+ B) :=
  ⟨CoalgHom.toAddMonoidHom'⟩

@[simp]
theorem coe_mk {f : A →ₗ[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A →c[R] B) : A → B) = f :=
  rfl

@[norm_cast]
theorem coe_mks {f : A → B} (h₁ h₂ h₃ h₄ ) : ⇑(⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A →c[R] B) = f :=
  rfl

-- Porting note: This theorem is new.
@[simp, norm_cast]
theorem coe_linearMap_mk {f : A →ₗ[R] B} (h h₁) : ((⟨f, h, h₁⟩ : A →c[R] B) : A →ₗ[R] B) = f :=
  rfl

-- make the coercion the simp-normal form
@[simp]
theorem toLinearMap_eq_coe (f : A →c[R] B) : f.toLinearMap = f :=
  rfl

@[simp, norm_cast]
theorem coe_toLinearMap (f : A →c[R] B) : ⇑(f : A →ₗ[R] B) = f :=
  rfl

@[simp, norm_cast]
theorem coe_toAddMonoidHom (f : A →c[R] B) : ⇑(f : A →+ B) = f :=
  rfl

variable (φ : A →c[R] B)

theorem coe_fn_injective : @Function.Injective (A →c[R] B) (A → B) (↑) :=
  DFunLike.coe_injective

theorem coe_fn_inj {φ₁ φ₂ : A →c[R] B} : (φ₁ : A → B) = φ₂ ↔ φ₁ = φ₂ :=
  DFunLike.coe_fn_eq

theorem coe_linearMap_injective : Function.Injective ((↑) : (A →c[R] B) → A →ₗ[R] B) := fun φ₁ φ₂ H =>
  coe_fn_injective <| show ((φ₁ : A →ₗ[R] B) : A → B) = ((φ₂ : A →ₗ[R] B) : A → B) from congr_arg _ H

theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (A →c[R] B) → A →+ B) :=
  LinearMap.toAddMonoidHom_injective.comp coe_linearMap_injective

protected theorem congr_fun {φ₁ φ₂ : A →c[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x :=
  DFunLike.congr_fun H x

protected theorem congr_arg (φ : A →c[R] B) {x y : A} (h : x = y) : φ x = φ y :=
  DFunLike.congr_arg φ h

@[ext]
theorem ext {φ₁ φ₂ : A →c[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
  DFunLike.ext _ _ H

theorem ext_iff {φ₁ φ₂ : A →c[R] B} : φ₁ = φ₂ ↔ ∀ x, φ₁ x = φ₂ x :=
  DFunLike.ext_iff

@[simp]
theorem mk_coe {f : A →c[R] B} (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : A →c[R] B) = f :=
  ext fun _ => rfl

#check LinearMap.congr_fun
@[simp]
theorem counit_comp_apply (x : A) : counit (φ x) = counit (R := R) x :=
  LinearMap.congr_fun φ.counit_comp _

@[simp]
theorem map_comp_comul_apply (x : A) :
    TensorProduct.map φ φ (comul x) = comul (R := R) (φ x) :=
  LinearMap.congr_fun φ.map_comp_comul _

protected theorem map_add (r s : A) : φ (r + s) = φ r + φ s :=
  map_add _ _ _

protected theorem map_zero : φ 0 = 0 :=
  map_zero _

-- @[simp] -- Porting note: simp can prove this
protected theorem map_smul (r : R) (x : A) : φ (r • x) = r • φ x :=
  map_smul _ _ _
/-
/-- If a `LinearMap` is `R`-linear, then it is an `CoalgHom`. -/
def mk' (f : A →ₗ[R] B) (h : ∀ (c : R) (x), f (c • x) = c • f x) : A →c[R] B :=
  { f with
    toFun := f
    commutes' := fun c => by simp only [Coalgebra.algebraMap_eq_smul_one, h, f.map_one] }
#align alg_hom.mk' CoalgHom.mk'

@[simp]
theorem coe_mk' (f : A →ₗ[R] B) (h : ∀ (c : R) (x), f (c • x) = c • f x) : ⇑(mk' f h) = f :=
  rfl
#align alg_hom.coe_mk' CoalgHom.coe_mk'-/

section

variable (R A)

/-- Identity map as an `CoalgHom`. -/
protected def id : A →c[R] A :=
{ LinearMap.id with
  counit_comp := by ext; rfl
  map_comp_comul := by simp only [map_id, LinearMap.id_comp, LinearMap.comp_id] }

@[simp]
theorem coe_id : ⇑(CoalgHom.id R A) = id :=
  rfl

@[simp]
theorem id_toLinearMap : (CoalgHom.id R A : A →ₗ[R] A) = LinearMap.id :=
  rfl

end

theorem id_apply (p : A) : CoalgHom.id R A p = p :=
  rfl

/-- Composition of algebra homeomorphisms. -/
def comp (φ₁ : B →c[R] C) (φ₂ : A →c[R] B) : A →c[R] C :=
  { φ₁.toLinearMap ∘ₗ φ₂ with
    counit_comp := by ext; simp only [LinearMap.coe_comp, coe_toLinearMap, Function.comp_apply,
      counit_comp_apply]
    map_comp_comul := by ext; simp only [map_comp, LinearMap.coe_comp, Function.comp_apply,
      map_comp_comul_apply, coe_toLinearMap]
       }

@[simp]
theorem coe_comp (φ₁ : B →c[R] C) (φ₂ : A →c[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ :=
  rfl

theorem comp_apply (φ₁ : B →c[R] C) (φ₂ : A →c[R] B) (p : A) : φ₁.comp φ₂ p = φ₁ (φ₂ p) :=
  rfl

@[simp] theorem comp_toLinearMap (φ₁ : B →c[R] C) (φ₂ : A →c[R] B) :
    (φ₁.comp φ₂ : A →ₗ[R] C) = (φ₁ : B →ₗ[R] C) ∘ₗ ↑φ₂ :=
  rfl

@[simp]
theorem comp_id : φ.comp (CoalgHom.id R A) = φ :=
  ext fun _x => rfl

@[simp]
theorem id_comp : (CoalgHom.id R B).comp φ = φ :=
  ext fun _x => rfl

theorem comp_assoc (φ₁ : C →c[R] D) (φ₂ : B →c[R] C) (φ₃ : A →c[R] B) :
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

theorem toLinearMap_injective :
    Function.Injective (toLinearMap : _ → A →ₗ[R] B) := fun _φ₁ _φ₂ h =>
  ext <| LinearMap.congr_fun h

@[simp]
theorem toLinearMap_id : toLinearMap (CoalgHom.id R A) = LinearMap.id :=
  LinearMap.ext fun _ => rfl

/-
/-- Promote a `LinearMap` to an `CoalgHom` by supplying proofs about the behavior on `1` and `*`. -/
@[simps]
def ofLinearMap (f : A →ₗ[R] B) (map_one : f 1 = 1) (map_mul : ∀ x y, f (x * y) = f x * f y) :
    A →c[R] B :=
  { f.toAddMonoidHom with
    toFun := f
    map_one' := map_one
    map_mul' := map_mul
    commutes' := fun c => by simp only [Coalgebra.algebraMap_eq_smul_one, f.map_smul, map_one] }
#align alg_hom.of_linear_map CoalgHom.ofLinearMap-/
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
#align alg_hom.to_linear_map_of_linear_map CoalgHom.toLinearMap_ofLinearMap

@[simp]
theorem ofLinearMap_id (map_one) (map_mul) :
    ofLinearMap LinearMap.id map_one map_mul = CoalgHom.id R A :=
  ext fun _ => rfl
#align alg_hom.of_linear_map_id CoalgHom.ofLinearMap_id
-/

theorem map_smul_of_tower {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A B R' R] (r : R')
    (x : A) : φ (r • x) = r • φ x :=
  φ.toLinearMap.map_smul_of_tower r x

/-theorem map_list_prod (s : List A) : φ s.prod = (s.map φ).prod :=
  φ.toLinearMap.map_list_prod s
#align alg_hom.map_list_prod CoalgHom.map_list_prod-/

@[simps (config := .lemmasOnly) toSemigroup_toMul_mul toOne_one]
instance End : Monoid (A →c[R] A) where
  mul := comp
  mul_assoc ϕ ψ χ := rfl
  one := CoalgHom.id R A
  one_mul ϕ := ext fun x => rfl
  mul_one ϕ := ext fun x => rfl

@[simp]
theorem one_apply (x : A) : (1 : A →c[R] A) x = x :=
  rfl

@[simp]
theorem mul_apply (φ ψ : A →c[R] A) (x : A) : (φ * ψ) x = φ (ψ x) :=
  rfl

/-theorem algebraMap_eq_apply (f : A →c[R] B) {y : R} {x : A} (h : algebraMap R A y = x) :
    algebraMap R B y = f x :=
  h ▸ (f.commutes _).symm
#align alg_hom.algebra_map_eq_apply CoalgHom.algebraMap_eq_apply-/

end AddCommMonoid
/-
section CommSemiring

variable [CommSemiring R] [CommSemiring A] [CommSemiring B]

variable [Coalgebra R A] [Coalgebra R B] (φ : A →c[R] B)

protected theorem map_multiset_prod (s : Multiset A) : φ s.prod = (s.map φ).prod :=
  map_multiset_prod _ _
#align alg_hom.map_multiset_prod CoalgHom.map_multiset_prod

protected theorem map_prod {ι : Type*} (f : ι → A) (s : Finset ι) :
    φ (∏ x in s, f x) = ∏ x in s, φ (f x) :=
  map_prod _ _ _
#align alg_hom.map_prod CoalgHom.map_prod

protected theorem map_finsupp_prod {α : Type*} [Zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A) :
    φ (f.prod g) = f.prod fun i a => φ (g i a) :=
  map_finsupp_prod _ _ _
#align alg_hom.map_finsupp_prod CoalgHom.map_finsupp_prod

end CommSemiring
-/
section AddCommGroup

variable [CommSemiring R] [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]

variable [Coalgebra R A] [Coalgebra R B] (φ : A →c[R] B)

protected theorem map_neg (x) : φ (-x) = -φ x :=
  map_neg _ _

protected theorem map_sub (x y) : φ (x - y) = φ x - φ y :=
  map_sub _ _ _

end AddCommGroup

end CoalgHom

namespace LinearMap
/-
variable {R S : Type*}

/-- Reinterpret a `LinearMap` as an `ℕ`-algebra homomorphism. -/
def toNatCoalgHom [AddCommMonoid R] [AddCommMonoid S] (f : R →ₗ[R] S) : R →c[ℕ] S :=
  { f with
    toFun := f
    commutes' := fun n => by simp }
#align ring_hom.to_nat_alg_hom LinearMap.toNatCoalgHom

/-- Reinterpret a `LinearMap` as a `ℤ`-algebra homomorphism. -/
def toIntCoalgHom [Ring R] [Ring S] [Coalgebra ℤ R] [Coalgebra ℤ S] (f : R →ₗ[R] S) : R →c[ℤ] S :=
  { f with commutes' := fun n => by simp }
#align ring_hom.to_int_alg_hom LinearMap.toIntCoalgHom

lemma toIntCoalgHom_injective [Ring R] [Ring S] [Coalgebra ℤ R] [Coalgebra ℤ S] :
    Function.Injective (LinearMap.toIntCoalgHom : (R →ₗ[R] S) → _) :=
  fun _ _ e ↦ DFunLike.ext _ _ (fun x ↦ DFunLike.congr_fun e x)

/-- Reinterpret a `LinearMap` as a `ℚ`-algebra homomorphism. This actually yields an equivalence,
see `LinearMap.equivRatCoalgHom`. -/
def toRatCoalgHom [Ring R] [Ring S] [Coalgebra ℚ R] [Coalgebra ℚ S] (f : R →ₗ[R] S) : R →c[ℚ] S :=
  { f with commutes' := f.map_rat_algebraMap }
#align ring_hom.to_rat_alg_hom LinearMap.toRatCoalgHom

@[simp]
theorem toRatCoalgHom_toLinearMap [Ring R] [Ring S] [Coalgebra ℚ R] [Coalgebra ℚ S] (f : R →ₗ[R] S) :
    ↑f.toRatCoalgHom = f :=
  LinearMap.ext fun _x => rfl
#align ring_hom.to_rat_alg_hom_to_ring_hom LinearMap.toRatCoalgHom_toLinearMap
-/
end LinearMap

section
/-
variable {R S : Type*}

@[simp]
theorem CoalgHom.toLinearMap_toRatCoalgHom [Ring R] [Ring S] [Coalgebra ℚ R] [Coalgebra ℚ S]
    (f : R →c[ℚ] S) : (f : R →ₗ[R] S).toRatCoalgHom = f :=
  CoalgHom.ext fun _x => rfl
#align alg_hom.to_ring_hom_to_rat_alg_hom CoalgHom.toLinearMap_toRatCoalgHom

/-- The equivalence between `LinearMap` and `ℚ`-algebra homomorphisms. -/
@[simps]
def LinearMap.equivRatCoalgHom [Ring R] [Ring S] [Coalgebra ℚ R] [Coalgebra ℚ S] : (R →ₗ[R] S) ≃ (R →c[ℚ] S)
    where
  toFun := LinearMap.toRatCoalgHom
  invFun := CoalgHom.toLinearMap
  left_inv f := LinearMap.toRatCoalgHom_toLinearMap f
  right_inv f := CoalgHom.toLinearMap_toRatCoalgHom f
#align ring_hom.equiv_rat_alg_hom LinearMap.equivRatCoalgHom
-/
end

namespace Coalgebra

variable (R : Type u) (A : Type v)

variable [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]
/-
/-- `CoalgebraMap` as an `CoalgHom`. -/
def ofId : R →c[R] A :=
  { algebraMap R A with commutes' := fun _ => rfl }
#align algebra.of_id Coalgebra.ofId
-/
variable {R}
/-
theorem ofId_apply (r) : ofId R A r = algebraMap R A r :=
  rfl
#align algebra.of_id_apply Coalgebra.ofId_apply

/-- This is a special case of a more general instance that we define in a later file. -/
instance subsingleton_id : Subsingleton (R →c[R] A) :=
  ⟨fun f g => CoalgHom.ext fun _ => (f.commutes _).trans (g.commutes _).symm⟩

/-- This ext lemma closes trivial subgoals create when chaining heterobasic ext lemmas. -/
@[ext high]
theorem ext_id (f g : R →c[R] A) : f = g := Subsingleton.elim _ _-/
/-
section MulDistribMulAction

instance : MulDistribMulAction (A →c[R] A) Aˣ where
  smul := fun f => Units.map f
  one_smul := fun x => by ext; rfl
  mul_smul := fun x y z => by ext; rfl
  smul_mul := fun x y z => by ext; exact x.map_mul _ _
  smul_one := fun x => by ext; exact x.map_one

end MulDistribMulAction-/
end Coalgebra
