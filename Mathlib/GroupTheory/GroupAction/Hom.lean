/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Antoine Chambert-Loir

! This file was ported from Lean 3 source module algebra.hom.group_action
! leanprover-community/mathlib commit e7bab9a85e92cf46c02cb4725a7be2f04691e3a7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

import Mathlib.Algebra.GroupRingAction.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Equiv

/-!
# Equivariant homomorphisms

## Main definitions

* `MulActionHom φ X Y`, the type of equivariant functions from `X` to `Y`,
  where `φ : M → N` is a map, `M` acting on the type `X` and `N` acting on the type of `Y`.
* `LinearMap φ A B`,
  the type of equivariant additive monoid homomorphisms from `A` to `B`,
  where `φ : M → N` is a morphism of monoids,
  `M` acting on the additive monoid `A` and `N` acting on the additive monoid of `B`
* `SMulSemiringHom φ R S`, the type of equivariant ring homomorphisms
  from `R` to `S`, where `φ : M → N` is a morphism of monoids,
  `M` acting on the ring `R` and `N` acting on the ring `S`.

The above types have corresponding classes:
* `MulActionSemiHomClass F φ X Y` states that `F` is a type of bundled `X → Y` homs
  which are `φ`-equivariant
* `SemilinearMapClass F φ A B` states that `F` is a type of bundled `A → B` homs
  preserving the additive monoid structure and `φ`-equivariant
* `SMulSemiringSemiHomClass F φ R S` states that `F` is a type of bundled `R → S` homs
  preserving the ring structure and `φ`-equivariant

* When `M = N` and `φ = MonoidHom.id M`, we provide classes `MulActionHomClass`, `LinearMapClass`and `SMulSemiringHomClass`.

## Notations

* `X →ₑ[φ] Y` is `MulActionHom φ X Y`.
* `A →ₑ+[φ] B` is `LinearMap φ A B`.
* `R →ₑ+*[φ] S` is `MulSemiringActionHom φ R S`.

* When `M = N` and `φ = MonoidHom.id M`, we provide the notation `X →[M] Y`
-/

section CompTriple

/-- Class of composing triples -/
class CompTriple  {M N P : Type _} (φ : M → N) (ψ : N → P) (χ : M → P) : Prop where
  /-- The maps form a commuting triangle -/
  comp_eq : ψ.comp φ = χ

attribute [simp] CompTriple.comp_eq

namespace CompTriple

lemma comp_id {N P : Type _} {ψ : N → P} :
    CompTriple (@id N) ψ ψ := {comp_eq := rfl}

lemma id_comp {M N : Type _} {φ : M → N} :
    CompTriple φ (@id N) φ := {comp_eq := rfl}

lemma comp {M N P : Type _}
    {φ : M → N} {ψ : N → P} :
  CompTriple φ ψ  (ψ.comp φ) := {comp_eq := rfl}

lemma comp_inv {M N : Type _} {φ : M → N} {ψ : N → M} (h : Function.RightInverse φ ψ):
    CompTriple φ ψ id := {comp_eq := h.id }

lemma apply {M N P : Type _}
    {φ : M → N} {ψ : N → P} {χ : M → P} (h : CompTriple φ ψ χ) (x : M) :
  ψ (φ x) = χ x := by
  rw [← h.comp_eq, Function.comp_apply]

end CompTriple

section CompTripleClass

/-- Class of composing triples -/
class CompTripleClass (F : Type _) {M N P : outParam (Type _)}
    (φ : outParam (M → N)) (ψ : outParam (N → P)) (χ : outParam (M → P)) : Prop where
  /-- The maps form a commuting triangle -/
  comp_eq : ψ.comp φ = χ

attribute [simp] CompTripleClass.comp_eq

namespace CompTripleClass

lemma comp_id (F : Type _) {N P : outParam (Type _)} (ψ : outParam (N → P)) :
    CompTripleClass F (@id N) ψ ψ := {comp_eq := rfl}

lemma id_comp (F : Type _) {M N : outParam (Type _)} (φ : outParam (M → N)) :
    CompTripleClass F φ (@id N) φ := {comp_eq := rfl}

lemma comp (F : Type _) {M N P : outParam (Type _)}
    (φ : outParam (M → N)) (ψ : outParam (N → P)) :
    CompTripleClass F φ ψ (ψ.comp φ) := {comp_eq := rfl}

lemma comp_inv {M N : outParam (Type _)} {φ : outParam (M → N)} {ψ :outParam (N → M)}
    (h : Function.RightInverse ↑φ ↑ψ) :
    CompTriple φ ψ id := {comp_eq := h.id }

lemma apply {M N P : outParam (Type _)}
    {φ : outParam (M → N)} {ψ : outParam (N → P)} {χ : outParam (M → P)}
    (h : CompTriple φ ψ χ) (x : M) :
    ψ (φ x) = χ x := by
  rw [← h.comp_eq, Function.comp_apply]

@[simp]
theorem comp_assoc {M N P Q : outParam (Type _)}
    {φ₁ : outParam (M → N)} {φ₂ : outParam (N → P)} {φ₁₂ : outParam (M → P)}
    (κ : CompTriple φ₁ φ₂ φ₁₂)
    {φ₃ : outParam (P → Q)} {φ₂₃ : outParam (N → Q)} (κ' : CompTriple φ₂ φ₃ φ₂₃)
    {φ₁₂₃ : outParam (M → Q)} :
    CompTriple φ₁ φ₂₃ φ₁₂₃ ↔ CompTriple φ₁₂ φ₃ φ₁₂₃ := by
  constructor
  all_goals {
    rintro ⟨h⟩
    exact ⟨ by simp only [← κ.comp_eq, ← h, ← κ'.comp_eq]; rfl ⟩ }

end CompTripleClass

end CompTripleClass

assert_not_exists Submonoid

section MulActionHom

variable {M : Type _} {N : Type _} {P : Type _}
variable (φ : M → N) (ψ : N → P) (χ : M → P)
variable (X : Type _) [SMul M X]
variable (Y : Type _) [SMul N Y]
variable (Z : Type _) [SMul P Z]


/-- Equivariant functions. -/
-- Porting note: This linter does not exist yet
-- @[nolint has_nonempty_instance]
structure MulActionHom where
  /-- The underlying function. -/
  toFun : X → Y
  /-- The proposition that the function commutes with the actions. -/
  map_smul' : ∀ (m : M) (x : X), toFun (m • x) = (φ m) • toFun x

/- Porting note: local notation given a name, conflict with Algebra.Hom.GroupAction
 see https://github.com/leanprover/lean4/issues/2000 -/
@[inherit_doc]
notation:25 (name := «MulActionHomLocal≺») X " →ₑ[" φ:25 "] " Y:0 => MulActionHom φ X Y

/-
/-- Equivariant functions -/
abbrev MulActionHom (M : Type _) (X Y : Type _) [SMul M X] [SMul M Y] := MulActionHom (@id M) X Y
-/

@[inherit_doc]
notation:25 (name := «MulActionHomIdLocal≺») X " →[" M:25 "] " Y:0 => MulActionHom (@id M) X Y

/-- `MulActionSemiHomClass F φ X Y` states that `F` is a type of morphisms which are `φ`-equivariant

You should extend this class when you extend `MulActionHom`. -/
class MulActionSemiHomClass (F : Type _) {M N : outParam (Type _)}
(φ : outParam (M → N)) (X Y : outParam (Type _)) [SMul M X] [SMul N Y] extends
  FunLike F X fun _ => Y where
  /-- The proposition that the function preserves the action. -/
  map_smulₛₗ : ∀ (f : F) (c : M) (x : X), f (c • x) = (φ c) • (f x)
#align smul_hom_class MulActionSemiHomClass

export MulActionSemiHomClass (map_smulₛₗ)

/-- `MulActionHomClass F M X Y` states that `F` is a type of
morphisms which are equivariant with respect to actions of `M`
This is an abbreviation of `MulActionSemiHomClass`. -/
abbrev MulActionHomClass (F : Type _) (M : outParam (Type _))
(X Y : outParam (Type _)) [SMul M X] [SMul M Y] :=
  MulActionSemiHomClass F (@id M) X Y

@[simp]
theorem map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [MulActionHomClass F M X Y]
    (f : F) (c : M) (x : X) : f (c • x) = c • f x :=
  map_smulₛₗ f c x

attribute [simp] map_smulₛₗ

-- porting note: removed has_coe_to_fun instance, coercions handled differently now
#noalign mul_action_hom.has_coe_to_fun

instance : MulActionSemiHomClass (X →ₑ[φ] Y) φ X Y
    where
  coe := MulActionHom.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_smulₛₗ := MulActionHom.map_smul'

initialize_simps_projections MulActionHom (toFun → apply)

namespace MulActionHom

variable {φ X Y}
variable {F : Type*}

/- porting note: inserted following def & instance for consistent coercion behaviour,
see also Algebra.Hom.Group -/
/-- Turn an element of a type `F` satisfying `MulActionSemiHomClass F φ X Y`
  into an actual `MulActionHom`.
  This is declared as the default coercion from `F` to `MulActionSemiHom φ X Y`. -/
@[coe]
def _root_.MulActionSemiHomClass.toMulActionHom [MulActionSemiHomClass F φ X Y] (f : F) :
    X →ₑ[φ] Y where
  toFun := FunLike.coe f
  map_smul' := map_smulₛₗ f

/-- Any type satisfying `MulActionSemiHomClass` can be cast into `MulActionHom` via
  `MulActionHomSemiClass.toMulActionHom`. -/
instance [MulActionSemiHomClass F φ X Y] : CoeTC F (X →ₑ[φ] Y) :=
  ⟨MulActionSemiHomClass.toMulActionHom⟩

protected theorem map_smulₑ [MulActionSemiHomClass F φ X Y] (f : F) (m : M) (x : X) :
    f (m • x) = (φ m) • f x :=
  map_smulₛₗ f m x
#align mul_action_hom.map_smul MulActionHom.map_smulₑ

protected lemma map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [MulActionHomClass F M X Y]
    (f : F) (m : M) (x : X) :
    f (m • x) = m • (f x) := map_smulₛₗ f m x

@[ext]
theorem ext [MulActionSemiHomClass F φ X Y] {f g : F} :
    (∀ x, f x = g x) → f = g :=
  FunLike.ext f g
#align mul_action_hom.ext MulActionHom.ext

theorem ext_iff [MulActionSemiHomClass F φ X Y] {f g : F} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align mul_action_hom.ext_iff MulActionHom.ext_iff

protected theorem congr_fun [MulActionSemiHomClass F φ X Y] {f g : F} (h : f = g) (x : X) :
    f x = g x :=
  FunLike.congr_fun h _
#align mul_action_hom.congr_fun MulActionHom.congr_fun

/-- Two equal maps on scalars give rise to an equivariant map for identity -/
def ofEq {φ' : M → N} (h : φ = φ') (f : X →ₑ[φ] Y) : X →ₑ[φ'] Y
    where
  toFun := f.toFun
  map_smul' m a := h ▸ f.map_smul' m a
#align equivariant_map.of_eq MulActionHom.ofEq

@[simp]
theorem ofEq_coe {φ' : M → N} (h : φ = φ') (f : X →ₑ[φ] Y) :
    (f.ofEq h).toFun = f.toFun := rfl
#align equivariant_map.of_eq_coe MulActionHom.ofEq_coe

@[simp]
theorem ofEq_apply {φ' : M → N} (h : φ = φ') (f : X →ₑ[φ] Y) (a : X) :
    (f.ofEq h) a = f a :=
  rfl
#align equivariant_map.of_eq_apply MulActionHom.ofEq_apply


variable {ψ χ} (M N)

/-- The identity map as an equivariant map. -/
protected def id : X →[M] X :=
  ⟨id, fun _ _ => rfl⟩
#align mul_action_hom.id MulActionHom.id

variable {M N Z}

@[simp]
theorem id_apply (x : X) :
    MulActionHom.id M x = x :=
  rfl
#align mul_action_hom.id_apply MulActionHom.id_apply

end MulActionHom

namespace MulActionHom
open MulActionHom

variable {φ ψ χ X Y Z}

/-- Composition of two equivariant maps. -/
def comp' (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y) (κ : CompTriple φ ψ χ) :
    X →ₑ[χ] Z :=
  ⟨g ∘ f, fun m x =>
    calc
      g (f (m • x)) = g (φ m • f x) := by rw [map_smulₛₗ]
      _ = ψ (φ m) • g (f x) := by rw [map_smulₛₗ]
      _ = (ψ ∘ φ) m • g (f x) := rfl
      _ = χ m • g (f x) := by rw [κ.comp_eq] ⟩

/-- Composition of two equivariant maps. -/
def comp (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y) : X →ₑ[ψ ∘ φ] Z :=
  g.comp' f (CompTriple.comp)
#align mul_action_hom.comp MulActionHom.comp

@[simp]
lemma comp_eq_comp' (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y) :
    g.comp f = g.comp' f (CompTriple.comp) := rfl

@[simp]
theorem comp'_apply
    (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y) (κ : CompTriple φ ψ χ) (x : X) :
    (g.comp' f κ) x = g (f x) := rfl

@[simp]
theorem comp_apply
    (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y) (x : X) : (g.comp f) x = g (f x) := rfl
#align mul_action_hom.comp_apply MulActionHom.comp_apply

@[simp]
theorem id_comp' (f : X →ₑ[φ] Y) :
    (MulActionHom.id N).comp' f (CompTriple.id_comp) = f :=
  ext fun x => by rw [comp'_apply, id_apply]

@[simp]
theorem id_comp (f : X →ₑ[φ] Y) :
    (MulActionHom.id N).comp f = f := by simp

#align mul_action_hom.id_comp MulActionHom.id_comp

@[simp]
theorem comp'_id (f : X →ₑ[φ] Y) :
    f.comp' (MulActionHom.id M) (CompTriple.comp_id)= f :=
  ext fun x => by rw [comp'_apply, id_apply]

@[simp]
theorem comp_id (f : X →ₑ[φ] Y) : f.comp (MulActionHom.id M) = f := by simp
#align mul_action_hom.comp_id MulActionHom.comp_id

@[simp]
theorem comp'_assoc {Q T : Type _} [SMul Q T]
    {η : P → Q} {θ : M → Q} {ζ : N → Q}
    (h : Z →ₑ[η] T) (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y)
    {κ : CompTriple φ ψ χ} {κ' : CompTriple χ η θ}
    {ξ : CompTriple ψ η ζ} {ξ' : CompTriple φ ζ θ} :
    h.comp' (g.comp' f κ) κ' = (h.comp' g ξ).comp' f ξ':=
  ext fun _ => rfl

@[simp]
theorem comp_assoc {Q T : Type _} [SMul Q T]
    {η : P → Q}
    (h : Z →ₑ[η] T) (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y) :
    h.comp (g.comp f) = (h.comp g).comp f :=
  ext fun _ => rfl
#align equivariant_map.comp_assoc MulActionHom.comp_assoc

variable {φ' : N → M}
variable {Y₁ : Type*} [SMul M Y₁]
/-- The inverse of a bijective equivariant map is equivariant. -/
@[simps]
def inverse (f : X →[M] Y₁) (g : Y₁ → X)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : Y₁ →[M] X
    where
  toFun := g
  map_smul' m x :=
    calc
      g (m • x) = g (m • f (g x)) := by rw [h₂]
      _ = g (f (m • g x)) := by simp only [map_smulₛₗ, id_eq]
      _ = m • g x := by rw [h₁]

/-- The inverse of a bijective equivariant map is equivariant. -/
@[simps]
def inverse' (f : X →ₑ[φ] Y) (g : Y → X) (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : Y →ₑ[φ'] X
    where
  toFun := g
  map_smul' m x :=
    calc
      g (m • x) = g (m • f (g x)) := by rw [h₂]
      _ = g ((φ (φ' m)) • f (g x)) := by rw [k]
      _ = g (f (φ' m • g x)) := by rw [map_smulₛₗ]
      _ = φ' m • g x := by rw [h₁]
#align mul_action_hom.inverse MulActionHom.inverse'

lemma inverse_eq_inverse' (f : X →[M] Y₁) (g : Y₁ → X)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
  inverse f g h₁ h₂ =  inverse' f g (congrFun rfl) h₁ h₂ := by
  rfl

-- Useful/necessary ?
theorem inverse'_inverse'
    {f : X →ₑ[φ] Y} {g : Y → X}
    {k₁ : Function.LeftInverse φ' φ} {k₂ : Function.RightInverse φ' φ}
    {h₁ : Function.LeftInverse g f} {h₂ : Function.RightInverse g f} :
    inverse' (inverse' f g k₂ h₁ h₂) f k₁ h₂ h₁ = f :=
  ext fun _ => rfl

theorem comp_inverse' {f : X →ₑ[φ] Y } {g : Y → X}
    {k₁ : Function.LeftInverse φ' φ} {k₂ : Function.RightInverse φ' φ}
    {h₁ : Function.LeftInverse g f} {h₂ : Function.RightInverse g f} :
    (inverse' f g k₂ h₁ h₂).comp' f (CompTriple.comp_inv k₁) = MulActionHom.id M := by
  rw [ext_iff]
  intro x
  simp only [comp'_apply, inverse_apply, id_apply]
  exact h₁ x

theorem inverse'_comp' {f : X →ₑ[φ] Y } {g : Y → X}
    {k₂ : Function.RightInverse φ' φ}
    {h₁ : Function.LeftInverse g f} {h₂ : Function.RightInverse g f} :
    f.comp' (inverse' f g k₂ h₁ h₂) (CompTriple.comp_inv k₂) = MulActionHom.id N := by
  rw [ext_iff]
  intro x
  simp only [comp'_apply, inverse_apply, id_apply]
  exact h₂ x

/-- If actions of `M` and `N` on `α` commute,
  then for `c : M`, `(c • · : α → α)` is an `N`-action homomorphism. -/
@[simps]
def _root_.SMulCommClass.toMulActionHom {M} (N α : Type _)
    [SMul M α] [SMul N α] [SMulCommClass M N α] (c : M) :
    α →[N] α where
  toFun := (c • ·)
  map_smul' := smul_comm _

end MulActionHom

end MulActionHom

section LinearMap

variable {M : Type _} [Monoid M]
variable {N : Type _} [Monoid N]
variable {P : Type _} [Monoid P]
variable (φ: M → N) (φ' : N → M) (ψ : N → P) (χ : M → P)
variable (A : Type _) [AddMonoid A] [DistribMulAction M A]
variable (B : Type _) [AddMonoid B] [DistribMulAction N B]
variable (B₁ : Type _) [AddMonoid B₁] [DistribMulAction M B₁]
variable (C : Type _) [AddMonoid C] [DistribMulAction P C]

variable (A' : Type _) [AddGroup A'] [DistribMulAction M A']
variable (B' : Type _) [AddGroup B'] [DistribMulAction N B']

/-- Equivariant additive monoid homomorphisms. -/
structure LinearMap extends A →ₑ[φ] B, A →+ B
#align distrib_mul_action_hom LinearMap

/-
/-- Equivariant additive monoid homomorphisms. -/
abbrev LinearMap (M : Type _) [Monoid M]
  (A : Type _) [AddMonoid A] [DistribMulAction M A]
  (B : Type _) [AddMonoid B] [DistribMulAction M B] :=
  DistribMulActionSemiHom (@id M) A B
-/

/-- Reinterpret an equivariant additive monoid homomorphism as an additive monoid homomorphism. -/
add_decl_doc LinearMap.toAddMonoidHom
#align distrib_mul_action_hom.to_add_monoid_hom LinearMap.toAddMonoidHom

/-- Reinterpret an equivariant additive monoid homomorphism as an equivariant function. -/
add_decl_doc LinearMap.toMulActionHom
#align distrib_mul_action_hom.to_mul_action_hom LinearMap.toMulActionHom

/- Porting note: local notation given a name, conflict with Algebra.Hom.Freiman
 see https://github.com/leanprover/lean4/issues/2000 -/
@[inherit_doc]
notation:25 (name := «LinearMapLocal≺»)
  A " →ₑ+[" φ:25 "] " B:0 => LinearMap φ A B

@[inherit_doc]
notation:25 (name := «LinearMapIdLocal≺»)
  A " →+[" M:25 "] " B:0 => LinearMap (@id M) A B

-- QUESTION/TODO : Impose that `φ` is a morphism of monoids?

/-- `SemilinearMapClass F φ A B` states that `F` is a type of morphisms
  preserving the additive monoid structure and equivariant with respect to `φ`.
    You should extend this class when you extend `LinearMap`. -/
class SemilinearMapClass (F : Type _)
  {M N : outParam (Type _)} (φ : outParam (M → N)) (A B : outParam (Type _))
  [Monoid M] [Monoid N] [AddMonoid A] [AddMonoid B] [DistribMulAction M A] [DistribMulAction N B]
  extends MulActionSemiHomClass F φ A B,
  AddMonoidHomClass F A B
#align distrib_mul_action_hom_class SemilinearMapClass

/-- `LinearMapClass F M A B` states that `F` is a type of morphisms preserving
  the additive monoid structure and equivariant with respect to the action of `M`.
    It is an abbreviation to `LinearMapClass F (MonoidHom.id M) A B` -/
abbrev LinearMapClass (F : Type _)
  (M : outParam (Type _)) (A B : outParam (Type _))
  [Monoid M] [Monoid N] [AddMonoid A] [AddMonoid B] [DistribMulAction M A] [DistribMulAction M B] :=
  SemilinearMapClass F (MonoidHom.id M) A B

/- porting note: Removed a @[nolint dangerousInstance] for
LinearMapClass.toAddMonoidHomClass not dangerous due to `outParam`s -/


namespace LinearMap

/- porting note: TODO decide whether the next two instances should be removed
Coercion is already handled by all the HomClass constructions I believe -/
-- instance coe : Coe (A →+[M] B) (A →+ B) :=
--   ⟨toAddMonoidHom⟩
-- #align distrib_mul_action_hom.has_coe LinearMap.coe

-- instance coe' : Coe (A →+[M] B) (A →[M] B) :=
--   ⟨toMulActionHom⟩
-- #align distrib_mul_action_hom.has_coe' LinearMap.coe'

-- porting note: removed has_coe_to_fun instance, coercions handled differently now

#noalign distrib_mul_action_hom.has_coe
#noalign distrib_mul_action_hom.has_coe'
#noalign distrib_mul_action_hom.has_coe_to_fun

instance : SemilinearMapClass (A →ₑ+[φ] B) φ A B
    where
  coe m := m.toFun
  coe_injective' f g h := by
    rcases f with ⟨tF, _, _⟩; rcases g with ⟨tG, _, _⟩
    cases tF; cases tG; congr
  map_smulₛₗ m := m.map_smul'
  map_zero := LinearMap.map_zero'
  map_add := LinearMap.map_add'

variable {φ φ' A B B₁}
variable {F : Type*}

/- porting note: inserted following def & instance for consistent coercion behaviour,
see also Algebra.Hom.Group -/
/-- Turn an element of a type `F` satisfying `MulActionHomClass F M X Y` into an actual
`MulActionHom`. This is declared as the default coercion from `F` to `MulActionHom M X Y`. -/
@[coe]
def _root_.SemilinearMapClass.toLinearMap
    [SemilinearMapClass F φ A B] (f : F) : A →ₑ+[φ] B :=
  { (f : A →+ B),  (f : A →ₑ[φ] B) with }

/-- Any type satisfying `MulActionHomClass` can be cast into `MulActionHom` via
  `MulActionHomClass.toMulActionHom`. -/
instance [SemilinearMapClass F φ A B] :
  CoeTC F (A →ₑ+[φ] B) :=
  ⟨SemilinearMapClass.toLinearMap⟩

/-- If `DistribMulAction` of `M` and `N` on `A` commute,
  then for each `c : M`, `(c • ·)` is an `N`-action additive homomorphism. -/
@[simps]
def _root_.SMulCommClass.toLinearMap {M} (N A : Type _) [Monoid N] [AddMonoid A]
    [DistribSMul M A] [DistribMulAction N A] [SMulCommClass M N A] (c : M) : A →+[N] A :=
  { SMulCommClass.toMulActionHom N A c,
    DistribSMul.toAddMonoidHom _ c with
    toFun := (c • ·) }

@[simp]
theorem toFun_eq_coe (f : A →ₑ+[φ] B) : f.toFun = f := rfl
#align distrib_mul_action_hom.to_fun_eq_coe LinearMap.toFun_eq_coe

@[norm_cast]
theorem coe_fn_coe (f : A →ₑ+[φ] B) : ⇑(f : A →+ B) = f :=
  rfl
#align distrib_mul_action_hom.coe_fn_coe LinearMap.coe_fn_coe

@[norm_cast]
theorem coe_fn_coe' (f : A →ₑ+[φ] B) : ⇑(f : A →ₑ[φ] B) = f :=
  rfl
#align distrib_mul_action_hom.coe_fn_coe' LinearMap.coe_fn_coe'

@[ext]
theorem ext {f g : A →ₑ+[φ] B} : (∀ x, f x = g x) → f = g :=
  FunLike.ext f g
#align distrib_mul_action_hom.ext LinearMap.ext

theorem ext_iff {f g : A →ₑ+[φ] B} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align distrib_mul_action_hom.ext_iff LinearMap.ext_iff

protected theorem congr_fun {f g : A →ₑ+[φ] B} (h : f = g) (x : A) : f x = g x :=
  FunLike.congr_fun h _
#align distrib_mul_action_hom.congr_fun LinearMap.congr_fun

theorem toMulActionHom_injective {f g : A →ₑ+[φ] B} (h : (f : A →ₑ[φ] B) = (g : A →ₑ[φ] B)) :
    f = g := by
  ext a
  exact MulActionHom.congr_fun h a
#align distrib_mul_action_hom.to_mul_action_hom_injective LinearMap.toMulActionHom_injective

theorem toAddMonoidHom_injective {f g : A →ₑ+[φ] B} (h : (f : A →+ B) = (g : A →+ B)) : f = g := by
  ext a
  exact FunLike.congr_fun h a
#align distrib_mul_action_hom.to_add_monoid_hom_injective LinearMap.toAddMonoidHom_injective

protected theorem map_zero (f : A →ₑ+[φ] B) : f 0 = 0 :=
  map_zero f
#align distrib_mul_action_hom.map_zero LinearMap.map_zero

protected theorem map_add (f : A →ₑ+[φ] B) (x y : A) : f (x + y) = f x + f y :=
  map_add f x y
#align distrib_mul_action_hom.map_add LinearMap.map_add

protected theorem map_neg (f : A' →ₑ+[φ] B') (x : A') : f (-x) = -f x :=
  map_neg f x
#align distrib_mul_action_hom.map_neg LinearMap.map_neg

protected theorem map_sub (f : A' →ₑ+[φ] B') (x y : A') : f (x - y) = f x - f y :=
  map_sub f x y
#align distrib_mul_action_hom.map_sub LinearMap.map_sub

protected theorem map_smulₑ (f : A →ₑ+[φ] B) (m : M) (x : A) : f (m • x) = (φ m) • f x :=
  map_smulₛₗ f m x
#align distrib_mul_action_hom.map_smul LinearMap.map_smulₑ

variable (M)

/-- The identity map as an equivariant additive monoid homomorphism. -/
protected def id : A →+[M] A :=
  ⟨MulActionHom.id _, rfl, fun _ _ => rfl⟩
#align distrib_mul_action_hom.id LinearMap.id

@[simp]
theorem id_apply (x : A) : LinearMap.id M x = x := by
  rfl
#align distrib_mul_action_hom.id_apply LinearMap.id_apply

variable {M C ψ χ}

-- porting note:  `simp` used to prove this, but now `change` is needed to push past the coercions
instance : Zero (A →ₑ+[φ] B) :=
  ⟨{ (0 : A →+ B) with
    map_smul' := fun m _ => by change (0 : B) = (φ m) • (0 : B); rw [smul_zero]}⟩

instance : One (A →+[M] A) :=
  ⟨LinearMap.id M⟩

@[simp]
theorem coe_zero : ⇑(0 : A →ₑ+[φ] B) = 0 :=
  rfl
#align distrib_mul_action_hom.coe_zero LinearMap.coe_zero

@[simp]
theorem coe_one : ⇑(1 : A →+[M] A) = id :=
  rfl
#align distrib_mul_action_hom.coe_one LinearMap.coe_one

theorem zero_apply (a : A) : (0 : A →ₑ+[φ] B) a = 0 :=
  rfl
#align distrib_mul_action_hom.zero_apply LinearMap.zero_apply

theorem one_apply (a : A) : (1 : A →+[M] A) a = a :=
  rfl
#align distrib_mul_action_hom.one_apply LinearMap.one_apply

instance : Inhabited (A →ₑ+[φ] B) :=
  ⟨0⟩

/-- Composition of two equivariant additive monoid homomorphisms. -/
def comp (g : B →ₑ+[ψ] C) (f : A →ₑ+[φ] B) : A →ₑ+[ψ ∘ φ] C :=
  { MulActionHom.comp (g : B →ₑ[ψ] C) (f : A →ₑ[φ] B) ,
    AddMonoidHom.comp (g : B →+ C) (f : A →+ B) with }
#align distrib_mul_action_hom.comp LinearMap.comp

/-- Composition of two equivariant additive monoid homomorphisms. -/
def comp' (g : B →ₑ+[ψ] C) (f : A →ₑ+[φ] B) (κ : CompTriple φ ψ χ) :
    A →ₑ+[χ] C :=
  { MulActionHom.comp' (g : B →ₑ[ψ] C) (f : A →ₑ[φ] B) κ,
    AddMonoidHom.comp (g : B →+ C) (f : A →+ B) with }

lemma comp_eq_comp' (g : B →ₑ+[ψ] C) (f : A →ₑ+[φ] B) :
    g.comp f = g.comp' f (CompTriple.comp) := rfl

@[simp]
theorem comp_apply (g : B →ₑ+[ψ] C) (f : A →ₑ+[φ] B) (x : A) :
    g.comp f x = g (f x) :=
  rfl
#align distrib_mul_action_hom.comp_apply LinearMap.comp_apply

@[simp]
theorem comp'_apply (g : B →ₑ+[ψ] C) (f : A →ₑ+[φ] B) {κ : CompTriple φ ψ χ} (x : A) :
    g.comp' f κ x = g (f x) :=
  rfl

@[simp]
theorem id_comp (f : A →ₑ+[φ] B) :
    comp (LinearMap.id N) f = f :=
  ext fun x => by rw [comp_apply, id_apply]
#align distrib_mul_action_hom.id_comp LinearMap.id_comp

@[simp]
theorem id_comp' (f : A →ₑ+[φ] B) :
    comp' (LinearMap.id N) f (CompTriple.id_comp) = f :=
  ext fun x => by rw [comp'_apply, id_apply]

@[simp]
theorem comp_id (f : A →ₑ+[φ] B) :
    comp f (LinearMap.id M) = f :=
  ext fun x => by rw [comp_apply, id_apply]
#align distrib_mul_action_hom.comp_id LinearMap.comp_id

@[simp]
theorem comp'_id (f : A →ₑ+[φ] B) :
    f.comp' (LinearMap.id M) (CompTriple.comp_id)= f :=
  ext fun x => by rw [comp'_apply, id_apply]

/-- The inverse of a bijective `LinearMap` is a `LinearMap`. -/
@[simps]
def inverse (f : A →+[M] B₁) (g : B₁ → A)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : B₁ →+[M] A :=
  { (f : A →+ B₁).inverse g h₁ h₂, (f : A →[M] B₁).inverse g h₁ h₂ with toFun := g }
#align distrib_mul_action_hom.inverse LinearMap.inverse

/-- The inverse of a bijective `LinearMap` is a `LinearMap`. -/
@[simps]
def inverse' (f : A →ₑ+[φ] B) (g : B → A) (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : B →ₑ+[φ'] A :=
  { (f : A →+ B).inverse g h₁ h₂, (f : A →ₑ[φ] B).inverse' g k h₁ h₂ with toFun := g }

section Semiring

variable (R : Type _) [Semiring R] [MulSemiringAction M R]
variable (R' : Type _) [Ring R'] [MulSemiringAction M R']
variable (S : Type _) [Semiring S] [MulSemiringAction N S]
variable (S' : Type _) [Ring S'] [MulSemiringAction N S']
variable (T : Type _) [Semiring T] [MulSemiringAction P T]

variable {R S M' N'}
variable [AddMonoid M'] [DistribMulAction R M']
variable [AddMonoid N'] [DistribMulAction S N']

variable {σ : R → S}
@[ext]
theorem ext_ring {f g : R →ₑ+[σ] N'} (h : f 1 = g 1) : f = g := by
  ext x
  rw [← mul_one x, ← smul_eq_mul R, f.map_smulₑ, g.map_smulₑ, h]

#align distrib_mul_action_hom.ext_ring LinearMap.ext_ring

theorem ext_ring_iff {f g : R →ₑ+[σ] N'} : f = g ↔ f 1 = g 1 :=
  ⟨fun h => h ▸ rfl, ext_ring⟩
#align distrib_mul_action_hom.ext_ring_iff LinearMap.ext_ring_iff

end Semiring

end LinearMap

variable (R : Type _) [Semiring R] [MulSemiringAction M R]
variable (R' : Type _) [Ring R'] [MulSemiringAction M R']
variable (S : Type _) [Semiring S] [MulSemiringAction N S]
variable (S' : Type _) [Ring S'] [MulSemiringAction N S']
variable (T : Type _) [Semiring T] [MulSemiringAction P T]

-- variable {R S M' N'}
-- variable [AddMonoid M'] [DistribMulAction R M']
-- variable [AddMonoid N'] [DistribMulAction S N']

/-- Equivariant ring homomorphisms. -/
-- Porting note: This linter does not exist yet
-- @[nolint has_nonempty_instance]
structure MulSemiringActionHom extends R →ₑ+[φ] S, R →+* S
#align mul_semiring_action_hom MulSemiringActionHom

/-
/-- Equivariant ring homomorphism -/
abbrev MulSemiringActionHom
  (M : Type _) [Monoid M]
  (R : Type _) [Semiring R] [MulSemiringAction M R]
  (S : Type _) [Semiring S] [MulSemiringAction M S]:= MulSemiringActionHom (MonoidHom.id M) R S
-/

/-- Reinterpret an equivariant ring homomorphism as a ring homomorphism. -/
add_decl_doc MulSemiringActionHom.toRingHom
#align mul_semiring_action_hom.to_ring_hom MulSemiringActionHom.toRingHom

/-- Reinterpret an equivariant ring homomorphism as an equivariant additive monoid homomorphism. -/
add_decl_doc MulSemiringActionHom.toLinearMap
#align mul_semiring_action_hom.to_distrib_mul_action_hom MulSemiringActionHom.toLinearMap

/- Porting note: local notation given a name, conflict with Algebra.Hom.Freiman
 see https://github.com/leanprover/lean4/issues/2000 -/
@[inherit_doc]
notation:25 (name := «MulSemiringActionHomLocal≺»)
  R " →ₑ+*[" φ:25 "] " S:0 => MulSemiringActionHom φ R S

@[inherit_doc]
notation:25 (name := «MulSemiringActionHomIdLocal≺»)
  R " →+*[" M:25 "] " S:0 => MulSemiringActionHom (MonoidHom.id M) R S

/-- `MulSemiringActionHomClass F φ R S` states that `F` is a type of morphisms preserving
the ring structure and equivariant with respect to `φ`.

You should extend this class when you extend `MulSemiringActionHom`. -/
class MulSemiringActionSemiHomClass (F : Type _)
  {M N : outParam (Type _)} [Monoid M] [Monoid N]
  (φ : outParam (M → N))
  (R S : outParam (Type _)) [Semiring R] [Semiring S]
  [DistribMulAction M R] [DistribMulAction N S] extends
  SemilinearMapClass F φ R S, RingHomClass F R S
#align mul_semiring_action_hom_class MulSemiringActionSemiHomClass

/-- `MulSemiringActionHomClass F M R S` states that `F` is a type of morphisms preserving
the ring structure and equivariant with respect to a `DistribMulAction`of `M` on `R` and `S` .
 -/
abbrev MulSemiringActionHomClass
    (F : Type _)
    {M : outParam (Type _)} [Monoid M]
    (R S : outParam (Type _)) [Semiring R] [Semiring S]
    [DistribMulAction M R] [DistribMulAction M S] :=
  MulSemiringActionSemiHomClass F (MonoidHom.id M) R S

/- porting note: Removed a @[nolint dangerousInstance] for MulSemiringActionHomClass.toRingHomClass
 not dangerous due to outParam -/

namespace MulSemiringActionHom

/- porting note: TODO decide whether the next two instances should be removed
Coercion is already handled by all the HomClass constructions I believe -/
-- @[coe]
-- instance coe : Coe (R →+*[M] S) (R →+* S) :=
--   ⟨toRingHom⟩
-- #align mul_semiring_action_hom.has_coe MulSemiringActionHom.coe

-- @[coe]
-- instance coe' : Coe (R →+*[M] S) (R →+[M] S) :=
--   ⟨toLinearMap⟩
-- #align mul_semiring_action_hom.has_coe' MulSemiringActionHom.coe'

-- porting note: removed has_coe_to_fun instance, coercions handled differently now

#noalign mul_semiring_action_hom.has_coe
#noalign mul_semiring_action_hom.has_coe'
#noalign mul_semiring_action_hom.has_coe_to_fun

instance : MulSemiringActionSemiHomClass (R →ₑ+*[φ] S) φ R S
    where
  coe m := m.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨tF, _, _⟩, _, _⟩; rcases g with ⟨⟨tG, _, _⟩, _, _⟩
    cases tF; cases tG; congr
  map_smulₛₗ m := m.map_smul'
  map_zero m := m.map_zero'
  map_add m := m.map_add'
  map_one := MulSemiringActionHom.map_one'
  map_mul := MulSemiringActionHom.map_mul'

variable {φ R S}
variable {F : Type*}

/- porting note: inserted following def & instance for consistent coercion behaviour,
see also Algebra.Hom.Group -/
/-- Turn an element of a type `F` satisfying `MulSemiringActionHomClass F M R S` into an actual
`MulSemiringActionHom`. This is declared as the default coercion from `F` to
`MulSemiringActionHom M X Y`. -/
@[coe]
def _root_.MulSemiringActionHomClass.toMulSemiringActionHom
    [MulSemiringActionSemiHomClass F φ R S] (f : F) : R →ₑ+*[φ] S :=
 { (f : R →+* S),  (f : R →ₑ+[φ] S) with }

/-- Any type satisfying `MulSemiringActionHomClass` can be cast into `MulSemiringActionHom` via
  `MulSemiringActionHomClass.toMulSemiringActionHom`. -/
instance [MulSemiringActionSemiHomClass F φ R S] : CoeTC F (R →ₑ+*[φ] S) :=
  ⟨MulSemiringActionHomClass.toMulSemiringActionHom⟩

@[norm_cast]
theorem coe_fn_coe (f : R →ₑ+*[φ] S) : ⇑(f : R →+* S) = f :=
  rfl
#align mul_semiring_action_hom.coe_fn_coe MulSemiringActionHom.coe_fn_coe

@[norm_cast]
theorem coe_fn_coe' (f : R →ₑ+*[φ] S) : ⇑(f : R →ₑ+[φ] S) = f :=
  rfl
#align mul_semiring_action_hom.coe_fn_coe' MulSemiringActionHom.coe_fn_coe'

@[ext]
theorem ext {f g : R →ₑ+*[φ] S} : (∀ x, f x = g x) → f = g :=
  FunLike.ext f g
#align mul_semiring_action_hom.ext MulSemiringActionHom.ext

theorem ext_iff {f g : R →ₑ+*[φ] S} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align mul_semiring_action_hom.ext_iff MulSemiringActionHom.ext_iff

protected theorem map_zero (f : R →ₑ+*[φ] S) : f 0 = 0 :=
  map_zero f
#align mul_semiring_action_hom.map_zero MulSemiringActionHom.map_zero

protected theorem map_add (f : R →ₑ+*[φ] S) (x y : R) : f (x + y) = f x + f y :=
  map_add f x y
#align mul_semiring_action_hom.map_add MulSemiringActionHom.map_add

protected theorem map_neg (f : R' →ₑ+*[φ] S') (x : R') : f (-x) = -f x :=
  map_neg f x
#align mul_semiring_action_hom.map_neg MulSemiringActionHom.map_neg

protected theorem map_sub (f : R' →ₑ+*[φ] S') (x y : R') : f (x - y) = f x - f y :=
  map_sub f x y
#align mul_semiring_action_hom.map_sub MulSemiringActionHom.map_sub

protected theorem map_one (f : R →ₑ+*[φ] S) : f 1 = 1 :=
  map_one f
#align mul_semiring_action_hom.map_one MulSemiringActionHom.map_one

protected theorem map_mul (f : R →ₑ+*[φ] S) (x y : R) : f (x * y) = f x * f y :=
  map_mul f x y
#align mul_semiring_action_hom.map_mul MulSemiringActionHom.map_mul

protected theorem map_smulₛₗ (f : R →ₑ+*[φ] S) (m : M) (x : R) : f (m • x) = φ m • f x :=
  map_smulₛₗ f m x
#align mul_semiring_action_hom.map_smulₛₗ MulSemiringActionHom.map_smulₛₗ

protected theorem map_smul [MulSemiringAction M S] (f : R →+*[M] S) (m : M) (x : R) :
    f (m • x) = m • f x :=
  map_smulₛₗ f m x
#align mul_semiring_action_hom.map_smul MulSemiringActionHom.map_smul

end MulSemiringActionHom

namespace MulSemiringActionHom

variable (M) {R}

/-- The identity map as an equivariant ring homomorphism. -/
protected def id : R →+*[M] R :=
  ⟨LinearMap.id _, rfl, (fun _ _ => rfl)⟩
#align mul_semiring_action_hom.id MulSemiringActionHom.id

@[simp]
theorem id_apply (x : R) : MulSemiringActionHom.id M x = x :=
  rfl
#align mul_semiring_action_hom.id_apply MulSemiringActionHom.id_apply


end MulSemiringActionHom

namespace MulSemiringActionHom
open MulSemiringActionHom

variable {R S T}

variable {φ φ' ψ χ}

/-- Composition of two equivariant additive ring homomorphisms. -/
def comp' (g : S →ₑ+*[ψ] T) (f : R →ₑ+*[φ] S)  (κ : CompTriple φ ψ χ) : R →ₑ+*[χ] T :=
  { LinearMap.comp' (g : S →ₑ+[ψ] T) (f : R →ₑ+[φ] S) κ,
    RingHom.comp (g : S →+* T) (f : R →+* S) with }

/-- Composition of two equivariant additive ring homomorphisms. -/
def comp (g : S →ₑ+*[ψ] T) (f : R →ₑ+*[φ] S) : R →ₑ+*[ψ ∘ φ] T :=
  g.comp' f (CompTriple.comp)
#align mul_semiring_action_hom.comp MulSemiringActionHom.comp

theorem comp_eq_comp' (g : S →ₑ+*[ψ] T) (f : R →ₑ+*[φ] S) :
    g.comp f = g.comp' f (CompTriple.comp) := rfl

@[simp]
theorem comp'_apply (g : S →ₑ+*[ψ] T) (f : R →ₑ+*[φ] S) {κ : CompTriple φ ψ χ} (x : R) :
    g.comp' f κ x = g (f x) :=
  rfl

@[simp]
theorem id_comp' (f : R →ₑ+*[φ] S) :
    (MulSemiringActionHom.id N).comp' f (CompTriple.id_comp)= f :=
  ext fun x => by rw [comp'_apply, id_apply]

@[simp]
theorem id_comp (f : R →ₑ+*[φ] S) :
    (MulSemiringActionHom.id N).comp f = f := by
  rw [comp_eq_comp', id_comp']

@[simp]
theorem comp'_id (f : R →ₑ+*[φ] S) :
    f.comp' (MulSemiringActionHom.id M) (CompTriple.comp_id) = f :=
  ext fun x => by rw [comp'_apply, id_apply]

@[simp]
theorem comp_id (f : R →ₑ+*[φ] S) :
    f.comp (MulSemiringActionHom.id M) = f := by
  rw [comp_eq_comp', comp'_id]
#align mul_semiring_action_hom.comp_id MulSemiringActionHom.comp_id

/-- The inverse of a bijective `MulSemiringActionHom` is a `MulSemiringActionHom`. -/
@[simps]
def inverse' (f : R →ₑ+*[φ] S) (g : S → R) (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : S →ₑ+*[φ'] R :=
  { (f : R →+ S).inverse g h₁ h₂,
    (f : R →* S).inverse g h₁ h₂,
    (f : R →ₑ[φ] S).inverse' g k h₁ h₂ with toFun := g, }

/-- The inverse of a bijective `MulSemiringActionHom` is a `MulSemiringActionHom`. -/
@[simps]
def inverse {S₁ : Type*} [Semiring S₁] [MulSemiringAction M S₁]
    (f : R →+*[M] S₁) (g : S₁ → R)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : S₁ →+*[M] R :=
  { (f : R →+ S₁).inverse g h₁ h₂,
    (f : R →* S₁).inverse g h₁ h₂,
    (f : R →[M] S₁).inverse g h₁ h₂ with toFun := g, }
#align mul_semiring_action_hom.inverse MulSemiringActionHom.inverse

end MulSemiringActionHom
