/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Group.Hom.CompTypeclasses
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Algebra.Ring.Action.Basic

/-!
# Equivariant homomorphisms

## Main definitions

* `MulActionHom φ X Y`, the type of equivariant functions from `X` to `Y`,
  where `φ : M → N` is a map, `M` acting on the type `X` and `N` acting on the type of `Y`.
  `AddActionHom φ X Y` is its additive version.
* `DistribMulActionHom φ A B`,
  the type of equivariant additive monoid homomorphisms from `A` to `B`,
  where `φ : M → N` is a morphism of monoids,
  `M` acting on the additive monoid `A` and `N` acting on the additive monoid of `B`
* `SMulSemiringHom φ R S`, the type of equivariant ring homomorphisms
  from `R` to `S`, where `φ : M → N` is a morphism of monoids,
  `M` acting on the ring `R` and `N` acting on the ring `S`.

The above types have corresponding classes:
* `MulActionHomClass F φ X Y` states that `F` is a type of bundled `X → Y` homs
  which are `φ`-equivariant;
  `AddActionHomClass F φ X Y` is its additive version.
* `DistribMulActionHomClass F φ A B` states that `F` is a type of bundled `A → B` homs
  preserving the additive monoid structure and `φ`-equivariant
* `SMulSemiringHomClass F φ R S` states that `F` is a type of bundled `R → S` homs
  preserving the ring structure and `φ`-equivariant

## Notation

We introduce the following notation to code equivariant maps
(the subscript index `ₑ` is for *equivariant*) :
* `X →ₑ[φ] Y` is `MulActionHom φ X Y` and `AddActionHom φ X Y`
* `A →ₑ+[φ] B` is `DistribMulActionHom φ A B`.
* `R →ₑ+*[φ] S` is `MulSemiringActionHom φ R S`.

When `M = N` and `φ = MonoidHom.id M`, we provide the backward compatible notation :
* `X →[M] Y` is `MulActionHom (@id M) X Y` and `AddActionHom (@id M) X Y`
* `A →+[M] B` is `DistribMulActionHom (MonoidHom.id M) A B`
* `R →+*[M] S` is `MulSemiringActionHom (MonoidHom.id M) R S`

The notation for `MulActionHom` and `AddActionHom` is the same, because it is unlikely
that it could lead to confusion — unless one needs types `M` and `X` with simultaneous
instances of `Mul M`, `Add M`, `SMul M X` and `VAdd M X`…

-/

@[expose] public section

assert_not_exists Submonoid

section MulActionHom

variable {M' : Type*}
variable {M : Type*} {N : Type*} {P : Type*}
variable (φ : M → N) (ψ : N → P) (χ : M → P)
variable (X : Type*) [SMul M X] [SMul M' X]
variable (Y : Type*) [SMul N Y] [SMul M' Y]
variable (Z : Type*) [SMul P Z]

/-- Equivariant functions :
When `φ : M → N` is a function, and types `X` and `Y` are endowed with additive actions
of `M` and `N`, a function `f : X → Y` is `φ`-equivariant if `f (m +ᵥ x) = (φ m) +ᵥ (f x)`. -/
structure AddActionHom {M N : Type*} (φ : M → N) (X : Type*) [VAdd M X] (Y : Type*) [VAdd N Y] where
  /-- The underlying function. -/
  protected toFun : X → Y
  /-- The proposition that the function commutes with the additive actions. -/
  protected map_vadd' : ∀ (m : M) (x : X), toFun (m +ᵥ x) = (φ m) +ᵥ toFun x

/-- Equivariant functions :
When `φ : M → N` is a function, and types `X` and `Y` are endowed with actions of `M` and `N`,
a function `f : X → Y` is `φ`-equivariant if `f (m • x) = (φ m) • (f x)`. -/
@[to_additive]
structure MulActionHom where
  /-- The underlying function. -/
  protected toFun : X → Y
  /-- The proposition that the function commutes with the actions. -/
  protected map_smul' : ∀ (m : M) (x : X), toFun (m • x) = (φ m) • toFun x

/-- `φ`-equivariant functions `X → Y`,
where `φ : M → N`, where `M` and `N` act on `X` and `Y` respectively. -/
notation:25 (name := «MulActionHomLocal≺») X " →ₑ[" φ:25 "] " Y:0 => MulActionHom φ X Y

/-- `M`-equivariant functions `X → Y` with respect to the action of `M`.
This is the same as `X →ₑ[@id M] Y`. -/
notation:25 (name := «MulActionHomIdLocal≺») X " →[" M:25 "] " Y:0 => MulActionHom (@id M) X Y

/-- `φ`-equivariant functions `X → Y`,
where `φ : M → N`, where `M` and `N` act additively on `X` and `Y` respectively

We use the same notation as for multiplicative actions, as conflicts are unlikely. -/
notation:25 (name := «AddActionHomLocal≺») X " →ₑ[" φ:25 "] " Y:0 => AddActionHom φ X Y

/-- `M`-equivariant functions `X → Y` with respect to the additive action of `M`.
This is the same as `X →ₑ[@id M] Y`.

We use the same notation as for multiplicative actions, as conflicts are unlikely. -/
notation:25 (name := «AddActionHomIdLocal≺») X " →[" M:25 "] " Y:0 => AddActionHom (@id M) X Y

/-- `AddActionSemiHomClass F φ X Y` states that
  `F` is a type of morphisms which are `φ`-equivariant.

You should extend this class when you extend `AddActionHom`. -/
class AddActionSemiHomClass (F : Type*)
    {M N : outParam Type*} (φ : outParam (M → N))
    (X Y : outParam Type*) [VAdd M X] [VAdd N Y] [FunLike F X Y] : Prop where
  /-- The proposition that the function preserves the action. -/
  map_vaddₛₗ : ∀ (f : F) (c : M) (x : X), f (c +ᵥ x) = (φ c) +ᵥ (f x)

/-- `MulActionSemiHomClass F φ X Y` states that
  `F` is a type of morphisms which are `φ`-equivariant.

You should extend this class when you extend `MulActionHom`. -/
@[to_additive]
class MulActionSemiHomClass (F : Type*)
    {M N : outParam Type*} (φ : outParam (M → N))
    (X Y : outParam Type*) [SMul M X] [SMul N Y] [FunLike F X Y] : Prop where
  /-- The proposition that the function preserves the action. -/
  map_smulₛₗ : ∀ (f : F) (c : M) (x : X), f (c • x) = (φ c) • (f x)

export MulActionSemiHomClass (map_smulₛₗ)
export AddActionSemiHomClass (map_vaddₛₗ)

/-- `MulActionHomClass F M X Y` states that `F` is a type of
morphisms which are equivariant with respect to actions of `M`
This is an abbreviation of `MulActionSemiHomClass`. -/
@[to_additive /-- `MulActionHomClass F M X Y` states that `F` is a type of
morphisms which are equivariant with respect to actions of `M`
This is an abbreviation of `MulActionSemiHomClass`. -/]
abbrev MulActionHomClass (F : Type*) (M : outParam Type*)
    (X Y : outParam Type*) [SMul M X] [SMul M Y] [FunLike F X Y] :=
  MulActionSemiHomClass F (@id M) X Y

@[to_additive] instance : FunLike (MulActionHom φ X Y) X Y where
  coe := MulActionHom.toFun
  coe_injective' f g h := by cases f; cases g; congr

@[to_additive (attr := simp)]
theorem map_smul {F M X Y : Type*} [SMul M X] [SMul M Y]
    [FunLike F X Y] [MulActionHomClass F M X Y]
    (f : F) (c : M) (x : X) : f (c • x) = c • f x :=
  map_smulₛₗ f c x

@[to_additive]
instance : MulActionSemiHomClass (X →ₑ[φ] Y) φ X Y where
  map_smulₛₗ := MulActionHom.map_smul'

initialize_simps_projections MulActionHom (toFun → apply)
initialize_simps_projections AddActionHom (toFun → apply)

namespace MulActionHom

variable {φ X Y}
variable {F : Type*} [FunLike F X Y]

/-- Turn an element of a type `F` satisfying `MulActionSemiHomClass F φ X Y`
  into an actual `MulActionHom`.
  This is declared as the default coercion from `F` to `MulActionSemiHom φ X Y`. -/
@[to_additive (attr := coe)
  /-- Turn an element of a type `F` satisfying `AddActionSemiHomClass F φ X Y`
  into an actual `AddActionHom`.
  This is declared as the default coercion from `F` to `AddActionSemiHom φ X Y`. -/]
def _root_.MulActionSemiHomClass.toMulActionHom [MulActionSemiHomClass F φ X Y] (f : F) :
    X →ₑ[φ] Y where
  toFun := DFunLike.coe f
  map_smul' := map_smulₛₗ f

/-- Any type satisfying `MulActionSemiHomClass` can be cast into `MulActionHom` via
  `MulActionHomSemiClass.toMulActionHom`. -/
@[to_additive]
instance [MulActionSemiHomClass F φ X Y] : CoeTC F (X →ₑ[φ] Y) :=
  ⟨MulActionSemiHomClass.toMulActionHom⟩

variable (M' X Y F) in
/-- If Y/X/M forms a scalar tower, any map X → Y preserving X-action also preserves M-action. -/
@[to_additive]
theorem _root_.IsScalarTower.smulHomClass [MulOneClass X] [SMul X Y] [IsScalarTower M' X Y]
    [MulActionHomClass F X X Y] : MulActionHomClass F M' X Y where
  map_smulₛₗ f m x := by
    rw [← mul_one (m • x), ← smul_eq_mul, map_smul, smul_assoc, ← map_smul,
      smul_eq_mul, mul_one, id_eq]

@[to_additive]
protected theorem map_smul (f : X →[M'] Y) (m : M') (x : X) : f (m • x) = m • f x :=
  map_smul f m x

@[to_additive (attr := ext)]
theorem ext {f g : X →ₑ[φ] Y} :
    (∀ x, f x = g x) → f = g :=
  DFunLike.ext f g

@[to_additive]
protected theorem congr_fun {f g : X →ₑ[φ] Y} (h : f = g) (x : X) :
    f x = g x :=
  DFunLike.congr_fun h _

/-- Two equal maps on scalars give rise to an equivariant map for identity -/
@[to_additive /-- Two equal maps on scalars give rise to an equivariant map for identity -/]
def ofEq {φ' : M → N} (h : φ = φ') (f : X →ₑ[φ] Y) : X →ₑ[φ'] Y where
  toFun := f.toFun
  map_smul' m a := h ▸ f.map_smul' m a

@[to_additive (attr := simp)]
theorem ofEq_coe {φ' : M → N} (h : φ = φ') (f : X →ₑ[φ] Y) :
    (f.ofEq h).toFun = f.toFun := rfl

@[to_additive (attr := simp)]
theorem ofEq_apply {φ' : M → N} (h : φ = φ') (f : X →ₑ[φ] Y) (a : X) :
    (f.ofEq h) a = f a :=
  rfl

lemma _root_.FaithfulSMul.of_injective
    [FaithfulSMul M' X] [MulActionHomClass F M' X Y] (f : F)
    (hf : Function.Injective f) :
    FaithfulSMul M' Y where
  eq_of_smul_eq_smul {_ _} h := eq_of_smul_eq_smul fun m ↦ hf <| by simp_rw [map_smul, h]

variable {ψ χ} (M N)

/-- The identity map as an equivariant map. -/
@[to_additive /-- The identity map as an equivariant map. -/]
protected def id : X →[M] X :=
  ⟨id, fun _ _ => rfl⟩

variable {M N Z}

@[to_additive (attr := simp)]
theorem id_apply (x : X) :
    MulActionHom.id M x = x :=
  rfl

end MulActionHom

namespace MulActionHom
open MulActionHom

variable {φ ψ χ X Y Z}

-- attribute [instance] CompTriple.id_comp CompTriple.comp_id

/-- Composition of two equivariant maps. -/
@[to_additive /-- Composition of two equivariant maps. -/]
def comp (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y) [κ : CompTriple φ ψ χ] :
    X →ₑ[χ] Z :=
  ⟨g ∘ f, fun m x =>
    calc
      g (f (m • x)) = g (φ m • f x) := by rw [map_smulₛₗ]
      _ = ψ (φ m) • g (f x) := by rw [map_smulₛₗ]
      _ = (ψ ∘ φ) m • g (f x) := rfl
      _ = χ m • g (f x) := by rw [κ.comp_eq] ⟩

@[to_additive (attr := simp)]
theorem comp_apply
    (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y) [CompTriple φ ψ χ] (x : X) :
    g.comp f x = g (f x) := rfl

@[to_additive (attr := simp)]
theorem id_comp (f : X →ₑ[φ] Y) :
    (MulActionHom.id N).comp f = f :=
  ext fun x => by rw [comp_apply, id_apply]

@[to_additive (attr := simp)]
theorem comp_id (f : X →ₑ[φ] Y) :
    f.comp (MulActionHom.id M) = f :=
  ext fun x => by rw [comp_apply, id_apply]

@[to_additive (attr := simp)]
theorem comp_assoc {Q T : Type*} [SMul Q T]
    {η : P → Q} {θ : M → Q} {ζ : N → Q}
    (h : Z →ₑ[η] T) (g : Y →ₑ[ψ] Z) (f : X →ₑ[φ] Y)
    [CompTriple φ ψ χ] [CompTriple χ η θ]
    [CompTriple ψ η ζ] [CompTriple φ ζ θ] :
    h.comp (g.comp f) = (h.comp g).comp f :=
  ext fun _ => rfl

variable {φ' : N → M}
variable {Y₁ : Type*} [SMul M Y₁]

/-- The inverse of a bijective equivariant map is equivariant. -/
@[to_additive (attr := simps) /-- The inverse of a bijective equivariant map is equivariant. -/]
def inverse (f : X →[M] Y₁) (g : Y₁ → X)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : Y₁ →[M] X where
  toFun := g
  map_smul' m x :=
    calc
      g (m • x) = g (m • f (g x)) := by rw [h₂]
      _ = g (f (m • g x)) := by simp only [map_smul]
      _ = m • g x := by rw [h₁]


/-- The inverse of a bijective equivariant map is equivariant. -/
@[to_additive (attr := simps) /-- The inverse of a bijective equivariant map is equivariant. -/]
def inverse' (f : X →ₑ[φ] Y) (g : Y → X) (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    Y →ₑ[φ'] X where
  toFun := g
  map_smul' m x :=
    calc
      g (m • x) = g (m • f (g x)) := by rw [h₂]
      _ = g ((φ (φ' m)) • f (g x)) := by rw [k]
      _ = g (f (φ' m • g x)) := by rw [map_smulₛₗ]
      _ = φ' m • g x := by rw [h₁]

@[to_additive]
lemma inverse_eq_inverse' (f : X →[M] Y₁) (g : Y₁ → X)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    inverse f g h₁ h₂ = inverse' f g (congrFun rfl) h₁ h₂ := by
  rfl

@[to_additive]
theorem inverse'_inverse'
    {f : X →ₑ[φ] Y} {g : Y → X}
    {k₁ : Function.LeftInverse φ' φ} {k₂ : Function.RightInverse φ' φ}
    {h₁ : Function.LeftInverse g f} {h₂ : Function.RightInverse g f} :
    inverse' (inverse' f g k₂ h₁ h₂) f k₁ h₂ h₁ = f :=
  ext fun _ => rfl

@[to_additive]
theorem comp_inverse' {f : X →ₑ[φ] Y} {g : Y → X}
    {k₁ : Function.LeftInverse φ' φ} {k₂ : Function.RightInverse φ' φ}
    {h₁ : Function.LeftInverse g f} {h₂ : Function.RightInverse g f} :
    (inverse' f g k₂ h₁ h₂).comp f (κ := CompTriple.comp_inv k₁) = MulActionHom.id M := by
  ext
  simpa using h₁.eq _

@[to_additive]
theorem inverse'_comp {f : X →ₑ[φ] Y} {g : Y → X}
    {k₂ : Function.RightInverse φ' φ}
    {h₁ : Function.LeftInverse g f} {h₂ : Function.RightInverse g f} :
    f.comp (inverse' f g k₂ h₁ h₂) (κ := CompTriple.comp_inv k₂) = MulActionHom.id N := by
  ext
  simpa using h₂.eq _

/-- If actions of `M` and `N` on `α` commute,
  then for `c : M`, `(c • · : α → α)` is an `N`-action homomorphism. -/
@[to_additive (attr := simps) /-- If additive actions of `M` and `N` on `α` commute,
  then for `c : M`, `(c • · : α → α)` is an `N`-additive action homomorphism. -/]
def _root_.SMulCommClass.toMulActionHom {M} (N α : Type*)
    [SMul M α] [SMul N α] [SMulCommClass M N α] (c : M) :
    α →[N] α where
  toFun := (c • ·)
  map_smul' := smul_comm _

end MulActionHom

end MulActionHom

/-- Evaluation at a point as a `MulActionHom`. -/
@[to_additive (attr := simps) /-- Evaluation at a point as an `AddActionHom`. -/]
def Pi.evalMulActionHom {ι M : Type*} {X : ι → Type*} [∀ i, SMul M (X i)] (i : ι) :
    (∀ i, X i) →[M] X i where
  toFun := Function.eval i
  map_smul' _ _ := rfl

namespace MulActionHom

section FstSnd

variable {M α β : Type*} [SMul M α] [SMul M β]

variable (M α β) in
/-- `Prod.fst` as a bundled `MulActionHom`. -/
@[to_additive (attr := simps -fullyApplied) /-- `Prod.fst` as a bundled `AddActionHom`. -/]
def fst : α × β →[M] α where
  toFun := Prod.fst
  map_smul' _ _ := rfl

variable (M α β) in
/-- `Prod.snd` as a bundled `MulActionHom`. -/
@[to_additive (attr := simps -fullyApplied) /-- `Prod.snd` as a bundled `AddActionHom`. -/]
def snd : α × β →[M] β where
  toFun := Prod.snd
  map_smul' _ _ := rfl

end FstSnd

variable {M N α β γ δ : Type*} [SMul M α] [SMul M β] [SMul N γ] [SMul N δ] {σ : M → N}

/-- If `f` and `g` are equivariant maps, then so is `x ↦ (f x, g x)`. -/
@[to_additive (attr := simps -fullyApplied) prod
  /-- If `f` and `g` are equivariant maps, then so is `x ↦ (f x, g x)`. -/]
def prod (f : α →ₑ[σ] γ) (g : α →ₑ[σ] δ) : α →ₑ[σ] γ × δ where
  toFun x := (f x, g x)
  map_smul' _ _ := Prod.ext (map_smulₛₗ f _ _) (map_smulₛₗ g _ _)

@[to_additive (attr := simp) fst_comp_prod]
lemma fst_comp_prod (f : α →ₑ[σ] γ) (g : α →ₑ[σ] δ) : (fst _ _ _).comp (prod f g) = f := rfl

@[to_additive (attr := simp) snd_comp_prod]
lemma snd_comp_prod (f : α →ₑ[σ] γ) (g : α →ₑ[σ] δ) : (snd _ _ _).comp (prod f g) = g := rfl

@[to_additive (attr := simp) prod_fst_snd]
lemma prod_fst_snd : prod (fst M α β) (snd M α β) = .id .. := rfl

/-- If `f` and `g` are equivariant maps, then so is `(x, y) ↦ (f x, g y)`. -/
@[to_additive (attr := simps -fullyApplied) prodMap
  /-- If `f` and `g` are equivariant maps, then so is `(x, y) ↦ (f x, g y)`. -/]
def prodMap (f : α →ₑ[σ] γ) (g : β →ₑ[σ] δ) : α × β →ₑ[σ] γ × δ where
  toFun := Prod.map f g
  __ := (f.comp (fst ..)).prod (g.comp (snd ..))

end MulActionHom

namespace MulActionHom

section

variable {R M N X Y : Type*} {σ : M → N}

attribute [local simp] map_smulₛₗ smul_sub

@[to_additive]
instance [SMul M X] [SMul N Y] [SMul R Y] [SMulCommClass N R Y] :
    SMul R (X →ₑ[σ] Y) where
  smul h f := ⟨h • f, by simp [smul_comm _ h]⟩

instance [SMul M X] [SMul N Y] [SMul R Y] [SMulCommClass N R Y] :
    FunLikeSMul R (X →ₑ[σ] Y) X Y where
  smul_apply _ _ _ := rfl

instance [SMul M X] [SMul N Y] [SMul ℕ Y] [SMulCommClass ℕ N Y] :
    SMul ℕ (X →ₑ[σ] Y) where
  smul h f := ⟨h • f, by simp [smul_comm]⟩

instance [SMul M X] [SMul N Y] [SMul ℕ Y] [SMulCommClass ℕ N Y] :
    FunLikeSMul ℕ (X →ₑ[σ] Y) X Y where
  smul_apply _ _ _ := rfl

/-@[to_additive (attr := simp, norm_cast)]
lemma coe_smul [SMul M X] [SMul N Y] [SMul R Y] [SMulCommClass N R Y] (f : X →ₑ[σ] Y) (r : R) :
    ⇑(r • f) = r • ⇑f := rfl-/

instance [SMul M X] [Zero Y] [SMulZeroClass N Y] :
    Zero (X →ₑ[σ] Y) where
  zero := ⟨0, by simp⟩

instance [SMul M X] [Zero Y] [SMulZeroClass N Y] : FunLikeZero (X →ₑ[σ] Y) X Y where
  zero_apply _ := rfl

/-@[simp, norm_cast]
lemma coe_zero [SMul M X] [Zero Y] [SMulZeroClass N Y] : ⇑(0 : X →ₑ[σ] Y) = 0 := rfl-/

instance [SMul M X] [AddZeroClass Y] [DistribSMul N Y] :
    AddZeroClass (X →ₑ[σ] Y) where
  add f g := ⟨f + g, by simp [smul_add]⟩
  zero_add _ := ext fun _ ↦ zero_add _
  add_zero _ := ext fun _ ↦ add_zero _

@[simp, norm_cast]
lemma coe_add [SMul M X] [AddZeroClass Y] [DistribSMul N Y] (f g : X →ₑ[σ] Y) :
    ⇑(f + g) = ⇑f + ⇑g := rfl

instance [SMul M X] [AddMonoid Y] [DistribSMul N Y] :
    AddMonoid (X →ₑ[σ] Y) where
  add_assoc _ _ _ := ext fun _ ↦ add_assoc _ _ _
  nsmul n f := n • f
  nsmul_zero f := ext fun x ↦ AddMonoid.nsmul_zero (f x)
  nsmul_succ n f := ext fun x ↦ AddMonoid.nsmul_succ n (f x)

instance [SMul M X] [AddCommMonoid Y] [DistribSMul N Y] :
    AddCommMonoid (X →ₑ[σ] Y) where
  add_comm _ _ := ext fun _ ↦ add_comm _ _

@[to_additive]
instance [SMul M X] [SMul N Y] [Monoid R] [MulAction R Y] [SMulCommClass N R Y] :
    MulAction R (X →ₑ[σ] Y) where
  one_smul _ := ext fun _ ↦ one_smul _ _
  mul_smul _ _ _ := ext fun _ ↦ mul_smul _ _ _

instance [AddZeroClass Y] [SMul M X] [DistribSMul N Y] [DistribSMul R Y] [SMulCommClass N R Y] :
    DistribSMul R (X →ₑ[σ] Y) where
  smul_zero y := ext fun _ ↦ smul_zero y
  smul_add y _ _ := ext fun _ ↦ smul_add y _ _

instance [AddMonoid Y] [Monoid R] [SMul M X] [DistribSMul N Y]
    [DistribMulAction R Y] [SMulCommClass N R Y] :
    DistribMulAction R (X →ₑ[σ] Y) where
  __ := inferInstanceAs (MulAction _ _)
  __ := inferInstanceAs (DistribSMul _ _)

instance [AddCommMonoid Y] [Semiring R] [SMul M X] [DistribSMul N Y]
    [Module R Y] [SMulCommClass N R Y] :
    Module R (X →ₑ[σ] Y) where
  add_smul _ _ _ := ext fun _ ↦ add_smul _ _ _
  zero_smul _ := ext fun _ ↦ zero_smul R _

instance [SMul M X] [AddGroup Y] [DistribSMul N Y] : AddGroup (X →ₑ[σ] Y) where
  sub f g := ⟨f - g, by simp [smul_sub]⟩
  neg f := ⟨-f, by simp⟩
  neg_add_cancel f := ext fun _ ↦ neg_add_cancel _
  sub_eq_add_neg _ _ := ext fun _ ↦ sub_eq_add_neg _ _
  zsmul z f := z • f
  zsmul_zero' f := ext fun x ↦ SubNegMonoid.zsmul_zero' _
  zsmul_neg' _ _ := ext fun x ↦ SubNegMonoid.zsmul_neg' _ _
  zsmul_succ' _ _ := ext fun x ↦ SubNegMonoid.zsmul_succ' _ _

@[simp, norm_cast]
lemma coe_neg [SMul M X] [AddGroup Y] [DistribSMul N Y] (f : X →ₑ[σ] Y) :
    ⇑(-f) = -⇑f := rfl

@[simp, norm_cast]
lemma coe_sub [SMul M X] [AddGroup Y] [DistribSMul N Y] (f g : X →ₑ[σ] Y) :
    ⇑(f - g) = ⇑f - ⇑g := rfl

instance [SMul M X] [AddCommGroup Y] [DistribSMul N Y] : AddCommGroup (X →ₑ[σ] Y) where

instance [SMul M X] [Monoid N] [Monoid Y] [MulDistribMulAction N Y] :
    Monoid (X →ₑ[σ] Y) where
  mul f g := ⟨f * g, by simp⟩
  mul_assoc _ _ _ := ext fun x ↦ mul_assoc _ _ _
  one := ⟨1, by simp⟩
  one_mul _ := ext fun x ↦ one_mul _
  mul_one _ := ext fun x ↦ mul_one _

@[simp, norm_cast]
lemma coe_mul [SMul M X] [Monoid N] [Monoid Y] [MulDistribMulAction N Y] (f g : X →ₑ[σ] Y) :
    ⇑(f * g) = ⇑f * ⇑g := rfl

@[simp, norm_cast]
lemma coe_one [SMul M X] [Monoid N] [Monoid Y] [MulDistribMulAction N Y] :
    ⇑(1 : X →ₑ[σ] Y) = 1 := rfl

instance [SMul M X] [Monoid N] [CommMonoid Y] [MulDistribMulAction N Y] :
    CommMonoid (X →ₑ[σ] Y) where
  mul_comm _ _ := ext fun _ ↦ mul_comm _ _

instance [SMul M X] [Monoid N] [Semiring Y] [MulSemiringAction N Y] :
    Semiring (X →ₑ[σ] Y) where
  __ := inferInstanceAs (Monoid _)
  __ := inferInstanceAs (AddCommMonoid _)
  zero_mul _ := ext fun x ↦ zero_mul _
  mul_zero _ := ext fun x ↦ mul_zero _
  left_distrib _ _ _ := ext fun x ↦ left_distrib _ _ _
  right_distrib _ _ _ := ext fun x ↦ right_distrib _ _ _

instance [SMul M X] [Monoid N] [CommSemiring Y] [MulSemiringAction N Y] :
    CommSemiring (X →ₑ[σ] Y) where

instance [SMul M X] [Monoid N] [Ring Y] [MulSemiringAction N Y] :
    Ring (X →ₑ[σ] Y) where

instance [SMul M X] [Monoid N] [CommRing Y] [MulSemiringAction N Y] :
    CommRing (X →ₑ[σ] Y) where

end

end MulActionHom

section DistribMulAction

variable {M : Type*} [Monoid M]
variable {N : Type*} [Monoid N]
variable {P : Type*} [Monoid P]
variable (φ : M →* N) (φ' : N →* M) (ψ : N →* P) (χ : M →* P)
variable (A : Type*) [AddMonoid A] [DistribMulAction M A]
variable (B : Type*) [AddMonoid B] [DistribMulAction N B]
variable (B₁ : Type*) [AddMonoid B₁] [DistribMulAction M B₁]
variable (C : Type*) [AddMonoid C] [DistribMulAction P C]

variable (A' : Type*) [AddGroup A'] [DistribMulAction M A']
variable (B' : Type*) [AddGroup B'] [DistribMulAction N B']

/-- Equivariant additive monoid homomorphisms. -/
structure DistribMulActionHom extends A →ₑ[φ] B, A →+ B

/-- Reinterpret an equivariant additive monoid homomorphism as an additive monoid homomorphism. -/
add_decl_doc DistribMulActionHom.toAddMonoidHom

/-- Reinterpret an equivariant additive monoid homomorphism as an equivariant function. -/
add_decl_doc DistribMulActionHom.toMulActionHom

@[inherit_doc]
notation:25 (name := «DistribMulActionHomLocal≺»)
  A " →ₑ+[" φ:25 "] " B:0 => DistribMulActionHom φ A B

@[inherit_doc]
notation:25 (name := «DistribMulActionHomIdLocal≺»)
  A " →+[" M:25 "] " B:0 => DistribMulActionHom (MonoidHom.id M) A B

-- QUESTION/TODO : Impose that `φ` is a morphism of monoids?

/-- `DistribMulActionSemiHomClass F φ A B` states that `F` is a type of morphisms
  preserving the additive monoid structure and equivariant with respect to `φ`.
    You should extend this class when you extend `DistribMulActionSemiHom`. -/
class DistribMulActionSemiHomClass (F : Type*)
    {M N : outParam Type*} (φ : outParam (M → N))
    (A B : outParam Type*)
    [Monoid M] [Monoid N]
    [AddMonoid A] [AddMonoid B] [DistribMulAction M A] [DistribMulAction N B]
    [FunLike F A B] : Prop
    extends MulActionSemiHomClass F φ A B, AddMonoidHomClass F A B

/-- `DistribMulActionHomClass F M A B` states that `F` is a type of morphisms preserving
  the additive monoid structure and equivariant with respect to the action of `M`.
    It is an abbreviation to `DistribMulActionHomClass F (MonoidHom.id M) A B`
You should extend this class when you extend `DistribMulActionHom`. -/
abbrev DistribMulActionHomClass (F : Type*) (M : outParam Type*)
    (A B : outParam Type*) [Monoid M] [AddMonoid A] [AddMonoid B]
    [DistribMulAction M A] [DistribMulAction M B] [FunLike F A B] :=
    DistribMulActionSemiHomClass F (MonoidHom.id M) A B

namespace DistribMulActionHom

instance : FunLike (A →ₑ+[φ] B) A B where
  coe m := m.toFun
  coe_injective' f g h := by
    rcases f with ⟨tF, _, _⟩; rcases g with ⟨tG, _, _⟩
    cases tF; cases tG; congr

instance : DistribMulActionSemiHomClass (A →ₑ+[φ] B) φ A B where
  map_smulₛₗ m := m.map_smul'
  map_zero := DistribMulActionHom.map_zero'
  map_add := DistribMulActionHom.map_add'

variable {φ φ' A B B₁}
variable {F : Type*} [FunLike F A B]

/-- Turn an element of a type `F` satisfying `MulActionHomClass F M X Y` into an actual
`MulActionHom`. This is declared as the default coercion from `F` to `MulActionHom M X Y`. -/
@[coe]
def _root_.DistribMulActionSemiHomClass.toDistribMulActionHom
    [DistribMulActionSemiHomClass F φ A B]
    (f : F) : A →ₑ+[φ] B :=
  { (f : A →+ B), (f : A →ₑ[φ] B) with }

/-- Any type satisfying `MulActionHomClass` can be cast into `MulActionHom`
via `MulActionHomClass.toMulActionHom`. -/
instance [DistribMulActionSemiHomClass F φ A B] : CoeTC F (A →ₑ+[φ] B) :=
  ⟨DistribMulActionSemiHomClass.toDistribMulActionHom⟩

/-- If `DistribMulAction` of `M` and `N` on `A` commute,
then for each `c : M`, `(c • ·)` is an `N`-action additive homomorphism. -/
@[simps]
def _root_.SMulCommClass.toDistribMulActionHom {M} (N A : Type*) [Monoid N] [AddMonoid A]
    [DistribSMul M A] [DistribMulAction N A] [SMulCommClass M N A] (c : M) : A →+[N] A :=
  { SMulCommClass.toMulActionHom N A c,
    DistribSMul.toAddMonoidHom _ c with
    toFun := (c • ·) }

@[simp]
theorem toFun_eq_coe (f : A →ₑ+[φ] B) : f.toFun = f := rfl

@[norm_cast]
theorem coe_fn_coe (f : A →ₑ+[φ] B) : ⇑(f : A →+ B) = f :=
  rfl

@[norm_cast]
theorem coe_fn_coe' (f : A →ₑ+[φ] B) : ⇑(f : A →ₑ[φ] B) = f :=
  rfl

@[ext]
theorem ext {f g : A →ₑ+[φ] B} : (∀ x, f x = g x) → f = g :=
  DFunLike.ext f g

protected theorem congr_fun {f g : A →ₑ+[φ] B} (h : f = g) (x : A) : f x = g x :=
  DFunLike.congr_fun h _

theorem toMulActionHom_injective {f g : A →ₑ+[φ] B} (h : (f : A →ₑ[φ] B) = (g : A →ₑ[φ] B)) :
    f = g := by
  ext a
  exact MulActionHom.congr_fun h a

theorem toAddMonoidHom_injective {f g : A →ₑ+[φ] B} (h : (f : A →+ B) = (g : A →+ B)) : f = g := by
  ext a
  exact DFunLike.congr_fun h a

protected theorem map_zero (f : A →ₑ+[φ] B) : f 0 = 0 :=
  map_zero f

protected theorem map_add (f : A →ₑ+[φ] B) (x y : A) : f (x + y) = f x + f y :=
  map_add f x y

protected theorem map_neg (f : A' →ₑ+[φ] B') (x : A') : f (-x) = -f x :=
  map_neg f x

protected theorem map_sub (f : A' →ₑ+[φ] B') (x y : A') : f (x - y) = f x - f y :=
  map_sub f x y

protected theorem map_smulₑ (f : A →ₑ+[φ] B) (m : M) (x : A) : f (m • x) = (φ m) • f x :=
  map_smulₛₗ f m x

variable (M)

/-- The identity map as an equivariant additive monoid homomorphism. -/
protected def id : A →+[M] A :=
  ⟨MulActionHom.id _, rfl, fun _ _ => rfl⟩

@[simp]
theorem id_apply (x : A) : DistribMulActionHom.id M x = x := by
  rfl

variable {M C ψ χ}

instance : Zero (A →ₑ+[φ] B) :=
  ⟨{ (0 : A →+ B) with map_smul' := fun m _ => by simp }⟩

instance : One (A →+[M] A) :=
  ⟨DistribMulActionHom.id M⟩

@[simp]
theorem coe_zero : ⇑(0 : A →ₑ+[φ] B) = 0 :=
  rfl

@[simp]
theorem coe_one : ⇑(1 : A →+[M] A) = id :=
  rfl

theorem zero_apply (a : A) : (0 : A →ₑ+[φ] B) a = 0 :=
  rfl

theorem one_apply (a : A) : (1 : A →+[M] A) a = a :=
  rfl

instance : Inhabited (A →ₑ+[φ] B) :=
  ⟨0⟩

/-- Composition of two equivariant additive monoid homomorphisms. -/
def comp (g : B →ₑ+[ψ] C) (f : A →ₑ+[φ] B) [κ : MonoidHom.CompTriple φ ψ χ] :
    A →ₑ+[χ] C :=
  { MulActionHom.comp (g : B →ₑ[ψ] C) (f : A →ₑ[φ] B),
    AddMonoidHom.comp (g : B →+ C) (f : A →+ B) with }

@[simp]
theorem comp_apply
    (g : B →ₑ+[ψ] C) (f : A →ₑ+[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A) : g.comp f x = g (f x) :=
  rfl

@[simp]
theorem id_comp (f : A →ₑ+[φ] B) : comp (DistribMulActionHom.id N) f = f :=
  ext fun x => by rw [comp_apply, id_apply]

@[simp]
theorem comp_id (f : A →ₑ+[φ] B) : f.comp (DistribMulActionHom.id M) = f :=
  ext fun x => by rw [comp_apply, id_apply]

@[simp]
theorem comp_assoc {Q D : Type*} [Monoid Q] [AddMonoid D] [DistribMulAction Q D]
    {η : P →* Q} {θ : M →* Q} {ζ : N →* Q}
    (h : C →ₑ+[η] D) (g : B →ₑ+[ψ] C) (f : A →ₑ+[φ] B)
    [MonoidHom.CompTriple φ ψ χ] [MonoidHom.CompTriple χ η θ]
    [MonoidHom.CompTriple ψ η ζ] [MonoidHom.CompTriple φ ζ θ] :
    h.comp (g.comp f) = (h.comp g).comp f :=
  ext fun _ => rfl

/-- The inverse of a bijective `DistribMulActionHom` is a `DistribMulActionHom`. -/
@[simps]
def inverse (f : A →+[M] B₁) (g : B₁ → A) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : B₁ →+[M] A :=
  { (f : A →+ B₁).inverse g h₁ h₂, f.toMulActionHom.inverse g h₁ h₂ with toFun := g }

section Semiring

variable (R : Type*) [Semiring R] [MulSemiringAction M R]
variable (S : Type*) [Semiring S] [MulSemiringAction N S]
variable (T : Type*) [Semiring T] [MulSemiringAction P T]

variable {R S N'}
variable [AddMonoid N'] [DistribMulAction S N']

variable {σ : R →* S}
@[ext]
theorem ext_ring {f g : R →ₑ+[σ] N'} (h : f 1 = g 1) : f = g := by
  ext x
  rw [← mul_one x, ← smul_eq_mul, f.map_smulₑ, g.map_smulₑ, h]

end Semiring

end DistribMulActionHom

variable (R : Type*) [Semiring R] [MulSemiringAction M R]
variable (R' : Type*) [Ring R'] [MulSemiringAction M R']
variable (S : Type*) [Semiring S] [MulSemiringAction N S]
variable (S' : Type*) [Ring S'] [MulSemiringAction N S']
variable (T : Type*) [Semiring T] [MulSemiringAction P T]

/-- Equivariant ring homomorphisms. -/
structure MulSemiringActionHom extends R →ₑ+[φ] S, R →+* S

/-- Reinterpret an equivariant ring homomorphism as a ring homomorphism. -/
add_decl_doc MulSemiringActionHom.toRingHom

/-- Reinterpret an equivariant ring homomorphism as an equivariant additive monoid homomorphism. -/
add_decl_doc MulSemiringActionHom.toDistribMulActionHom

@[inherit_doc]
notation:25 (name := «MulSemiringActionHomLocal≺»)
  R " →ₑ+*[" φ:25 "] " S:0 => MulSemiringActionHom φ R S

@[inherit_doc]
notation:25 (name := «MulSemiringActionHomIdLocal≺»)
  R " →+*[" M:25 "] " S:0 => MulSemiringActionHom (MonoidHom.id M) R S

/-- `MulSemiringActionHomClass F φ R S` states that `F` is a type of morphisms preserving
the ring structure and equivariant with respect to `φ`.

You should extend this class when you extend `MulSemiringActionHom`. -/
class MulSemiringActionSemiHomClass (F : Type*)
    {M N : outParam Type*} [Monoid M] [Monoid N]
    (φ : outParam (M → N))
    (R S : outParam Type*) [Semiring R] [Semiring S]
    [DistribMulAction M R] [DistribMulAction N S] [FunLike F R S] : Prop
    extends DistribMulActionSemiHomClass F φ R S, RingHomClass F R S

/-- `MulSemiringActionHomClass F M R S` states that `F` is a type of morphisms preserving
the ring structure and equivariant with respect to a `DistribMulAction` of `M` on `R` and `S`.
-/
abbrev MulSemiringActionHomClass
    (F : Type*)
    {M : outParam Type*} [Monoid M]
    (R S : outParam Type*) [Semiring R] [Semiring S]
    [DistribMulAction M R] [DistribMulAction M S] [FunLike F R S] :=
  MulSemiringActionSemiHomClass F (MonoidHom.id M) R S

namespace MulSemiringActionHom

instance : FunLike (R →ₑ+*[φ] S) R S where
  coe m := m.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨tF, _, _⟩, _, _⟩; rcases g with ⟨⟨tG, _, _⟩, _, _⟩
    cases tF; cases tG; congr

instance : MulSemiringActionSemiHomClass (R →ₑ+*[φ] S) φ R S where
  map_zero m := m.map_zero'
  map_add m := m.map_add'
  map_one := MulSemiringActionHom.map_one'
  map_mul := MulSemiringActionHom.map_mul'
  map_smulₛₗ m := m.map_smul'

variable {φ R S}
variable {F : Type*} [FunLike F R S]

/-- Turn an element of a type `F` satisfying `MulSemiringActionHomClass F M R S` into an actual
`MulSemiringActionHom`. This is declared as the default coercion from `F` to
`MulSemiringActionHom M X Y`. -/
@[coe]
def _root_.MulSemiringActionHomClass.toMulSemiringActionHom
    [MulSemiringActionSemiHomClass F φ R S]
    (f : F) : R →ₑ+*[φ] S :=
  { (f : R →+* S), (f : R →ₑ+[φ] S) with }

/-- Any type satisfying `MulSemiringActionHomClass` can be cast into `MulSemiringActionHom` via
  `MulSemiringActionHomClass.toMulSemiringActionHom`. -/
instance [MulSemiringActionSemiHomClass F φ R S] :
    CoeTC F (R →ₑ+*[φ] S) :=
  ⟨MulSemiringActionHomClass.toMulSemiringActionHom⟩

@[norm_cast]
theorem coe_fn_coe (f : R →ₑ+*[φ] S) : ⇑(f : R →+* S) = f :=
  rfl

@[norm_cast]
theorem coe_fn_coe' (f : R →ₑ+*[φ] S) : ⇑(f : R →ₑ+[φ] S) = f :=
  rfl

@[ext]
theorem ext {f g : R →ₑ+*[φ] S} : (∀ x, f x = g x) → f = g :=
  DFunLike.ext f g

protected theorem map_zero (f : R →ₑ+*[φ] S) : f 0 = 0 :=
  map_zero f

protected theorem map_add (f : R →ₑ+*[φ] S) (x y : R) : f (x + y) = f x + f y :=
  map_add f x y

protected theorem map_neg (f : R' →ₑ+*[φ] S') (x : R') : f (-x) = -f x :=
  map_neg f x

protected theorem map_sub (f : R' →ₑ+*[φ] S') (x y : R') : f (x - y) = f x - f y :=
  map_sub f x y

protected theorem map_one (f : R →ₑ+*[φ] S) : f 1 = 1 :=
  map_one f

protected theorem map_mul (f : R →ₑ+*[φ] S) (x y : R) : f (x * y) = f x * f y :=
  map_mul f x y

protected theorem map_smulₛₗ (f : R →ₑ+*[φ] S) (m : M) (x : R) : f (m • x) = φ m • f x :=
  map_smulₛₗ f m x

protected theorem map_smul [MulSemiringAction M S] (f : R →+*[M] S) (m : M) (x : R) :
    f (m • x) = m • f x :=
  map_smulₛₗ f m x

end MulSemiringActionHom

namespace MulSemiringActionHom

variable (M) {R}

/-- The identity map as an equivariant ring homomorphism. -/
protected def id : R →+*[M] R :=
  ⟨DistribMulActionHom.id _, rfl, (fun _ _ => rfl)⟩

@[simp]
theorem id_apply (x : R) : MulSemiringActionHom.id M x = x :=
  rfl


end MulSemiringActionHom

namespace MulSemiringActionHom
open MulSemiringActionHom

variable {R S T}

variable {φ φ' ψ χ}

/-- Composition of two equivariant additive ring homomorphisms. -/
def comp (g : S →ₑ+*[ψ] T) (f : R →ₑ+*[φ] S) [κ : MonoidHom.CompTriple φ ψ χ] : R →ₑ+*[χ] T :=
  { DistribMulActionHom.comp (g : S →ₑ+[ψ] T) (f : R →ₑ+[φ] S),
    RingHom.comp (g : S →+* T) (f : R →+* S) with }

@[simp]
theorem comp_apply (g : S →ₑ+*[ψ] T) (f : R →ₑ+*[φ] S) [MonoidHom.CompTriple φ ψ χ] (x : R) :
    g.comp f x = g (f x) := rfl

@[simp]
theorem id_comp (f : R →ₑ+*[φ] S) : (MulSemiringActionHom.id N).comp f = f :=
  ext fun x => by rw [comp_apply, id_apply]

@[simp]
theorem comp_id (f : R →ₑ+*[φ] S) : f.comp (MulSemiringActionHom.id M) = f :=
  ext fun x => by rw [comp_apply, id_apply]

/-- The inverse of a bijective `MulSemiringActionHom` is a `MulSemiringActionHom`. -/
@[simps]
def inverse' (f : R →ₑ+*[φ] S) (g : S → R) (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    S →ₑ+*[φ'] R :=
  { (f : R →+ S).inverse g h₁ h₂,
    (f : R →* S).inverse g h₁ h₂,
    (f : R →ₑ[φ] S).inverse' g k h₁ h₂ with
    toFun := g }

/-- The inverse of a bijective `MulSemiringActionHom` is a `MulSemiringActionHom`. -/
@[simps]
def inverse {S₁ : Type*} [Semiring S₁] [MulSemiringAction M S₁]
    (f : R →+*[M] S₁) (g : S₁ → R)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    S₁ →+*[M] R :=
  { (f : R →+ S₁).inverse g h₁ h₂,
    (f : R →* S₁).inverse g h₁ h₂,
    f.toMulActionHom.inverse g h₁ h₂ with
    toFun := g }

end MulSemiringActionHom

end DistribMulAction

lemma IsSMulRegular.of_injective {R M : Type*} [SMul R M]
    {N F} [SMul R N] [FunLike F M N] [MulActionHomClass F R M N]
    (f : F) {r : R} (h1 : Function.Injective f) (h2 : IsSMulRegular N r) :
    IsSMulRegular M r := fun x y h3 => h1 <| h2 <|
  (map_smulₛₗ f r x).symm.trans ((congrArg f h3).trans (map_smulₛₗ f r y))
