/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.BigOperators.Multiset.Basic
import Mathlib.Data.FunLike.Basic

#align_import algebra.hom.freiman from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-!
# Freiman homomorphisms

In this file, we define Freiman homomorphisms. An `n`-Freiman homomorphism on `A` is a function
`f : α → β` such that `f (x₁) * ... * f (xₙ) = f (y₁) * ... * f (yₙ)` for all
`x₁, ..., xₙ, y₁, ..., yₙ ∈ A` such that `x₁ * ... * xₙ = y₁ * ... * yₙ`. In particular, any
`MulHom` is a Freiman homomorphism.

They are of interest in additive combinatorics.

## Main declaration

* `FreimanHom`: Freiman homomorphism.
* `AddFreimanHom`: Additive Freiman homomorphism.

## Notation

* `A →*[n] β`: Multiplicative `n`-Freiman homomorphism on `A`
* `A →+[n] β`: Additive `n`-Freiman homomorphism on `A`

## Implementation notes

In the context of combinatorics, we are interested in Freiman homomorphisms over sets which are not
necessarily closed under addition/multiplication. This means we must parametrize them with a set in
an `AddMonoid`/`Monoid` instead of the `AddMonoid`/`Monoid` itself.

## References

[Yufei Zhao, *18.225: Graph Theory and Additive Combinatorics*](https://yufeizhao.com/gtac/)

## TODO

`MonoidHom.toFreimanHom` could be relaxed to `MulHom.toFreimanHom` by proving
`(s.map f).prod = (t.map f).prod` directly by induction instead of going through `f s.prod`.

Define `n`-Freiman isomorphisms.

Affine maps induce Freiman homs. Concretely, provide the `AddFreimanHomClass (α →ₐ[𝕜] β) A β n`
instance.
-/


open Multiset

variable {F α β γ δ G : Type*}

/-- An additive `n`-Freiman homomorphism is a map which preserves sums of `n` elements. -/
structure AddFreimanHom (A : Set α) (β : Type*) [AddCommMonoid α] [AddCommMonoid β] (n : ℕ) where
  /-- The underlying function. -/
  toFun : α → β
  /-- An additive `n`-Freiman homomorphism preserves sums of `n` elements. -/
  map_sum_eq_map_sum' {s t : Multiset α} (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A)
    (hs : Multiset.card s = n) (ht : Multiset.card t = n) (h : s.sum = t.sum) :
    (s.map toFun).sum = (t.map toFun).sum
#align add_freiman_hom AddFreimanHom

/-- An `n`-Freiman homomorphism on a set `A` is a map which preserves products of `n` elements. -/
@[to_additive AddFreimanHom]
structure FreimanHom (A : Set α) (β : Type*) [CommMonoid α] [CommMonoid β] (n : ℕ) where
  /-- The underlying function. -/
  toFun : α → β
  /-- An `n`-Freiman homomorphism preserves products of `n` elements. -/
  map_prod_eq_map_prod' {s t : Multiset α} (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A)
    (hs : Multiset.card s = n) (ht : Multiset.card t = n) (h : s.prod = t.prod) :
    (s.map toFun).prod = (t.map toFun).prod
#align freiman_hom FreimanHom

/- Porting note: local notation given a name, conflict with Algebra.Hom.GroupAction
 see https://github.com/leanprover/lean4/issues/2000 -/
@[inherit_doc]
notation:25 (name := «AddFreimanHomLocal≺») A " →+[" n:25 "] " β:0 => AddFreimanHom A β n

/- Porting note: local notation given a name, conflict with Algebra.Hom.GroupAction
 see https://github.com/leanprover/lean4/issues/2000 -/
@[inherit_doc]
notation:25 (name := «FreimanHomLocal≺») A " →*[" n:25 "] " β:0 => FreimanHom A β n

/-- `AddFreimanHomClass F A β n` states that `F` is a type of `n`-ary sums-preserving morphisms.
You should extend this class when you extend `AddFreimanHom`. -/
class AddFreimanHomClass (F : Type*) (A : outParam <| Set α) (β : outParam <| Type*)
  [AddCommMonoid α] [AddCommMonoid β] (n : ℕ) [FunLike F α β] : Prop where
  /-- An additive `n`-Freiman homomorphism preserves sums of `n` elements. -/
  map_sum_eq_map_sum' (f : F) {s t : Multiset α} (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A)
    (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A) (hs : Multiset.card s = n) (ht : Multiset.card t = n)
    (h : s.sum = t.sum) :
    (s.map f).sum = (t.map f).sum
#align add_freiman_hom_class AddFreimanHomClass

/-- `FreimanHomClass F A β n` states that `F` is a type of `n`-ary products-preserving morphisms.
You should extend this class when you extend `FreimanHom`. -/
@[to_additive AddFreimanHomClass
      "`AddFreimanHomClass F A β n` states that `F` is a type of `n`-ary
      sums-preserving morphisms. You should extend this class when you extend `AddFreimanHom`."]
class FreimanHomClass (F : Type*) (A : outParam <| Set α) (β : outParam <| Type*) [CommMonoid α]
  [CommMonoid β] (n : ℕ) [FunLike F α β] : Prop where
  /-- An `n`-Freiman homomorphism preserves products of `n` elements. -/
  map_prod_eq_map_prod' (f : F) {s t : Multiset α} (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A)
    (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A) (hs : Multiset.card s = n) (ht : Multiset.card t = n)
    (h : s.prod = t.prod) :
    (s.map f).prod = (t.map f).prod
#align freiman_hom_class FreimanHomClass

variable [FunLike F α β]

section CommMonoid

variable [CommMonoid α] [CommMonoid β] [CommMonoid γ] [CommMonoid δ] [CommGroup G] {A : Set α}
  {B : Set β} {C : Set γ} {n : ℕ} {a b c d : α}

/- porting note: inserted following def & instance for consistent coercion behaviour,
see also Algebra.Hom.Group for similar -/
/-- Turn an element of a type `F` satisfying `FreimanHomClass F A β n` into an actual
`FreimanHom`. This is declared as the default coercion from `F` to `FreimanHom A β n`. -/
@[to_additive (attr := coe)
    " Turn an element of a type `F` satisfying `AddFreimanHomClass F A β n` into an actual
    `AddFreimanHom`. This is declared as the default coercion from `F` to `AddFreimanHom A β n`."]
def _root_.FreimanHomClass.toFreimanHom [FreimanHomClass F A β n] (f : F) : A →*[n] β where
  toFun := DFunLike.coe f
  map_prod_eq_map_prod' := FreimanHomClass.map_prod_eq_map_prod' f

/-- Any type satisfying `SMulHomClass` can be cast into `MulActionHom` via
  `SMulHomClass.toMulActionHom`. -/
instance [FreimanHomClass F A β n] : CoeTC F (A →*[n] β) :=
  ⟨FreimanHomClass.toFreimanHom⟩


@[to_additive]
theorem map_prod_eq_map_prod [FreimanHomClass F A β n] (f : F) {s t : Multiset α}
    (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A)
    (hs : Multiset.card s = n) (ht : Multiset.card t = n)
    (h : s.prod = t.prod) : (s.map f).prod = (t.map f).prod :=
  FreimanHomClass.map_prod_eq_map_prod' f hsA htA hs ht h
#align map_prod_eq_map_prod map_prod_eq_map_prod
#align map_sum_eq_map_sum map_sum_eq_map_sum

@[to_additive]
theorem map_mul_map_eq_map_mul_map [FreimanHomClass F A β 2] (f : F) (ha : a ∈ A) (hb : b ∈ A)
    (hc : c ∈ A) (hd : d ∈ A) (h : a * b = c * d) : f a * f b = f c * f d := by
  simp_rw [← prod_pair] at h ⊢
  refine' map_prod_eq_map_prod f _ _ (card_pair _ _) (card_pair _ _) h <;> simp [ha, hb, hc, hd]
#align map_mul_map_eq_map_mul_map map_mul_map_eq_map_mul_map
#align map_add_map_eq_map_add_map map_add_map_eq_map_add_map

namespace FreimanHom

@[to_additive]
instance instFunLike : FunLike (A →*[n] β) α β where
  coe := toFun
  coe_injective' f g h := by cases f; cases g; congr
#align freiman_hom.fun_like FreimanHom.instFunLike
#align add_freiman_hom.fun_like AddFreimanHom.instFunLike

@[to_additive addFreimanHomClass]
instance freimanHomClass : FreimanHomClass (A →*[n] β) A β n where
  map_prod_eq_map_prod' := map_prod_eq_map_prod'
#align freiman_hom.freiman_hom_class FreimanHom.freimanHomClass
#align add_freiman_hom.freiman_hom_class AddFreimanHom.addFreimanHomClass

-- Porting note: not helpful in lean4
-- /-- Helper instance for when there's too many metavariables to apply `DFunLike.hasCoeToFun`
-- directly. -/
-- @[to_additive
--       "Helper instance for when there's too many metavariables to apply
--       `fun_like.has_coe_to_fun` directly."]
-- instance : CoeFun (A →*[n] β) fun _ => α → β :=
--   ⟨toFun⟩

initialize_simps_projections FreimanHom (toFun → apply)
initialize_simps_projections AddFreimanHom (toFun → apply)

@[to_additive (attr := simp)]
theorem toFun_eq_coe (f : A →*[n] β) : f.toFun = f :=
  rfl
#align freiman_hom.to_fun_eq_coe FreimanHom.toFun_eq_coe
#align add_freiman_hom.to_fun_eq_coe AddFreimanHom.toFun_eq_coe

@[to_additive (attr := ext)]
theorem ext ⦃f g : A →*[n] β⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h
#align freiman_hom.ext FreimanHom.ext
#align add_freiman_hom.ext AddFreimanHom.ext

@[to_additive (attr := simp)]
theorem coe_mk (f : α → β)
    (h :
      ∀ s t : Multiset α,
        (∀ ⦃x⦄, x ∈ s → x ∈ A) →
          (∀ ⦃x⦄, x ∈ t → x ∈ A) →
            Multiset.card s = n → Multiset.card t = n →
              s.prod = t.prod → (s.map f).prod = (t.map f).prod) :
    ⇑(mk f (h _ _)) = f :=
  rfl
#align freiman_hom.coe_mk FreimanHom.coe_mk
#align add_freiman_hom.coe_mk AddFreimanHom.coe_mk

@[to_additive (attr := simp)]
theorem mk_coe (f : A →*[n] β) (h) : mk f h = f :=
  ext fun _ => rfl
#align freiman_hom.mk_coe FreimanHom.mk_coe
#align add_freiman_hom.mk_coe AddFreimanHom.mk_coe

/-- The identity map from a commutative monoid to itself. -/
@[to_additive (attr := simps) "The identity map from an additive commutative monoid to itself."]
protected def id (A : Set α) (n : ℕ) : A →*[n] α where
  toFun x := x
  map_prod_eq_map_prod' _ _ _ _ h := by rw [map_id', map_id', h]
#align freiman_hom.id FreimanHom.id
#align add_freiman_hom.id AddFreimanHom.id
#align freiman_hom.id_apply FreimanHom.id_apply

/-- Composition of Freiman homomorphisms as a Freiman homomorphism. -/
@[to_additive "Composition of additive Freiman homomorphisms as an additive Freiman homomorphism."]
protected def comp (f : B →*[n] γ) (g : A →*[n] β) (hAB : A.MapsTo g B) : A →*[n] γ where
  toFun := f ∘ g
  map_prod_eq_map_prod' hsA htA hs ht h := by
    rw [← map_map, ← map_map]
    apply map_prod_eq_map_prod f _ _ ((card_map _ _).trans hs)
    · rwa [card_map]
    · apply (map_prod_eq_map_prod g hsA htA hs ht h)
    · simpa using fun a h => hAB (hsA h)
    · simpa using fun a h => hAB (htA h)
#align freiman_hom.comp FreimanHom.comp
#align add_freiman_hom.comp AddFreimanHom.comp

@[to_additive (attr := simp)]
theorem coe_comp (f : B →*[n] γ) (g : A →*[n] β) {hfg} : ⇑(f.comp g hfg) = f ∘ g :=
  rfl
#align freiman_hom.coe_comp FreimanHom.coe_comp
#align add_freiman_hom.coe_comp AddFreimanHom.coe_comp

@[to_additive]
theorem comp_apply (f : B →*[n] γ) (g : A →*[n] β) {hfg} (x : α) : f.comp g hfg x = f (g x) :=
  rfl
#align freiman_hom.comp_apply FreimanHom.comp_apply
#align add_freiman_hom.comp_apply AddFreimanHom.comp_apply

@[to_additive]
theorem comp_assoc (f : A →*[n] β) (g : B →*[n] γ) (h : C →*[n] δ) {hf hhg hgf}
    {hh : A.MapsTo (g.comp f hgf) C} : (h.comp g hhg).comp f hf = h.comp (g.comp f hgf) hh :=
  rfl
#align freiman_hom.comp_assoc FreimanHom.comp_assoc
#align add_freiman_hom.comp_assoc AddFreimanHom.comp_assoc

@[to_additive (attr := simp)]
theorem cancel_right {g₁ g₂ : B →*[n] γ} {f : A →*[n] β} (hf : Function.Surjective f) {hg₁ hg₂} :
    g₁.comp f hg₁ = g₂.comp f hg₂ ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun h => h ▸ rfl⟩
#align freiman_hom.cancel_right FreimanHom.cancel_right
#align add_freiman_hom.cancel_right AddFreimanHom.cancel_right

@[to_additive]
theorem cancel_right_on {g₁ g₂ : B →*[n] γ} {f : A →*[n] β} (hf : A.SurjOn f B) {hf'} :
    A.EqOn (g₁.comp f hf') (g₂.comp f hf') ↔ B.EqOn g₁ g₂ :=
  by simp [hf.cancel_right hf']
#align freiman_hom.cancel_right_on FreimanHom.cancel_right_on
#align add_freiman_hom.cancel_right_on AddFreimanHom.cancel_right_on

@[to_additive]
theorem cancel_left_on {g : B →*[n] γ} {f₁ f₂ : A →*[n] β} (hg : B.InjOn g) {hf₁ hf₂} :
    A.EqOn (g.comp f₁ hf₁) (g.comp f₂ hf₂) ↔ A.EqOn f₁ f₂ :=
  by simp [hg.cancel_left hf₁ hf₂]
#align freiman_hom.cancel_left_on FreimanHom.cancel_left_on
#align add_freiman_hom.cancel_left_on AddFreimanHom.cancel_left_on

@[to_additive (attr := simp)]
theorem comp_id (f : A →*[n] β) {hf} : f.comp (FreimanHom.id A n) hf = f :=
  ext fun _ => rfl
#align freiman_hom.comp_id FreimanHom.comp_id
#align add_freiman_hom.comp_id AddFreimanHom.comp_id

@[to_additive (attr := simp)]
theorem id_comp (f : A →*[n] β) {hf} : (FreimanHom.id B n).comp f hf = f :=
  ext fun _ => rfl
#align freiman_hom.id_comp FreimanHom.id_comp
#align add_freiman_hom.id_comp AddFreimanHom.id_comp

/-- `FreimanHom.const A n b` is the Freiman homomorphism sending everything to `b`. -/
@[to_additive "`AddFreimanHom.const An b` is the Freiman homomorphism sending everything to `b`."]
def const (A : Set α) (n : ℕ) (b : β) : A →*[n] β where
  toFun _ := b
  map_prod_eq_map_prod' _ _ hs ht _ := by
    simp only [map_const', hs, prod_replicate, ht]
#align freiman_hom.const FreimanHom.const
#align add_freiman_hom.const AddFreimanHom.const

@[to_additive (attr := simp)]
theorem const_apply (n : ℕ) (b : β) (x : α) : const A n b x = b :=
  rfl
#align freiman_hom.const_apply FreimanHom.const_apply
#align add_freiman_hom.const_apply AddFreimanHom.const_apply

@[to_additive (attr := simp)]
theorem const_comp (n : ℕ) (c : γ) (f : A →*[n] β) {hf} : (const B n c).comp f hf = const A n c :=
  rfl
#align freiman_hom.const_comp FreimanHom.const_comp
#align add_freiman_hom.const_comp AddFreimanHom.const_comp

/-- `1` is the Freiman homomorphism sending everything to `1`. -/
@[to_additive "`0` is the Freiman homomorphism sending everything to `0`."]
instance : One (A →*[n] β) :=
  ⟨const A n 1⟩

@[to_additive (attr := simp)]
theorem one_apply (x : α) : (1 : A →*[n] β) x = 1 :=
  rfl
#align freiman_hom.one_apply FreimanHom.one_apply
#align add_freiman_hom.zero_apply AddFreimanHom.zero_apply

@[to_additive (attr := simp)]
theorem one_comp (f : A →*[n] β) {hf} : (1 : B →*[n] γ).comp f hf = 1 :=
  rfl
#align freiman_hom.one_comp FreimanHom.one_comp
#align add_freiman_hom.zero_comp AddFreimanHom.zero_comp

@[to_additive]
instance : Inhabited (A →*[n] β) :=
  ⟨1⟩

/-- `f * g` is the Freiman homomorphism sends `x` to `f x * g x`. -/
@[to_additive "`f + g` is the Freiman homomorphism sending `x` to `f x + g x`."]
instance : Mul (A →*[n] β) :=
  ⟨fun f g =>
    { toFun := fun x => f x * g x
      map_prod_eq_map_prod' := fun hsA htA hs ht h => by
          rw [prod_map_mul, prod_map_mul]
          rw [map_prod_eq_map_prod f hsA htA hs ht h]
          rw [map_prod_eq_map_prod g hsA htA hs ht h]}⟩

@[to_additive (attr := simp)]
theorem mul_apply (f g : A →*[n] β) (x : α) : (f * g) x = f x * g x :=
  rfl
#align freiman_hom.mul_apply FreimanHom.mul_apply
#align add_freiman_hom.add_apply AddFreimanHom.add_apply

@[to_additive]
theorem mul_comp (g₁ g₂ : B →*[n] γ) (f : A →*[n] β) {hg hg₁ hg₂} :
    (g₁ * g₂).comp f hg = g₁.comp f hg₁ * g₂.comp f hg₂ :=
  rfl
#align freiman_hom.mul_comp FreimanHom.mul_comp
#align add_freiman_hom.add_comp AddFreimanHom.add_comp

/-- If `f` is a Freiman homomorphism to a commutative group, then `f⁻¹` is the Freiman homomorphism
sending `x` to `(f x)⁻¹`. -/
@[to_additive
      "If `f` is a Freiman homomorphism to an additive commutative group, then `-f` is the
      Freiman homomorphism sending `x` to `-f x`."]
instance : Inv (A →*[n] G) :=
  ⟨fun f =>
    { toFun := fun x => (f x)⁻¹
      map_prod_eq_map_prod' := fun hsA htA hs ht h => by
        rw [prod_map_inv, prod_map_inv, map_prod_eq_map_prod f hsA htA hs ht h] }⟩

@[to_additive (attr := simp)]
theorem inv_apply (f : A →*[n] G) (x : α) : f⁻¹ x = (f x)⁻¹ :=
  rfl
#align freiman_hom.inv_apply FreimanHom.inv_apply
#align add_freiman_hom.neg_apply AddFreimanHom.neg_apply

@[to_additive (attr := simp)]
theorem inv_comp (f : B →*[n] G) (g : A →*[n] β) {hf hf'} : f⁻¹.comp g hf = (f.comp g hf')⁻¹ :=
  ext fun _ => rfl
#align freiman_hom.inv_comp FreimanHom.inv_comp
#align add_freiman_hom.neg_comp AddFreimanHom.neg_comp

/-- If `f` and `g` are Freiman homomorphisms to a commutative group, then `f / g` is the Freiman
homomorphism sending `x` to `f x / g x`. -/
@[to_additive
      "If `f` and `g` are additive Freiman homomorphisms to an additive commutative group,
      then `f - g` is the additive Freiman homomorphism sending `x` to `f x - g x`"]
instance : Div (A →*[n] G) :=
  ⟨fun f g =>
    { toFun := fun x => f x / g x
      map_prod_eq_map_prod' := fun hsA htA hs ht h => by
        rw [prod_map_div, prod_map_div, map_prod_eq_map_prod f hsA htA hs ht h,
          map_prod_eq_map_prod g hsA htA hs ht h] }⟩

@[to_additive (attr := simp)]
theorem div_apply (f g : A →*[n] G) (x : α) : (f / g) x = f x / g x :=
  rfl
#align freiman_hom.div_apply FreimanHom.div_apply
#align add_freiman_hom.sub_apply AddFreimanHom.sub_apply

@[to_additive (attr := simp)]
theorem div_comp (f₁ f₂ : B →*[n] G) (g : A →*[n] β) {hf hf₁ hf₂} :
    (f₁ / f₂).comp g hf = f₁.comp g hf₁ / f₂.comp g hf₂ :=
  ext fun _ => rfl
#align freiman_hom.div_comp FreimanHom.div_comp
#align add_freiman_hom.sub_comp AddFreimanHom.sub_comp

/-! ### Instances -/


/-- `A →*[n] β` is a `CommMonoid`. -/
@[to_additive "`α →+[n] β` is an `AddCommMonoid`."]
instance commMonoid : CommMonoid (A →*[n] β) where
  mul_assoc a b c := by
    ext
    apply mul_assoc
  one_mul a := by
    ext
    apply one_mul
  mul_one a := by
    ext
    apply mul_one
  mul_comm a b := by
    ext
    apply mul_comm
#align freiman_hom.comm_monoid FreimanHom.commMonoid
#align add_freiman_hom.add_comm_monoid AddFreimanHom.addCommMonoid

/-- If `β` is a commutative group, then `A →*[n] β` is a commutative group too. -/
@[to_additive
      "If `β` is an additive commutative group, then `A →*[n] β` is an additive commutative
      group too."]
instance commGroup {β} [CommGroup β] : CommGroup (A →*[n] β) :=
  { FreimanHom.commMonoid with
    div_eq_mul_inv := by
      intros
      ext
      apply div_eq_mul_inv
    mul_left_inv := by
      intros
      ext
      apply mul_left_inv}
#align freiman_hom.comm_group FreimanHom.commGroup
#align add_freiman_hom.add_comm_group AddFreimanHom.addCommGroup

end FreimanHom

/-! ### Hom hierarchy -/


--TODO: change to `MonoidHomClass F A β → FreimanHomClass F A β n` once `map_multiset_prod` is
-- generalized
/-- A monoid homomorphism is naturally a `FreimanHom` on its entire domain.

We can't leave the domain `A : Set α` of the `FreimanHom` a free variable, since it wouldn't be
inferrable. -/
@[to_additive AddMonoidHom.addFreimanHomClass
      " An additive monoid homomorphism is naturally an `AddFreimanHom` on its entire
      domain.

      We can't leave the domain `A : Set α` of the `AddFreimanHom` a free variable, since it
      wouldn't be inferrable."]
instance MonoidHom.freimanHomClass : FreimanHomClass (α →* β) Set.univ β n where
  map_prod_eq_map_prod' f s t _ _ _ _ h := by
    rw [← f.map_multiset_prod, h, f.map_multiset_prod]
#align monoid_hom.freiman_hom_class MonoidHom.freimanHomClass
#align add_monoid_hom.freiman_hom_class AddMonoidHom.addFreimanHomClass

/-- A `MonoidHom` is naturally a `FreimanHom`. -/
@[to_additive AddMonoidHom.toAddFreimanHom
      "An `AddMonoidHom` is naturally an `AddFreimanHom`"]
def MonoidHom.toFreimanHom (A : Set α) (n : ℕ) (f : α →* β) : A →*[n] β where
  toFun := f
  map_prod_eq_map_prod' _ _ :=
    map_prod_eq_map_prod f (fun _ _ => Set.mem_univ _) fun _ _ => Set.mem_univ _
#align monoid_hom.to_freiman_hom MonoidHom.toFreimanHom
#align add_monoid_hom.to_add_freiman_hom AddMonoidHom.toAddFreimanHom

@[to_additive (attr := simp) toAddFreimanHom_coe]
theorem MonoidHom.toFreimanHom_coe (f : α →* β) : (f.toFreimanHom A n : α → β) = f :=
  rfl
#align monoid_hom.to_freiman_hom_coe MonoidHom.toFreimanHom_coe
#align add_monoid_hom.to_freiman_hom_coe AddMonoidHom.toAddFreimanHom_coe

@[to_additive AddMonoidHom.toAddFreimanHom_injective]
theorem MonoidHom.toFreimanHom_injective :
    Function.Injective (MonoidHom.toFreimanHom A n : (α →* β) → A →*[n] β) := fun f g h =>
   by rwa [toFreimanHom, toFreimanHom, FreimanHom.mk.injEq, DFunLike.coe_fn_eq] at h
#align monoid_hom.to_freiman_hom_injective MonoidHom.toFreimanHom_injective
#align add_monoid_hom.to_freiman_hom_injective AddMonoidHom.toAddFreimanHom_injective

end CommMonoid

section CancelCommMonoid

variable [CommMonoid α] [CancelCommMonoid β] {A : Set α} {m n : ℕ}

@[to_additive]
theorem map_prod_eq_map_prod_of_le [FreimanHomClass F A β n] (f : F) {s t : Multiset α}
    (hsA : ∀ x ∈ s, x ∈ A) (htA : ∀ x ∈ t, x ∈ A)
    (hs : Multiset.card s = m) (ht : Multiset.card t = m)
    (hst : s.prod = t.prod) (h : m ≤ n) : (s.map f).prod = (t.map f).prod := by
  obtain rfl | hm := m.eq_zero_or_pos
  · rw [card_eq_zero] at hs ht
    rw [hs, ht]
  simp? [← hs, card_pos_iff_exists_mem] at hm says
    simp only [← hs, gt_iff_lt, card_pos_iff_exists_mem] at hm
  obtain ⟨a, ha⟩ := hm
  suffices
    ((s + Multiset.replicate (n - m) a).map f).prod =
      ((t + Multiset.replicate (n - m) a).map f).prod by
    simp_rw [Multiset.map_add, prod_add] at this
    exact mul_right_cancel this
  replace ha := hsA _ ha
  apply map_prod_eq_map_prod f (A := A) (β := β) (n := n) (fun x hx => _) (fun x hx => _) _ _ _
  -- Porting note: below could be golfed when wlog is available
  · intro x hx
    rw [mem_add] at hx
    cases' hx with hx hx
    · exact hsA x hx
    · rwa [eq_of_mem_replicate hx]
  · intro x hx
    rw [mem_add] at hx
    cases' hx with hx hx
    · exact htA x hx
    · rwa [eq_of_mem_replicate hx]
  · rw [_root_.map_add, card_replicate, hs]; simp [h]
  · rw [_root_.map_add, card_replicate, ht]; simp [h]
  · rw [prod_add, prod_add, hst]
#align map_prod_eq_map_prod_of_le map_prod_eq_map_prod_of_le
#align map_sum_eq_map_sum_of_le map_sum_eq_map_sum_of_le

/-- `α →*[n] β` is naturally included in `A →*[m] β` for any `m ≤ n`. -/
@[to_additive AddFreimanHom.toAddFreimanHom
      "`α →+[n] β` is naturally included in `α →+[m] β`
      for any `m ≤ n`"]
def FreimanHom.toFreimanHom (h : m ≤ n) (f : A →*[n] β) : A →*[m] β where
  toFun := f
  map_prod_eq_map_prod' hsA htA hs ht hst := map_prod_eq_map_prod_of_le f hsA htA hs ht hst h
#align freiman_hom.to_freiman_hom FreimanHom.toFreimanHom
#align add_freiman_hom.to_add_freiman_hom AddFreimanHom.toAddFreimanHom

/-- An `n`-Freiman homomorphism is also a `m`-Freiman homomorphism for any `m ≤ n`. -/
@[to_additive AddFreimanHom.addFreimanHomClass_of_le
      "An additive `n`-Freiman homomorphism is
      also an additive `m`-Freiman homomorphism for any `m ≤ n`."]
theorem FreimanHom.FreimanHomClass_of_le [FreimanHomClass F A β n] (h : m ≤ n) :
    FreimanHomClass F A β m where
  map_prod_eq_map_prod' f _ _ hsA htA hs ht hst :=
    map_prod_eq_map_prod_of_le f hsA htA hs ht hst h
#align freiman_hom.freiman_hom_class_of_le FreimanHom.FreimanHomClass_of_le
#align add_freiman_hom.add_freiman_hom_class_of_le AddFreimanHom.addFreimanHomClass_of_le

@[to_additive (attr := simp) AddFreimanHom.toAddFreimanHom_coe]
theorem FreimanHom.toFreimanHom_coe (h : m ≤ n) (f : A →*[n] β) :
    (f.toFreimanHom h : α → β) = f :=
  rfl
#align freiman_hom.to_freiman_hom_coe FreimanHom.toFreimanHom_coe
#align add_freiman_hom.to_add_freiman_hom_coe AddFreimanHom.toAddFreimanHom_coe

@[to_additive AddFreimanHom.toAddFreimanHom_injective]
theorem FreimanHom.toFreimanHom_injective (h : m ≤ n) :
    Function.Injective (FreimanHom.toFreimanHom h : (A →*[n] β) → A →*[m] β) := fun f g hfg =>
  FreimanHom.ext <| by convert DFunLike.ext_iff.1 hfg using 0
#align freiman_hom.to_freiman_hom_injective FreimanHom.toFreimanHom_injective
#align add_freiman_hom.to_freiman_hom_injective AddFreimanHom.toAddFreimanHom_injective

end CancelCommMonoid
