/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.GroupTheory.Complement

/-!
# Semidirect product

This file defines semidirect products of groups, and the canonical maps in and out of the
semidirect product. The semidirect product of `N` and `G` given a hom `φ` from
`G` to the automorphism group of `N` is the product of sets with the group
`⟨n₁, g₁⟩ * ⟨n₂, g₂⟩ = ⟨n₁ * φ g₁ n₂, g₁ * g₂⟩`

## Key definitions

There are two homs into the semidirect product `inl : N →* N ⋊[φ] G` and
`inr : G →* N ⋊[φ] G`, and `lift` can be used to define maps `N ⋊[φ] G →* H`
out of the semidirect product given maps `fn : N →* H` and `fg : G →* H` that satisfy the
condition `∀ n g, fn (φ g n) = fg g * fn n * fg g⁻¹`

## Notation

This file introduces the global notation `N ⋊[φ] G` for `SemidirectProduct N G φ`

## Tags
group, semidirect product
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open Subgroup

variable (N : Type*) (G : Type*) {H : Type*} [Group N] [Group G] [Group H]

-- Don't generate sizeOf and injectivity lemmas, which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The semidirect product of groups `N` and `G`, given a map `φ` from `G` to the automorphism
  group of `N`. It is the product of sets with the group operation
  `⟨n₁, g₁⟩ * ⟨n₂, g₂⟩ = ⟨n₁ * φ g₁ n₂, g₁ * g₂⟩` -/
@[ext]
structure SemidirectProduct (φ : G →* MulAut N) where
  /-- The element of N -/
  left : N
  /-- The element of G -/
  right : G
  deriving DecidableEq

attribute [pp_using_anonymous_constructor] SemidirectProduct

@[inherit_doc]
notation:35 N " ⋊[" φ:35 "] " G:35 => SemidirectProduct N G φ

namespace SemidirectProduct

variable {N G}
variable {φ : G →* MulAut N}

instance : Mul (SemidirectProduct N G φ) where
  mul a b := ⟨a.1 * φ a.2 b.1, a.2 * b.2⟩

lemma mul_def (a b : SemidirectProduct N G φ) : a * b = ⟨a.1 * φ a.2 b.1, a.2 * b.2⟩ := rfl

@[simp]
theorem mul_left (a b : N ⋊[φ] G) : (a * b).left = a.left * φ a.right b.left := rfl

@[simp]
theorem mul_right (a b : N ⋊[φ] G) : (a * b).right = a.right * b.right := rfl

instance : One (SemidirectProduct N G φ) where one := ⟨1, 1⟩

@[simp]
theorem one_left : (1 : N ⋊[φ] G).left = 1 := rfl

@[simp]
theorem one_right : (1 : N ⋊[φ] G).right = 1 := rfl

instance : Inv (SemidirectProduct N G φ) where
  inv x := ⟨φ x.2⁻¹ x.1⁻¹, x.2⁻¹⟩

@[simp]
theorem inv_left (a : N ⋊[φ] G) : a⁻¹.left = φ a.right⁻¹ a.left⁻¹ := rfl

@[simp]
theorem inv_right (a : N ⋊[φ] G) : a⁻¹.right = a.right⁻¹ := rfl

instance : Group (N ⋊[φ] G) where
  mul_assoc a b c := SemidirectProduct.ext (by simp [mul_assoc]) (by simp [mul_assoc])
  one_mul a := SemidirectProduct.ext (by simp) (one_mul a.2)
  mul_one a := SemidirectProduct.ext (by simp) (mul_one _)
  inv_mul_cancel a := SemidirectProduct.ext (by simp) (by simp)

instance : Inhabited (N ⋊[φ] G) := ⟨1⟩

/-- The canonical map `N →* N ⋊[φ] G` sending `n` to `⟨n, 1⟩` -/
def inl : N →* N ⋊[φ] G where
  toFun n := ⟨n, 1⟩
  map_one' := rfl
  map_mul' := by intros; ext <;>
    simp only [mul_left, map_one, MulAut.one_apply, mul_right, mul_one]

@[simp]
theorem left_inl (n : N) : (inl n : N ⋊[φ] G).left = n := rfl

@[simp]
theorem right_inl (n : N) : (inl n : N ⋊[φ] G).right = 1 := rfl

theorem inl_injective : Function.Injective (inl : N → N ⋊[φ] G) :=
  Function.injective_iff_hasLeftInverse.2 ⟨left, left_inl⟩

@[simp]
theorem inl_inj {n₁ n₂ : N} : (inl n₁ : N ⋊[φ] G) = inl n₂ ↔ n₁ = n₂ :=
  inl_injective.eq_iff

/-- The canonical map `G →* N ⋊[φ] G` sending `g` to `⟨1, g⟩` -/
def inr : G →* N ⋊[φ] G where
  toFun g := ⟨1, g⟩
  map_one' := rfl
  map_mul' := by intros; ext <;> simp

@[simp]
theorem left_inr (g : G) : (inr g : N ⋊[φ] G).left = 1 := rfl

@[simp]
theorem right_inr (g : G) : (inr g : N ⋊[φ] G).right = g := rfl

theorem inr_injective : Function.Injective (inr : G → N ⋊[φ] G) :=
  Function.injective_iff_hasLeftInverse.2 ⟨right, right_inr⟩

@[simp]
theorem inr_inj {g₁ g₂ : G} : (inr g₁ : N ⋊[φ] G) = inr g₂ ↔ g₁ = g₂ :=
  inr_injective.eq_iff

theorem inl_aut (g : G) (n : N) : (inl (φ g n) : N ⋊[φ] G) = inr g * inl n * inr g⁻¹ := by
  ext <;> simp

theorem inl_aut_inv (g : G) (n : N) : (inl ((φ g)⁻¹ n) : N ⋊[φ] G) = inr g⁻¹ * inl n * inr g := by
  rw [← map_inv, inl_aut, inv_inv]

@[simp]
theorem mk_eq_inl_mul_inr (g : G) (n : N) : (⟨n, g⟩ : N ⋊[φ] G) = inl n * inr g := by ext <;> simp

@[simp]
theorem inl_left_mul_inr_right (x : N ⋊[φ] G) : inl x.left * inr x.right = x := by ext <;> simp

/-- The canonical projection map `N ⋊[φ] G →* G`, as a group hom. -/
def rightHom : N ⋊[φ] G →* G where
  toFun := SemidirectProduct.right
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem rightHom_eq_right : (rightHom : N ⋊[φ] G → G) = right := rfl

@[simp]
theorem rightHom_comp_inl : (rightHom : N ⋊[φ] G →* G).comp inl = 1 := by ext; simp [rightHom]

@[simp]
theorem rightHom_comp_inr : (rightHom : N ⋊[φ] G →* G).comp inr = MonoidHom.id _ := by
  ext; simp [rightHom]

@[simp]
theorem rightHom_inl (n : N) : rightHom (inl n : N ⋊[φ] G) = 1 := by simp [rightHom]

@[simp]
theorem rightHom_inr (g : G) : rightHom (inr g : N ⋊[φ] G) = g := by simp [rightHom]

theorem rightHom_surjective : Function.Surjective (rightHom : N ⋊[φ] G → G) :=
  Function.surjective_iff_hasRightInverse.2 ⟨inr, rightHom_inr⟩

theorem range_inl_eq_ker_rightHom : (inl : N →* N ⋊[φ] G).range = rightHom.ker :=
  le_antisymm (fun _ ↦ by simp +contextual [MonoidHom.mem_ker, eq_comm])
    fun x hx ↦ ⟨x.left, by ext <;> simp_all [MonoidHom.mem_ker]⟩

/-- The bijection between the semidirect product and the product. -/
@[simps]
def equivProd : N ⋊[φ] G ≃ N × G where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩

/-- The group isomorphism between a semidirect product with respect to the trivial map
  and the product. -/
@[simps (rhsMd := .default)]
def mulEquivProd : N ⋊[1] G ≃* N × G :=
  { equivProd with map_mul' _ _ := rfl }

section lift

variable (fn : N →* H) (fg : G →* H)
  (h : ∀ g, fn.comp (φ g).toMonoidHom = (MulAut.conj (fg g)).toMonoidHom.comp fn)

/-- Define a group hom `N ⋊[φ] G →* H`, by defining maps `N →* H` and `G →* H` -/
def lift : N ⋊[φ] G →* H where
  toFun a := fn a.1 * fg a.2
  map_one' := by simp
  map_mul' a b := by
    have := fun n g ↦ DFunLike.ext_iff.1 (h n) g
    simp only [MulAut.conj_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
    simp only [mul_left, mul_right, map_mul, this, mul_assoc, inv_mul_cancel_left]

@[simp]
theorem lift_inl (n : N) : lift fn fg h (inl n) = fn n := by simp [lift]

@[simp]
theorem lift_comp_inl : (lift fn fg h).comp inl = fn := by ext; simp

@[simp]
theorem lift_inr (g : G) : lift fn fg h (inr g) = fg g := by simp [lift]

@[simp]
theorem lift_comp_inr : (lift fn fg h).comp inr = fg := by ext; simp

theorem lift_unique (F : N ⋊[φ] G →* H) :
    F = lift (F.comp inl) (F.comp inr) fun _ ↦ by ext; simp [inl_aut] := by
  rw [DFunLike.ext_iff]
  simp only [lift, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk, ← map_mul,
    inl_left_mul_inr_right, forall_const]

/-- Two maps out of the semidirect product are equal if they're equal after composition
  with both `inl` and `inr` -/
theorem hom_ext {f g : N ⋊[φ] G →* H} (hl : f.comp inl = g.comp inl)
    (hr : f.comp inr = g.comp inr) : f = g := by
  rw [lift_unique f, lift_unique g]
  simp only [*]

/-- The homomorphism from a semidirect product of subgroups to the ambient group. -/
@[simps!]
def monoidHomSubgroup {H K : Subgroup G} (h : K ≤ normalizer H) :
    H ⋊[(H.normalizerMonoidHom).comp (inclusion h)] K →* G :=
  lift H.subtype K.subtype (by simp [DFunLike.ext_iff])

/-- The isomorphism from a semidirect product of complementary subgroups to the ambient group. -/
@[simps!]
noncomputable def mulEquivSubgroup {H K : Subgroup G} [H.Normal] (h : H.IsComplement' K) :
    H ⋊[(H.normalizerMonoidHom).comp (inclusion (H.normalizer_eq_top ▸ le_top))] K ≃* G :=
  MulEquiv.ofBijective (monoidHomSubgroup _) ((equivProd.bijective_comp _).mpr h)

end lift

section Map

variable {N₁ G₁ N₂ G₂ : Type*} [Group N₁] [Group G₁] [Group N₂] [Group G₂]
  {φ₁ : G₁ →* MulAut N₁} {φ₂ : G₂ →* MulAut N₂}
  (fn : N₁ →* N₂) (fg : G₁ →* G₂)
  (h : ∀ g : G₁, fn.comp (φ₁ g).toMonoidHom = (φ₂ (fg g)).toMonoidHom.comp fn)

/-- Define a map from `N₁ ⋊[φ₁] G₁` to `N₂ ⋊[φ₂] G₂` given maps `N₁ →* N₂` and `G₁ →* G₂` that
  satisfy a commutativity condition `∀ n g, fn (φ₁ g n) = φ₂ (fg g) (fn n)`. -/
def map : N₁ ⋊[φ₁] G₁ →* N₂ ⋊[φ₂] G₂ where
  toFun x := ⟨fn x.1, fg x.2⟩
  map_one' := by simp
  map_mul' x y := by
    replace h := DFunLike.ext_iff.1 (h x.right) y.left
    ext <;> simp_all

@[simp]
theorem map_left (g : N₁ ⋊[φ₁] G₁) : (map fn fg h g).left = fn g.left := rfl

@[simp]
theorem map_right (g : N₁ ⋊[φ₁] G₁) : (map fn fg h g).right = fg g.right := rfl

@[simp]
theorem rightHom_comp_map : rightHom.comp (map fn fg h) = fg.comp rightHom := rfl

@[simp]
theorem map_inl (n : N₁) : map fn fg h (inl n) = inl (fn n) := by simp [map]

@[simp]
theorem map_comp_inl : (map fn fg h).comp inl = inl.comp fn := by ext <;> simp

@[simp]
theorem map_inr (g : G₁) : map fn fg h (inr g) = inr (fg g) := by simp [map]

@[simp]
theorem map_comp_inr : (map fn fg h).comp inr = inr.comp fg := by ext <;> simp [map]

end Map

section Congr

variable {N₁ G₁ N₂ G₂ : Type*} [Group N₁] [Group G₁] [Group N₂] [Group G₂]
  {φ₁ : G₁ →* MulAut N₁} {φ₂ : G₂ →* MulAut N₂}
  (fn : N₁ ≃* N₂) (fg : G₁ ≃* G₂)
  (h : ∀ g : G₁, (φ₁ g).trans fn = fn.trans (φ₂ (fg g)))

/-- Define an isomorphism from `N₁ ⋊[φ₁] G₁` to `N₂ ⋊[φ₂] G₂` given isomorphisms `N₁ ≃* N₂` and
  `G₁ ≃* G₂` that satisfy a commutativity condition `∀ n g, fn (φ₁ g n) = φ₂ (fg g) (fn n)`. -/
@[simps]
def congr : N₁ ⋊[φ₁] G₁ ≃* N₂ ⋊[φ₂] G₂ where
  toFun x := ⟨fn x.1, fg x.2⟩
  invFun x := ⟨fn.symm x.1, fg.symm x.2⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' x y := by
    replace h := DFunLike.ext_iff.1 (h x.right) y.left
    ext <;> simp_all

/-- Define an isomorphism from `N₁ ⋊[φ₁] G₁` to `N₂ ⋊[φ₂] G₂` without specifying `φ₂`. -/
@[simps!]
def congr' :
    N₁ ⋊[φ₁] G₁ ≃* N₂ ⋊[MonoidHom.comp (MulAut.congr fn) (φ₁.comp fg.symm)] G₂ :=
  congr fn fg (fun _ ↦ by ext; simp)

end Congr

@[simp]
lemma card : Nat.card (N ⋊[φ] G) = Nat.card N * Nat.card G :=
  Nat.card_prod _ _ ▸ Nat.card_congr equivProd

end SemidirectProduct
