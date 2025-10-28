/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Data.FunLike.GradedFunLike
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Homomorphisms of graded (semi)rings

This file defines bundled homomorphisms of graded (semi)rings. We use the same structure
`GradedRingHom 𝒜 ℬ`, a.k.a. `𝒜 →+*ᵍ ℬ`, for both types of homomorphisms.

We do **not** define a separate class of graded ring homomorphisms; instead, we use
`[GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]`.

## Main definitions

* `GradedRingHom`: Graded (semi)ring homomorphisms. Ring homomorphism which preserves the grading.

## Notation

* `→+*ᵍ`: Graded (semi)ring hom.

## Implementation notes

* We don't really need the fact that they are graded rings until the theorem `decompose_map` which
describes how the decomposition interacts with the map.
-/

variable {ι A B C D σ τ ψ ω : Type*}
  [Semiring A] [Semiring B] [Semiring C] [Semiring D]
  [SetLike σ A] [SetLike τ B] [SetLike ψ C] [SetLike ω D]

section SetLike

/-- Bundled graded (semi)ring homomorphisms. Use `GradedRingHom` for the namespace,
and `GRingHom` for other identifiers, and `𝒜 →+*ᵍ ℬ` for the notation. -/
structure GradedRingHom (𝒜 : ι → σ) (ℬ : ι → τ) extends A →+* B where
  map_mem' {i : ι} {x : A} : x ∈ 𝒜 i → toRingHom x ∈ ℬ i

variable {𝒜 : ι → σ} {ℬ : ι → τ} {𝒞 : ι → ψ} {𝒟 : ι → ω}

@[inherit_doc]
notation:25 𝒜 " →+*ᵍ " ℬ => GradedRingHom 𝒜 ℬ

namespace GradedRingHom

section ofClass
variable {F : Type*} [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]

/-- Turn an element of a type `F` satisfying `[GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]` into an
actual `GradedRingHom`. This is declared as the default coercion from `F` to `𝒜 →+*ᵍ ℬ`. -/
@[coe]
def ofClass (f : F) : 𝒜 →+*ᵍ ℬ where
  __ := (f : A →+* B)
  map_mem' := map_mem f

/-- Any type satisfying `GradedRingHomClass` can be cast into `GradedRingHom` via
`GradedRingHomClass.toGRingHom`. -/
instance instCoeOfClass : CoeTC F (𝒜 →+*ᵍ ℬ) :=
  ⟨ofClass⟩

end ofClass

section coe

instance instGradedFunLike : GradedFunLike (𝒜 →+*ᵍ ℬ) 𝒜 ℬ where
  map_mem f := f.map_mem'
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

instance instRingHomClass : RingHomClass (𝒜 →+*ᵍ ℬ) A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

initialize_simps_projections GradedRingHom (toFun → apply)

theorem toFun_eq_coe (f : 𝒜 →+*ᵍ ℬ) : f.toFun = f :=
  rfl

@[simp]
theorem coe_mk (f : A →+* B) (h) : ((⟨f, h⟩ : 𝒜 →+*ᵍ ℬ) : A → B) = f :=
  rfl

@[simp]
theorem coe_coe {F : Type*} [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B] (f : F) :
    ((f : 𝒜 →+*ᵍ ℬ) : A → B) = f :=
  rfl

attribute [coe] GradedRingHom.toRingHom

instance coeToRingHom : CoeOut (𝒜 →+*ᵍ ℬ) (A →+* B) :=
  ⟨GradedRingHom.toRingHom⟩

@[simp]
theorem toRingHom_eq_coe (f : 𝒜 →+*ᵍ ℬ) : f.toRingHom = f :=
  rfl

@[simp]
theorem toMonoidHom_eq_coe (f : 𝒜 →+*ᵍ ℬ) : ((f : A →+* B) : A →* B) = f :=
  rfl

@[simp]
theorem toMonoidWithZeroHom_eq_coe (f : 𝒜 →+*ᵍ ℬ) : (f : A →+* B).toMonoidWithZeroHom = f :=
  rfl

@[simp]
theorem toAddMonoidHom_eq_coe (f : 𝒜 →+*ᵍ ℬ) : ((f : A →+* B) : A →+ B) = f :=
  rfl

/-- Copy of a `GradedRingHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
def copy (f : 𝒜 →+*ᵍ ℬ) (f' : A → B) (h : f' = f) : 𝒜 →+*ᵍ ℬ where
  __ := f.toRingHom.copy f' h
  map_mem' hx := congr($h _ ∈ ℬ _).to_iff.mpr <| f.map_mem' hx

@[simp]
theorem coe_copy (f : 𝒜 →+*ᵍ ℬ) (f' : A → B) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : 𝒜 →+*ᵍ ℬ) (f' : A → B) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

end coe

section

variable (f : 𝒜 →+*ᵍ ℬ)

protected theorem congr_fun {f g : 𝒜 →+*ᵍ ℬ} (h : f = g) (x : A) : f x = g x :=
  DFunLike.congr_fun h x

protected theorem congr_arg (f : 𝒜 →+*ᵍ ℬ) {x y : A} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h

theorem coe_inj ⦃f g : 𝒜 →+*ᵍ ℬ⦄ (h : (f : A → B) = g) : f = g :=
  DFunLike.coe_injective h

@[ext]
theorem ext ⦃f g : 𝒜 →+*ᵍ ℬ⦄ : (∀ x, f x = g x) → f = g :=
  DFunLike.ext _ _

@[simp]
theorem mk_coe (f : 𝒜 →+*ᵍ ℬ) (h₁ h₂ h₃ h₄ h₅) : .mk ⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ h₅ = f :=
  ext fun _ => rfl

theorem coe_ringHom_injective : (fun f : 𝒜 →+*ᵍ ℬ => (f : A →+* B)).Injective := fun _ _ h =>
  ext <| DFunLike.congr_fun (F := A →+* B) h

/-- Graded ring homomorphisms map zero to zero. -/
protected theorem map_zero (f : 𝒜 →+*ᵍ ℬ) : f 0 = 0 :=
  map_zero f

/-- Graded ring homomorphisms map one to one. -/
protected theorem map_one (f : 𝒜 →+*ᵍ ℬ) : f 1 = 1 :=
  map_one f

/-- Graded ring homomorphisms preserve addition. -/
protected theorem map_add (f : 𝒜 →+*ᵍ ℬ) : ∀ a b, f (a + b) = f a + f b :=
  map_add f

/-- Graded ring homomorphisms preserve multiplication. -/
protected theorem map_mul (f : 𝒜 →+*ᵍ ℬ) : ∀ a b, f (a * b) = f a * f b :=
  map_mul f

/-- Graded ring homomorphisms preserve the grading. -/
protected theorem map_mem (f : 𝒜 →+*ᵍ ℬ) : ∀ {i a}, a ∈ 𝒜 i → f a ∈ ℬ i :=
  map_mem f

end

section Ring
variable {A B σ τ : Type*}
variable [Ring A] [Ring B] [SetLike σ A] [SetLike τ B]
variable (𝒜 : ι → σ) (ℬ : ι → τ)

/-- Graded ring homomorphisms preserve additive inverse. -/
protected theorem map_neg (f : 𝒜 →+*ᵍ ℬ) (x : A) : f (-x) = -f x :=
  map_neg f x

/-- Graded ring homomorphisms preserve subtraction. -/
protected theorem map_sub (f : 𝒜 →+*ᵍ ℬ) (x y : A) :
    f (x - y) = f x - f y :=
  map_sub f x y

end Ring

variable (𝒜) in
/-- The identity graded ring homomorphism from a graded ring to itself. -/
def id : 𝒜 →+*ᵍ 𝒜 where
  __ := RingHom.id _
  map_mem' h := h

@[simp, norm_cast]
theorem coe_id : ⇑(GradedRingHom.id 𝒜) = _root_.id := rfl

@[simp]
theorem id_apply (x : A) : GradedRingHom.id 𝒜 x = x :=
  rfl

@[simp]
theorem coe_ringHom_id : (id 𝒜 : A →+* A) = RingHom.id A :=
  rfl

/-- Composition of graded ring homomorphisms is a graded ring homomorphism. -/
def comp (g : ℬ →+*ᵍ 𝒞) (f : 𝒜 →+*ᵍ ℬ) : 𝒜 →+*ᵍ 𝒞 where
  __ := g.toRingHom.comp f
  map_mem' := g.map_mem ∘ f.map_mem

/-- Composition of graded ring homomorphisms is associative. -/
theorem comp_assoc (h : 𝒞 →+*ᵍ 𝒟) (g : ℬ →+*ᵍ 𝒞) (f : 𝒜 →+*ᵍ ℬ) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
theorem coe_comp (hnp : ℬ →+*ᵍ 𝒞) (hmn : 𝒜 →+*ᵍ ℬ) : (hnp.comp hmn : A → C) = hnp ∘ hmn :=
  rfl

theorem comp_apply (hnp : ℬ →+*ᵍ 𝒞) (hmn : 𝒜 →+*ᵍ ℬ) (x : A) :
    (hnp.comp hmn : A → C) x = hnp (hmn x) :=
  rfl

@[simp]
theorem comp_id (f : 𝒜 →+*ᵍ ℬ) : f.comp (id 𝒜) = f :=
  ext fun _ => rfl

@[simp]
theorem id_comp (f : 𝒜 →+*ᵍ ℬ) : (id ℬ).comp f = f :=
  ext fun _ => rfl

instance instOne : One (𝒜 →+*ᵍ 𝒜) where one := id _
instance instMul : Mul (𝒜 →+*ᵍ 𝒜) where mul := comp

lemma one_def : (1 : 𝒜 →+*ᵍ 𝒜) = id 𝒜 := rfl

lemma mul_def (f g : 𝒜 →+*ᵍ 𝒜) : f * g = f.comp g := rfl

@[simp, norm_cast] lemma coe_one : ⇑(1 : 𝒜 →+*ᵍ 𝒜) = _root_.id := rfl

@[simp, norm_cast] lemma coe_mul (f g : 𝒜 →+*ᵍ 𝒜) : ⇑(f * g) = f ∘ g := rfl

instance instMonoid : Monoid (𝒜 →+*ᵍ 𝒜) where
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _
  npow n f := (npowRec n f).copy f^[n] <| by induction n <;> simp [npowRec, *]
  npow_succ _ _ := DFunLike.coe_injective <| Function.iterate_succ _ _

@[simp, norm_cast] lemma coe_pow (f : 𝒜 →+*ᵍ 𝒜) (n : ℕ) : ⇑(f ^ n) = f^[n] := rfl

@[simp]
theorem cancel_right {g₁ g₂ : ℬ →+*ᵍ 𝒞} {f : 𝒜 →+*ᵍ ℬ} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 (GradedRingHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]
theorem cancel_left {g : ℬ →+*ᵍ 𝒞} {f₁ f₂ : 𝒜 →+*ᵍ ℬ} (hg : Function.Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun x => hg <| by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

end GradedRingHom

end SetLike

section GradedRingHomClass

variable [AddSubmonoidClass σ A] [AddSubmonoidClass τ B]

section
variable (𝒜 : ι → σ) (ℬ : ι → τ)
variable {F : Type*} [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]

-- Note: if `GradedAddHom` is added later, then the assumptions can be relaxed.
/-- A graded ring homomorphism descends to an additive homomorphism on each indexed component. -/
@[simps!] def gradedAddHom (f : F) (i : ι) : 𝒜 i →+ ℬ i where
  toFun x := ⟨f x, map_mem f x.2⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

end

section
variable [AddMonoid ι] (𝒜 : ι → σ) (ℬ : ι → τ) [SetLike.GradedMonoid 𝒜] [SetLike.GradedMonoid ℬ]
variable {F : Type*} [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]

/-- A graded ring homomorphism descends to a ring homomorphism on the zeroth component. -/
@[simps!] def gradedZeroRingHom (f : F) : 𝒜 0 →+* ℬ 0 where
  __ := gradedAddHom _ _ f 0
  map_one' := Subtype.ext <| map_one _
  map_mul' _ _ := Subtype.ext <| map_mul ..

end

section GradedRing
variable [DecidableEq ι] [AddMonoid ι] (𝒜 : ι → σ) (ℬ : ι → τ) [GradedRing 𝒜] [GradedRing ℬ]
variable {F : Type*} [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]

@[simp] lemma decompose_map (f : F) {x : A} :
    DirectSum.decompose ℬ (f x) = .map (gradedAddHom _ _ f) (.decompose 𝒜 x) := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 x, map_sum, DirectSum.decompose_sum,
    DirectSum.decompose_sum, map_sum]
  congr 1
  ext n : 1
  rw [DirectSum.decompose_of_mem _ (map_mem f (Subtype.prop _)),
    DirectSum.decompose_of_mem _ (Subtype.prop _), DirectSum.map_of]
  rfl

lemma map_coe_decompose (f : F) {x : A} {i : ι} :
    f (DirectSum.decompose 𝒜 x i) = DirectSum.decompose ℬ (f x) i := by
  simp

end GradedRing

end GradedRingHomClass
