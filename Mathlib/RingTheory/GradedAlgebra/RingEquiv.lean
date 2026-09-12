/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-! # Graded ring isomorphisms
We define `GradedRingEquiv 𝒜 ℬ` to mean isomorphisms of graded rings, with notation `𝒜 ≃+*ᵍ ℬ`.

When possible, instead of parametrizing results over `(e : 𝒜 ≃+*ᵍ ℬ)`, you should parametrize over
`[GradedEquivLike E 𝒜 ℬ] [RingEquivClass E A B] (e : E)`.
-/

@[expose] public section

open Graded

variable {A B C D ι σ τ ψ ω : Type*}

/-- A graded ring isomorphism between `𝒜` and `ℬ`. -/
structure GradedRingEquiv [Semiring A] [Semiring B] [SetLike σ A] [SetLike τ B]
    [AddSubmonoidClass σ A] [AddSubmonoidClass τ B] [DecidableEq ι] [AddMonoid ι]
    (𝒜 : ι → σ) (ℬ : ι → τ) [GradedRing 𝒜] [GradedRing ℬ] extends A ≃+* B where
  map_mem {i x} : x ∈ 𝒜 i → toFun x ∈ ℬ i

@[inherit_doc]
infixl:25 " ≃+*ᵍ " => GradedRingEquiv

/-- The underlying ring equivalence. -/
add_decl_doc GradedRingEquiv.toRingEquiv

namespace GradedRingEquiv

section GradedSemiring
variable [Semiring A] [Semiring B] [Semiring C] [Semiring D]
  [SetLike σ A] [SetLike τ B] [SetLike ψ C] [SetLike ω D]
  [AddSubmonoidClass σ A] [AddSubmonoidClass τ B]
  [AddSubmonoidClass ψ C] [AddSubmonoidClass ω D]
  [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι → σ} {ℬ : ι → τ} {𝒞 : ι → ψ} {𝒟 : ι → ω}
  [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞] [GradedRing 𝒟]

/-- Turn an element of a type `E` satisfying
`[EquivLike E A B] [GradedEquivLike E 𝒜 ℬ] [RingEquivClass E A B]` into an actual
`GradedRingEquiv`.

The preferred way in future mathlib will be to use structural projections instead. -/
def ofClass {E : Type*} [EquivLike E A B] [GradedEquivLike E 𝒜 ℬ] [RingEquivClass E A B]
    (e : E) : 𝒜 ≃+*ᵍ ℬ :=
  { (e : A ≃ B), (.ofClass e : 𝒜 →+*ᵍ ℬ) with }

/-- The underlying graded ring homomorphism. -/
@[coe] def toGradedRingHom (e : 𝒜 ≃+*ᵍ ℬ) : 𝒜 →+*ᵍ ℬ :=
  { e, e.toRingEquiv.toRingHom with }

instance : CoeTC (𝒜 ≃+*ᵍ ℬ) (𝒜 →+*ᵍ ℬ) := ⟨toGradedRingHom⟩

attribute [coe] toRingEquiv

instance : CoeTC (𝒜 ≃+*ᵍ ℬ) (A ≃+* B) := ⟨toRingEquiv⟩

section coe

private lemma mem_of_map_mem' (e : 𝒜 ≃+*ᵍ ℬ) {i x} (h : e.toFun x ∈ ℬ i) : x ∈ 𝒜 i := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 x]
  refine sum_mem fun j hj ↦ ?_
  obtain rfl | hij := eq_or_ne i j
  · exact SetLike.coe_mem _
  rw [DFinsupp.mem_support_iff, ← Subtype.coe_ne_coe, ZeroMemClass.coe_zero,
    ← e.toRingEquiv.map_ne_zero_iff] at hj
  let e' : 𝒜 →+*ᵍ ℬ := { e with map_one' := e.map_one, map_zero' := e.map_zero }
  conv_lhs at hj => exact e'.map_directSumDecompose _ _
  conv_lhs at hj => enter [1,1]; exact DirectSum.decompose_of_mem _ h
  rw [DirectSum.of_eq_of_ne _ _ _ hij.symm] at hj
  exact (hj rfl).elim

instance : EquivLike (𝒜 ≃+*ᵍ ℬ) A B where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' e f h₁ h₂ := by
    cases e
    cases f
    congr 1
    exact RingEquiv.ext (congr($h₁ ·))
  left_inv f := f.left_inv
  right_inv f := f.right_inv

instance : GradedEquivLike (𝒜 ≃+*ᵍ ℬ) 𝒜 ℬ where
  map_mem_iff e {_ _} := ⟨mem_of_map_mem' e, e.map_mem⟩

instance : RingEquivClass (𝒜 ≃+*ᵍ ℬ) A B where
  map_add f := f.map_add'
  map_mul f := f.map_mul'

/-- Two graded ring isomorphisms agree if they are defined by the same underlying function. -/
@[ext]
theorem ext {f g : 𝒜 ≃+*ᵍ ℬ} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Consider using `congr(f $h)`. -/
protected theorem congr_arg {f : 𝒜 ≃+*ᵍ ℬ} {x x' : A} : x = x' → f x = f x' :=
  DFunLike.congr_arg f

/-- Consider using `congr($h x)`. -/
protected theorem congr_fun {f g : 𝒜 ≃+*ᵍ ℬ} (h : f = g) (x : A) : f x = g x :=
  DFunLike.congr_fun h x

@[simp] theorem gradedRingHom_ofClass_eq_coe (e : 𝒜 ≃+*ᵍ ℬ) :
    .ofClass e = e.toGradedRingHom := rfl

-- bridging lemma between the old convention and the new convention
-- in the future `RingEquivClass.toRingEquiv` won't be a coercion and so the name will be
-- `ringEquiv_ofClass_eq_coe`.
@[simp] theorem coe_ringEquiv_eq_coe (e : 𝒜 ≃+*ᵍ ℬ) :
    RingEquivClass.toRingEquiv e = e.toRingEquiv := rfl

@[simp] theorem coe_mk (e h) : ⇑(⟨e, h⟩ : 𝒜 ≃+*ᵍ ℬ) = e := rfl

@[simp]
theorem mk_coe (e : 𝒜 ≃+*ᵍ ℬ) (e' h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨e, e', h₁, h₂⟩, h₃, h₄⟩, h₅⟩ : 𝒜 ≃+*ᵍ ℬ) = e := ext fun _ => rfl

@[simp] theorem coe_toEquiv (f : 𝒜 ≃+*ᵍ ℬ) : ⇑(f : A ≃ B) = f := rfl

@[simp] theorem coe_coe_ringEquiv (f : 𝒜 ≃+*ᵍ ℬ) : ⇑f.toRingEquiv = f := rfl

@[simp, norm_cast]
theorem coe_toMulEquiv (f : 𝒜 ≃+*ᵍ ℬ) : ⇑(f : A ≃* B) = f := rfl

@[simp] theorem coe_toAddEquiv (f : 𝒜 ≃+*ᵍ ℬ) : ⇑(f : A ≃+ B) = f := rfl

theorem coe_injective : Function.Injective ((↑) : (𝒜 ≃+*ᵍ ℬ) → A → B) :=
  DFunLike.coe_injective'

theorem coe_gradedRingHom_injective : Function.Injective ((↑) : (𝒜 ≃+*ᵍ ℬ) → 𝒜 →+*ᵍ ℬ) :=
  fun _ _ h ↦ coe_injective congr($h)

theorem coe_ringHom_injective : Function.Injective ((↑) : (𝒜 ≃+*ᵍ ℬ) → A →+* B) :=
  fun _ _ h ↦ coe_injective congr($h)

theorem coe_monoidHom_injective : Function.Injective ((↑) : (𝒜 ≃+*ᵍ ℬ) → A →* B) :=
  fun _ _ h ↦ coe_injective congr($h)

theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (𝒜 ≃+*ᵍ ℬ) → A →+ B) :=
  fun _ _ h ↦ coe_injective congr($h)

theorem coe_ringEquiv_injective : Function.Injective ((↑) : (𝒜 ≃+*ᵍ ℬ) → A ≃+* B) :=
  fun _ _ h ↦ coe_injective congr($h)

theorem coe_mulEquiv_injective : Function.Injective ((↑) : (𝒜 ≃+*ᵍ ℬ) → A ≃* B) :=
  fun _ _ h ↦ coe_injective congr($h)

theorem coe_addEquiv_injective : Function.Injective ((↑) : (𝒜 ≃+*ᵍ ℬ) → A ≃+ B) :=
  fun _ _ h ↦ coe_injective congr($h)

theorem coe_equiv_injective : Function.Injective ((↑) : (𝒜 ≃+*ᵍ ℬ) → A ≃ B) :=
  fun _ _ h ↦ coe_injective congr($h)

end coe

section map
variable (e : 𝒜 ≃+*ᵍ ℬ)

/-- A graded ring isomorphism preserves zero. -/
protected theorem map_zero : e 0 = 0 :=
  map_zero e

/-- A graded ring isomorphism preserves one. -/
protected theorem map_one : e 1 = 1 :=
  map_one e

/-- A graded ring isomorphism preserves addition. -/
protected theorem map_add (x y : A) : e (x + y) = e x + e y :=
  map_add e x y

/-- A graded ring isomorphism preserves multiplication. -/
protected theorem map_mul (x y : A) : e (x * y) = e x * e y :=
  map_mul e x y

protected theorem map_pow (x : A) (n : ℕ) : e (x ^ n) = e x ^ n :=
  map_pow e x n

protected theorem map_eq_zero_iff (x : A) : e x = 0 ↔ x = 0 :=
  e.toRingEquiv.map_eq_zero_iff

protected theorem map_ne_zero_iff (x : A) : e x ≠ 0 ↔ x ≠ 0 :=
  e.toRingEquiv.map_ne_zero_iff

protected theorem map_eq_one_iff (x : A) : e x = 1 ↔ x = 1 :=
  e.toRingEquiv.map_eq_one_iff

protected theorem map_ne_one_iff (x : A) : e x ≠ 1 ↔ x ≠ 1 :=
  e.toRingEquiv.map_ne_one_iff

end map

section bijective

protected theorem bijective (e : 𝒜 ≃+*ᵍ ℬ) : Function.Bijective e :=
  EquivLike.bijective e

protected theorem injective (e : 𝒜 ≃+*ᵍ ℬ) : Function.Injective e :=
  EquivLike.injective e

protected theorem surjective (e : 𝒜 ≃+*ᵍ ℬ) : Function.Surjective e :=
  EquivLike.surjective e

end bijective

section symm

/-- The inverse of a graded ring isomorphism is a graded ring isomorphism. -/
@[symm] protected def symm (e : 𝒜 ≃+*ᵍ ℬ) : ℬ ≃+*ᵍ 𝒜 where
  __ := e.toRingEquiv.symm
  map_mem hx := mem_of_map_mem e <| by convert hx; exact EquivLike.apply_inv_apply e _

@[simp] theorem invFun_eq_symm (f : 𝒜 ≃+*ᵍ ℬ) : EquivLike.inv f = f.symm := rfl

@[simp] theorem symm_symm (e : 𝒜 ≃+*ᵍ ℬ) : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective (GradedRingEquiv.symm : (𝒜 ≃+*ᵍ ℬ) → ℬ ≃+*ᵍ 𝒜) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem mk_coe' (e : 𝒜 ≃+*ᵍ ℬ) (f h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨f, ⇑e, h₁, h₂⟩, h₃, h₄⟩, h₅⟩ : ℬ ≃+*ᵍ 𝒜) = e.symm :=
  symm_bijective.injective <| ext fun _ ↦ rfl

/-- Auxiliary definition to avoid looping in `dsimp` with `RingEquiv.symm_mk`. -/
protected def symm_mk.aux (f : B → A) (g h₁ h₂ h₃ h₄ h₅) :=
  (mk (𝒜 := ℬ) (ℬ := 𝒜) ⟨⟨f, g, h₁, h₂⟩, h₃, h₄⟩ h₅).symm

@[simp]
theorem symm_mk (f : B → A) (g h₁ h₂ h₃ h₄ h₅) :
    (mk ⟨⟨f, g, h₁, h₂⟩, h₃, h₄⟩ h₅).symm =
      { symm_mk.aux (𝒜 := 𝒜) (ℬ := ℬ) f g h₁ h₂ h₃ h₄ h₅ with
        toFun := g
        invFun := f } :=
  rfl

@[simp] theorem coe_toEquiv_symm (e : 𝒜 ≃+*ᵍ ℬ) : (e.symm : B ≃ A) = (e : A ≃ B).symm := rfl

@[simp]
theorem coe_toMulEquiv_symm (e : 𝒜 ≃+*ᵍ ℬ) : (e.symm : B ≃* A) = (e : A ≃* B).symm := rfl

@[simp]
theorem coe_toAddEquiv_symm (e : 𝒜 ≃+*ᵍ ℬ) : (e.symm : B ≃+ A) = (e : A ≃+ B).symm := rfl

@[simp]
theorem coe_toRingEquiv_symm (e : 𝒜 ≃+*ᵍ ℬ) : (e.symm : B ≃* A) = (e : A ≃* B).symm := rfl

@[simp]
theorem apply_symm_apply (e : 𝒜 ≃+*ᵍ ℬ) : ∀ x, e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : 𝒜 ≃+*ᵍ ℬ) : ∀ x, e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply

theorem image_eq_preimage (e : 𝒜 ≃+*ᵍ ℬ) (s : Set A) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage_symm s

theorem symm_apply_eq (e : 𝒜 ≃+*ᵍ ℬ) {x : B} {y : A} :
    e.symm x = y ↔ x = e y := Equiv.symm_apply_eq _

theorem eq_symm_apply (e : 𝒜 ≃+*ᵍ ℬ) {x : B} {y : A} :
    y = e.symm x ↔ e y = x := Equiv.eq_symm_apply _

end symm

section Simps

/-- See Note [custom simps projection] -/
def Simps.apply (e : 𝒜 ≃+*ᵍ ℬ) : A → B := ⇑e

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : 𝒜 ≃+*ᵍ ℬ) : B → A := ⇑e.symm

initialize_simps_projections GradedRingEquiv (toFun → apply, invFun → symm_apply)

end Simps

section refl

variable (𝒜) in
/-- The identity map as a graded ring isomorphism. -/
@[simps!] protected def refl : 𝒜 ≃+*ᵍ 𝒜 :=
  { RingEquiv.refl A, GradedRingHom.id 𝒜 with }

@[simp] theorem symm_refl : (GradedRingEquiv.refl 𝒜).symm = GradedRingEquiv.refl 𝒜 := rfl

@[simp] theorem coe_refl : ⇑(GradedRingEquiv.refl 𝒜) = id := rfl

@[simp] theorem coe_toRingEquiv_refl : (GradedRingEquiv.refl 𝒜 : A ≃+* A) = RingEquiv.refl A := rfl

@[simp] theorem coe_addEquiv_refl : (GradedRingEquiv.refl 𝒜 : A ≃+ A) = AddEquiv.refl A := rfl

@[simp] theorem coe_mulEquiv_refl : (GradedRingEquiv.refl 𝒜 : A ≃* A) = MulEquiv.refl A := rfl

@[simp] theorem toEquiv_refl : GradedRingEquiv.refl 𝒜 = Equiv.refl A := rfl

@[simp]
theorem coe_gradedRingHom_refl : (GradedRingEquiv.refl 𝒜 : 𝒜 →+*ᵍ 𝒜) = .id 𝒜 := rfl

@[simp] theorem coe_ringHom_refl : (GradedRingEquiv.refl 𝒜 : A →+* A) = .id A := rfl

@[simp] theorem coe_monoidHom_refl : (GradedRingEquiv.refl 𝒜 : A →* A) = .id A := rfl

@[simp] theorem coe_addMonoidHom_refl : (GradedRingEquiv.refl 𝒜 : A →+ A) = .id A := rfl

end refl

section trans
variable (e₁ : 𝒜 ≃+*ᵍ ℬ) (e₂ : ℬ ≃+*ᵍ 𝒞)

/-- The composition of two graded ring isomorphisms. -/
@[trans, simps! apply] protected def trans (e₁ : 𝒜 ≃+*ᵍ ℬ) (e₂ : ℬ ≃+*ᵍ 𝒞) : 𝒜 ≃+*ᵍ 𝒞 where
  __ := e₁.toRingEquiv.trans e₂.toRingEquiv
  map_mem := e₂.map_mem ∘ e₁.map_mem

@[simp] theorem coe_trans : ⇑(e₁.trans e₂) = e₂ ∘ e₁ := rfl

theorem symm_trans_apply (a : C) : (e₁.trans e₂).symm a = e₁.symm (e₂.symm a) := rfl

@[simp] theorem symm_trans : (e₁.trans e₂).symm = e₂.symm.trans e₁.symm := rfl

@[simp] theorem coe_ringEquiv_trans : (e₁.trans e₂ : A ≃+* C) = (e₁ : A ≃+* B).trans ↑e₂ := rfl

@[simp] theorem coe_mulEquiv_trans : (e₁.trans e₂ : A ≃* C) = (e₁ : A ≃* B).trans ↑e₂ := rfl

@[simp] theorem coe_addEquiv_trans : (e₁.trans e₂ : A ≃+ C) = (e₁ : A ≃+ B).trans ↑e₂ := rfl

@[simp] theorem coe_gradedRingHom_trans : (e₁.trans e₂ : 𝒜 →+*ᵍ 𝒞) = (e₂ : ℬ →+*ᵍ 𝒞).comp ↑e₁ := rfl

@[simp] theorem coe_ringHom_trans : (e₁.trans e₂ : A →+* C) = (e₂ : B →+* C).comp ↑e₁ := rfl

@[simp] theorem coe_monoidHom_trans : (e₁.trans e₂ : A →* C) = (e₂ : B →* C).comp ↑e₁ := rfl

@[simp] theorem coe_addMonoidHom_trans : (e₁.trans e₂ : A →+ C) = (e₂ : B →+ C).comp ↑e₁ := rfl

@[simp] theorem self_trans_symm : e₁.trans e₁.symm = .refl 𝒜 :=
  coe_equiv_injective e₁.toEquiv.self_trans_symm

@[simp] theorem symm_trans_self : e₁.symm.trans e₁ = .refl ℬ :=
  coe_equiv_injective e₁.toEquiv.symm_trans_self

end trans

section unique

/-- If `A` and `B` are both unique (i.e. with exactly 1 element) then they are isomorphic. -/
def ofUnique [Unique A] [Unique B] : 𝒜 ≃+*ᵍ ℬ where
  __ := RingEquiv.ofUnique
  map_mem hx := by convert ZeroMemClass.zero_mem (ℬ _); subsingleton

instance [Unique A] [Unique B] : Unique (𝒜 ≃+*ᵍ ℬ) where
  default := .ofUnique
  uniq _ := ext fun _ ↦ Subsingleton.elim _ _

end unique

section ofBijective

/-- Produce a graded ring isomorphism from a bijective graded ring homomorphism. -/
noncomputable def ofBijective (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Bijective f) : 𝒜 ≃+*ᵍ ℬ :=
  { RingEquiv.ofBijective f hf, (f : 𝒜 →+*ᵍ ℬ) with }

variable (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Bijective f)

@[simp] theorem coe_ofBijective : ⇑(ofBijective f hf) = f := rfl

@[simp] theorem coe_toGradedRingHom_ofBijective : (ofBijective f hf : 𝒜 →+*ᵍ ℬ) = f := rfl

theorem ofBijective_apply (x : A) : ofBijective f hf x = f x := rfl

@[simp]
lemma ofBijective_symm_comp (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Bijective f) :
    ((ofBijective f hf).symm : ℬ →+*ᵍ 𝒜).comp f = .id 𝒜 :=
  GradedRingHom.ext fun _ ↦ (ofBijective f hf).injective <| apply_symm_apply ..

@[simp]
lemma comp_ofBijective_symm (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Bijective f) :
    f.comp ((ofBijective f hf).symm : ℬ →+*ᵍ 𝒜) = .id ℬ :=
  GradedRingHom.ext fun _ ↦ (ofBijective f hf).symm.injective <| apply_symm_apply ..

@[simp]
theorem comp_symm (e : 𝒜 ≃+*ᵍ ℬ) : (e : 𝒜 →+*ᵍ ℬ).comp (e.symm : ℬ →+*ᵍ 𝒜) = .id ℬ :=
  GradedRingHom.ext e.apply_symm_apply

@[simp]
theorem symm_comp (e : 𝒜 ≃+*ᵍ ℬ) : (e.symm : ℬ →+*ᵍ 𝒜).comp (e : 𝒜 →+*ᵍ ℬ) = .id 𝒜 :=
  GradedRingHom.ext e.symm_apply_apply

end ofBijective

/-- Construct a mutually-inverse pair of graded ring homomorphisms into a graded ring isomorphism.
-/
def ofGradedRingHom (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜) (h₁ : g.comp f = GradedRingHom.id 𝒜)
    (h₂ : f.comp g = GradedRingHom.id ℬ) : 𝒜 ≃+*ᵍ ℬ where
  __ := f
  __ := RingEquiv.ofRingHom f.toRingHom g.toRingHom congr($h₂) congr($h₁)

@[simp] lemma coe_ofGradedRingHom (f : 𝒜 →+*ᵍ ℬ) (g h₁ h₂) :
    ⇑(ofGradedRingHom f g h₁ h₂ : 𝒜 ≃+*ᵍ ℬ) = f := rfl

@[simp] lemma toGradedRingHom_ofGradedRingHom (f : 𝒜 →+*ᵍ ℬ) (g h₁ h₂) :
    (ofGradedRingHom f g h₁ h₂ : 𝒜 →+*ᵍ ℬ) = f := rfl

@[simp] lemma toMonoidHom_ofGradedRingHom (f : 𝒜 →+*ᵍ ℬ) (g h₁ h₂) :
    (ofGradedRingHom f g h₁ h₂ : A →* B) = f := rfl

@[simp] lemma toAddMonoidHom_ofGradedRingHom (f : 𝒜 →+*ᵍ ℬ) (g h₁ h₂) :
    (ofGradedRingHom f g h₁ h₂ : A →+ B) = f := rfl

@[simp] lemma symm_ofGradedRingHom (f : 𝒜 →+*ᵍ ℬ) (g h₁ h₂) :
    (ofGradedRingHom f g h₁ h₂).symm = ofGradedRingHom g f h₂ h₁ := rfl

end GradedSemiring

section GradedRing
variable [Ring A] [Ring B]
  [SetLike σ A] [SetLike τ B] [AddSubmonoidClass σ A] [AddSubmonoidClass τ B]
  [DecidableEq ι] [AddMonoid ι] {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (e : 𝒜 ≃+*ᵍ ℬ) (x y : A)

protected theorem map_neg : e (-x) = -e x :=
  map_neg e x

protected theorem map_sub : e (x - y) = e x - e y :=
  map_sub e x y

protected theorem map_neg_one : e (-1) = -1 :=
  RingEquiv.map_neg_one _

protected theorem map_eq_neg_one_iff {x : A} : e x = -1 ↔ x = -1 :=
  RingEquiv.map_eq_neg_one_iff _

end GradedRing

end GradedRingEquiv
