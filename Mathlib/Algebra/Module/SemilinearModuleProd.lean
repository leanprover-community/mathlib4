/-
Copyright (c) 2026 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# Twisted product module by a ring homomorphism

For `Module R E` and `Module S F` and `σ : R →+* S`, we define the `R`-module structure
on `E × F` given by `s • ⟨x, y⟩ := ⟨s • x, σ s • y⟩`. As an example, this gives a natural `ℂ`-linear
space structure on the graph of antilinear operator.

Problem with defining a new `Semiring T` : there is a canonical instance `Module T (E × F)` and
we want it to work.
If we define either a type synonym or one-field structure, say `T`, we want that `Module T E` is
the usual one while `Module T F` is the twisted one. However, in the case of interest (`E = F = ℂ`)
with `σ = starRingEnd ℂ`, we are forced to use the usual instance `Module T ℂ`. So it seems
necessary to define a new type for the module with twist and duplicate code.

-/

@[expose] public section

open Complex

set_option linter.unusedVariables false in
/-- A `E ×[σ] F` or `E ×[σ] F` is a module structure on the product `E × F` with
the `SMul` given by `s • ⟨x, y⟩ := ⟨s • x, σ s • y⟩`. -/
@[ext]
structure SemilinearProdModule {R S : Type*} [Ring R] [Ring S] (σ : R →+* S) (E : Type*)
    [AddCommGroup E] [Module R E] (F : Type*) [AddCommGroup F] [Module S F] where
  /-- The first element of a pair. -/
  fst : E
  /-- The second element of a pair. -/
  snd : F

@[inherit_doc] notation:25 E " ×[" σ:25 "] " F:0 => SemilinearProdModule σ E F

namespace SemilinearProdModule

variable {R S : Type*} [Ring R] [Ring S] (σ : R →+* S) {E : Type*} [AddCommGroup E]
  [Module R E] {F : Type*} [AddCommGroup F] [Module S F]

instance : Add (E ×[σ] F) where
  add x y := mk (x.fst + y.fst) (x.snd + y.snd)

@[simp]
lemma add_fst (x y : E ×[σ] F) : (x + y).fst = x.fst + y.fst := rfl

@[simp]
lemma add_snd (x y : E ×[σ] F) : (x + y).snd = x.snd + y.snd := rfl

instance : Neg (E ×[σ] F) where
  neg x := mk (-x.fst) (-x.snd)

@[simp]
lemma neg_fst (x : E ×[σ] F) : (-x).fst = -x.fst := rfl

@[simp]
lemma neg_snd (x : E ×[σ] F) : (-x).snd = -x.snd := rfl

instance : Zero (E ×[σ] F) where
  zero := mk 0 0

@[simp]
lemma zero_fst : (0 : E ×[σ] F).fst = 0 := rfl

@[simp]
lemma zero_snd : (0 : E ×[σ] F).snd = 0 := rfl

instance : AddCommGroup (E ×[σ] F) where
  add_assoc x y z := by ext <;> simpa using add_assoc _ _ _
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  nsmul n x := mk (n • x.fst) (n • x.snd)
  zsmul n x := mk (n • x.fst) (n • x.snd)
  neg_add_cancel x := by ext <;> simp
  add_comm x y := by ext <;> simpa using add_comm _ _
  zsmul_zero' x := by ext <;> simp
  zsmul_succ' n x := by ext <;> simp [add_smul]
  nsmul_zero x := by ext <;> simp
  nsmul_succ n x := by ext <;> simp [add_smul]
  zsmul_neg' n x := by ext <;> simp [add_smul]

instance : SMul R (E ×[σ] F) where
  smul s x := mk (s • x.fst) (σ s • x.snd)

@[simp]
lemma smul_fst (s : R) (x : E ×[σ] F) : (s • x).fst = s • x.fst := rfl

@[simp]
lemma smul_snd (s : R) (x : E ×[σ] F) : (s • x).snd = σ s • x.snd := rfl

instance : Module R (E ×[σ] F) where
  mul_smul s t x := by ext <;> simp [mul_smul]
  one_smul x := by ext <;> simp
  smul_zero s := by ext <;> simp
  smul_add s x y := by ext <;> simp [smul_add]
  add_smul s t x := by ext <;> simp [add_smul]
  zero_smul x := by ext <;> simp

variable (E F) in
/-- The module `(E ×[σ] F)` is additively isomorphic to the product of modules. -/
def prodEquiv : (E ×[σ] F) ≃+ E × F where
  toFun := fun x => ⟨x.fst, x.snd⟩
  invFun := fun x => mk x.fst x.snd
  map_add' x y := by simp

lemma prodEquiv_apply (x : (E ×[σ] F)) : prodEquiv σ E F x = ⟨x.fst, x.snd⟩ := rfl

@[simp]
lemma prodEquiv_fst (x : (E ×[σ] F)) : (prodEquiv σ E F x).fst = x.fst := rfl

@[simp]
lemma prodEquiv_snd (x : (E ×[σ] F)) : (prodEquiv σ E F x).snd = x.snd := rfl


@[simp] lemma prodEquiv_fst_mem (x : (E ×[σ] F)) (s : Set E) :
    (prodEquiv σ E F x).fst ∈ s ↔ x.fst ∈ s := by simp

@[simp] lemma prodEquiv_snd_mem (x : (E ×[σ] F)) (s : Set F) :
    (prodEquiv σ E F x).snd ∈ s ↔ x.snd ∈ s := by simp

section Submodule

variable {R S : Type*} [Ring R] [Ring S] (σ : R →+* S) {E : Type*} [AddCommGroup E]
  [Module R E] {F : Type*} [AddCommGroup F] [Module S F]

open Submodule

variable (s : Submodule R E) (t : Submodule S F)

/-- The product of two submodules as a submodule of `(E ×[σ] F)`. -/
def prod : Submodule R (E ×[σ] F) where
  carrier := {x | x.fst ∈ s ∧ x.snd ∈ t }
  add_mem' hx hy := ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
  zero_mem' := by simp
  smul_mem' c x hx := ⟨s.smul_mem c hx.1, t.smul_mem (σ c) hx.2⟩

@[simp]
theorem mem_prod {s : Submodule R E} {t : Submodule S F} {p : E ×[σ] F} :
    p ∈ SemilinearProdModule.prod σ s t ↔ p.fst ∈ s ∧ p.snd ∈ t :=
  Iff.rfl

theorem prod_mono {s₁ s₂ : Submodule R E} {t₁ t₂ : Submodule S F} (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) :
    SemilinearProdModule.prod σ s₁ t₁ ≤ SemilinearProdModule.prod σ s₂ t₂ :=
  fun _ hx ↦ by rw [mem_prod]; exact ⟨hs hx.1, ht hx.2⟩

@[simp]
theorem top_prod_top :
    SemilinearProdModule.prod σ (⊤ : Submodule R E) (⊤ : Submodule S F) = ⊤ :=
  ext fun _ => by simp

@[simp]
theorem bot_prod_bot :
    SemilinearProdModule.prod σ (⊥ : Submodule R E) (⊥ : Submodule S F) = ⊥ := by
  ext x
  simp only [mem_prod, mem_bot]
  constructor
  · intro h
    ext
    · exact h.1
    · exact h.2
  · intro h; rw [h]; exact Prod.mk_eq_zero.mp rfl

/-- The product of submodules as `(E ×[σ] F)` is additively isomorphic to their product. -/
def prodEquivSubmodule (s : Submodule R E) (t : Submodule S F) :
    SemilinearProdModule.prod σ s t ≃+ s × t where
  toFun := fun x =>
    ⟨⟨x.val.fst, ((mem_prod σ).mp x.property).1⟩, x.val.snd, ((mem_prod σ).mp x.property).2⟩
  invFun := fun x => ⟨mk x.fst x.snd, (mem_prod σ).mpr ⟨x.fst.property, x.snd.property⟩⟩
  map_add' x y := by simp

theorem span_prod_le (s : Set E) (t : Set F) :
    span R ((prodEquiv σ E F).toFun ⁻¹'  (s ×ˢ t)) ≤ prod σ (span R s) (span S t) := by
  apply span_le.mpr
  intro x hx
  simp only [AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, Set.mem_preimage,
    Set.mem_prod, prodEquiv_fst, prodEquiv_snd] at hx
  exact ⟨Set.mem_of_mem_of_subset hx.1 subset_span, Set.mem_of_mem_of_subset hx.2 subset_span⟩

@[simp]
theorem prod_inf_prod {p p' : Submodule R E} {q q' : Submodule S F} :
    prod σ p q ⊓ prod σ p' q' = prod σ (p ⊓ p') (q ⊓ q') := by
  ext x; exact ⟨by intro _; simp_all, by intro _; simp_all⟩

@[simp]
theorem prod_sup_prod {p p' : Submodule R E} {q q' : Submodule S F} :
    prod σ p q ⊔ prod σ p' q' = prod σ (p ⊔ p') (q ⊔ q') := by
  apply le_antisymm
  · rw [sup_le_iff]
    exact ⟨by apply prod_mono <;> exact le_sup_left, by apply prod_mono <;> exact le_sup_right⟩
  · intro x hx
    rw [mem_prod, mem_sup, mem_sup] at hx
    simp_rw [mem_sup, mem_prod]
    obtain ⟨y, hy, z, hz, h⟩ := hx.1
    obtain ⟨y', hy', z', hz', h'⟩ := hx.2
    refine ⟨mk y y', ⟨hy, hy'⟩, mk z z', ⟨hz, hz'⟩, ?_⟩
    ext
    · exact h
    · exact h'

end Submodule

end SemilinearProdModule

end

section

open Complex SemilinearProdModule

-- the desired result. the second component is twisted.
example :
    I • (mk 0 1 : ℂ ×[starRingEnd ℂ] ℂ) = (mk 0 (-I) : ℂ ×[starRingEnd ℂ] ℂ) := by
  ext <;> simp

-- cf. the usual `Prod` structure.
example : I • (⟨0, 1⟩ : ℂ × ℂ) = (⟨0, I⟩ : ℂ × ℂ) := by ext <;> simp

end

-- below is a failed attempt to use a type synonym for `R`.
-- it does not work because of multiple `SMul` instances.

section

set_option linter.unusedVariables false in
/-- A `WithTwist σ` with `σ : R →+* S` is a type synonym of `R`, where when there is `Module S F`,
we define `Mpdule (WithTwist σ) F` by `r • x = (σ r) • x`. -/
@[nolint unusedArguments]
def WithTwist {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S) := R

namespace WithTwist

variable {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)

instance : Semiring (WithTwist σ) := inferInstanceAs (Semiring R)

section

variable {E : Type*} [SMul R E]

instance : SMul (WithTwist σ) E where
  smul r x := (id r : R) • x

instance : SMul R (WithTwist σ) where
  smul r x := r • (id x : R)

instance : Module R (WithTwist σ) where
  mul_smul _ _ _ := by simp [mul_assoc]
  one_smul _ := by simp
  smul_zero _ := by simp
  smul_add _ _ _ := by simp [mul_add]
  add_smul _ _ _ := by simp [add_mul]
  zero_smul _ := by simp

/-- The semilinear map `(WithTwist σ) →ₛₗ[σ] S` identical to `σ`. -/
def toLinearMap : (WithTwist σ) →ₛₗ[σ] S where
  toFun r := σ r
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

end

section

variable {F : Type*} [SMul S F]

instance : SMul (WithTwist σ) F where
  smul r x := σ r • x

@[simp]
lemma smul_eq (s : WithTwist σ) (x : F) : s • x = σ s • x := rfl

end

section

variable {E : Type*} [AddCommMonoid E] [Module R E]

instance : Module (WithTwist σ) E := inferInstanceAs (Module R E)

variable {F : Type*} [AddCommMonoid F] [Module S F]

instance : Module (WithTwist σ) F where
  mul_smul _ _ _ := by simp [mul_smul]
  one_smul _ := by simp
  smul_zero _ := by simp
  smul_add _ _ _ := by simp [smul_add]
  add_smul _ _ _ := by simp [add_smul]
  zero_smul _ := by simp

end

end WithTwist

example :
  Complex.I • (⟨0, 1⟩ : ℂ × (WithTwist ((starRingEnd ℂ))))
  = (⟨0, Complex.I⟩ : ℂ × (WithTwist ((starRingEnd ℂ))))
  := by
  ext
  · simp
  · simp

end
