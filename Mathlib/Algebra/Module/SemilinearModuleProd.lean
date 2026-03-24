/-
Copyright (c) 2026 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Module.Prod

/-!
# Twisted product module by a ring homomorphism

For `Module R E` and `Module S F` and `σ : R →+* S`, we define the `R`-module structure
on a type `E ×[σ] F` with two-field structure given by `s • (mk x y) := mk (s • x) (σ s • y)`. As an
example, this gives a natural `ℂ`-linear space structure on the graph of antilinear operator.

## Implementation notes

The main application is the case where one has `Module ℂ E`, `Module ℂ F` and an antilinear operator
`A : E →ₛₗ[starRingEnd ℂ] F`. The graph of `A` is a `ℂ`-module, but `ℂ` acts linearly on `E` while
antilinearly on `F`. Such a graph cannot be a `Submodule ℂ (E × F)` because there is already the
natural instance `Module ℂ (E × F)` where `ℂ` acts linearly on `F`.

In order to implement this, defining a type synonym `R` of `ℂ` does not work, because one might want
to take `E = F`, on which any `R : Ring` can have only one instance `Module R F`, in particular,
there is already the canonical instance `Module R (E × F)`. This means that we cannot use the
product module `E × F`, but we have to make a new type and duplicate code for `E ×[σ] F`. -/

@[expose] public section

/-- A `E ×[σ] F` or `E ×[σ] F` is a module structure on the product `E × F` with
the `SMul` given by `s • (mk x y) := mk (s • x) (σ s • y)`. -/
@[ext]
structure SemilinearProdModule {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
  (E : Type*) (F : Type*) where
  /-- The first element of a pair. -/
  fst : E
  /-- The second element of a pair. -/
  snd : F

@[inherit_doc] notation:35 E " ×[" σ:35 "] " F:35 => SemilinearProdModule σ E F

namespace SemilinearProdModule

section SMul

variable {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
  {E : Type*} [SMul R E] {F : Type*} [SMul S F]

instance : SMul R (E ×[σ] F) where
  smul s x := mk (s • x.fst) (σ s • x.snd)

@[simp]
lemma smul_fst (s : R) (x : E ×[σ] F) : (s • x).fst = s • x.fst := rfl

@[simp]
lemma smul_snd (s : R) (x : E ×[σ] F) : (s • x).snd = σ s • x.snd := rfl

end SMul

section Add

variable {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
  {E : Type*} [AddCommMonoid E] {F : Type*} [AddCommMonoid F]

instance : Add (E ×[σ] F) where
  add x y := mk (x.fst + y.fst) (x.snd + y.snd)

@[simp]
lemma add_fst (x y : E ×[σ] F) : (x + y).fst = x.fst + y.fst := rfl

@[simp]
lemma add_snd (x y : E ×[σ] F) : (x + y).snd = x.snd + y.snd := rfl

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

end Add

section AddCommGroup

variable {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
  {E : Type*} [AddCommGroup E] {F : Type*} [AddCommGroup F]

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

end AddCommGroup

section Module

variable {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
  {E : Type*} [AddCommGroup E] [Module R E] {F : Type*} [AddCommGroup F] [Module S F]

instance : Module R (E ×[σ] F) where
  mul_smul s t x := by ext <;> simp [mul_smul]
  one_smul x := by ext <;> simp
  smul_zero s := by ext <;> simp
  smul_add s x y := by ext <;> simp [smul_add]
  add_smul s t x := by ext <;> simp [add_smul]
  zero_smul x := by ext <;> simp

end Module

section Submodule

variable {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
  {E : Type*} [AddCommGroup E] [Module R E] {F : Type*} [AddCommGroup F] [Module S F]

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

namespace LinearMap

variable {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)
  (E : Type*) [AddCommGroup E] [Module R E]
  (F : Type*) [AddCommGroup F] [Module S F]
  {M : Type*} [AddCommGroup M] [Module R M]

/-- The first projection of a product is a linear map. -/
def fstₛₗ : (E ×[σ] F) →ₗ[R] E where
  toFun x := x.fst
  map_add' _x _y := rfl
  map_smul' _x _y := rfl

/-- The second projection of a product is a linear map. -/
def sndₛₗ : (E ×[σ] F) →ₛₗ[σ] F where
  toFun x := x.snd
  map_add' _x _y := rfl
  map_smul' _x _y := rfl

@[simp] lemma fstₛₗ_apply (x : E ×[σ] F) :
    fstₛₗ σ E F x = x.fst := rfl

@[simp] lemma sndₛₗ_apply (x : E ×[σ] F) :
    sndₛₗ σ E F x = x.snd := rfl

@[simp, norm_cast] lemma coe_fstₛₗ : ⇑(fstₛₗ σ E F) = fun x => x.fst := rfl

@[simp, norm_cast] lemma coe_sndₛₗ : ⇑(sndₛₗ σ E F) = fun x => x.snd := rfl

theorem fstₛₗ_surjective : Function.Surjective (fstₛₗ σ E F) :=
  fun x => ⟨SemilinearProdModule.mk x 0, rfl⟩

theorem sndₛₗ_surjective : Function.Surjective (sndₛₗ σ E F) :=
  fun x => ⟨SemilinearProdModule.mk 0 x, rfl⟩

section prodₛₗ

variable {σ E F}

/-- Combine a linear map `f : M →ₗ[R] E` and a semilinear map
`g : M →ₛₗ[σ] F` into a linear map with target `E ×[σ] F`. -/
@[simps]
def prodₛₗ (f : M →ₗ[R] E) (g : M →ₛₗ[σ] F) : M →ₗ[R] E ×[σ] F where
  toFun x := SemilinearProdModule.mk (f x) (g x)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

-- not adapted because no function exist corresponding to `Pi.prod`
-- theorem coe_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : ⇑(f.prod g) = Pi.prod f g :=
--   rfl

@[simp] lemma prodₛₗ_apply (f : M →ₗ[R] E) (g : M →ₛₗ[σ] F) (x : M) :
    prodₛₗ f g x = SemilinearProdModule.mk (f x) (g x) := rfl

@[simp] lemma fstₛₗ_prodₛₗ (f : M →ₗ[R] E) (g : M →ₛₗ[σ] F) :
    (fstₛₗ σ E F).comp (prodₛₗ f g) = f := by ext x; rfl

@[simp] lemma sndₛₗ_prodₛₗ (f : M →ₗ[R] E) (g : M →ₛₗ[σ] F) :
    (sndₛₗ σ E F).comp (prodₛₗ f g) = g := by ext x; rfl

@[simp]
theorem pair_fstₛₗ_sndₛₗ : prodₛₗ (fstₛₗ σ E F) (sndₛₗ σ E F) = LinearMap.id := rfl

theorem prod_compₛₗ {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] (f : M₂ →ₗ[R] E) (g : M₂ →ₛₗ[σ] F)
    (h : M →ₗ[R] M₂) : (f.prodₛₗ g).comp h = (f.comp h).prodₛₗ (g.comp h) :=
  rfl

/-- Taking the twisted product of two maps with the same domain is equivalent to taking the twisted
product of their codomains.

Note that, differently from `LinearMap.prodEquiv`, we do not take separate semirings, as we do not
clearly see applications of such generalization. -/
@[simps]
def prodEquivₛₗ {R S : Type*} [CommSemiring R] [Semiring S] (σ : R →+* S)
  {E : Type*} [AddCommGroup E] [Module R E]
  {F : Type*} [AddCommGroup F] [Module S F]
  {M : Type*} [AddCommGroup M] [Module R M] [SMulCommClass S S F] :
    ((M →ₗ[R] E) ×[σ] (M →ₛₗ[σ] F)) ≃ₗ[R] M →ₗ[R] E ×[σ] F where
  toFun f := f.1.prodₛₗ f.2
  invFun f := SemilinearProdModule.mk ((fstₛₗ _ _ _).comp f) ((sndₛₗ _ _ _).comp f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end prodₛₗ

section

variable {R S : Type*} [Semiring R] [Semiring S] (σ : R ≃+* S)
  (E : Type*) [AddCommGroup E] [Module R E]
  (F : Type*) [AddCommGroup F] [Module S F]
  {M : Type*} [AddCommGroup M] [Module R M]

/-- The left injection into a product is a linear map. -/
def inlₛₗ : E →ₗ[R] E ×[(σ : R →+* S)] F :=
  prodₛₗ LinearMap.id 0

@[simp]
lemma inlₛₗ_apply (v : E) : inlₛₗ σ E F v = SemilinearProdModule.mk v 0 := rfl

/-- The right injection into a product is a linear map. -/
def inrₛₗ : F →ₛₗ[(σ.symm : S →+* R)] E ×[(σ : R →+* S)] F where
  toFun v := SemilinearProdModule.mk 0 v
  map_add' v w := by ext <;> simp
  map_smul' c v := by ext <;> simp

@[simp]
lemma inrₛₗ_apply (v : F) : inrₛₗ σ E F v = SemilinearProdModule.mk 0 v := rfl

theorem range_inlₛₗ : range (inlₛₗ σ E F) = ker (sndₛₗ (σ : R →+* S) E F) := by
  ext x
  simp only [mem_ker, mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro h
    refine ⟨x.fst, by ext <;> simp_all⟩

theorem ker_sndₛₗ : ker (sndₛₗ (σ : R →+* S) E F) = range (inlₛₗ σ E F) :=
  Eq.symm <| range_inlₛₗ σ E F

theorem range_inrₛₗ : range (inrₛₗ σ E F) = ker (fstₛₗ (σ : R →+* S) E F) := by
  ext x
  simp only [mem_ker, mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro h
    refine ⟨x.snd, by ext <;> simp_all⟩

theorem ker_fstₛₗ : ker (fstₛₗ (σ : R →+* S) E F) = range (inrₛₗ σ E F) :=
  Eq.symm <| range_inrₛₗ σ E F

abbrev comp_symm_eq_id : RingHomCompTriple (σ.symm : S →+* R) (σ : R →+* S) (RingHom.id S) where
  comp_eq := by simp

@[simp] theorem fstₛₗ_comp_inlₛₗ : fstₛₗ (σ : R →+* S) E F ∘ₛₗ inlₛₗ σ E F = id := rfl

@[simp] theorem sndₛₗ_comp_inlₛₗ : sndₛₗ (σ : R →+* S) E F ∘ₛₗ inlₛₗ σ E F = 0 := rfl

@[simp] theorem fstₛₗ_comp_inrₛₗ : fstₛₗ (σ : R →+* S) E F ∘ₛₗ inrₛₗ σ E F = 0 := rfl

@[simp] theorem sndₛₗ_comp_inrₛₗ :
    @LinearMap.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (comp_symm_eq_id σ)
      (sndₛₗ (σ : R →+* S) E F) (inrₛₗ σ E F) = id := by ext; simp


@[simp]
theorem coe_inlₛₗ :
    (inlₛₗ σ E F : E → E ×[(σ : R →+* S)] F) = fun x => SemilinearProdModule.mk x 0 := rfl

@[simp]
theorem coe_inrₛₗ :
    (inrₛₗ σ E F : F → E ×[(σ : R →+* S)] F) = fun x => SemilinearProdModule.mk 0 x := by
  ext <;> rfl

theorem inlₛₗ_eq_prodₛₗ : inlₛₗ σ E F = prodₛₗ LinearMap.id 0 :=
  rfl

-- theorem inr_eq_prod : inr R M M₂ = prod 0 LinearMap.id :=
--   rfl

theorem inlₛₗ_injective : Function.Injective (inlₛₗ σ E F) := fun _ => by simp

theorem inrₛₗ_injective : Function.Injective (inrₛₗ σ E F) := fun _ => by simp

end

section coprodₛₗ

variable {M : Type*} [AddCommGroup M] [Module S M] (σ : R →+* S)

variable {σ E F}

/-- The coprod function `x : M × M₂ ↦ f x.1 + g x.2` is a linear map. -/
def coprodₛₗ (f : E →ₛₗ[σ] M) (g : F →ₗ[S] M) : E ×[σ] F →ₛₗ[σ] M :=
  f.comp (fstₛₗ _ _ _) + g.comp (sndₛₗ _ _ _)

@[simp]
theorem coprodₛₗ_apply (f : E →ₛₗ[σ] M) (g : F →ₗ[S] M) (x : E ×[σ] F) :
    coprodₛₗ f g x = f x.1 + g x.2 := rfl

theorem coprodₛₗ_zero_left (g : F →ₗ[S] M) : (0 : E →ₛₗ[σ] M).coprodₛₗ g = g.comp (sndₛₗ σ E F) :=
  zero_add _

theorem coprodₛₗ_zero_right (f : E →ₛₗ[σ] M) : f.coprodₛₗ (0 : F →ₗ[S] M) = f.comp (fstₛₗ σ E F) :=
  add_zero _

variable (σ) in
abbrev ring_comp_eq {T : Type*} [Semiring T] (σ₂ : S →+* T) :
    RingHomCompTriple σ σ₂ (σ₂.comp σ) where
  comp_eq := rfl

abbrev ring_id_comp_eq {T : Type*} [Semiring T] (σ₂ : S →+* T) :
    RingHomCompTriple (RingHom.id S) σ₂ (σ₂) where
  comp_eq := rfl

theorem comp_coprodₛₗ {M₂ : Type*} [AddCommGroup M₂] [Module S M₂] (f : M →ₗ[S] M₂)
    (g₁ : E →ₛₗ[σ] M) (g₂ : F →ₗ[S] M) :
    f.comp (g₁.coprodₛₗ g₂) = (f.comp g₁).coprodₛₗ (f.comp g₂) :=
  ext fun x => f.map_add (g₁ x.1) (g₂ x.2)

variable {R S : Type*} [Semiring R] [Semiring S] (σ : R ≃+* S)
  (E : Type*) [AddCommGroup E] [Module R E]
  (F : Type*) [AddCommGroup F] [Module S F]
  {M : Type*} [AddCommGroup M] [Module S M]

abbrev comp_id_eq : RingHomCompTriple (RingHom.id R) (σ : R →+* S) (σ : R →+* S) where
  comp_eq := rfl

@[simp]
theorem coprodₛₗ_inlₛₗ (f : E →ₛₗ[(σ : R →+* S)] M) (g : F →ₗ[S] M) :
    @LinearMap.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (comp_id_eq σ) (coprodₛₗ f g) (inlₛₗ σ E F)
    = f := by ext; simp

abbrev id_comp_eq : RingHomCompTriple ((σ.symm : S →+* R)) (σ : R →+* S) (RingHom.id S) where
  comp_eq := by simp

@[simp]
theorem coprodₛₗ_inrₛₗ (f : E →ₛₗ[(σ : R →+* S)] M) (g : F →ₗ[S] M) :
    @LinearMap.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (id_comp_eq σ) (coprodₛₗ f g) (inrₛₗ σ E F)
      = g := by
  ext; simp

-- theorem fst_eq_coprod : fst R M M₂ = coprod LinearMap.id 0 := by ext; simp

-- theorem snd_eq_coprod : snd R M M₂ = coprod 0 LinearMap.id := by ext; simp

-- @[simp]
-- theorem coprod_comp_prod (f : M₂ →ₗ[R] M₄) (g : M₃ →ₗ[R] M₄) (f' : M →ₗ[R] M₂) (g' : M →ₗ[R] M₃) :
--     (f.coprod g).comp (f'.prod g') = f.comp f' + g.comp g' :=
--   rfl

-- @[simp]
-- theorem coprod_map_prod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) (S : Submodule R M)
--     (S' : Submodule R M₂) : (Submodule.prod S S').map (LinearMap.coprod f g) = S.map f ⊔ S'.map g :=
--   SetLike.coe_injective <| by
--     simp only [LinearMap.coprod_apply, Submodule.coe_sup, Submodule.map_coe]
--     rw [← Set.image2_add, Set.image2_image_left, Set.image2_image_right]
--     exact Set.image_prod fun m m₂ => f m + g m₂

-- @[simp]
-- theorem coprod_comp_inl_inr (f : M × M₂ →ₗ[R] M₃) :
--     (f.comp (inl R M M₂)).coprod (f.comp (inr R M M₂)) = f := by
--   rw [← comp_coprod, coprod_inl_inr, comp_id]

-- /-- Taking the product of two maps with the same codomain is equivalent to taking the product of
-- their domains.

-- See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
-- @[simps]
-- def coprodEquiv [Module S M₃] [SMulCommClass R S M₃] :
--     ((M →ₗ[R] M₃) × (M₂ →ₗ[R] M₃)) ≃ₗ[S] M × M₂ →ₗ[R] M₃ where
--   toFun f := f.1.coprod f.2
--   invFun f := (f.comp (inl _ _ _), f.comp (inr _ _ _))
--   left_inv f := by simp only [coprod_inl, coprod_inr]
--   right_inv f := by simp only [← comp_coprod, comp_id, coprod_inl_inr]
--   map_add' a b := by
--     ext
--     simp only [Prod.snd_add, add_apply, coprod_apply, Prod.fst_add, add_add_add_comm]
--   map_smul' r a := by
--     dsimp
--     ext
--     simp only [smul_add, smul_apply, coprod_apply]

-- theorem prod_ext_iff {f g : M × M₂ →ₗ[R] M₃} :
--     f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _) :=
--   (coprodEquiv ℕ).symm.injective.eq_iff.symm.trans Prod.ext_iff

end coprodₛₗ

-- prodMap ignored

section Graph

open LinearMap

variable (f : E →ₛₗ[σ] F)

/-- Graph of a semilinear map. -/
def graphₛₗ : Submodule R (E ×[σ] F) where
  carrier := { p | p.snd = f p.fst }
  add_mem' (ha : _ = _) (hb : _ = _) := by
    change _ + _ = f (_ + _)
    rw [map_add, ha, hb]
  zero_mem' := Eq.symm (map_zero f)
  smul_mem' c x (hx : _ = _) := by
    change _ • _ = f (_ • _)
    rw [hx, map_smulₛₗ]

@[simp]
theorem mem_graphₛₗ_iff (x : E ×[σ] F) : x ∈ f.graphₛₗ ↔ x.2 = f x.1 :=
  Iff.rfl

theorem graphₛₗ_eq_ker_coprodₛₗ : f.graphₛₗ = ker (coprodₛₗ (-f) LinearMap.id) := by
  ext x
  change _ = _ ↔ -f x.1 + x.2 = _
  rw [add_comm, add_neg_eq_zero]

theorem graphₛₗ_eq_range_prodₛₗ : f.graphₛₗ = range (prodₛₗ LinearMap.id f) := by
  ext x
  refine ⟨fun hx => ⟨x.1, ?_⟩, fun ⟨u, hu⟩ => hu ▸ rfl⟩
  ext
  · simp
  · simpa using hx.symm

-- section LineTest

-- open Set Function

-- variable {R S G H I : Type*}
--   [Semiring R] [Semiring S] {σ : R →+* S} [RingHomSurjective σ]
--   [AddCommMonoid G] [Module R G]
--   [AddCommMonoid H] [Module S H]
--   [AddCommMonoid I] [Module S I]

-- /-- **Vertical line test** for linear maps.

-- Let `f : G → H × I` be a linear (or semilinear) map to a product. Assume that `f` is surjective on
-- the first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at
-- most once. Then the image of `f` is the graph of some linear map `f' : H → I`. -/
-- lemma LinearMap.exists_range_eq_graph {f : G →ₛₗ[σ] H × I} (hf₁ : Surjective (Prod.fst ∘ f))
--     (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 → (f g₁).2 = (f g₂).2) :
--     ∃ f' : H →ₗ[S] I, LinearMap.range f = LinearMap.graph f' := by
--   obtain ⟨f', hf'⟩ :=
--     AddMonoidHom.exists_mrange_eq_mgraph (G := G) (H := H) (I := I) (f := f) hf₁ hf
--   simp only [SetLike.ext_iff, AddMonoidHom.mem_mrange, AddMonoidHom.coe_coe,
--     AddMonoidHom.mem_mgraph] at hf'
--   use
--   { toFun := f'.toFun
--     map_add' := f'.map_add'
--     map_smul' := by
--       intro s h
--       simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, RingHom.id_apply]
--       refine (hf' (s • h, _)).mp ?_
--       rw [← Prod.smul_mk, ← LinearMap.mem_range]
--       apply Submodule.smul_mem
--       rw [LinearMap.mem_range, hf'] }
--   ext x
--   simpa only [mem_range, Eq.comm, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, mem_graph_iff,
--     coe_mk, AddHom.coe_mk, AddMonoidHom.coe_coe, Set.mem_range] using hf' x

-- /-- **Vertical line test** for linear maps.

-- Let `G ≤ H × I` be a submodule of a product of modules. Assume that `G` maps bijectively to the
-- first factor. Then `G` is the graph of some linear map `f : H →ₗ[R] I`. -/
-- lemma Submodule.exists_eq_graph {G : Submodule S (H × I)} (hf₁ : Bijective (Prod.fst ∘ G.subtype)) :
--     ∃ f : H →ₗ[S] I, G = LinearMap.graph f := by
--   simpa only [range_subtype] using LinearMap.exists_range_eq_graph hf₁.surjective
--       (fun a b h ↦ congr_arg (Prod.snd ∘ G.subtype) (hf₁.injective h))

-- /-- **Line test** for module isomorphisms.

-- Let `f : G → H × I` be a linear (or semilinear) map to a product of modules. Assume that `f` is
-- surjective onto both factors and that the image of `f` intersects every "vertical line"
-- `{(h, i) | i : I}` and every "horizontal line" `{(h, i) | h : H}` at most once. Then the image of
-- `f` is the graph of some module isomorphism `f' : H ≃ I`. -/
-- lemma LinearMap.exists_linearEquiv_eq_graph {f : G →ₛₗ[σ] H × I} (hf₁ : Surjective (Prod.fst ∘ f))
--     (hf₂ : Surjective (Prod.snd ∘ f)) (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2) :
--     ∃ e : H ≃ₗ[S] I, range f = e.toLinearMap.graph := by
--   obtain ⟨e₁, he₁⟩ := f.exists_range_eq_graph hf₁ fun _ _ ↦ (hf _ _).1
--   obtain ⟨e₂, he₂⟩ := ((LinearEquiv.prodComm _ _ _).toLinearMap.comp f).exists_range_eq_graph
--     (by simpa) <| by simp [hf]
--   have he₁₂ h i : e₁ h = i ↔ e₂ i = h := by
--     simp only [SetLike.ext_iff, LinearMap.mem_graph_iff] at he₁ he₂
--     rw [Eq.comm, ← he₁ (h, i), Eq.comm, ← he₂ (i, h)]
--     simp only [mem_range, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
--       LinearEquiv.prodComm_apply, Prod.swap_eq_iff_eq_swap, Prod.swap_prod_mk]
--   exact ⟨
--   { toFun := e₁
--     map_smul' := e₁.map_smul'
--     map_add' := e₁.map_add'
--     invFun := e₂
--     left_inv := fun h ↦ by rw [← he₁₂]
--     right_inv := fun i ↦ by rw [he₁₂] }, he₁⟩

-- /-- **Goursat's lemma** for module isomorphisms.

-- Let `G ≤ H × I` be a submodule of a product of modules. Assume that the natural maps from `G` to
-- both factors are bijective. Then `G` is the graph of some module isomorphism `f : H ≃ I`. -/
-- lemma Submodule.exists_equiv_eq_graph {G : Submodule S (H × I)}
--     (hG₁ : Bijective (Prod.fst ∘ G.subtype)) (hG₂ : Bijective (Prod.snd ∘ G.subtype)) :
--     ∃ e : H ≃ₗ[S] I, G = e.toLinearMap.graph := by
--   simpa only [range_subtype] using LinearMap.exists_linearEquiv_eq_graph
--     hG₁.surjective hG₂.surjective fun _ _ ↦ hG₁.injective.eq_iff.trans hG₂.injective.eq_iff.symm

-- end LineTest
end Graph

end LinearMap

end

-- section map_mul

-- variable {A : Type*} [NonUnitalNonAssocSemiring A] [Module R A]
-- variable {B : Type*} [NonUnitalNonAssocSemiring B] [Module R B]

-- theorem inl_map_mul (a₁ a₂ : A) :
--     LinearMap.inl R A B (a₁ * a₂) = LinearMap.inl R A B a₁ * LinearMap.inl R A B a₂ :=
--   Prod.ext rfl (by simp)

-- theorem inr_map_mul (b₁ b₂ : B) :
--     LinearMap.inr R A B (b₁ * b₂) = LinearMap.inr R A B b₁ * LinearMap.inr R A B b₂ :=
--   Prod.ext (by simp) rfl

-- end map_mul

-- end LinearMap

-- end Prod

-- namespace LinearMap

-- variable (R M M₂)
-- variable [CommSemiring R]
-- variable [AddCommMonoid M] [AddCommMonoid M₂]
-- variable [Module R M] [Module R M₂]

-- /-- `LinearMap.prodMap` as an `AlgHom` -/
-- @[simps!]
-- def prodMapAlgHom : Module.End R M × Module.End R M₂ →ₐ[R] Module.End R (M × M₂) :=
--   { prodMapRingHom R M M₂ with commutes' := fun _ => rfl }

-- end LinearMap

-- namespace LinearMap

-- open Submodule

-- variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
--   [Module R M] [Module R M₂] [Module R M₃] [Module R M₄]

-- theorem range_coprod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) : range (f.coprod g) = range f ⊔ range g :=
--   Submodule.ext fun x => by simp [mem_sup]

-- theorem isCompl_range_inl_inr : IsCompl (range <| inl R M M₂) (range <| inr R M M₂) := by
--   constructor
--   · rw [disjoint_def]
--     rintro ⟨_, _⟩ ⟨x, hx⟩ ⟨y, hy⟩
--     simp only [Prod.ext_iff, inl_apply, inr_apply] at hx hy ⊢
--     exact ⟨hy.1.symm, hx.2.symm⟩
--   · rw [codisjoint_iff_le_sup]
--     rintro ⟨x, y⟩ -
--     simp only [mem_sup, mem_range]
--     refine ⟨(x, 0), ⟨x, rfl⟩, (0, y), ⟨y, rfl⟩, ?_⟩
--     simp

-- theorem sup_range_inl_inr : (range <| inl R M M₂) ⊔ (range <| inr R M M₂) = ⊤ :=
--   IsCompl.sup_eq_top isCompl_range_inl_inr

-- theorem disjoint_inl_inr : Disjoint (range <| inl R M M₂) (range <| inr R M M₂) := by
--   simp +contextual [disjoint_def, @eq_comm M 0]

-- theorem map_coprod_prod (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) (p : Submodule R M)
--     (q : Submodule R M₂) : map (coprod f g) (p.prod q) = map f p ⊔ map g q :=
--   coprod_map_prod f g p q

-- theorem comap_prod_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) (p : Submodule R M₂)
--     (q : Submodule R M₃) : comap (prod f g) (p.prod q) = comap f p ⊓ comap g q :=
--   Submodule.ext fun _x => Iff.rfl

-- theorem prod_eq_inf_comap (p : Submodule R M) (q : Submodule R M₂) :
--     p.prod q = p.comap (LinearMap.fst R M M₂) ⊓ q.comap (LinearMap.snd R M M₂) :=
--   Submodule.ext fun _x => Iff.rfl

-- theorem prod_eq_sup_map (p : Submodule R M) (q : Submodule R M₂) :
--     p.prod q = p.map (LinearMap.inl R M M₂) ⊔ q.map (LinearMap.inr R M M₂) := by
--   rw [← map_coprod_prod, coprod_inl_inr, map_id]

-- theorem span_inl_union_inr {s : Set M} {t : Set M₂} :
--     span R (inl R M M₂ '' s ∪ inr R M M₂ '' t) = (span R s).prod (span R t) := by
--   rw [span_union, prod_eq_sup_map, ← span_image, ← span_image]

-- @[simp]
-- theorem ker_prod (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) : ker (prod f g) = ker f ⊓ ker g := by
--   rw [ker, ← prod_bot, comap_prod_prod]; rfl

-- theorem range_prod_le (f : M →ₗ[R] M₂) (g : M →ₗ[R] M₃) :
--     range (prod f g) ≤ (range f).prod (range g) := by
--   simp only [SetLike.le_def, prod_apply, mem_range, mem_prod, exists_imp]
--   rintro _ x rfl
--   exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩

-- theorem ker_prod_ker_le_ker_coprod {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂] {M₃ : Type*}
--     [AddCommMonoid M₃] [Module R M₃] (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) :
--     (ker f).prod (ker g) ≤ ker (f.coprod g) := by
--   rintro ⟨y, z⟩
--   simp +contextual

-- theorem ker_coprod_of_disjoint_range {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] {M₃ : Type*}
--     [AddCommGroup M₃] [Module R M₃] (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃)
--     (hd : Disjoint (range f) (range g)) : ker (f.coprod g) = (ker f).prod (ker g) := by
--   apply le_antisymm _ (ker_prod_ker_le_ker_coprod f g)
--   rintro ⟨y, z⟩ h
--   simp only [mem_ker, mem_prod, coprod_apply] at h ⊢
--   have : f y ∈ (range f) ⊓ (range g) := by
--     simp only [true_and, mem_range, mem_inf, exists_apply_eq_apply]
--     use -z
--     rwa [eq_comm, map_neg, ← sub_eq_zero, sub_neg_eq_add]
--   rw [hd.eq_bot, mem_bot] at this
--   rw [this] at h
--   simpa [this] using h

-- set_option backward.isDefEq.respectTransparency false in
-- /-- Given a linear map `f : E →ₗ[R] F` and a complement `C` of its kernel, we get a linear
-- equivalence between `C` and `range f`. -/
-- @[simps!]
-- noncomputable def kerComplementEquivRange {R M M₂ : Type*} [Ring R] [AddCommGroup M]
--     [AddCommGroup M₂] [Module R M] [Module R M₂] (f : M →ₗ[R] M₂) {C : Submodule R M}
--     (h : IsCompl C (LinearMap.ker f)) : C ≃ₗ[R] range f :=
--   .ofBijective (codRestrict (range f) f (mem_range_self f) ∘ₗ C.subtype)
--   ⟨by simpa [← ker_eq_bot, ker_codRestrict, ker_comp, ← disjoint_iff_comap_eq_bot] using h.disjoint,
--    by
--     rintro ⟨-, x, rfl⟩
--     obtain ⟨y, z, hy, hz, rfl⟩ := codisjoint_iff_exists_add_eq.mp h.codisjoint x
--     use ⟨y, hy⟩
--     simpa [Subtype.ext_iff]⟩

-- end LinearMap

-- namespace Submodule

-- open LinearMap

-- variable [Semiring R]
-- variable [AddCommMonoid M] [AddCommMonoid M₂]
-- variable [Module R M] [Module R M₂]

-- theorem sup_eq_range (p q : Submodule R M) : p ⊔ q = range (p.subtype.coprod q.subtype) :=
--   Submodule.ext fun x => by simp [Submodule.mem_sup]

-- variable (p : Submodule R M) (q : Submodule R M₂)

-- @[simp]
-- theorem map_inl : p.map (inl R M M₂) = prod p ⊥ := by
--   ext ⟨x, y⟩
--   simp only [and_left_comm, eq_comm, mem_map, Prod.mk_inj, inl_apply, mem_bot, exists_eq_left',
--     mem_prod]

-- @[simp]
-- theorem map_inr : q.map (inr R M M₂) = prod ⊥ q := by
--   ext ⟨x, y⟩; simp [and_left_comm, eq_comm, and_comm]

-- @[simp]
-- theorem comap_fst : p.comap (fst R M M₂) = prod p ⊤ := by ext ⟨x, y⟩; simp

-- @[simp]
-- theorem comap_snd : q.comap (snd R M M₂) = prod ⊤ q := by ext ⟨x, y⟩; simp

-- @[simp]
-- theorem prod_comap_inl : (prod p q).comap (inl R M M₂) = p := by ext; simp

-- @[simp]
-- theorem prod_comap_inr : (prod p q).comap (inr R M M₂) = q := by ext; simp

-- @[simp]
-- theorem prod_map_fst : (prod p q).map (fst R M M₂) = p := by
--   ext x; simp [(⟨0, zero_mem _⟩ : ∃ x, x ∈ q)]

-- @[simp]
-- theorem prod_map_snd : (prod p q).map (snd R M M₂) = q := by
--   ext x; simp [(⟨0, zero_mem _⟩ : ∃ x, x ∈ p)]

-- @[simp]
-- theorem ker_inl : ker (inl R M M₂) = ⊥ := by rw [ker, ← prod_bot, prod_comap_inl]

-- @[simp]
-- theorem ker_inr : ker (inr R M M₂) = ⊥ := by rw [ker, ← prod_bot, prod_comap_inr]

-- @[simp]
-- theorem range_fst : range (fst R M M₂) = ⊤ := by rw [range_eq_map, ← prod_top, prod_map_fst]

-- @[simp]
-- theorem range_snd : range (snd R M M₂) = ⊤ := by rw [range_eq_map, ← prod_top, prod_map_snd]

-- variable (R M M₂)

-- /-- `M` as a submodule of `M × N`. -/
-- def fst : Submodule R (M × M₂) :=
--   (⊥ : Submodule R M₂).comap (LinearMap.snd R M M₂)

-- /-- `M` as a submodule of `M × N` is isomorphic to `M`. -/
-- @[simps]
-- def fstEquiv : Submodule.fst R M M₂ ≃ₗ[R] M where
--   toFun x := x.1.1
--   invFun m := ⟨⟨m, 0⟩, by aesop⟩
--   map_add' := by simp
--   map_smul' := by simp
--   left_inv x := by aesop (add norm simp Submodule.fst)
--   right_inv x := by simp

-- theorem fst_map_fst : (Submodule.fst R M M₂).map (LinearMap.fst R M M₂) = ⊤ := by
--   aesop

-- theorem fst_map_snd : (Submodule.fst R M M₂).map (LinearMap.snd R M M₂) = ⊥ := by
--   aesop (add simp fst)

-- /-- `N` as a submodule of `M × N`. -/
-- def snd : Submodule R (M × M₂) :=
--   (⊥ : Submodule R M).comap (LinearMap.fst R M M₂)

-- /-- `N` as a submodule of `M × N` is isomorphic to `N`. -/
-- @[simps]
-- def sndEquiv : Submodule.snd R M M₂ ≃ₗ[R] M₂ where
--   toFun x := x.1.2
--   invFun n := ⟨⟨0, n⟩, by aesop⟩
--   map_add' := by simp
--   map_smul' := by simp
--   left_inv x := by aesop (add norm simp Submodule.snd)

-- theorem snd_map_fst : (Submodule.snd R M M₂).map (LinearMap.fst R M M₂) = ⊥ := by
--   aesop (add simp snd)

-- theorem snd_map_snd : (Submodule.snd R M M₂).map (LinearMap.snd R M M₂) = ⊤ := by
--   aesop

-- theorem fst_sup_snd : Submodule.fst R M M₂ ⊔ Submodule.snd R M M₂ = ⊤ := by
--   rw [eq_top_iff]
--   rintro ⟨m, n⟩ -
--   rw [show (m, n) = (m, 0) + (0, n) by simp]
--   apply Submodule.add_mem (Submodule.fst R M M₂ ⊔ Submodule.snd R M M₂)
--   · exact Submodule.mem_sup_left (Submodule.mem_comap.mpr (by simp))
--   · exact Submodule.mem_sup_right (Submodule.mem_comap.mpr (by simp))

-- theorem fst_inf_snd : Submodule.fst R M M₂ ⊓ Submodule.snd R M M₂ = ⊥ := by
--   aesop

-- theorem le_prod_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} {q : Submodule R (M × M₂)} :
--     q ≤ p₁.prod p₂ ↔ map (LinearMap.fst R M M₂) q ≤ p₁ ∧ map (LinearMap.snd R M M₂) q ≤ p₂ := by
--   constructor
--   · intro h
--     constructor
--     · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
--       exact (h hy1).1
--     · rintro x ⟨⟨y1, y2⟩, ⟨hy1, rfl⟩⟩
--       exact (h hy1).2
--   · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ h
--     exact ⟨hH ⟨_, h, rfl⟩, hK ⟨_, h, rfl⟩⟩

-- theorem prod_le_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} {q : Submodule R (M × M₂)} :
--     p₁.prod p₂ ≤ q ↔ map (LinearMap.inl R M M₂) p₁ ≤ q ∧ map (LinearMap.inr R M M₂) p₂ ≤ q := by
--   constructor
--   · intro h
--     constructor
--     · rintro _ ⟨x, hx, rfl⟩
--       apply h
--       exact ⟨hx, zero_mem p₂⟩
--     · rintro _ ⟨x, hx, rfl⟩
--       apply h
--       exact ⟨zero_mem p₁, hx⟩
--   · rintro ⟨hH, hK⟩ ⟨x1, x2⟩ ⟨h1, h2⟩
--     have h1' : (LinearMap.inl R _ _) x1 ∈ q := by
--       apply hH
--       simpa using h1
--     have h2' : (LinearMap.inr R _ _) x2 ∈ q := by
--       apply hK
--       simpa using h2
--     simpa using add_mem h1' h2'

-- theorem prod_eq_bot_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} :
--     p₁.prod p₂ = ⊥ ↔ p₁ = ⊥ ∧ p₂ = ⊥ := by
--   simp only [eq_bot_iff, prod_le_iff, (gc_map_comap _).le_iff_le, comap_bot, ker_inl, ker_inr]

-- theorem prod_eq_top_iff {p₁ : Submodule R M} {p₂ : Submodule R M₂} :
--     p₁.prod p₂ = ⊤ ↔ p₁ = ⊤ ∧ p₂ = ⊤ := by
--   simp only [eq_top_iff, le_prod_iff, map_top, range_fst, range_snd]

-- end Submodule

-- namespace LinearEquiv

-- /-- Product of modules is commutative up to linear isomorphism. -/
-- @[simps apply]
-- def prodComm (R M N : Type*) [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
--     [Module R N] : (M × N) ≃ₗ[R] N × M :=
--   { AddEquiv.prodComm with
--     toFun := Prod.swap
--     map_smul' := fun _r ⟨_m, _n⟩ => rfl }

-- section prodComm

-- variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂]

-- theorem fst_comp_prodComm :
--     (LinearMap.fst R M₂ M).comp (prodComm R M M₂).toLinearMap = (LinearMap.snd R M M₂) := by
--   ext <;> simp

-- theorem snd_comp_prodComm :
--     (LinearMap.snd R M₂ M).comp (prodComm R M M₂).toLinearMap = (LinearMap.fst R M M₂) := by
--   ext <;> simp

-- @[simp]
-- theorem symm_prodComm : (prodComm R M M₂).symm = prodComm R M₂ M := rfl

-- end prodComm

-- /-- Product of modules is associative up to linear isomorphism. -/
-- @[simps apply]
-- def prodAssoc (R M₁ M₂ M₃ : Type*) [Semiring R]
--     [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
--     [Module R M₁] [Module R M₂] [Module R M₃] : ((M₁ × M₂) × M₃) ≃ₗ[R] (M₁ × (M₂ × M₃)) :=
--   { AddEquiv.prodAssoc with
--     map_smul' := fun _r ⟨_m, _n⟩ => rfl }

-- section prodAssoc

-- variable {M₁ : Type*}
-- variable [Semiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
-- variable [Module R M₁] [Module R M₂] [Module R M₃]

-- theorem fst_comp_prodAssoc :
--     (LinearMap.fst R M₁ (M₂ × M₃)).comp (prodAssoc R M₁ M₂ M₃).toLinearMap =
--     (LinearMap.fst R M₁ M₂).comp (LinearMap.fst R (M₁ × M₂) M₃) := by
--   ext <;> simp

-- theorem snd_comp_prodAssoc :
--     (LinearMap.snd R M₁ (M₂ × M₃)).comp (prodAssoc R M₁ M₂ M₃).toLinearMap =
--     (LinearMap.snd R M₁ M₂).prodMap (LinearMap.id : M₃ →ₗ[R] M₃) := by
--   ext <;> simp

-- end prodAssoc

-- section SkewSwap

-- variable (R M N)
-- variable [Semiring R]
-- variable [AddCommGroup M] [AddCommGroup N]
-- variable [Module R M] [Module R N]

-- /-- The map `(x, y) ↦ (-y, x)` as a linear equivalence. -/
-- protected def skewSwap : (M × N) ≃ₗ[R] (N × M) where
--   toFun x := (-x.2, x.1)
--   invFun x := (x.2, -x.1)
--   map_add' _ _ := by
--     simp [add_comm]
--   map_smul' _ _ := by
--     simp
--   left_inv _ := by
--     simp
--   right_inv _ := by
--     simp

-- variable {R M N}

-- @[simp]
-- theorem skewSwap_apply (x : M × N) : LinearEquiv.skewSwap R M N x = (-x.2, x.1) := rfl

-- @[simp]
-- theorem skewSwap_symm_apply (x : N × M) : (LinearEquiv.skewSwap R M N).symm x = (x.2, -x.1) := rfl

-- end SkewSwap

-- section

-- variable (R M M₂ M₃ M₄)
-- variable [Semiring R]
-- variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
-- variable [Module R M] [Module R M₂] [Module R M₃] [Module R M₄]

-- /-- Four-way commutativity of `prod`. The name matches `mul_mul_mul_comm`. -/
-- @[simps apply]
-- def prodProdProdComm : ((M × M₂) × M₃ × M₄) ≃ₗ[R] (M × M₃) × M₂ × M₄ :=
--   { AddEquiv.prodProdProdComm M M₂ M₃ M₄ with
--     toFun := fun mnmn => ((mnmn.1.1, mnmn.2.1), (mnmn.1.2, mnmn.2.2))
--     invFun := fun mmnn => ((mmnn.1.1, mmnn.2.1), (mmnn.1.2, mmnn.2.2))
--     map_smul' := fun _c _mnmn => rfl }

-- @[simp]
-- theorem prodProdProdComm_symm :
--     (prodProdProdComm R M M₂ M₃ M₄).symm = prodProdProdComm R M M₃ M₂ M₄ :=
--   rfl

-- @[simp]
-- theorem prodProdProdComm_toAddEquiv :
--     (prodProdProdComm R M M₂ M₃ M₄ : _ ≃+ _) = AddEquiv.prodProdProdComm M M₂ M₃ M₄ :=
--   rfl

-- end

-- section

-- variable [Semiring R]
-- variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
-- variable {module_M : Module R M} {module_M₂ : Module R M₂}
-- variable {module_M₃ : Module R M₃} {module_M₄ : Module R M₄}
-- variable (e₁ : M ≃ₗ[R] M₂) (e₂ : M₃ ≃ₗ[R] M₄)

-- /-- Product of linear equivalences; the maps come from `Equiv.prodCongr`. -/
-- protected def prodCongr : (M × M₃) ≃ₗ[R] M₂ × M₄ :=
--   { e₁.toAddEquiv.prodCongr e₂.toAddEquiv with
--     map_smul' := fun c _x => Prod.ext (e₁.map_smulₛₗ c _) (e₂.map_smulₛₗ c _) }

-- theorem prodCongr_symm : (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm :=
--   rfl

-- @[simp]
-- theorem prodCongr_apply (p) : e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2) :=
--   rfl

-- @[simp, norm_cast]
-- theorem coe_prodCongr :
--     (e₁.prodCongr e₂ : M × M₃ →ₗ[R] M₂ × M₄) = (e₁ : M →ₗ[R] M₂).prodMap (e₂ : M₃ →ₗ[R] M₄) :=
--   rfl

-- end

-- section

-- variable [Semiring R]
-- variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommGroup M₄]
-- variable {module_M : Module R M} {module_M₂ : Module R M₂}
-- variable {module_M₃ : Module R M₃} {module_M₄ : Module R M₄}
-- variable (e₁ : M ≃ₗ[R] M₂) (e₂ : M₃ ≃ₗ[R] M₄)

-- /-- Equivalence given by a block lower diagonal matrix. `e₁` and `e₂` are diagonal square blocks,
--   and `f` is a rectangular block below the diagonal. -/
-- protected def skewProd (f : M →ₗ[R] M₄) : (M × M₃) ≃ₗ[R] M₂ × M₄ :=
--   { ((e₁ : M →ₗ[R] M₂).comp (LinearMap.fst R M M₃)).prod
--       ((e₂ : M₃ →ₗ[R] M₄).comp (LinearMap.snd R M M₃) +
--         f.comp (LinearMap.fst R M M₃)) with
--     invFun := fun p : M₂ × M₄ => (e₁.symm p.1, e₂.symm (p.2 - f (e₁.symm p.1)))
--     left_inv := fun p => by simp
--     right_inv := fun p => by simp }

-- @[simp]
-- theorem skewProd_apply (f : M →ₗ[R] M₄) (x) : e₁.skewProd e₂ f x = (e₁ x.1, e₂ x.2 + f x.1) :=
--   rfl

-- @[simp]
-- theorem skewProd_symm_apply (f : M →ₗ[R] M₄) (x) :
--     (e₁.skewProd e₂ f).symm x = (e₁.symm x.1, e₂.symm (x.2 - f (e₁.symm x.1))) :=
--   rfl

-- end

-- section Unique

-- variable [Semiring R]
-- variable [AddCommMonoid M] [AddCommMonoid M₂]
-- variable [Module R M] [Module R M₂] [Unique M₂]

-- /-- Multiplying by the trivial module from the left does not change the structure.
-- This is the `LinearEquiv` version of `AddEquiv.uniqueProd`. -/
-- @[simps!]
-- def uniqueProd : (M₂ × M) ≃ₗ[R] M :=
--   AddEquiv.uniqueProd.toLinearEquiv (by simp [AddEquiv.uniqueProd])

-- lemma coe_uniqueProd :
--     (uniqueProd (R := R) (M := M) (M₂ := M₂) : (M₂ × M) ≃ M) = Equiv.uniqueProd M M₂ := rfl

-- /-- Multiplying by the trivial module from the right does not change the structure.
-- This is the `LinearEquiv` version of `AddEquiv.prodUnique`. -/
-- @[simps!]
-- def prodUnique : (M × M₂) ≃ₗ[R] M :=
--   AddEquiv.prodUnique.toLinearEquiv (by simp [AddEquiv.prodUnique])

-- lemma coe_prodUnique :
--     (prodUnique (R := R) (M := M) (M₂ := M₂) : (M × M₂) ≃ M) = Equiv.prodUnique M M₂ := rfl

-- end Unique

-- end LinearEquiv

-- namespace LinearMap

-- open Submodule

-- variable [Ring R]
-- variable [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]
-- variable [Module R M] [Module R M₂] [Module R M₃]

-- /-- If the union of the kernels `ker f` and `ker g` spans the domain, then the range of
-- `Prod f g` is equal to the product of `range f` and `range g`. -/
-- theorem range_prod_eq {f : M →ₗ[R] M₂} {g : M →ₗ[R] M₃} (h : ker f ⊔ ker g = ⊤) :
--     range (prod f g) = (range f).prod (range g) := by
--   refine le_antisymm (f.range_prod_le g) ?_
--   simp only [SetLike.le_def, prod_apply, mem_range, mem_prod, exists_imp, and_imp,
--     Prod.forall, Pi.prod]
--   rintro _ _ x rfl y rfl
--   -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify `(f := f)`
--   simp only [Prod.mk_inj, ← sub_mem_ker_iff (f := f)]
--   have : y - x ∈ ker f ⊔ ker g := by simp only [h, mem_top]
--   rcases mem_sup.1 this with ⟨x', hx', y', hy', H⟩
--   refine ⟨x' + x, ?_, ?_⟩
--   · rwa [add_sub_cancel_right]
--   · simp [← eq_sub_iff_add_eq.1 H, map_add, mem_ker.mp hy']

-- end LinearMap

-- namespace LinearMap

-- section Graph

-- variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommGroup M₃] [AddCommGroup M₄]
--   [Module R M] [Module R M₂] [Module R M₃] [Module R M₄] (f : M →ₗ[R] M₂) (g : M₃ →ₗ[R] M₄)

-- /-- Graph of a linear map. -/
-- def graph : Submodule R (M × M₂) where
--   carrier := { p | p.2 = f p.1 }
--   add_mem' (ha : _ = _) (hb : _ = _) := by
--     change _ + _ = f (_ + _)
--     rw [map_add, ha, hb]
--   zero_mem' := Eq.symm (map_zero f)
--   smul_mem' c x (hx : _ = _) := by
--     change _ • _ = f (_ • _)
--     rw [map_smul, hx]

-- @[simp]
-- theorem mem_graph_iff (x : M × M₂) : x ∈ f.graph ↔ x.2 = f x.1 :=
--   Iff.rfl

-- theorem graph_eq_ker_coprod : g.graph = ker ((-g).coprod LinearMap.id) := by
--   ext x
--   change _ = _ ↔ -g x.1 + x.2 = _
--   rw [add_comm, add_neg_eq_zero]

-- theorem graph_eq_range_prod : f.graph = range (LinearMap.id.prod f) := by
--   ext x
--   exact ⟨fun hx => ⟨x.1, Prod.ext rfl hx.symm⟩, fun ⟨u, hu⟩ => hu ▸ rfl⟩

-- end Graph

-- end LinearMap

-- section LineTest

-- open Set Function

-- variable {R S G H I : Type*}
--   [Semiring R] [Semiring S] {σ : R →+* S} [RingHomSurjective σ]
--   [AddCommMonoid G] [Module R G]
--   [AddCommMonoid H] [Module S H]
--   [AddCommMonoid I] [Module S I]

-- /-- **Vertical line test** for linear maps.

-- Let `f : G → H × I` be a linear (or semilinear) map to a product. Assume that `f` is surjective on
-- the first factor and that the image of `f` intersects every "vertical line" `{(h, i) | i : I}` at
-- most once. Then the image of `f` is the graph of some linear map `f' : H → I`. -/
-- lemma LinearMap.exists_range_eq_graph {f : G →ₛₗ[σ] H × I} (hf₁ : Surjective (Prod.fst ∘ f))
--     (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 → (f g₁).2 = (f g₂).2) :
--     ∃ f' : H →ₗ[S] I, LinearMap.range f = LinearMap.graph f' := by
--   obtain ⟨f', hf'⟩ :=
--     AddMonoidHom.exists_mrange_eq_mgraph (G := G) (H := H) (I := I) (f := f) hf₁ hf
--   simp only [SetLike.ext_iff, AddMonoidHom.mem_mrange, AddMonoidHom.coe_coe,
--     AddMonoidHom.mem_mgraph] at hf'
--   use
--   { toFun := f'.toFun
--     map_add' := f'.map_add'
--     map_smul' := by
--       intro s h
--       simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, RingHom.id_apply]
--       refine (hf' (s • h, _)).mp ?_
--       rw [← Prod.smul_mk, ← LinearMap.mem_range]
--       apply Submodule.smul_mem
--       rw [LinearMap.mem_range, hf'] }
--   ext x
--   simpa only [mem_range, Eq.comm, ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, mem_graph_iff,
--     coe_mk, AddHom.coe_mk, AddMonoidHom.coe_coe, Set.mem_range] using hf' x

-- /-- **Vertical line test** for linear maps.

-- Let `G ≤ H × I` be a submodule of a product of modules. Assume that `G` maps bijectively to the
-- first factor. Then `G` is the graph of some linear map `f : H →ₗ[R] I`. -/
-- lemma Submodule.exists_eq_graph {G : Submodule S (H × I)} (hf₁ : Bijective (Prod.fst ∘ G.subtype)) :
--     ∃ f : H →ₗ[S] I, G = LinearMap.graph f := by
--   simpa only [range_subtype] using LinearMap.exists_range_eq_graph hf₁.surjective
--       (fun a b h ↦ congr_arg (Prod.snd ∘ G.subtype) (hf₁.injective h))

-- /-- **Line test** for module isomorphisms.

-- Let `f : G → H × I` be a linear (or semilinear) map to a product of modules. Assume that `f` is
-- surjective onto both factors and that the image of `f` intersects every "vertical line"
-- `{(h, i) | i : I}` and every "horizontal line" `{(h, i) | h : H}` at most once. Then the image of
-- `f` is the graph of some module isomorphism `f' : H ≃ I`. -/
-- lemma LinearMap.exists_linearEquiv_eq_graph {f : G →ₛₗ[σ] H × I} (hf₁ : Surjective (Prod.fst ∘ f))
--     (hf₂ : Surjective (Prod.snd ∘ f)) (hf : ∀ g₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2) :
--     ∃ e : H ≃ₗ[S] I, range f = e.toLinearMap.graph := by
--   obtain ⟨e₁, he₁⟩ := f.exists_range_eq_graph hf₁ fun _ _ ↦ (hf _ _).1
--   obtain ⟨e₂, he₂⟩ := ((LinearEquiv.prodComm _ _ _).toLinearMap.comp f).exists_range_eq_graph
--     (by simpa) <| by simp [hf]
--   have he₁₂ h i : e₁ h = i ↔ e₂ i = h := by
--     simp only [SetLike.ext_iff, LinearMap.mem_graph_iff] at he₁ he₂
--     rw [Eq.comm, ← he₁ (h, i), Eq.comm, ← he₂ (i, h)]
--     simp only [mem_range, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
--       LinearEquiv.prodComm_apply, Prod.swap_eq_iff_eq_swap, Prod.swap_prod_mk]
--   exact ⟨
--   { toFun := e₁
--     map_smul' := e₁.map_smul'
--     map_add' := e₁.map_add'
--     invFun := e₂
--     left_inv := fun h ↦ by rw [← he₁₂]
--     right_inv := fun i ↦ by rw [he₁₂] }, he₁⟩

-- /-- **Goursat's lemma** for module isomorphisms.

-- Let `G ≤ H × I` be a submodule of a product of modules. Assume that the natural maps from `G` to
-- both factors are bijective. Then `G` is the graph of some module isomorphism `f : H ≃ I`. -/
-- lemma Submodule.exists_equiv_eq_graph {G : Submodule S (H × I)}
--     (hG₁ : Bijective (Prod.fst ∘ G.subtype)) (hG₂ : Bijective (Prod.snd ∘ G.subtype)) :
--     ∃ e : H ≃ₗ[S] I, G = e.toLinearMap.graph := by
--   simpa only [range_subtype] using LinearMap.exists_linearEquiv_eq_graph
--     hG₁.surjective hG₂.surjective fun _ _ ↦ hG₁.injective.eq_iff.trans hG₂.injective.eq_iff.symm

-- end LineTest
