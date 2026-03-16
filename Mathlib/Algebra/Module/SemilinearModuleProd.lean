/-
Copyright (c) 2026 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Range

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

In order to implement this, note that defining a type synonym `R` of `ℂ` does not work, because one
might want to take `E = F`, on which any `R : Ring` can have only one instance `Module R F`,
in particular, there is already the canonical instance `Module R (E × F)`.
This means that we cannot use the product module `E × F`, but we have to make a type synonym and
duplicate code for `E ×[σ] F`. -/

@[expose] public section

set_option linter.unusedVariables false in
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

@[simp] lemma fst_apply (x : E ×[σ] F) :
    fstₛₗ σ E F x = x.fst := rfl

@[simp] lemma snd_apply (x : E ×[σ] F) :
    sndₛₗ σ E F x = x.snd := rfl

@[simp, norm_cast] lemma coe_fstₛₗ : ⇑(fstₛₗ σ E F) = fun x => x.fst := rfl

@[simp, norm_cast] lemma coe_sndₛₗ : ⇑(sndₛₗ σ E F) = fun x => x.snd := rfl

theorem fstₛₗ_surjective : Function.Surjective (fstₛₗ σ E F) :=
  fun x => ⟨SemilinearProdModule.mk x 0, rfl⟩

theorem sndₛₗ_surjective : Function.Surjective (sndₛₗ σ E F) :=
  fun x => ⟨SemilinearProdModule.mk 0 x, rfl⟩

section prodₛₗ

variable {E F}

/-- Combine a linear map `f : M →ₗ[R] E` and a semilinear map
`g : M →ₛₗ[σ] F` into a linear map with target `E ×[σ] F`. -/
def prodₛₗ (f : M →ₗ[R] E) (g : M →ₛₗ[σ] F) : M →ₗ[R] E ×[σ] F where
  toFun x := SemilinearProdModule.mk (f x) (g x)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

@[simp] lemma prodₛₗ_apply (f : M →ₗ[R] E) (g : M →ₛₗ[σ] F) (x : M) :
    prodₛₗ σ f g x = SemilinearProdModule.mk (f x) (g x) := rfl

@[simp] lemma fst_prodₛₗ (f : M →ₗ[R] E) (g : M →ₛₗ[σ] F) :
    (fstₛₗ σ E F).comp (prodₛₗ σ f g) = f := by ext x; rfl

@[simp] lemma snd_prodₛₗ (f : M →ₗ[R] E) (g : M →ₛₗ[σ] F) :
    (sndₛₗ σ E F).comp (prodₛₗ σ f g) = g := by ext x; rfl

end prodₛₗ

section coprodₛₗ

variable {M : Type*} [AddCommGroup M] [Module S M]

variable {E F}

/-- The coprod function `x : M × M₂ ↦ f x.1 + g x.2` is a linear map. -/
def coprodₛₗ (f : E →ₛₗ[σ] M) (g : F →ₗ[S] M) : E ×[σ] F →ₛₗ[σ] M :=
  f.comp (fstₛₗ _ _ _) + g.comp (sndₛₗ _ _ _)

@[simp]
theorem coprodₛₗ_apply (f : E →ₛₗ[σ] F) (g : F →ₗ[S] F) (x : E ×[σ] F) :
    coprodₛₗ σ f g x = f x.1 + g x.2 := rfl

-- @[simp]
-- theorem coprod_inl (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) : (coprod f g).comp (inl R M M₂) = f := by
--   ext; simp only [map_zero, add_zero, coprod_apply, inl_apply, comp_apply]

-- @[simp]
-- theorem coprod_inr (f : M →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) : (coprod f g).comp (inr R M M₂) = g := by
--   ext; simp only [map_zero, coprod_apply, inr_apply, zero_add, comp_apply]

-- @[simp]
-- theorem coprod_inl_inr : coprod (inl R M M₂) (inr R M M₂) = LinearMap.id := by
--   ext <;>
--     simp only [Prod.mk_add_mk, add_zero, id_apply, coprod_apply, inl_apply, inr_apply, zero_add]

-- theorem coprod_zero_left (g : M₂ →ₗ[R] M₃) : (0 : M →ₗ[R] M₃).coprod g = g.comp (snd R M M₂) :=
--   zero_add _

-- theorem coprod_zero_right (f : M →ₗ[R] M₃) : f.coprod (0 : M₂ →ₗ[R] M₃) = f.comp (fst R M M₂) :=
--   add_zero _

-- theorem comp_coprod (f : M₃ →ₗ[R] M₄) (g₁ : M →ₗ[R] M₃) (g₂ : M₂ →ₗ[R] M₃) :
--     f.comp (g₁.coprod g₂) = (f.comp g₁).coprod (f.comp g₂) :=
--   ext fun x => f.map_add (g₁ x.1) (g₂ x.2)

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

theorem graphₛₗ_eq_ker_coprodₛₗ : f.graphₛₗ = ker (coprodₛₗ σ (-f) LinearMap.id) := by
  ext x
  change _ = _ ↔ -f x.1 + x.2 = _
  rw [add_comm, add_neg_eq_zero]

theorem graphₛₗ_eq_range_prodₛₗ : f.graphₛₗ = range (prodₛₗ σ LinearMap.id f) := by
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
