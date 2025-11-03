/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Data.Set.Finite.Range

/-!
# Range of linear maps

The range `LinearMap.range` of a (semi)linear map `f : M → M₂` is a submodule of `M₂`.

More specifically, `LinearMap.range` applies to any `SemilinearMapClass` over a `RingHomSurjective`
ring homomorphism.

Note that this also means that dot notation (i.e. `f.range` for a linear map `f`) does not work.

## Notation

* We continue to use the notations `M →ₛₗ[σ] M₂` and `M →ₗ[R] M₂` for the type of semilinear
  (resp. linear) maps from `M` to `M₂` over the ring homomorphism `σ` (resp. over the ring `R`).

## Tags
linear algebra, vector space, module, range
-/

open Function

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}
variable {K : Type*}
variable {M : Type*} {M₂ : Type*} {M₃ : Type*}
variable {V : Type*} {V₂ : Type*}

namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

open Submodule

variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

section

variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]

/-- The range of a linear map `f : M → M₂` is a submodule of `M₂`.
See Note [range copy pattern]. -/
def range [RingHomSurjective τ₁₂] (f : F) : Submodule R₂ M₂ :=
  (map f ⊤).copy (Set.range f) Set.image_univ.symm

theorem coe_range [RingHomSurjective τ₁₂] (f : F) : (range f : Set M₂) = Set.range f :=
  rfl

@[deprecated (since := "2025-08-31")] alias range_coe := coe_range

theorem range_toAddSubmonoid [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
    (range f).toAddSubmonoid = AddMonoidHom.mrange f :=
  rfl

@[simp]
theorem mem_range [RingHomSurjective τ₁₂] {f : F} {x} : x ∈ range f ↔ ∃ y, f y = x :=
  Iff.rfl

theorem range_eq_map [RingHomSurjective τ₁₂] (f : F) : range f = map f ⊤ := by
  ext
  simp

theorem mem_range_self [RingHomSurjective τ₁₂] (f : F) (x : M) : f x ∈ range f :=
  ⟨x, rfl⟩

@[simp]
theorem range_id : range (LinearMap.id : M →ₗ[R] M) = ⊤ :=
  SetLike.coe_injective Set.range_id

theorem range_comp [RingHomSurjective τ₁₂] [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃]
    (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) : range (g.comp f : M →ₛₗ[τ₁₃] M₃) = map g (range f) :=
  SetLike.coe_injective (Set.range_comp g f)

theorem range_comp_le_range [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃] (f : M →ₛₗ[τ₁₂] M₂)
    (g : M₂ →ₛₗ[τ₂₃] M₃) : range (g.comp f : M →ₛₗ[τ₁₃] M₃) ≤ range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)

theorem range_eq_top [RingHomSurjective τ₁₂] {f : F} :
    range f = ⊤ ↔ Surjective f := by
  rw [SetLike.ext'_iff, coe_range, top_coe, Set.range_eq_univ]

theorem range_eq_top_of_surjective [RingHomSurjective τ₁₂] (f : F) (hf : Surjective f) :
    range f = ⊤ := range_eq_top.2 hf

theorem range_add_le [RingHomSurjective τ₁₂] (f g : M →ₛₗ[τ₁₂] M₂) :
    range (f + g) ≤ range f ⊔ range g := by
  rintro - ⟨_, rfl⟩
  apply add_mem_sup
  all_goals simp only [mem_range, exists_apply_eq_apply]

theorem range_le_iff_comap [RingHomSurjective τ₁₂] {f : F} {p : Submodule R₂ M₂} :
    range f ≤ p ↔ comap f p = ⊤ := by rw [range_eq_map, map_le_iff_le_comap, eq_top_iff]

theorem map_le_range [RingHomSurjective τ₁₂] {f : F} {p : Submodule R M} : map f p ≤ range f :=
  SetLike.coe_mono (Set.image_subset_range f p)

@[simp]
theorem range_neg {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} [Semiring R] [Ring R₂]
    [AddCommMonoid M] [AddCommGroup M₂] [Module R M] [Module R₂ M₂] {τ₁₂ : R →+* R₂}
    [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : LinearMap.range (-f) = LinearMap.range f := by
  change range ((-LinearMap.id : M₂ →ₗ[R₂] M₂).comp f) = _
  rw [range_comp, Submodule.map_neg, Submodule.map_id]

@[simp] lemma range_domRestrict [Module R M₂] (K : Submodule R M) (f : M →ₗ[R] M₂) :
    range (domRestrict f K) = K.map f := by ext; simp

lemma range_domRestrict_le_range [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (S : Submodule R M) :
    LinearMap.range (f.domRestrict S) ≤ LinearMap.range f := by
  rintro x ⟨⟨y, hy⟩, rfl⟩
  exact LinearMap.mem_range_self f y

@[simp]
theorem _root_.AddMonoidHom.coe_toIntLinearMap_range {M M₂ : Type*} [AddCommGroup M]
    [AddCommGroup M₂] (f : M →+ M₂) :
    LinearMap.range f.toIntLinearMap = AddSubgroup.toIntSubmodule f.range := rfl

lemma _root_.Submodule.map_comap_eq_of_le [RingHomSurjective τ₁₂] {f : F} {p : Submodule R₂ M₂}
    (h : p ≤ LinearMap.range f) : (p.comap f).map f = p :=
  SetLike.coe_injective <| Set.image_preimage_eq_of_subset h

lemma range_restrictScalars [SMul R R₂] [Module R₂ M] [Module R M₂] [CompatibleSMul M M₂ R R₂]
    [IsScalarTower R R₂ M₂] (f : M →ₗ[R₂] M₂) :
    LinearMap.range (f.restrictScalars R) = (LinearMap.range f).restrictScalars R := rfl

end

/-- The decreasing sequence of submodules consisting of the ranges of the iterates of a linear map.
-/
@[simps]
def iterateRange (f : M →ₗ[R] M) : ℕ →o (Submodule R M)ᵒᵈ where
  toFun n := LinearMap.range (f ^ n)
  monotone' n m w x h := by
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le  w
    rw [LinearMap.mem_range] at h
    obtain ⟨m, rfl⟩ := h
    rw [LinearMap.mem_range]
    use (f ^ c) m
    rw [pow_add, Module.End.mul_apply]

/-- Restrict the codomain of a linear map `f` to `f.range`.

This is the bundled version of `Set.rangeFactorization`. -/
abbrev rangeRestrict [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : M →ₛₗ[τ₁₂] LinearMap.range f :=
  f.codRestrict (LinearMap.range f) (LinearMap.mem_range_self f)

/-- The range of a linear map is finite if the domain is finite.
Note: this instance can form a diamond with `Subtype.fintype` in the
  presence of `Fintype M₂`. -/
instance fintypeRange [Fintype M] [DecidableEq M₂] [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
    Fintype (range f) :=
  Set.fintypeRange f

variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]

theorem range_codRestrict {τ₂₁ : R₂ →+* R} [RingHomSurjective τ₂₁] (p : Submodule R M)
    (f : M₂ →ₛₗ[τ₂₁] M) (hf) :
    range (codRestrict p f hf) = comap p.subtype (LinearMap.range f) := by
  simpa only [range_eq_map] using map_codRestrict _ _ _ _

theorem _root_.Submodule.map_comap_eq [RingHomSurjective τ₁₂] (f : F) (q : Submodule R₂ M₂) :
    map f (comap f q) = range f ⊓ q :=
  le_antisymm (le_inf map_le_range (map_comap_le _ _)) <| by
    rintro _ ⟨⟨x, _, rfl⟩, hx⟩; exact ⟨x, hx, rfl⟩

theorem _root_.Submodule.map_comap_eq_self [RingHomSurjective τ₁₂] {f : F} {q : Submodule R₂ M₂}
    (h : q ≤ range f) : map f (comap f q) = q := by rwa [Submodule.map_comap_eq, inf_eq_right]

@[simp]
theorem range_zero [RingHomSurjective τ₁₂] : range (0 : M →ₛₗ[τ₁₂] M₂) = ⊥ := by
  simpa only [range_eq_map] using Submodule.map_zero _

section

variable [RingHomSurjective τ₁₂]

theorem range_le_bot_iff (f : M →ₛₗ[τ₁₂] M₂) : range f ≤ ⊥ ↔ f = 0 := by
  rw [range_le_iff_comap]; exact ker_eq_top

theorem range_eq_bot {f : M →ₛₗ[τ₁₂] M₂} : range f = ⊥ ↔ f = 0 := by
  rw [← range_le_bot_iff, le_bot_iff]

theorem range_le_ker_iff {f : M →ₛₗ[τ₁₂] M₂} {g : M₂ →ₛₗ[τ₂₃] M₃} :
    range f ≤ ker g ↔ (g.comp f : M →ₛₗ[τ₁₃] M₃) = 0 :=
  ⟨fun h => ker_eq_top.1 <| eq_top_iff'.2 fun _ => h <| ⟨_, rfl⟩, fun h x hx =>
    mem_ker.2 <| Exists.elim hx fun y hy => by rw [← hy, ← comp_apply, h, zero_apply]⟩

theorem comap_le_comap_iff {f : F} (hf : range f = ⊤) {p p'} : comap f p ≤ comap f p' ↔ p ≤ p' :=
  ⟨fun H ↦ by rwa [SetLike.le_def, (range_eq_top.1 hf).forall], comap_mono⟩

theorem comap_injective {f : F} (hf : range f = ⊤) : Injective (comap f) := fun _ _ h =>
  le_antisymm ((comap_le_comap_iff hf).1 (le_of_eq h)) ((comap_le_comap_iff hf).1 (ge_of_eq h))

-- TODO (?): generalize to semilinear maps with `f ∘ₗ g` bijective.
theorem ker_eq_range_of_comp_eq_id {M P} [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] {f : M →ₗ[R] P} {g : P →ₗ[R] M} (h : f ∘ₗ g = .id) :
    ker f = range (LinearMap.id - g ∘ₗ f) :=
  le_antisymm (fun x hx ↦ ⟨x, show x - g (f x) = x by rw [hx, map_zero, sub_zero]⟩) <|
    range_le_ker_iff.mpr <| by rw [comp_sub, comp_id, ← comp_assoc, h, id_comp, sub_self]

end

end AddCommMonoid

section Ring

variable [Ring R] [Ring R₂]
variable [AddCommGroup M] [AddCommGroup M₂]
variable [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂}
variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]
variable {f : F}

open Submodule

theorem range_toAddSubgroup [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
    (range f).toAddSubgroup = f.toAddMonoidHom.range :=
  rfl

theorem ker_le_iff [RingHomSurjective τ₁₂] {p : Submodule R M} :
    ker f ≤ p ↔ ∃ y ∈ range f, f ⁻¹' {y} ⊆ p := by
  constructor
  · intro h
    use 0
    rw [← SetLike.mem_coe, coe_range]
    exact ⟨⟨0, map_zero f⟩, h⟩
  · rintro ⟨y, h₁, h₂⟩
    rw [SetLike.le_def]
    intro z hz
    simp only [mem_ker] at hz
    rw [← SetLike.mem_coe, coe_range, Set.mem_range] at h₁
    obtain ⟨x, hx⟩ := h₁
    have hx' : x ∈ p := h₂ hx
    have hxz : z + x ∈ p := by
      apply h₂
      simp [hx, hz]
    suffices z + x - x ∈ p by simpa only [this, add_sub_cancel_right]
    exact p.sub_mem hxz hx'

end Ring

section Semifield

variable [Semifield K]
variable [AddCommMonoid V] [Module K V]
variable [AddCommMonoid V₂] [Module K V₂]

theorem range_smul (f : V →ₗ[K] V₂) (a : K) (h : a ≠ 0) : range (a • f) = range f := by
  simpa only [range_eq_map] using Submodule.map_smul f _ a h

theorem range_smul' (f : V →ₗ[K] V₂) (a : K) :
    range (a • f) = ⨆ _ : a ≠ 0, range f := by
  simpa only [range_eq_map] using Submodule.map_smul' f _ a

end Semifield

end LinearMap

namespace Submodule

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable (p : Submodule R M)
variable {τ₁₂ : R →+* R₂}
variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]

open LinearMap

@[simp]
theorem map_top [RingHomSurjective τ₁₂] (f : F) : map f ⊤ = range f :=
  (range_eq_map f).symm
@[simp]
theorem range_subtype : range p.subtype = p := by simpa using map_comap_subtype p ⊤

theorem map_subtype_le (p' : Submodule R p) : map p.subtype p' ≤ p := by
  simpa using (map_le_range : map p.subtype p' ≤ range p.subtype)

/-- Under the canonical linear map from a submodule `p` to the ambient space `M`, the image of the
maximal submodule of `p` is just `p`. -/
theorem map_subtype_top : map p.subtype (⊤ : Submodule R p) = p := by simp

@[simp]
theorem comap_subtype_eq_top {p p' : Submodule R M} : comap p.subtype p' = ⊤ ↔ p ≤ p' :=
  eq_top_iff.trans <| map_le_iff_le_comap.symm.trans <| by rw [map_subtype_top]

@[simp]
theorem comap_subtype_self : comap p.subtype p = ⊤ :=
  comap_subtype_eq_top.2 le_rfl

theorem submoduleOf_self (N : Submodule R M) : N.submoduleOf N = ⊤ := comap_subtype_self _

theorem submoduleOf_sup_of_le {N₁ N₂ N : Submodule R M} (h₁ : N₁ ≤ N) (h₂ : N₂ ≤ N) :
    (N₁ ⊔ N₂).submoduleOf N = N₁.submoduleOf N ⊔ N₂.submoduleOf N := by
  apply Submodule.map_injective_of_injective N.subtype_injective
  simp only [submoduleOf, map_comap_eq]
  simp_all

@[simp]
lemma comap_subtype_le_iff {p q r : Submodule R M} :
    q.comap p.subtype ≤ r.comap p.subtype ↔ p ⊓ q ≤ p ⊓ r :=
  ⟨fun h ↦ by simpa using map_mono (f := p.subtype) h,
   fun h ↦ by simpa using comap_mono (f := p.subtype) h⟩

theorem range_inclusion (p q : Submodule R M) (h : p ≤ q) :
    range (inclusion h) = comap q.subtype p := by
  rw [← map_top, inclusion, LinearMap.map_codRestrict, map_top, range_subtype]

@[simp]
theorem map_subtype_range_inclusion {p p' : Submodule R M} (h : p ≤ p') :
    map p'.subtype (range <| inclusion h) = p := by simp [range_inclusion, map_comap_eq, h]

lemma restrictScalars_map [SMul R R₂] [Module R₂ M] [Module R M₂] [IsScalarTower R R₂ M]
    [IsScalarTower R R₂ M₂] (f : M →ₗ[R₂] M₂) (M' : Submodule R₂ M) :
    (M'.map f).restrictScalars R = (M'.restrictScalars R).map (f.restrictScalars R) := rfl

/-- If `N ⊆ M` then submodules of `N` are the same as submodules of `M` contained in `N`.

See also `Submodule.mapIic`. -/
def MapSubtype.orderIso : Submodule R p ≃o { p' : Submodule R M // p' ≤ p } where
  toFun p' := ⟨map p.subtype p', map_subtype_le p _⟩
  invFun q := comap p.subtype q
  left_inv p' := comap_map_eq_of_injective (by exact Subtype.val_injective) p'
  right_inv := fun ⟨q, hq⟩ => Subtype.ext <| by simp [map_comap_subtype p, inf_of_le_right hq]
  map_rel_iff' {p₁ p₂} := Subtype.coe_le_coe.symm.trans <| by
    dsimp
    rw [map_le_iff_le_comap,
      comap_map_eq_of_injective (show Injective p.subtype from Subtype.coe_injective) p₂]

@[deprecated (since := "2025-06-03")] alias MapSubtype.relIso := MapSubtype.orderIso

/-- If `p ⊆ M` is a submodule, the ordering of submodules of `p` is embedded in the ordering of
submodules of `M`. -/
def MapSubtype.orderEmbedding : Submodule R p ↪o Submodule R M :=
  (RelIso.toRelEmbedding <| MapSubtype.orderIso p).trans <|
    Subtype.relEmbedding (X := Submodule R M) (fun p p' ↦ p ≤ p') _

@[simp]
theorem map_subtype_embedding_eq (p' : Submodule R p) :
    MapSubtype.orderEmbedding p p' = map p.subtype p' :=
  rfl

/-- If `N ⊆ M` then submodules of `N` are the same as submodules of `M` contained in `N`. -/
def mapIic (p : Submodule R M) :
    Submodule R p ≃o Set.Iic p :=
  Submodule.MapSubtype.orderIso p

@[simp] lemma coe_mapIic_apply
    (p : Submodule R M) (q : Submodule R p) :
    (p.mapIic q : Submodule R M) = q.map p.subtype :=
  rfl

end AddCommMonoid

end Submodule

namespace LinearMap

section Semiring

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

/-- A monomorphism is injective. -/
theorem ker_eq_bot_of_cancel {f : M →ₛₗ[τ₁₂] M₂}
    (h : ∀ u v : ker f →ₗ[R] M, f.comp u = f.comp v → u = v) : ker f = ⊥ := by
  have h₁ : f.comp (0 : ker f →ₗ[R] M) = 0 := comp_zero _
  rw [← Submodule.range_subtype (ker f),
    ← h 0 (ker f).subtype (Eq.trans h₁ (comp_ker_subtype f).symm)]
  exact range_zero

theorem range_comp_of_range_eq_top [RingHomSurjective τ₁₂] [RingHomSurjective τ₂₃]
    [RingHomSurjective τ₁₃] {f : M →ₛₗ[τ₁₂] M₂} (g : M₂ →ₛₗ[τ₂₃] M₃) (hf : range f = ⊤) :
    range (g.comp f : M →ₛₗ[τ₁₃] M₃) = range g := by rw [range_comp, hf, Submodule.map_top]

section Image

/-- If `O` is a submodule of `M`, and `Φ : O →ₗ M'` is a linear map,
then `(ϕ : O →ₗ M').submoduleImage N` is `ϕ(N)` as a submodule of `M'` -/
def submoduleImage {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
    (ϕ : O →ₗ[R] M') (N : Submodule R M) : Submodule R M' :=
  (N.comap O.subtype).map ϕ

@[simp]
theorem mem_submoduleImage {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
    {ϕ : O →ₗ[R] M'} {N : Submodule R M} {x : M'} :
    x ∈ ϕ.submoduleImage N ↔ ∃ (y : _) (yO : y ∈ O), y ∈ N ∧ ϕ ⟨y, yO⟩ = x := by
  refine Submodule.mem_map.trans ⟨?_, ?_⟩ <;> simp_rw [Submodule.mem_comap]
  · rintro ⟨⟨y, yO⟩, yN : y ∈ N, h⟩
    exact ⟨y, yO, yN, h⟩
  · rintro ⟨y, yO, yN, h⟩
    exact ⟨⟨y, yO⟩, yN, h⟩

theorem mem_submoduleImage_of_le {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
    {ϕ : O →ₗ[R] M'} {N : Submodule R M} (hNO : N ≤ O) {x : M'} :
    x ∈ ϕ.submoduleImage N ↔ ∃ (y : _) (yN : y ∈ N), ϕ ⟨y, hNO yN⟩ = x := by
  grind [mem_submoduleImage]

theorem submoduleImage_apply_of_le {M' : Type*} [AddCommMonoid M'] [Module R M']
    {O : Submodule R M} (ϕ : O →ₗ[R] M') (N : Submodule R M) (hNO : N ≤ O) :
    ϕ.submoduleImage N = range (ϕ.comp (Submodule.inclusion hNO)) := by
  rw [submoduleImage, range_comp, Submodule.range_inclusion]

end Image

section rangeRestrict

variable [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂)

@[simp] theorem range_rangeRestrict : range f.rangeRestrict = ⊤ := by simp [f.range_codRestrict _]

theorem surjective_rangeRestrict : Surjective f.rangeRestrict := by
  rw [← range_eq_top, range_rangeRestrict]

@[simp] theorem ker_rangeRestrict : ker f.rangeRestrict = ker f := LinearMap.ker_codRestrict _ _ _

@[simp] theorem injective_rangeRestrict_iff : Injective f.rangeRestrict ↔ Injective f :=
  Set.injective_codRestrict _

end rangeRestrict

end Semiring

end LinearMap
