/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import Mathlib.Algebra.Module.Submodule.Ker

#align_import linear_algebra.basic from "leanprover-community/mathlib"@"9d684a893c52e1d6692a504a118bfccbae04feeb"

/-!
# Range of linear maps

The range `LinearMap.range` of a (semi)linear map `f : M → M₂` is a submodule of `M₂`.

More specifically, `LinearMap.range` applies to any `SemilinearMapClass` over a `RingHomSurjective`
ring homomorphism.

Note that this also means that dot notation (i.e. `f.range` for a linear map `f`) does not work.

## Notations

* We continue to use the notations `M →ₛₗ[σ] M₂` and `M →ₗ[R] M₂` for the type of semilinear
  (resp. linear) maps from `M` to `M₂` over the ring homomorphism `σ` (resp. over the ring `R`).

## Tags
linear algebra, vector space, module, range
-/

open Function

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}
variable {K : Type*} {K₂ : Type*}
variable {M : Type*} {M₂ : Type*} {M₃ : Type*}
variable {V : Type*} {V₂ : Type*}

namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

open Submodule

variable {σ₂₁ : R₂ →+* R} {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

section

variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]

/-- The range of a linear map `f : M → M₂` is a submodule of `M₂`.
See Note [range copy pattern]. -/
def range [RingHomSurjective τ₁₂] (f : F) : Submodule R₂ M₂ :=
  (map f ⊤).copy (Set.range f) Set.image_univ.symm
#align linear_map.range LinearMap.range

theorem range_coe [RingHomSurjective τ₁₂] (f : F) : (range f : Set M₂) = Set.range f :=
  rfl
#align linear_map.range_coe LinearMap.range_coe

theorem range_toAddSubmonoid [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
    f.range.toAddSubmonoid = AddMonoidHom.mrange f :=
  rfl
#align linear_map.range_to_add_submonoid LinearMap.range_toAddSubmonoid

@[simp]
theorem mem_range [RingHomSurjective τ₁₂] {f : F} {x} : x ∈ range f ↔ ∃ y, f y = x :=
  Iff.rfl
#align linear_map.mem_range LinearMap.mem_range

theorem range_eq_map [RingHomSurjective τ₁₂] (f : F) : range f = map f ⊤ := by
  ext
  simp
#align linear_map.range_eq_map LinearMap.range_eq_map

theorem mem_range_self [RingHomSurjective τ₁₂] (f : F) (x : M) : f x ∈ range f :=
  ⟨x, rfl⟩
#align linear_map.mem_range_self LinearMap.mem_range_self

@[simp]
theorem range_id : range (LinearMap.id : M →ₗ[R] M) = ⊤ :=
  SetLike.coe_injective Set.range_id
#align linear_map.range_id LinearMap.range_id

theorem range_comp [RingHomSurjective τ₁₂] [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃]
    (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) : range (g.comp f : M →ₛₗ[τ₁₃] M₃) = map g (range f) :=
  SetLike.coe_injective (Set.range_comp g f)
#align linear_map.range_comp LinearMap.range_comp

theorem range_comp_le_range [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃] (f : M →ₛₗ[τ₁₂] M₂)
    (g : M₂ →ₛₗ[τ₂₃] M₃) : range (g.comp f : M →ₛₗ[τ₁₃] M₃) ≤ range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)
#align linear_map.range_comp_le_range LinearMap.range_comp_le_range

theorem range_eq_top [RingHomSurjective τ₁₂] {f : F} : range f = ⊤ ↔ Surjective f := by
  rw [SetLike.ext'_iff, range_coe, top_coe, Set.range_iff_surjective]
#align linear_map.range_eq_top LinearMap.range_eq_top

theorem range_le_iff_comap [RingHomSurjective τ₁₂] {f : F} {p : Submodule R₂ M₂} :
    range f ≤ p ↔ comap f p = ⊤ := by rw [range_eq_map, map_le_iff_le_comap, eq_top_iff]
#align linear_map.range_le_iff_comap LinearMap.range_le_iff_comap

theorem map_le_range [RingHomSurjective τ₁₂] {f : F} {p : Submodule R M} : map f p ≤ range f :=
  SetLike.coe_mono (Set.image_subset_range f p)
#align linear_map.map_le_range LinearMap.map_le_range

@[simp]
theorem range_neg {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} [Semiring R] [Ring R₂]
    [AddCommMonoid M] [AddCommGroup M₂] [Module R M] [Module R₂ M₂] {τ₁₂ : R →+* R₂}
    [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : LinearMap.range (-f) = LinearMap.range f := by
  change range ((-LinearMap.id : M₂ →ₗ[R₂] M₂).comp f) = _
  rw [range_comp, Submodule.map_neg, Submodule.map_id]
#align linear_map.range_neg LinearMap.range_neg

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

end

/-- The decreasing sequence of submodules consisting of the ranges of the iterates of a linear map.
-/
@[simps]
def iterateRange (f : M →ₗ[R] M) : ℕ →o (Submodule R M)ᵒᵈ where
  toFun n := LinearMap.range (f ^ n)
  monotone' n m w x h := by
    obtain ⟨c, rfl⟩ := le_iff_exists_add.mp w
    rw [LinearMap.mem_range] at h
    obtain ⟨m, rfl⟩ := h
    rw [LinearMap.mem_range]
    use (f ^ c) m
    rw [pow_add, LinearMap.mul_apply]
#align linear_map.iterate_range LinearMap.iterateRange

/-- Restrict the codomain of a linear map `f` to `f.range`.

This is the bundled version of `Set.rangeFactorization`. -/
abbrev rangeRestrict [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : M →ₛₗ[τ₁₂] LinearMap.range f :=
  f.codRestrict (LinearMap.range f) (LinearMap.mem_range_self f)
#align linear_map.range_restrict LinearMap.rangeRestrict

/-- The range of a linear map is finite if the domain is finite.
Note: this instance can form a diamond with `Subtype.fintype` in the
  presence of `Fintype M₂`. -/
instance fintypeRange [Fintype M] [DecidableEq M₂] [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
    Fintype (range f) :=
  Set.fintypeRange f
#align linear_map.fintype_range LinearMap.fintypeRange

variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]

theorem range_codRestrict {τ₂₁ : R₂ →+* R} [RingHomSurjective τ₂₁] (p : Submodule R M)
    (f : M₂ →ₛₗ[τ₂₁] M) (hf) :
    range (codRestrict p f hf) = comap p.subtype (LinearMap.range f) := by
  simpa only [range_eq_map] using map_codRestrict _ _ _ _
#align linear_map.range_cod_restrict LinearMap.range_codRestrict

theorem _root_.Submodule.map_comap_eq [RingHomSurjective τ₁₂] (f : F) (q : Submodule R₂ M₂) :
    map f (comap f q) = range f ⊓ q :=
  le_antisymm (le_inf map_le_range (map_comap_le _ _)) <| by
    rintro _ ⟨⟨x, _, rfl⟩, hx⟩; exact ⟨x, hx, rfl⟩
#align submodule.map_comap_eq Submodule.map_comap_eq

theorem _root_.Submodule.map_comap_eq_self [RingHomSurjective τ₁₂] {f : F} {q : Submodule R₂ M₂}
    (h : q ≤ range f) : map f (comap f q) = q := by rwa [Submodule.map_comap_eq, inf_eq_right]
#align submodule.map_comap_eq_self Submodule.map_comap_eq_self

@[simp]
theorem range_zero [RingHomSurjective τ₁₂] : range (0 : M →ₛₗ[τ₁₂] M₂) = ⊥ := by
  simpa only [range_eq_map] using Submodule.map_zero _
#align linear_map.range_zero LinearMap.range_zero

section

variable [RingHomSurjective τ₁₂]

theorem range_le_bot_iff (f : M →ₛₗ[τ₁₂] M₂) : range f ≤ ⊥ ↔ f = 0 := by
  rw [range_le_iff_comap]; exact ker_eq_top
#align linear_map.range_le_bot_iff LinearMap.range_le_bot_iff

theorem range_eq_bot {f : M →ₛₗ[τ₁₂] M₂} : range f = ⊥ ↔ f = 0 := by
  rw [← range_le_bot_iff, le_bot_iff]
#align linear_map.range_eq_bot LinearMap.range_eq_bot

theorem range_le_ker_iff {f : M →ₛₗ[τ₁₂] M₂} {g : M₂ →ₛₗ[τ₂₃] M₃} :
    range f ≤ ker g ↔ (g.comp f : M →ₛₗ[τ₁₃] M₃) = 0 :=
  ⟨fun h => ker_eq_top.1 <| eq_top_iff'.2 fun x => h <| ⟨_, rfl⟩, fun h x hx =>
    mem_ker.2 <| Exists.elim hx fun y hy => by rw [← hy, ← comp_apply, h, zero_apply]⟩
#align linear_map.range_le_ker_iff LinearMap.range_le_ker_iff

theorem comap_le_comap_iff {f : F} (hf : range f = ⊤) {p p'} : comap f p ≤ comap f p' ↔ p ≤ p' :=
  ⟨fun H x hx => by rcases range_eq_top.1 hf x with ⟨y, hy, rfl⟩; exact H hx, comap_mono⟩
#align linear_map.comap_le_comap_iff LinearMap.comap_le_comap_iff

theorem comap_injective {f : F} (hf : range f = ⊤) : Injective (comap f) := fun _ _ h =>
  le_antisymm ((comap_le_comap_iff hf).1 (le_of_eq h)) ((comap_le_comap_iff hf).1 (ge_of_eq h))
#align linear_map.comap_injective LinearMap.comap_injective

end

end AddCommMonoid

section Ring

variable [Ring R] [Ring R₂] [Ring R₃]
variable [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]
variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]
variable {f : F}

open Submodule

theorem range_toAddSubgroup [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
    (range f).toAddSubgroup = f.toAddMonoidHom.range :=
  rfl
#align linear_map.range_to_add_subgroup LinearMap.range_toAddSubgroup

theorem ker_le_iff [RingHomSurjective τ₁₂] {p : Submodule R M} :
    ker f ≤ p ↔ ∃ y ∈ range f, f ⁻¹' {y} ⊆ p := by
  constructor
  · intro h
    use 0
    rw [← SetLike.mem_coe, range_coe]
    exact ⟨⟨0, map_zero f⟩, h⟩
  · rintro ⟨y, h₁, h₂⟩
    rw [SetLike.le_def]
    intro z hz
    simp only [mem_ker, SetLike.mem_coe] at hz
    rw [← SetLike.mem_coe, range_coe, Set.mem_range] at h₁
    obtain ⟨x, hx⟩ := h₁
    have hx' : x ∈ p := h₂ hx
    have hxz : z + x ∈ p := by
      apply h₂
      simp [hx, hz]
    suffices z + x - x ∈ p by simpa only [this, add_sub_cancel_right]
    exact p.sub_mem hxz hx'
#align linear_map.ker_le_iff LinearMap.ker_le_iff

end Ring

section Semifield

variable [Semifield K] [Semifield K₂]
variable [AddCommMonoid V] [Module K V]
variable [AddCommMonoid V₂] [Module K V₂]

theorem range_smul (f : V →ₗ[K] V₂) (a : K) (h : a ≠ 0) : range (a • f) = range f := by
  simpa only [range_eq_map] using Submodule.map_smul f _ a h
#align linear_map.range_smul LinearMap.range_smul

theorem range_smul' (f : V →ₗ[K] V₂) (a : K) :
    range (a • f) = ⨆ _ : a ≠ 0, range f := by
  simpa only [range_eq_map] using Submodule.map_smul' f _ a
#align linear_map.range_smul' LinearMap.range_smul'

end Semifield

end LinearMap

namespace Submodule

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable (p p' : Submodule R M) (q : Submodule R₂ M₂)
variable {τ₁₂ : R →+* R₂}
variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂]

open LinearMap

@[simp]
theorem map_top [RingHomSurjective τ₁₂] (f : F) : map f ⊤ = range f :=
  (range_eq_map f).symm
#align submodule.map_top Submodule.map_top
@[simp]
theorem range_subtype : range p.subtype = p := by simpa using map_comap_subtype p ⊤
#align submodule.range_subtype Submodule.range_subtype

theorem map_subtype_le (p' : Submodule R p) : map p.subtype p' ≤ p := by
  simpa using (map_le_range : map p.subtype p' ≤ range p.subtype)
#align submodule.map_subtype_le Submodule.map_subtype_le

/-- Under the canonical linear map from a submodule `p` to the ambient space `M`, the image of the
maximal submodule of `p` is just `p`. -/
-- @[simp] -- Porting note (#10618): simp can prove this
theorem map_subtype_top : map p.subtype (⊤ : Submodule R p) = p := by simp
#align submodule.map_subtype_top Submodule.map_subtype_top

@[simp]
theorem comap_subtype_eq_top {p p' : Submodule R M} : comap p.subtype p' = ⊤ ↔ p ≤ p' :=
  eq_top_iff.trans <| map_le_iff_le_comap.symm.trans <| by rw [map_subtype_top]
#align submodule.comap_subtype_eq_top Submodule.comap_subtype_eq_top

@[simp]
theorem comap_subtype_self : comap p.subtype p = ⊤ :=
  comap_subtype_eq_top.2 le_rfl
#align submodule.comap_subtype_self Submodule.comap_subtype_self

theorem range_inclusion (p q : Submodule R M) (h : p ≤ q) :
    range (inclusion h) = comap q.subtype p := by
  rw [← map_top, inclusion, LinearMap.map_codRestrict, map_top, range_subtype]
#align submodule.range_of_le Submodule.range_inclusion

@[simp]
theorem map_subtype_range_inclusion {p p' : Submodule R M} (h : p ≤ p') :
    map p'.subtype (range <| inclusion h) = p := by simp [range_inclusion, map_comap_eq, h]
#align submodule.map_subtype_range_of_le Submodule.map_subtype_range_inclusion

/-- If `N ⊆ M` then submodules of `N` are the same as submodules of `M` contained in `N`.

See also `Submodule.mapIic`. -/
def MapSubtype.relIso : Submodule R p ≃o { p' : Submodule R M // p' ≤ p } where
  toFun p' := ⟨map p.subtype p', map_subtype_le p _⟩
  invFun q := comap p.subtype q
  left_inv p' := comap_map_eq_of_injective (by exact Subtype.val_injective) p'
  right_inv := fun ⟨q, hq⟩ => Subtype.ext_val <| by simp [map_comap_subtype p, inf_of_le_right hq]
  map_rel_iff' {p₁ p₂} := Subtype.coe_le_coe.symm.trans <| by
    dsimp
    rw [map_le_iff_le_comap,
      comap_map_eq_of_injective (show Injective p.subtype from Subtype.coe_injective) p₂]
#align submodule.map_subtype.rel_iso Submodule.MapSubtype.relIso

/-- If `p ⊆ M` is a submodule, the ordering of submodules of `p` is embedded in the ordering of
submodules of `M`. -/
def MapSubtype.orderEmbedding : Submodule R p ↪o Submodule R M :=
  (RelIso.toRelEmbedding <| MapSubtype.relIso p).trans <|
    Subtype.relEmbedding (X := Submodule R M) (fun p p' ↦ p ≤ p') _
#align submodule.map_subtype.order_embedding Submodule.MapSubtype.orderEmbedding

@[simp]
theorem map_subtype_embedding_eq (p' : Submodule R p) :
    MapSubtype.orderEmbedding p p' = map p.subtype p' :=
  rfl
#align submodule.map_subtype_embedding_eq Submodule.map_subtype_embedding_eq

/-- If `N ⊆ M` then submodules of `N` are the same as submodules of `M` contained in `N`. -/
def mapIic [Semiring R] [AddCommMonoid M] [Module R M] (p : Submodule R M) :
    Submodule R p ≃o Set.Iic p :=
  Submodule.MapSubtype.relIso p

@[simp] lemma coe_mapIic_apply [Semiring R] [AddCommMonoid M] [Module R M]
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
    ← h 0 f.ker.subtype (Eq.trans h₁ (comp_ker_subtype f).symm)]
  exact range_zero
#align linear_map.ker_eq_bot_of_cancel LinearMap.ker_eq_bot_of_cancel

theorem range_comp_of_range_eq_top [RingHomSurjective τ₁₂] [RingHomSurjective τ₂₃]
    [RingHomSurjective τ₁₃] {f : M →ₛₗ[τ₁₂] M₂} (g : M₂ →ₛₗ[τ₂₃] M₃) (hf : range f = ⊤) :
    range (g.comp f : M →ₛₗ[τ₁₃] M₃) = range g := by rw [range_comp, hf, Submodule.map_top]
#align linear_map.range_comp_of_range_eq_top LinearMap.range_comp_of_range_eq_top

section Image

/-- If `O` is a submodule of `M`, and `Φ : O →ₗ M'` is a linear map,
then `(ϕ : O →ₗ M').submoduleImage N` is `ϕ(N)` as a submodule of `M'` -/
def submoduleImage {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
    (ϕ : O →ₗ[R] M') (N : Submodule R M) : Submodule R M' :=
  (N.comap O.subtype).map ϕ
#align linear_map.submodule_image LinearMap.submoduleImage

@[simp]
theorem mem_submoduleImage {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
    {ϕ : O →ₗ[R] M'} {N : Submodule R M} {x : M'} :
    x ∈ ϕ.submoduleImage N ↔ ∃ (y : _) (yO : y ∈ O), y ∈ N ∧ ϕ ⟨y, yO⟩ = x := by
  refine Submodule.mem_map.trans ⟨?_, ?_⟩ <;> simp_rw [Submodule.mem_comap]
  · rintro ⟨⟨y, yO⟩, yN : y ∈ N, h⟩
    exact ⟨y, yO, yN, h⟩
  · rintro ⟨y, yO, yN, h⟩
    exact ⟨⟨y, yO⟩, yN, h⟩
#align linear_map.mem_submodule_image LinearMap.mem_submoduleImage

theorem mem_submoduleImage_of_le {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
    {ϕ : O →ₗ[R] M'} {N : Submodule R M} (hNO : N ≤ O) {x : M'} :
    x ∈ ϕ.submoduleImage N ↔ ∃ (y : _) (yN : y ∈ N), ϕ ⟨y, hNO yN⟩ = x := by
  refine mem_submoduleImage.trans ⟨?_, ?_⟩
  · rintro ⟨y, yO, yN, h⟩
    exact ⟨y, yN, h⟩
  · rintro ⟨y, yN, h⟩
    exact ⟨y, hNO yN, yN, h⟩
#align linear_map.mem_submodule_image_of_le LinearMap.mem_submoduleImage_of_le

theorem submoduleImage_apply_of_le {M' : Type*} [AddCommGroup M'] [Module R M']
    {O : Submodule R M} (ϕ : O →ₗ[R] M') (N : Submodule R M) (hNO : N ≤ O) :
    ϕ.submoduleImage N = range (ϕ.comp (Submodule.inclusion hNO)) := by
  rw [submoduleImage, range_comp, Submodule.range_inclusion]
#align linear_map.submodule_image_apply_of_le LinearMap.submoduleImage_apply_of_le

end Image

section rangeRestrict

variable [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂)

@[simp] theorem range_rangeRestrict : range f.rangeRestrict = ⊤ := by simp [f.range_codRestrict _]
#align linear_map.range_range_restrict LinearMap.range_rangeRestrict

theorem surjective_rangeRestrict : Surjective f.rangeRestrict := by
  rw [← range_eq_top, range_rangeRestrict]

@[simp] theorem ker_rangeRestrict : ker f.rangeRestrict = ker f := LinearMap.ker_codRestrict _ _ _
#align linear_map.ker_range_restrict LinearMap.ker_rangeRestrict

end rangeRestrict

end Semiring

end LinearMap
