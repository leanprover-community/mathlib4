/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Prod

/-!
# Projection to a subspace

In this file we define
* `Submodule.linearProjOfIsCompl (p q : Submodule R E) (h : IsCompl p q)`:
  the projection of a module `E` to a submodule `p` along its complement `q`;
  it is the unique linear map `f : E → p` such that `f x = x` for `x ∈ p` and `f x = 0` for `x ∈ q`.
* `Submodule.isComplEquivProj p`: equivalence between submodules `q`
  such that `IsCompl p q` and projections `f : E → p`, `∀ x ∈ p, f x = x`.

We also provide some lemmas justifying correctness of our definitions.

## Tags

projection, complement subspace
-/

noncomputable section Ring

variable {R : Type*} [Ring R] {E : Type*} [AddCommGroup E] [Module R E]
variable {F : Type*} [AddCommGroup F] [Module R F] {G : Type*} [AddCommGroup G] [Module R G]
variable (p q : Submodule R E)
variable {S : Type*} [Semiring S] {M : Type*} [AddCommMonoid M] [Module S M] (m : Submodule S M)

namespace LinearMap

variable {p}

open Submodule

theorem ker_id_sub_eq_of_proj {f : E →ₗ[R] p} (hf : ∀ x : p, f x = x) :
    ker (id - p.subtype.comp f) = p := by
  ext x
  simp only [comp_apply, mem_ker, subtype_apply, sub_apply, id_apply, sub_eq_zero]
  exact ⟨fun h => h.symm ▸ Submodule.coe_mem _, fun hx => by rw [hf ⟨x, hx⟩, Subtype.coe_mk]⟩

theorem range_eq_of_proj {f : E →ₗ[R] p} (hf : ∀ x : p, f x = x) : range f = ⊤ :=
  range_eq_top.2 fun x => ⟨x, hf x⟩

theorem isCompl_of_proj {f : E →ₗ[R] p} (hf : ∀ x : p, f x = x) : IsCompl p (ker f) := by
  constructor
  · rw [disjoint_iff_inf_le]
    rintro x ⟨hpx, hfx⟩
    rw [SetLike.mem_coe, mem_ker, hf ⟨x, hpx⟩, mk_eq_zero] at hfx
    simp only [hfx, SetLike.mem_coe, zero_mem]
  · rw [codisjoint_iff_le_sup]
    intro x _
    rw [mem_sup']
    refine ⟨f x, ⟨x - f x, ?_⟩, add_sub_cancel _ _⟩
    rw [mem_ker, LinearMap.map_sub, hf, sub_self]

end LinearMap

namespace Submodule

open LinearMap

/-- If `q` is a complement of `p`, then `M/p ≃ q`. -/
def quotientEquivOfIsCompl (h : IsCompl p q) : (E ⧸ p) ≃ₗ[R] q :=
  LinearEquiv.symm <|
    LinearEquiv.ofBijective (p.mkQ.comp q.subtype)
      ⟨by rw [← ker_eq_bot, ker_comp, ker_mkQ, disjoint_iff_comap_eq_bot.1 h.symm.disjoint], by
        rw [← range_eq_top, range_comp, range_subtype, map_mkQ_eq_top, h.sup_eq_top]⟩

@[simp]
theorem quotientEquivOfIsCompl_symm_apply (h : IsCompl p q) (x : q) :
    -- Porting note: type ascriptions needed on the RHS
    (quotientEquivOfIsCompl p q h).symm x = (Quotient.mk x : E ⧸ p) := rfl

@[simp]
theorem quotientEquivOfIsCompl_apply_mk_coe (h : IsCompl p q) (x : q) :
    quotientEquivOfIsCompl p q h (Quotient.mk x) = x :=
  (quotientEquivOfIsCompl p q h).apply_symm_apply x

@[simp]
theorem mk_quotientEquivOfIsCompl_apply (h : IsCompl p q) (x : E ⧸ p) :
    (Quotient.mk (quotientEquivOfIsCompl p q h x) : E ⧸ p) = x :=
  (quotientEquivOfIsCompl p q h).symm_apply_apply x

/-- If `q` is a complement of `p`, then `p × q` is isomorphic to `E`. It is the unique
linear map `f : E → p` such that `f x = x` for `x ∈ p` and `f x = 0` for `x ∈ q`. -/
def prodEquivOfIsCompl (h : IsCompl p q) : (p × q) ≃ₗ[R] E := by
  apply LinearEquiv.ofBijective (p.subtype.coprod q.subtype)
  constructor
  · rw [← ker_eq_bot, ker_coprod_of_disjoint_range, ker_subtype, ker_subtype, prod_bot]
    rw [range_subtype, range_subtype]
    exact h.1
  · rw [← range_eq_top, ← sup_eq_range, h.sup_eq_top]

@[simp]
theorem coe_prodEquivOfIsCompl (h : IsCompl p q) :
    (prodEquivOfIsCompl p q h : p × q →ₗ[R] E) = p.subtype.coprod q.subtype := rfl

@[simp]
theorem coe_prodEquivOfIsCompl' (h : IsCompl p q) (x : p × q) :
    prodEquivOfIsCompl p q h x = x.1 + x.2 := rfl

@[simp]
theorem prodEquivOfIsCompl_symm_apply_left (h : IsCompl p q) (x : p) :
    (prodEquivOfIsCompl p q h).symm x = (x, 0) :=
  (prodEquivOfIsCompl p q h).symm_apply_eq.2 <| by simp

@[simp]
theorem prodEquivOfIsCompl_symm_apply_right (h : IsCompl p q) (x : q) :
    (prodEquivOfIsCompl p q h).symm x = (0, x) :=
  (prodEquivOfIsCompl p q h).symm_apply_eq.2 <| by simp

@[simp]
theorem prodEquivOfIsCompl_symm_apply_fst_eq_zero (h : IsCompl p q) {x : E} :
    ((prodEquivOfIsCompl p q h).symm x).1 = 0 ↔ x ∈ q := by
  conv_rhs => rw [← (prodEquivOfIsCompl p q h).apply_symm_apply x]
  rw [coe_prodEquivOfIsCompl', Submodule.add_mem_iff_left _ (Submodule.coe_mem _),
    mem_right_iff_eq_zero_of_disjoint h.disjoint]

@[simp]
theorem prodEquivOfIsCompl_symm_apply_snd_eq_zero (h : IsCompl p q) {x : E} :
    ((prodEquivOfIsCompl p q h).symm x).2 = 0 ↔ x ∈ p := by
  conv_rhs => rw [← (prodEquivOfIsCompl p q h).apply_symm_apply x]
  rw [coe_prodEquivOfIsCompl', Submodule.add_mem_iff_right _ (Submodule.coe_mem _),
    mem_left_iff_eq_zero_of_disjoint h.disjoint]

@[simp]
theorem prodComm_trans_prodEquivOfIsCompl (h : IsCompl p q) :
    LinearEquiv.prodComm R q p ≪≫ₗ prodEquivOfIsCompl p q h = prodEquivOfIsCompl q p h.symm :=
  LinearEquiv.ext fun _ => add_comm _ _

/-- Projection to a submodule along a complement.

See also `LinearMap.linearProjOfIsCompl`. -/
def linearProjOfIsCompl (h : IsCompl p q) : E →ₗ[R] p :=
  LinearMap.fst R p q ∘ₗ ↑(prodEquivOfIsCompl p q h).symm

variable {p q}

@[simp]
theorem linearProjOfIsCompl_apply_left (h : IsCompl p q) (x : p) :
    linearProjOfIsCompl p q h x = x := by simp [linearProjOfIsCompl]

@[simp]
theorem linearProjOfIsCompl_range (h : IsCompl p q) : range (linearProjOfIsCompl p q h) = ⊤ :=
  range_eq_of_proj (linearProjOfIsCompl_apply_left h)

theorem linearProjOfIsCompl_surjective (h : IsCompl p q) :
    Function.Surjective (linearProjOfIsCompl p q h) :=
  range_eq_top.mp (linearProjOfIsCompl_range h)

@[simp]
theorem linearProjOfIsCompl_apply_eq_zero_iff (h : IsCompl p q) {x : E} :
    linearProjOfIsCompl p q h x = 0 ↔ x ∈ q := by simp [linearProjOfIsCompl]

theorem linearProjOfIsCompl_apply_right' (h : IsCompl p q) (x : E) (hx : x ∈ q) :
    linearProjOfIsCompl p q h x = 0 :=
  (linearProjOfIsCompl_apply_eq_zero_iff h).2 hx

@[simp]
theorem linearProjOfIsCompl_apply_right (h : IsCompl p q) (x : q) :
    linearProjOfIsCompl p q h x = 0 :=
  linearProjOfIsCompl_apply_right' h x x.2

@[simp]
theorem linearProjOfIsCompl_ker (h : IsCompl p q) : ker (linearProjOfIsCompl p q h) = q :=
  ext fun _ => mem_ker.trans (linearProjOfIsCompl_apply_eq_zero_iff h)

theorem linearProjOfIsCompl_comp_subtype (h : IsCompl p q) :
    (linearProjOfIsCompl p q h).comp p.subtype = LinearMap.id :=
  LinearMap.ext <| linearProjOfIsCompl_apply_left h

theorem linearProjOfIsCompl_idempotent (h : IsCompl p q) (x : E) :
    linearProjOfIsCompl p q h (linearProjOfIsCompl p q h x) = linearProjOfIsCompl p q h x :=
  linearProjOfIsCompl_apply_left h _

theorem existsUnique_add_of_isCompl_prod (hc : IsCompl p q) (x : E) :
    ∃! u : p × q, (u.fst : E) + u.snd = x :=
  (prodEquivOfIsCompl _ _ hc).toEquiv.bijective.existsUnique _

theorem existsUnique_add_of_isCompl (hc : IsCompl p q) (x : E) :
    ∃ (u : p) (v : q), (u : E) + v = x ∧ ∀ (r : p) (s : q), (r : E) + s = x → r = u ∧ s = v :=
  let ⟨u, hu₁, hu₂⟩ := existsUnique_add_of_isCompl_prod hc x
  ⟨u.1, u.2, hu₁, fun r s hrs => Prod.eq_iff_fst_eq_snd_eq.1 (hu₂ ⟨r, s⟩ hrs)⟩

theorem linear_proj_add_linearProjOfIsCompl_eq_self (hpq : IsCompl p q) (x : E) :
    (p.linearProjOfIsCompl q hpq x + q.linearProjOfIsCompl p hpq.symm x : E) = x := by
  dsimp only [linearProjOfIsCompl]
  rw [← prodComm_trans_prodEquivOfIsCompl _ _ hpq]
  exact (prodEquivOfIsCompl _ _ hpq).apply_symm_apply x

end Submodule

namespace LinearMap

open Submodule

/-- Projection to the image of an injection along a complement.

This has an advantage over `Submodule.linearProjOfIsCompl` in that it allows the user better
definitional control over the type. -/
def linearProjOfIsCompl {F : Type*} [AddCommGroup F] [Module R F]
    (i : F →ₗ[R] E) (hi : Function.Injective i)
    (h : IsCompl (LinearMap.range i) q) : E →ₗ[R] F :=
  (LinearEquiv.ofInjective i hi).symm ∘ₗ (LinearMap.range i).linearProjOfIsCompl q h

@[simp]
theorem linearProjOfIsCompl_apply_left {F : Type*} [AddCommGroup F] [Module R F]
    (i : F →ₗ[R] E) (hi : Function.Injective i)
    (h : IsCompl (LinearMap.range i) q) (x : F) :
    linearProjOfIsCompl q i hi h (i x) = x := by
  let ix : LinearMap.range i := ⟨i x, mem_range_self i x⟩
  change linearProjOfIsCompl q i hi h ix = x
  rw [linearProjOfIsCompl, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.symm_apply_eq, Submodule.linearProjOfIsCompl_apply_left, Subtype.ext_iff,
    LinearEquiv.ofInjective_apply]

/-- Given linear maps `φ` and `ψ` from complement submodules, `LinearMap.ofIsCompl` is
the induced linear map over the entire module. -/
def ofIsCompl {p q : Submodule R E} (h : IsCompl p q) (φ : p →ₗ[R] F) (ψ : q →ₗ[R] F) : E →ₗ[R] F :=
  LinearMap.coprod φ ψ ∘ₗ ↑(Submodule.prodEquivOfIsCompl _ _ h).symm

variable {p q}

@[simp]
theorem ofIsCompl_left_apply (h : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} (u : p) :
    ofIsCompl h φ ψ (u : E) = φ u := by simp [ofIsCompl]

@[simp]
theorem ofIsCompl_right_apply (h : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} (v : q) :
    ofIsCompl h φ ψ (v : E) = ψ v := by simp [ofIsCompl]

theorem ofIsCompl_eq (h : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} {χ : E →ₗ[R] F}
    (hφ : ∀ u, φ u = χ u) (hψ : ∀ u, ψ u = χ u) : ofIsCompl h φ ψ = χ := by
  ext x
  obtain ⟨_, _, rfl, _⟩ := existsUnique_add_of_isCompl h x
  simp [ofIsCompl, hφ, hψ]

theorem ofIsCompl_eq' (h : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} {χ : E →ₗ[R] F}
    (hφ : φ = χ.comp p.subtype) (hψ : ψ = χ.comp q.subtype) : ofIsCompl h φ ψ = χ :=
  ofIsCompl_eq h (fun _ => hφ.symm ▸ rfl) fun _ => hψ.symm ▸ rfl

@[simp]
theorem ofIsCompl_zero (h : IsCompl p q) : (ofIsCompl h 0 0 : E →ₗ[R] F) = 0 :=
  ofIsCompl_eq _ (fun _ => rfl) fun _ => rfl

@[simp]
theorem ofIsCompl_add (h : IsCompl p q) {φ₁ φ₂ : p →ₗ[R] F} {ψ₁ ψ₂ : q →ₗ[R] F} :
    ofIsCompl h (φ₁ + φ₂) (ψ₁ + ψ₂) = ofIsCompl h φ₁ ψ₁ + ofIsCompl h φ₂ ψ₂ :=
  ofIsCompl_eq _ (by simp) (by simp)

@[simp]
theorem ofIsCompl_smul {R : Type*} [CommRing R] {E : Type*} [AddCommGroup E] [Module R E]
    {F : Type*} [AddCommGroup F] [Module R F] {p q : Submodule R E} (h : IsCompl p q)
    {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} (c : R) : ofIsCompl h (c • φ) (c • ψ) = c • ofIsCompl h φ ψ :=
  ofIsCompl_eq _ (by simp) (by simp)

section

variable {R₁ : Type*} [CommRing R₁] [Module R₁ E] [Module R₁ F]

/-- The linear map from `(p →ₗ[R₁] F) × (q →ₗ[R₁] F)` to `E →ₗ[R₁] F`. -/
def ofIsComplProd {p q : Submodule R₁ E} (h : IsCompl p q) :
    (p →ₗ[R₁] F) × (q →ₗ[R₁] F) →ₗ[R₁] E →ₗ[R₁] F where
  toFun φ := ofIsCompl h φ.1 φ.2
  map_add' := by intro φ ψ; rw [Prod.snd_add, Prod.fst_add, ofIsCompl_add]
  map_smul' := by intro c φ; simp [Prod.smul_snd, Prod.smul_fst, ofIsCompl_smul]

@[simp]
theorem ofIsComplProd_apply {p q : Submodule R₁ E} (h : IsCompl p q)
    (φ : (p →ₗ[R₁] F) × (q →ₗ[R₁] F)) : ofIsComplProd h φ = ofIsCompl h φ.1 φ.2 :=
  rfl

/-- The natural linear equivalence between `(p →ₗ[R₁] F) × (q →ₗ[R₁] F)` and `E →ₗ[R₁] F`. -/
def ofIsComplProdEquiv {p q : Submodule R₁ E} (h : IsCompl p q) :
    ((p →ₗ[R₁] F) × (q →ₗ[R₁] F)) ≃ₗ[R₁] E →ₗ[R₁] F :=
  { ofIsComplProd h with
    invFun := fun φ => ⟨φ.domRestrict p, φ.domRestrict q⟩
    left_inv := fun φ ↦ by
      ext x
      · exact ofIsCompl_left_apply h x
      · exact ofIsCompl_right_apply h x
    right_inv := fun φ ↦ by
      ext x
      obtain ⟨a, b, hab, _⟩ := existsUnique_add_of_isCompl h x
      rw [← hab]; simp }

end

@[simp]
theorem linearProjOfIsCompl_of_proj (f : E →ₗ[R] p) (hf : ∀ x : p, f x = x) :
    p.linearProjOfIsCompl (ker f) (isCompl_of_proj hf) = f := by
  ext x
  have : x ∈ p ⊔ (ker f) := by simp only [(isCompl_of_proj hf).sup_eq_top, mem_top]
  rcases mem_sup'.1 this with ⟨x, y, rfl⟩
  simp [hf]

/-- If `f : E →ₗ[R] F` and `g : E →ₗ[R] G` are two surjective linear maps and
their kernels are complement of each other, then `x ↦ (f x, g x)` defines
a linear equivalence `E ≃ₗ[R] F × G`. -/
def equivProdOfSurjectiveOfIsCompl (f : E →ₗ[R] F) (g : E →ₗ[R] G) (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) : E ≃ₗ[R] F × G :=
  LinearEquiv.ofBijective (f.prod g)
    ⟨by simp [← ker_eq_bot, hfg.inf_eq_bot], by
      rw [← range_eq_top]
      simp [range_prod_eq hfg.sup_eq_top, *]⟩

@[simp]
theorem coe_equivProdOfSurjectiveOfIsCompl {f : E →ₗ[R] F} {g : E →ₗ[R] G} (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) :
    (equivProdOfSurjectiveOfIsCompl f g hf hg hfg : E →ₗ[R] F × G) = f.prod g := rfl

@[simp]
theorem equivProdOfSurjectiveOfIsCompl_apply {f : E →ₗ[R] F} {g : E →ₗ[R] G} (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) (x : E) :
    equivProdOfSurjectiveOfIsCompl f g hf hg hfg x = (f x, g x) := rfl

end LinearMap

namespace Submodule

open LinearMap

/-- Equivalence between submodules `q` such that `IsCompl p q` and linear maps `f : E →ₗ[R] p`
such that `∀ x : p, f x = x`. -/
def isComplEquivProj : { q // IsCompl p q } ≃ { f : E →ₗ[R] p // ∀ x : p, f x = x } where
  toFun q := ⟨linearProjOfIsCompl p q q.2, linearProjOfIsCompl_apply_left q.2⟩
  invFun f := ⟨ker (f : E →ₗ[R] p), isCompl_of_proj f.2⟩
  left_inv := fun ⟨q, hq⟩ => by simp only [linearProjOfIsCompl_ker, Subtype.coe_mk]
  right_inv := fun ⟨f, hf⟩ => Subtype.eq <| f.linearProjOfIsCompl_of_proj hf

@[simp]
theorem coe_isComplEquivProj_apply (q : { q // IsCompl p q }) :
    (p.isComplEquivProj q : E →ₗ[R] p) = linearProjOfIsCompl p q q.2 := rfl

@[simp]
theorem coe_isComplEquivProj_symm_apply (f : { f : E →ₗ[R] p // ∀ x : p, f x = x }) :
    (p.isComplEquivProj.symm f : Submodule R E) = ker (f : E →ₗ[R] p) := rfl

/-- The idempotent endomorphisms of a module with range equal to a submodule are in 1-1
correspondence with linear maps to the submodule that restrict to the identity on the submodule. -/
@[simps] def isIdempotentElemEquiv :
    { f : Module.End R E // IsIdempotentElem f ∧ range f = p } ≃
    { f : E →ₗ[R] p // ∀ x : p, f x = x } where
  toFun f := ⟨f.1.codRestrict _ fun x ↦ by simp_rw [← f.2.2]; exact mem_range_self f.1 x,
    fun ⟨x, hx⟩ ↦ Subtype.ext <| by
      obtain ⟨x, rfl⟩ := f.2.2.symm ▸ hx
      exact DFunLike.congr_fun f.2.1 x⟩
  invFun f := ⟨p.subtype ∘ₗ f.1, LinearMap.ext fun x ↦ by simp [f.2], le_antisymm
    ((range_comp_le_range _ _).trans_eq p.range_subtype)
    fun x hx ↦ ⟨x, Subtype.ext_iff.1 <| f.2 ⟨x, hx⟩⟩⟩

end Submodule

namespace LinearMap

open Submodule

/--
A linear endomorphism of a module `E` is a projection onto a submodule `p` if it sends every element
of `E` to `p` and fixes every element of `p`.
The definition allow more generally any `FunLike` type and not just linear maps, so that it can be
used for example with `ContinuousLinearMap` or `Matrix`.
-/
structure IsProj {F : Type*} [FunLike F M M] (f : F) : Prop where
  map_mem : ∀ x, f x ∈ m
  map_id : ∀ x ∈ m, f x = x

theorem isProj_iff_isIdempotentElem (f : M →ₗ[S] M) :
    (∃ p : Submodule S M, IsProj p f) ↔ IsIdempotentElem f := by
  constructor
  · intro ⟨p, hp⟩
    ext x
    exact hp.map_id (f x) (hp.map_mem x)
  · intro h
    use range f
    constructor
    · intro x
      exact mem_range_self f x
    · intro x hx
      obtain ⟨y, hy⟩ := mem_range.1 hx
      rw [← hy, ← Module.End.mul_apply, h]

@[deprecated (since := "2025-01-12")] alias isProj_iff_idempotent := isProj_iff_isIdempotentElem

namespace IsProj

variable {p m}

/-- Restriction of the codomain of a projection of onto a subspace `p` to `p` instead of the whole
space.
-/
def codRestrict {f : M →ₗ[S] M} (h : IsProj m f) : M →ₗ[S] m :=
  f.codRestrict m h.map_mem

@[simp]
theorem codRestrict_apply {f : M →ₗ[S] M} (h : IsProj m f) (x : M) : ↑(h.codRestrict x) = f x :=
  f.codRestrict_apply m x

@[simp]
theorem codRestrict_apply_cod {f : M →ₗ[S] M} (h : IsProj m f) (x : m) : h.codRestrict x = x := by
  ext
  rw [codRestrict_apply]
  exact h.map_id x x.2

theorem codRestrict_ker {f : M →ₗ[S] M} (h : IsProj m f) : ker h.codRestrict = ker f :=
  f.ker_codRestrict m _

theorem isCompl {f : E →ₗ[R] E} (h : IsProj p f) : IsCompl p (ker f) := by
  rw [← codRestrict_ker]
  exact isCompl_of_proj h.codRestrict_apply_cod

theorem eq_conj_prod_map' {f : E →ₗ[R] E} (h : IsProj p f) :
    f = (p.prodEquivOfIsCompl (ker f) h.isCompl).toLinearMap ∘ₗ
        prodMap id 0 ∘ₗ (p.prodEquivOfIsCompl (ker f) h.isCompl).symm.toLinearMap := by
  rw [← LinearMap.comp_assoc, LinearEquiv.eq_comp_toLinearMap_symm]
  ext x
  · simp only [coe_prodEquivOfIsCompl, comp_apply, coe_inl, coprod_apply, coe_subtype,
      map_zero, add_zero, h.map_id x x.2, prodMap_apply, id_apply]
  · simp only [coe_prodEquivOfIsCompl, comp_apply, coe_inr, coprod_apply, map_zero,
      coe_subtype, zero_add, map_coe_ker, prodMap_apply, zero_apply, add_zero]

end IsProj

end LinearMap

end Ring

section CommRing

namespace LinearMap

variable {R : Type*} [CommRing R] {E : Type*} [AddCommGroup E] [Module R E] {p : Submodule R E}

theorem IsProj.eq_conj_prodMap {f : E →ₗ[R] E} (h : IsProj p f) :
    f = (p.prodEquivOfIsCompl (ker f) h.isCompl).conj (prodMap id 0) := by
  rw [LinearEquiv.conj_apply]
  exact h.eq_conj_prod_map'

end LinearMap

end CommRing
