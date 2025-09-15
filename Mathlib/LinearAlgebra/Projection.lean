/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.Module.Submodule.Invariant
import Mathlib.LinearAlgebra.GeneralLinearGroup
import Mathlib.Algebra.Ring.Idempotent

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
    simp only [hfx, zero_mem]
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

/-- If `q` is a complement of `p`, then `p × q` is isomorphic to `E`. -/
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

/-- Projection to a submodule along a complement. It is the unique
linear map `f : E → p` such that `f x = x` for `x ∈ p` and `f x = 0` for `x ∈ q`.

See also `LinearMap.linearProjOfIsCompl`. -/
def linearProjOfIsCompl (h : IsCompl p q) : E →ₗ[R] p :=
  LinearMap.fst R p q ∘ₗ ↑(prodEquivOfIsCompl p q h).symm

variable {p q}

/-- The linear projection onto a subspace along its complement
as a map from the full space to itself, as opposed to `Submodule.linearProjOfIsCompl`,
which maps into the subtype.
This version is important as it satisfies `IsIdempotentElem`. -/
noncomputable def IsCompl.projection (hpq : IsCompl p q) :=
  p.subtype ∘ₗ p.linearProjOfIsCompl q hpq

open Submodule

theorem IsCompl.projection_apply (hpq : IsCompl p q) (x : E) :
    hpq.projection x = p.linearProjOfIsCompl q hpq x :=
  rfl

@[simp]
theorem coe_linearProjOfIsCompl_apply (hpq : IsCompl p q) (x : E) :
    (p.linearProjOfIsCompl q hpq x : E) = hpq.projection x :=
  rfl

@[simp]
theorem IsCompl.projection_apply_mem (hpq : IsCompl p q) (x : E) :
    hpq.projection x ∈ p :=
  SetLike.coe_mem _

@[simp]
theorem linearProjOfIsCompl_apply_left (h : IsCompl p q) (x : p) :
    linearProjOfIsCompl p q h x = x := by simp [linearProjOfIsCompl]

@[simp]
theorem IsCompl.projection_apply_left (hpq : IsCompl p q) (x : p) :
    hpq.projection x = x := by simp [projection]

@[simp]
theorem linearProjOfIsCompl_range (h : IsCompl p q) : range (linearProjOfIsCompl p q h) = ⊤ :=
  range_eq_of_proj (linearProjOfIsCompl_apply_left h)

@[simp]
theorem IsCompl.projection_range (hpq : IsCompl p q) : range hpq.projection = p := by
  simp [projection, range_comp]

theorem linearProjOfIsCompl_surjective (h : IsCompl p q) :
    Function.Surjective (linearProjOfIsCompl p q h) :=
  range_eq_top.mp (linearProjOfIsCompl_range h)

@[simp]
theorem linearProjOfIsCompl_apply_eq_zero_iff (h : IsCompl p q) {x : E} :
    linearProjOfIsCompl p q h x = 0 ↔ x ∈ q := by simp [linearProjOfIsCompl]

@[simp]
theorem IsCompl.projection_apply_eq_zero_iff (hpq : IsCompl p q) {x : E} :
    hpq.projection x = 0 ↔ x ∈ q := by
  simp [projection, -coe_linearProjOfIsCompl_apply]

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

@[simp]
theorem IsCompl.projection_ker (hpq : IsCompl p q) :
    ker hpq.projection = q := by
  simp [projection, ker_comp]

theorem linearProjOfIsCompl_comp_subtype (h : IsCompl p q) :
    (linearProjOfIsCompl p q h).comp p.subtype = LinearMap.id :=
  LinearMap.ext <| linearProjOfIsCompl_apply_left h

theorem linearProjOfIsCompl_isCompl_projection (h : IsCompl p q) (x : E) :
    linearProjOfIsCompl p q h (h.projection x) = linearProjOfIsCompl p q h x :=
  linearProjOfIsCompl_apply_left h _

@[deprecated (since := "2025-07-29")] alias linearProjOfIsCompl_idempotent :=
  linearProjOfIsCompl_isCompl_projection

/-- The linear projection onto a subspace along its complement is an idempotent. -/
@[simp]
theorem IsCompl.projection_isIdempotentElem (hpq : IsCompl p q) :
    IsIdempotentElem hpq.projection :=
  LinearMap.ext fun _ ↦ congr($(linearProjOfIsCompl_isCompl_projection hpq _))

theorem existsUnique_add_of_isCompl_prod (hc : IsCompl p q) (x : E) :
    ∃! u : p × q, (u.fst : E) + u.snd = x :=
  (prodEquivOfIsCompl _ _ hc).toEquiv.bijective.existsUnique _

theorem existsUnique_add_of_isCompl (hc : IsCompl p q) (x : E) :
    ∃ (u : p) (v : q), (u : E) + v = x ∧ ∀ (r : p) (s : q), (r : E) + s = x → r = u ∧ s = v :=
  let ⟨u, hu₁, hu₂⟩ := existsUnique_add_of_isCompl_prod hc x
  ⟨u.1, u.2, hu₁, fun r s hrs => Prod.eq_iff_fst_eq_snd_eq.1 (hu₂ ⟨r, s⟩ hrs)⟩

theorem IsCompl.projection_add_projection_eq_self (hpq : IsCompl p q) (x : E) :
    hpq.projection x + hpq.symm.projection x = x := by
  dsimp only [IsCompl.projection, linearProjOfIsCompl]
  rw [← prodComm_trans_prodEquivOfIsCompl _ _ hpq]
  exact (prodEquivOfIsCompl _ _ hpq).apply_symm_apply x

@[deprecated (since := "2025-07-29")] alias linearProjOfIsCompl_add_linearProjOfIsCompl_eq_self :=
  IsCompl.projection_add_projection_eq_self

@[deprecated (since := "2025-07-11")] alias linear_proj_add_linearProjOfIsCompl_eq_self :=
  linearProjOfIsCompl_add_linearProjOfIsCompl_eq_self

lemma IsCompl.projection_eq_self_sub_projection (hpq : IsCompl p q) (x : E) :
    hpq.symm.projection x = x - hpq.projection x := by
  rw [eq_sub_iff_add_eq, projection_add_projection_eq_self]

@[deprecated (since := "2025-07-29")] alias linearProjOfIsCompl_eq_self_sub_linearProjOfIsCompl :=
  IsCompl.projection_eq_self_sub_projection

/-- The projection to `p` along `q` of `x` equals `x` if and only if `x ∈ p`. -/
@[simp] lemma IsCompl.projection_eq_self_iff (hpq : IsCompl p q) (x : E) :
    hpq.projection x = x ↔ x ∈ p := by
  rw [eq_comm, ← sub_eq_zero, ← projection_eq_self_sub_projection, projection_apply_eq_zero_iff]

@[deprecated (since := "2025-07-29")] alias linearProjOfIsCompl_eq_self_iff :=
  IsCompl.projection_eq_self_iff

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

theorem ofIsCompl_eq_add (hpq : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} :
    ofIsCompl hpq φ ψ = (φ ∘ₗ p.linearProjOfIsCompl q hpq)
      + (ψ ∘ₗ q.linearProjOfIsCompl p hpq.symm) := by
  ext x
  obtain ⟨a, b, rfl, _⟩ := existsUnique_add_of_isCompl hpq x
  simp

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

theorem surjective_comp_linearProjOfIsCompl (h : IsCompl p q) [Module R M] :
    Function.Surjective (comp (p.linearProjOfIsCompl q h) : (M →ₗ[R] E) → _) :=
  fun f ↦ ⟨p.subtype ∘ₗ f, by ext; simp⟩

theorem surjective_comp_subtype_of_isComplemented (h : IsComplemented p) [Module R M] :
    Function.Surjective fun f : E →ₗ[R] M ↦ f ∘ₗ p.subtype :=
  have ⟨q, h⟩ := h; fun f ↦ ⟨f ∘ₗ p.linearProjOfIsCompl q h, by ext; simp⟩

@[simp]
theorem range_ofIsCompl (hpq : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} :
    range (ofIsCompl hpq φ ψ) = range φ ⊔ range ψ := by
  rw [ofIsCompl_eq_add]
  apply le_antisymm
  · apply range_add_le _ _ |>.trans
    gcongr
    all_goals exact range_comp_le_range ..
  · apply sup_le
    all_goals rintro - ⟨x, rfl⟩; exact ⟨x, by simp⟩

theorem ofIsCompl_subtype_zero_eq (hpq : IsCompl p q) :
    ofIsCompl hpq p.subtype 0 = hpq.projection := by
  simp [ofIsCompl_eq_add, IsCompl.projection]

theorem ofIsCompl_symm (hpq : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} :
    ofIsCompl hpq.symm ψ φ = ofIsCompl hpq φ ψ := by
  simp [ofIsCompl_eq_add, add_comm]

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
  left_inv := fun ⟨q, hq⟩ => by simp only [linearProjOfIsCompl_ker]
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

theorem isProj_range_iff_isIdempotentElem (f : M →ₗ[S] M) :
    IsProj (range f) f ↔ IsIdempotentElem f := by
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun hf =>
    ⟨fun x => mem_range_self f x, fun x ⟨y, hy⟩ => by rw [← hy, ← Module.End.mul_apply, hf.eq]⟩⟩
  ext x
  exact h2 (f x) (h1 x)

alias ⟨_, IsIdempotentElem.isProj_range⟩ := isProj_range_iff_isIdempotentElem

theorem isProj_iff_isIdempotentElem (f : M →ₗ[S] M) :
    (∃ p : Submodule S M, IsProj p f) ↔ IsIdempotentElem f := by
  refine ⟨fun ⟨p, hp⟩ => ?_, fun h => ⟨_, IsIdempotentElem.isProj_range _ h⟩⟩
  ext x
  exact hp.map_id (f x) (hp.map_mem x)

namespace IsProj

variable {p m}

theorem isIdempotentElem {f : M →ₗ[S] M} (h : IsProj m f) : IsIdempotentElem f :=
  f.isProj_iff_isIdempotentElem.mp ⟨m, h⟩

theorem mem_iff_map_id {f : M →ₗ[S] M} (hf : IsProj m f) {x : M} :
    x ∈ m ↔ f x = x :=
  ⟨hf.map_id x, fun h ↦ h ▸ hf.map_mem x⟩

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
  rw [← codRestrict_ker h]
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

theorem submodule_unique {f : M →ₗ[S] M} {m₁ m₂ : Submodule S M}
    (hf₁ : IsProj m₁ f) (hf₂ : IsProj m₂ f) : m₁ = m₂ := by
  ext; simp [hf₁.mem_iff_map_id, hf₂.mem_iff_map_id]

open LinearMap in
protected theorem range {f : M →ₗ[S] M} (h : IsProj m f) : range f = m :=
  h.isIdempotentElem.isProj_range.submodule_unique h

variable (S M) in
protected theorem bot : IsProj (⊥ : Submodule S M) (0 : M →ₗ[S] M) :=
  ⟨congrFun rfl, by simp only [mem_bot, zero_apply, forall_eq]⟩

variable (S M) in
protected theorem top : IsProj (⊤ : Submodule S M) (id (R := S)) :=
  ⟨fun _ ↦ trivial, fun _ ↦ congrFun rfl⟩

theorem subtype_comp_codRestrict {U : Submodule S M} {f : M →ₗ[S] M} (hf : IsProj U f) :
    U.subtype ∘ₗ hf.codRestrict = f := rfl

theorem submodule_eq_top_iff {f : M →ₗ[S] M} (hf : IsProj m f) :
    m = (⊤ : Submodule S M) ↔ f = LinearMap.id := by
  constructor <;> rintro rfl
  · ext
    simp [hf.map_id]
  · rw [← hf.range, range_id]

theorem submodule_eq_bot_iff {f : M →ₗ[S] M} (hf : IsProj m f) :
    m = (⊥ : Submodule S M) ↔ f = 0 := by
  constructor <;> rintro rfl
  · ext
    simpa using hf.map_mem _
  · rw [← hf.range, range_zero]

end IsProj

open LinearMap in
lemma IsIdempotentElem.isCompl {f : E →ₗ[R] E} (hf : IsIdempotentElem f) :
    IsCompl (range f) (ker f) := hf.isProj_range.isCompl

open LinearMap in
/-- Given an idempotent linear operator `p`, we have
`x ∈ range p` if and only if `p(x) = x` for all `x`. -/
theorem IsIdempotentElem.mem_range_iff {p : M →ₗ[S] M} (hp : IsIdempotentElem p) {x : M} :
    x ∈ range p ↔ p x = x := hp.isProj_range.mem_iff_map_id

open LinearMap in
/-- An idempotent linear operator is equal to the linear projection onto
its range along its kernel. -/
theorem IsIdempotentElem.eq_isCompl_projection {T : E →ₗ[R] E} (hT : IsIdempotentElem T) :
    T = hT.isCompl.projection := by
  convert ofIsCompl_subtype_zero_eq hT.isCompl
  exact ofIsCompl_eq _ (by simp [hT.isProj_range.map_id]) (by simp) |>.symm

open LinearMap in
/-- A linear map is an idempotent if and only if it equals the projection
onto its range along its kernel. -/
theorem isIdempotentElem_iff_eq_isCompl_projection_range_ker {T : E →ₗ[R] E} :
    IsIdempotentElem T ↔ ∃ (h : IsCompl (range T) (ker T)), T = h.projection :=
  ⟨fun hT => ⟨hT.isProj_range.isCompl, hT.eq_isCompl_projection⟩,
   fun ⟨hT, h⟩ => h.symm ▸ hT.projection_isIdempotentElem⟩

open LinearMap in
/-- Given an idempotent linear operator `q`,
we have `q ∘ p = p` iff `range p ⊆ range q` for all `p`. -/
theorem IsIdempotentElem.comp_eq_right_iff {q : M →ₗ[S] M} (hq : IsIdempotentElem q)
    {E : Type*} [AddCommMonoid E] [Module S E] (p : E →ₗ[S] M) :
    q.comp p = p ↔ range p ≤ range q := by
  simp_rw [LinearMap.ext_iff, comp_apply, ← hq.mem_range_iff,
    SetLike.le_def, mem_range, forall_exists_index, forall_apply_eq_imp_iff]

open LinearMap in
/-- Idempotent operators are equal iff their range and kernels are. -/
lemma IsIdempotentElem.ext_iff {p q : E →ₗ[R] E}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    p = q ↔ range p = range q ∧ ker p = ker q := by
  refine ⟨fun h => ⟨congrArg range h, congrArg ker h⟩, fun ⟨hr, hk⟩ => ?_⟩
  ext x
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩, rfl, _⟩ :=
    (ker p).existsUnique_add_of_isCompl hp.isCompl.symm x
  simp [mem_ker.mp, hv, (hk ▸ hv), (mem_range_iff hp).mp, hw, (mem_range_iff hq).mp, (hr ▸ hw)]

alias ⟨_, IsIdempotentElem.ext⟩ := IsIdempotentElem.ext_iff

theorem IsIdempotentElem.range_eq_ker {E : Type*} [AddCommGroup E] [Module S E]
    {p : E →ₗ[S] E} (hp : IsIdempotentElem p) : LinearMap.range p = LinearMap.ker (1 - p) :=
  le_antisymm
    (LinearMap.range_le_ker_iff.mpr hp.one_sub_mul_self)
    fun x hx ↦ ⟨x, by simpa [sub_eq_zero, eq_comm (a := x)] using hx⟩

open LinearMap in
theorem IsIdempotentElem.ker_eq_range {E : Type*} [AddCommGroup E] [Module S E]
    {p : E →ₗ[S] E} (hp : IsIdempotentElem p) : LinearMap.ker p = LinearMap.range (1 - p) := by
  simpa using hp.one_sub.range_eq_ker.symm

open LinearMap in
theorem IsIdempotentElem.comp_eq_left_iff {M : Type*} [AddCommGroup M] [Module S M] {q : M →ₗ[S] M}
    (hq : IsIdempotentElem q) {E : Type*} [AddCommGroup E] [Module S E] (p : M →ₗ[S] E) :
    p ∘ₗ q = p ↔ ker q ≤ ker p := by
  simp [hq.ker_eq_range, range_le_ker_iff, comp_sub, Module.End.one_eq_id, sub_eq_zero,
    eq_comm (a := p)]

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

namespace LinearMap.IsIdempotentElem

open Submodule LinearMap

variable {E R : Type*} [Ring R] [AddCommGroup E] [Module R E] {T f : E →ₗ[R] E}

/-- `range f` is invariant under `T` if and only if `f ∘ₗ T ∘ₗ f = T ∘ₗ f`,
for idempotent `f`. -/
lemma range_mem_invtSubmodule_iff (hf : IsIdempotentElem f) :
    range f ∈ Module.End.invtSubmodule T ↔ f ∘ₗ T ∘ₗ f = T ∘ₗ f := by
  rw [hf.comp_eq_right_iff, range_comp, Module.End.mem_invtSubmodule_iff_map_le]

alias ⟨conj_eq_of_range_mem_invtSubmodule, range_mem_invtSubmodule⟩ := range_mem_invtSubmodule_iff

lemma _root_.LinearMap.IsProj.mem_invtSubmodule_iff {U : Submodule R E}
    (hf : IsProj U f) : U ∈ Module.End.invtSubmodule T ↔ f ∘ₗ T ∘ₗ f = T ∘ₗ f :=
  hf.range ▸ hf.isIdempotentElem.range_mem_invtSubmodule_iff

open LinearMap in
/-- `ker f` is invariant under `T` if and only if `f ∘ₗ T ∘ₗ f = f ∘ₗ T`,
for idempotent `f`. -/
lemma ker_mem_invtSubmodule_iff (hf : IsIdempotentElem f) :
    ker f ∈ Module.End.invtSubmodule T ↔ f ∘ₗ T ∘ₗ f = f ∘ₗ T := by
  rw [← comp_assoc, hf.comp_eq_left_iff, ker_comp, Module.End.mem_invtSubmodule]

alias ⟨conj_eq_of_ker_mem_invtSubmodule, ker_mem_invtSubmodule⟩ := ker_mem_invtSubmodule_iff

/-- An idempotent operator `f` commutes with a linear operator `T` if and only if
both `range f` and `ker f` are invariant under `T`. -/
lemma commute_iff (hf : IsIdempotentElem f) :
    Commute f T ↔ (range f ∈ Module.End.invtSubmodule T ∧ ker f ∈ Module.End.invtSubmodule T) := by
  simp_rw [hf.range_mem_invtSubmodule_iff, hf.ker_mem_invtSubmodule_iff, ← Module.End.mul_eq_comp]
  exact ⟨fun h => (by simp [← h.eq, ← mul_assoc, hf.eq]), fun ⟨h1, h2⟩ => h2.symm.trans h1⟩

/-- An idempotent operator `f` commutes with an unit operator `T` if and only if
`T (range f) = range f` and `T (ker f) = ker f`. -/
theorem commute_iff_of_isUnit (hT : IsUnit T) (hf : IsIdempotentElem f) :
    Commute f T ↔ (range f).map T = range f ∧ (ker f).map T = ker f := by
  lift T to GeneralLinearGroup R E using hT
  have {a : E ≃ₗ[R] E} {b : Submodule R E} : b ≤ b.map a.toLinearMap ↔ b ≤ b.map a := by rfl
  simp_rw [← GeneralLinearGroup.generalLinearEquiv_to_linearMap, le_antisymm_iff,
    ← Module.End.mem_invtSubmodule_iff_map_le, this, ← Module.End.mem_invtSubmodule_symm_iff_le_map,
    and_and_and_comm (c := (ker f ∈ _)), ← hf.commute_iff,
    GeneralLinearGroup.generalLinearEquiv_to_linearMap, iff_self_and]
  exact Commute.units_inv_right

end LinearMap.IsIdempotentElem
