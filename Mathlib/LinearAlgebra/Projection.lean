/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.LinearAlgebra.Quotient
import Mathlib.LinearAlgebra.Prod

#align_import linear_algebra.projection from "leanprover-community/mathlib"@"6d584f1709bedbed9175bd9350df46599bdd7213"

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
  -- ⊢ x ∈ ker (id - comp (Submodule.subtype p) f) ↔ x ∈ p
  simp only [comp_apply, mem_ker, subtype_apply, sub_apply, id_apply, sub_eq_zero]
  -- ⊢ x = ↑(↑f x) ↔ x ∈ p
  exact ⟨fun h => h.symm ▸ Submodule.coe_mem _, fun hx => by erw [hf ⟨x, hx⟩, Subtype.coe_mk]⟩
  -- 🎉 no goals
#align linear_map.ker_id_sub_eq_of_proj LinearMap.ker_id_sub_eq_of_proj

theorem range_eq_of_proj {f : E →ₗ[R] p} (hf : ∀ x : p, f x = x) : range f = ⊤ :=
  range_eq_top.2 fun x => ⟨x, hf x⟩
#align linear_map.range_eq_of_proj LinearMap.range_eq_of_proj

theorem isCompl_of_proj {f : E →ₗ[R] p} (hf : ∀ x : p, f x = x) : IsCompl p (ker f) := by
  constructor
  -- ⊢ Disjoint p (ker f)
  · rw [disjoint_iff_inf_le]
    -- ⊢ p ⊓ ker f ≤ ⊥
    rintro x ⟨hpx, hfx⟩
    -- ⊢ x ∈ ⊥
    erw [SetLike.mem_coe, mem_ker, hf ⟨x, hpx⟩, mk_eq_zero] at hfx
    -- ⊢ x ∈ ⊥
    simp only [hfx, SetLike.mem_coe, zero_mem]
    -- 🎉 no goals
  · rw [codisjoint_iff_le_sup]
    -- ⊢ ⊤ ≤ p ⊔ ker f
    intro x _
    -- ⊢ x ∈ p ⊔ ker f
    rw [mem_sup']
    -- ⊢ ∃ y z, ↑y + ↑z = x
    refine' ⟨f x, ⟨x - f x, _⟩, add_sub_cancel'_right _ _⟩
    -- ⊢ x - ↑(↑f x) ∈ ker f
    rw [mem_ker, LinearMap.map_sub, hf, sub_self]
    -- 🎉 no goals
#align linear_map.is_compl_of_proj LinearMap.isCompl_of_proj

end LinearMap

namespace Submodule

open LinearMap

/-- If `q` is a complement of `p`, then `M/p ≃ q`. -/
def quotientEquivOfIsCompl (h : IsCompl p q) : (E ⧸ p) ≃ₗ[R] q :=
  LinearEquiv.symm <|
    LinearEquiv.ofBijective (p.mkQ.comp q.subtype)
      ⟨by rw [← ker_eq_bot, ker_comp, ker_mkQ, disjoint_iff_comap_eq_bot.1 h.symm.disjoint], by
          -- 🎉 no goals
        rw [← range_eq_top, range_comp, range_subtype, map_mkQ_eq_top, h.sup_eq_top]⟩
        -- 🎉 no goals
#align submodule.quotient_equiv_of_is_compl Submodule.quotientEquivOfIsCompl

@[simp]
theorem quotientEquivOfIsCompl_symm_apply (h : IsCompl p q) (x : q) :
    -- Porting note: type ascriptions needed on the RHS
    (quotientEquivOfIsCompl p q h).symm x = (Quotient.mk (x:E) : E ⧸ p) := rfl
#align submodule.quotient_equiv_of_is_compl_symm_apply Submodule.quotientEquivOfIsCompl_symm_apply

@[simp]
theorem quotientEquivOfIsCompl_apply_mk_coe (h : IsCompl p q) (x : q) :
    quotientEquivOfIsCompl p q h (Quotient.mk x) = x :=
  (quotientEquivOfIsCompl p q h).apply_symm_apply x
#align submodule.quotient_equiv_of_is_compl_apply_mk_coe Submodule.quotientEquivOfIsCompl_apply_mk_coe

@[simp]
theorem mk_quotientEquivOfIsCompl_apply (h : IsCompl p q) (x : E ⧸ p) :
    (Quotient.mk (quotientEquivOfIsCompl p q h x) : E ⧸ p) = x :=
  (quotientEquivOfIsCompl p q h).symm_apply_apply x
#align submodule.mk_quotient_equiv_of_is_compl_apply Submodule.mk_quotientEquivOfIsCompl_apply

/-- If `q` is a complement of `p`, then `p × q` is isomorphic to `E`. It is the unique
linear map `f : E → p` such that `f x = x` for `x ∈ p` and `f x = 0` for `x ∈ q`. -/
def prodEquivOfIsCompl (h : IsCompl p q) : (p × q) ≃ₗ[R] E := by
  apply LinearEquiv.ofBijective (p.subtype.coprod q.subtype)
  -- ⊢ Function.Bijective ↑(coprod (Submodule.subtype p) (Submodule.subtype q))
  constructor
  -- ⊢ Function.Injective ↑(coprod (Submodule.subtype p) (Submodule.subtype q))
  · rw [← ker_eq_bot, ker_coprod_of_disjoint_range, ker_subtype, ker_subtype, prod_bot]
    -- ⊢ Disjoint (range (Submodule.subtype p)) (range (Submodule.subtype q))
    rw [range_subtype, range_subtype]
    -- ⊢ Disjoint p q
    exact h.1
    -- 🎉 no goals
  · rw [← range_eq_top, ← sup_eq_range, h.sup_eq_top]
    -- 🎉 no goals
#align submodule.prod_equiv_of_is_compl Submodule.prodEquivOfIsCompl

@[simp]
theorem coe_prodEquivOfIsCompl (h : IsCompl p q) :
    (prodEquivOfIsCompl p q h : p × q →ₗ[R] E) = p.subtype.coprod q.subtype := rfl
#align submodule.coe_prod_equiv_of_is_compl Submodule.coe_prodEquivOfIsCompl

@[simp]
theorem coe_prodEquivOfIsCompl' (h : IsCompl p q) (x : p × q) :
    prodEquivOfIsCompl p q h x = x.1 + x.2 := rfl
#align submodule.coe_prod_equiv_of_is_compl' Submodule.coe_prodEquivOfIsCompl'

@[simp]
theorem prodEquivOfIsCompl_symm_apply_left (h : IsCompl p q) (x : p) :
    (prodEquivOfIsCompl p q h).symm x = (x, 0) :=
  (prodEquivOfIsCompl p q h).symm_apply_eq.2 <| by simp
                                                   -- 🎉 no goals
#align submodule.prod_equiv_of_is_compl_symm_apply_left Submodule.prodEquivOfIsCompl_symm_apply_left

@[simp]
theorem prodEquivOfIsCompl_symm_apply_right (h : IsCompl p q) (x : q) :
    (prodEquivOfIsCompl p q h).symm x = (0, x) :=
  (prodEquivOfIsCompl p q h).symm_apply_eq.2 <| by simp
                                                   -- 🎉 no goals
#align submodule.prod_equiv_of_is_compl_symm_apply_right Submodule.prodEquivOfIsCompl_symm_apply_right

@[simp]
theorem prodEquivOfIsCompl_symm_apply_fst_eq_zero (h : IsCompl p q) {x : E} :
    ((prodEquivOfIsCompl p q h).symm x).1 = 0 ↔ x ∈ q := by
  conv_rhs => rw [← (prodEquivOfIsCompl p q h).apply_symm_apply x]
  -- ⊢ (↑(LinearEquiv.symm (prodEquivOfIsCompl p q h)) x).fst = 0 ↔ ↑(prodEquivOfIs …
  rw [coe_prodEquivOfIsCompl', Submodule.add_mem_iff_left _ (Submodule.coe_mem _),
    mem_right_iff_eq_zero_of_disjoint h.disjoint]
#align submodule.prod_equiv_of_is_compl_symm_apply_fst_eq_zero Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero

@[simp]
theorem prodEquivOfIsCompl_symm_apply_snd_eq_zero (h : IsCompl p q) {x : E} :
    ((prodEquivOfIsCompl p q h).symm x).2 = 0 ↔ x ∈ p := by
  conv_rhs => rw [← (prodEquivOfIsCompl p q h).apply_symm_apply x]
  -- ⊢ (↑(LinearEquiv.symm (prodEquivOfIsCompl p q h)) x).snd = 0 ↔ ↑(prodEquivOfIs …
  rw [coe_prodEquivOfIsCompl', Submodule.add_mem_iff_right _ (Submodule.coe_mem _),
    mem_left_iff_eq_zero_of_disjoint h.disjoint]
#align submodule.prod_equiv_of_is_compl_symm_apply_snd_eq_zero Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero

@[simp]
theorem prodComm_trans_prodEquivOfIsCompl (h : IsCompl p q) :
    LinearEquiv.prodComm R q p ≪≫ₗ prodEquivOfIsCompl p q h = prodEquivOfIsCompl q p h.symm :=
  LinearEquiv.ext fun _ => add_comm _ _
#align submodule.prod_comm_trans_prod_equiv_of_is_compl Submodule.prodComm_trans_prodEquivOfIsCompl

/-- Projection to a submodule along its complement. -/
def linearProjOfIsCompl (h : IsCompl p q) : E →ₗ[R] p :=
  LinearMap.fst R p q ∘ₗ ↑(prodEquivOfIsCompl p q h).symm
#align submodule.linear_proj_of_is_compl Submodule.linearProjOfIsCompl

variable {p q}

@[simp]
theorem linearProjOfIsCompl_apply_left (h : IsCompl p q) (x : p) :
    linearProjOfIsCompl p q h x = x := by simp [linearProjOfIsCompl]
                                          -- 🎉 no goals
#align submodule.linear_proj_of_is_compl_apply_left Submodule.linearProjOfIsCompl_apply_left

@[simp]
theorem linearProjOfIsCompl_range (h : IsCompl p q) : range (linearProjOfIsCompl p q h) = ⊤ :=
  range_eq_of_proj (linearProjOfIsCompl_apply_left h)
#align submodule.linear_proj_of_is_compl_range Submodule.linearProjOfIsCompl_range

@[simp]
theorem linearProjOfIsCompl_apply_eq_zero_iff (h : IsCompl p q) {x : E} :
    linearProjOfIsCompl p q h x = 0 ↔ x ∈ q := by simp [linearProjOfIsCompl]
                                                  -- 🎉 no goals
#align submodule.linear_proj_of_is_compl_apply_eq_zero_iff Submodule.linearProjOfIsCompl_apply_eq_zero_iff

theorem linearProjOfIsCompl_apply_right' (h : IsCompl p q) (x : E) (hx : x ∈ q) :
    linearProjOfIsCompl p q h x = 0 :=
  (linearProjOfIsCompl_apply_eq_zero_iff h).2 hx
#align submodule.linear_proj_of_is_compl_apply_right' Submodule.linearProjOfIsCompl_apply_right'

@[simp]
theorem linearProjOfIsCompl_apply_right (h : IsCompl p q) (x : q) :
    linearProjOfIsCompl p q h x = 0 :=
  linearProjOfIsCompl_apply_right' h x x.2
#align submodule.linear_proj_of_is_compl_apply_right Submodule.linearProjOfIsCompl_apply_right

@[simp]
theorem linearProjOfIsCompl_ker (h : IsCompl p q) : ker (linearProjOfIsCompl p q h) = q :=
  ext fun _ => mem_ker.trans (linearProjOfIsCompl_apply_eq_zero_iff h)
#align submodule.linear_proj_of_is_compl_ker Submodule.linearProjOfIsCompl_ker

theorem linearProjOfIsCompl_comp_subtype (h : IsCompl p q) :
    (linearProjOfIsCompl p q h).comp p.subtype = LinearMap.id :=
  LinearMap.ext <| linearProjOfIsCompl_apply_left h
#align submodule.linear_proj_of_is_compl_comp_subtype Submodule.linearProjOfIsCompl_comp_subtype

theorem linearProjOfIsCompl_idempotent (h : IsCompl p q) (x : E) :
    linearProjOfIsCompl p q h (linearProjOfIsCompl p q h x) = linearProjOfIsCompl p q h x :=
  linearProjOfIsCompl_apply_left h _
#align submodule.linear_proj_of_is_compl_idempotent Submodule.linearProjOfIsCompl_idempotent

theorem existsUnique_add_of_isCompl_prod (hc : IsCompl p q) (x : E) :
    ∃! u : p × q, (u.fst : E) + u.snd = x :=
  (prodEquivOfIsCompl _ _ hc).toEquiv.bijective.existsUnique _
#align submodule.exists_unique_add_of_is_compl_prod Submodule.existsUnique_add_of_isCompl_prod

theorem existsUnique_add_of_isCompl (hc : IsCompl p q) (x : E) :
    ∃ (u : p) (v : q), (u : E) + v = x ∧ ∀ (r : p) (s : q), (r : E) + s = x → r = u ∧ s = v :=
  let ⟨u, hu₁, hu₂⟩ := existsUnique_add_of_isCompl_prod hc x
  ⟨u.1, u.2, hu₁, fun r s hrs => Prod.eq_iff_fst_eq_snd_eq.1 (hu₂ ⟨r, s⟩ hrs)⟩
#align submodule.exists_unique_add_of_is_compl Submodule.existsUnique_add_of_isCompl

theorem linear_proj_add_linearProjOfIsCompl_eq_self (hpq : IsCompl p q) (x : E) :
    (p.linearProjOfIsCompl q hpq x + q.linearProjOfIsCompl p hpq.symm x : E) = x := by
  dsimp only [linearProjOfIsCompl]
  -- ⊢ ↑(↑(comp (LinearMap.fst R { x // x ∈ p } { x // x ∈ q }) ↑(LinearEquiv.symm  …
  rw [← prodComm_trans_prodEquivOfIsCompl _ _ hpq]
  -- ⊢ ↑(↑(comp (LinearMap.fst R { x // x ∈ p } { x // x ∈ q }) ↑(LinearEquiv.symm  …
  exact (prodEquivOfIsCompl _ _ hpq).apply_symm_apply x
  -- 🎉 no goals
#align submodule.linear_proj_add_linear_proj_of_is_compl_eq_self Submodule.linear_proj_add_linearProjOfIsCompl_eq_self

end Submodule

namespace LinearMap

open Submodule

/-- Given linear maps `φ` and `ψ` from complement submodules, `LinearMap.ofIsCompl` is
the induced linear map over the entire module. -/
def ofIsCompl {p q : Submodule R E} (h : IsCompl p q) (φ : p →ₗ[R] F) (ψ : q →ₗ[R] F) : E →ₗ[R] F :=
  LinearMap.coprod φ ψ ∘ₗ ↑(Submodule.prodEquivOfIsCompl _ _ h).symm
#align linear_map.of_is_compl LinearMap.ofIsCompl

variable {p q}

@[simp]
theorem ofIsCompl_left_apply (h : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} (u : p) :
    ofIsCompl h φ ψ (u : E) = φ u := by simp [ofIsCompl]
                                        -- 🎉 no goals
#align linear_map.of_is_compl_left_apply LinearMap.ofIsCompl_left_apply

@[simp]
theorem ofIsCompl_right_apply (h : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} (v : q) :
    ofIsCompl h φ ψ (v : E) = ψ v := by simp [ofIsCompl]
                                        -- 🎉 no goals
#align linear_map.of_is_compl_right_apply LinearMap.ofIsCompl_right_apply

theorem ofIsCompl_eq (h : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} {χ : E →ₗ[R] F}
    (hφ : ∀ u, φ u = χ u) (hψ : ∀ u, ψ u = χ u) : ofIsCompl h φ ψ = χ := by
  ext x
  -- ⊢ ↑(ofIsCompl h φ ψ) x = ↑χ x
  obtain ⟨_, _, rfl, _⟩ := existsUnique_add_of_isCompl h x
  -- ⊢ ↑(ofIsCompl h φ ψ) (↑w✝¹ + ↑w✝) = ↑χ (↑w✝¹ + ↑w✝)
  simp [ofIsCompl, hφ, hψ]
  -- 🎉 no goals
#align linear_map.of_is_compl_eq LinearMap.ofIsCompl_eq

theorem ofIsCompl_eq' (h : IsCompl p q) {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} {χ : E →ₗ[R] F}
    (hφ : φ = χ.comp p.subtype) (hψ : ψ = χ.comp q.subtype) : ofIsCompl h φ ψ = χ :=
  ofIsCompl_eq h (fun _ => hφ.symm ▸ rfl) fun _ => hψ.symm ▸ rfl
#align linear_map.of_is_compl_eq' LinearMap.ofIsCompl_eq'

@[simp]
theorem ofIsCompl_zero (h : IsCompl p q) : (ofIsCompl h 0 0 : E →ₗ[R] F) = 0 :=
  ofIsCompl_eq _ (fun _ => rfl) fun _ => rfl
#align linear_map.of_is_compl_zero LinearMap.ofIsCompl_zero

@[simp]
theorem ofIsCompl_add (h : IsCompl p q) {φ₁ φ₂ : p →ₗ[R] F} {ψ₁ ψ₂ : q →ₗ[R] F} :
    ofIsCompl h (φ₁ + φ₂) (ψ₁ + ψ₂) = ofIsCompl h φ₁ ψ₁ + ofIsCompl h φ₂ ψ₂ :=
  ofIsCompl_eq _ (by simp) (by simp)
                     -- 🎉 no goals
                               -- 🎉 no goals
#align linear_map.of_is_compl_add LinearMap.ofIsCompl_add

@[simp]
theorem ofIsCompl_smul {R : Type*} [CommRing R] {E : Type*} [AddCommGroup E] [Module R E]
    {F : Type*} [AddCommGroup F] [Module R F] {p q : Submodule R E} (h : IsCompl p q)
    {φ : p →ₗ[R] F} {ψ : q →ₗ[R] F} (c : R) : ofIsCompl h (c • φ) (c • ψ) = c • ofIsCompl h φ ψ :=
  ofIsCompl_eq _ (by simp) (by simp)
                     -- 🎉 no goals
                               -- 🎉 no goals
#align linear_map.of_is_compl_smul LinearMap.ofIsCompl_smul

section

variable {R₁ : Type*} [CommRing R₁] [Module R₁ E] [Module R₁ F]

/-- The linear map from `(p →ₗ[R₁] F) × (q →ₗ[R₁] F)` to `E →ₗ[R₁] F`. -/
def ofIsComplProd {p q : Submodule R₁ E} (h : IsCompl p q) :
    (p →ₗ[R₁] F) × (q →ₗ[R₁] F) →ₗ[R₁] E →ₗ[R₁] F where
  toFun φ := ofIsCompl h φ.1 φ.2
  map_add' := by intro φ ψ; dsimp only; rw [Prod.snd_add, Prod.fst_add, ofIsCompl_add]
                 -- ⊢ (fun φ => ofIsCompl h φ.fst φ.snd) (φ + ψ) = (fun φ => ofIsCompl h φ.fst φ.s …
                            -- ⊢ ofIsCompl h (φ + ψ).fst (φ + ψ).snd = ofIsCompl h φ.fst φ.snd + ofIsCompl h  …
                                        -- 🎉 no goals
  map_smul' := by intro c φ; simp [Prod.smul_snd, Prod.smul_fst, ofIsCompl_smul]
                  -- ⊢ AddHom.toFun { toFun := fun φ => ofIsCompl h φ.fst φ.snd, map_add' := (_ : ∀ …
                             -- 🎉 no goals
#align linear_map.of_is_compl_prod LinearMap.ofIsComplProd

@[simp]
theorem ofIsComplProd_apply {p q : Submodule R₁ E} (h : IsCompl p q)
    (φ : (p →ₗ[R₁] F) × (q →ₗ[R₁] F)) : ofIsComplProd h φ = ofIsCompl h φ.1 φ.2 :=
  rfl
#align linear_map.of_is_compl_prod_apply LinearMap.ofIsComplProd_apply

/-- The natural linear equivalence between `(p →ₗ[R₁] F) × (q →ₗ[R₁] F)` and `E →ₗ[R₁] F`. -/
def ofIsComplProdEquiv {p q : Submodule R₁ E} (h : IsCompl p q) :
    ((p →ₗ[R₁] F) × (q →ₗ[R₁] F)) ≃ₗ[R₁] E →ₗ[R₁] F :=
  { ofIsComplProd h with
    invFun := fun φ => ⟨φ.domRestrict p, φ.domRestrict q⟩
    left_inv := fun φ ↦ by
      ext x
      -- ⊢ ↑((fun φ => (domRestrict φ p, domRestrict φ q)) (AddHom.toFun { toAddHom :=  …
      · exact ofIsCompl_left_apply h x
        -- 🎉 no goals
      · exact ofIsCompl_right_apply h x
        -- 🎉 no goals
    right_inv := fun φ ↦ by
      ext x
      -- ⊢ ↑(AddHom.toFun { toAddHom := src✝.toAddHom, map_smul' := (_ : ∀ (r : R₁) (x  …
      obtain ⟨a, b, hab, _⟩ := existsUnique_add_of_isCompl h x
      -- ⊢ ↑(AddHom.toFun { toAddHom := src✝.toAddHom, map_smul' := (_ : ∀ (r : R₁) (x  …
      rw [← hab]; simp }
      -- ⊢ ↑(AddHom.toFun { toAddHom := src✝.toAddHom, map_smul' := (_ : ∀ (r : R₁) (x  …
                  -- 🎉 no goals
#align linear_map.of_is_compl_prod_equiv LinearMap.ofIsComplProdEquiv

end

@[simp, nolint simpNF] -- Porting note: linter claims that LHS doesn't simplify, but it does
theorem linearProjOfIsCompl_of_proj (f : E →ₗ[R] p) (hf : ∀ x : p, f x = x) :
    p.linearProjOfIsCompl (ker f) (isCompl_of_proj hf) = f := by
  ext x
  -- ⊢ ↑(↑(linearProjOfIsCompl p (ker f) (_ : IsCompl p (ker f))) x) = ↑(↑f x)
  have : x ∈ p ⊔ (ker f) := by simp only [(isCompl_of_proj hf).sup_eq_top, mem_top]
  -- ⊢ ↑(↑(linearProjOfIsCompl p (ker f) (_ : IsCompl p (ker f))) x) = ↑(↑f x)
  rcases mem_sup'.1 this with ⟨x, y, rfl⟩
  -- ⊢ ↑(↑(linearProjOfIsCompl p (ker f) (_ : IsCompl p (ker f))) (↑x + ↑y)) = ↑(↑f …
  simp [hf]
  -- 🎉 no goals
#align linear_map.linear_proj_of_is_compl_of_proj LinearMap.linearProjOfIsCompl_of_proj

/-- If `f : E →ₗ[R] F` and `g : E →ₗ[R] G` are two surjective linear maps and
their kernels are complement of each other, then `x ↦ (f x, g x)` defines
a linear equivalence `E ≃ₗ[R] F × G`. -/
def equivProdOfSurjectiveOfIsCompl (f : E →ₗ[R] F) (g : E →ₗ[R] G) (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) : E ≃ₗ[R] F × G :=
  LinearEquiv.ofBijective (f.prod g)
    ⟨by simp [← ker_eq_bot, hfg.inf_eq_bot], by
        -- 🎉 no goals
      rw [← range_eq_top]
      -- ⊢ range (prod f g) = ⊤
      simp [range_prod_eq hfg.sup_eq_top, *]⟩
      -- 🎉 no goals
#align linear_map.equiv_prod_of_surjective_of_is_compl LinearMap.equivProdOfSurjectiveOfIsCompl

@[simp]
theorem coe_equivProdOfSurjectiveOfIsCompl {f : E →ₗ[R] F} {g : E →ₗ[R] G} (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) :
    (equivProdOfSurjectiveOfIsCompl f g hf hg hfg : E →ₗ[R] F × G) = f.prod g := rfl
#align linear_map.coe_equiv_prod_of_surjective_of_is_compl LinearMap.coe_equivProdOfSurjectiveOfIsCompl

@[simp]
theorem equivProdOfSurjectiveOfIsCompl_apply {f : E →ₗ[R] F} {g : E →ₗ[R] G} (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) (x : E) :
    equivProdOfSurjectiveOfIsCompl f g hf hg hfg x = (f x, g x) := rfl
#align linear_map.equiv_prod_of_surjective_of_is_compl_apply LinearMap.equivProdOfSurjectiveOfIsCompl_apply

end LinearMap

namespace Submodule

open LinearMap

/-- Equivalence between submodules `q` such that `IsCompl p q` and linear maps `f : E →ₗ[R] p`
such that `∀ x : p, f x = x`. -/
def isComplEquivProj : { q // IsCompl p q } ≃ { f : E →ₗ[R] p // ∀ x : p, f x = x } where
  toFun q := ⟨linearProjOfIsCompl p q q.2, linearProjOfIsCompl_apply_left q.2⟩
  invFun f := ⟨ker (f : E →ₗ[R] p), isCompl_of_proj f.2⟩
  left_inv := fun ⟨q, hq⟩ => by simp only [linearProjOfIsCompl_ker, Subtype.coe_mk]
                                -- 🎉 no goals
  right_inv := fun ⟨f, hf⟩ => Subtype.eq <| f.linearProjOfIsCompl_of_proj hf
#align submodule.is_compl_equiv_proj Submodule.isComplEquivProj

@[simp]
theorem coe_isComplEquivProj_apply (q : { q // IsCompl p q }) :
    (p.isComplEquivProj q : E →ₗ[R] p) = linearProjOfIsCompl p q q.2 := rfl
#align submodule.coe_is_compl_equiv_proj_apply Submodule.coe_isComplEquivProj_apply

@[simp]
theorem coe_isComplEquivProj_symm_apply (f : { f : E →ₗ[R] p // ∀ x : p, f x = x }) :
    (p.isComplEquivProj.symm f : Submodule R E) = ker (f : E →ₗ[R] p) := rfl
#align submodule.coe_is_compl_equiv_proj_symm_apply Submodule.coe_isComplEquivProj_symm_apply

end Submodule

namespace LinearMap

open Submodule

/--
A linear endomorphism of a module `E` is a projection onto a submodule `p` if it sends every element
of `E` to `p` and fixes every element of `p`.
The definition allow more generally any `FunLike` type and not just linear maps, so that it can be
used for example with `ContinuousLinearMap` or `Matrix`.
-/
structure IsProj {F : Type*} [FunLike F M fun _ => M] (f : F) : Prop where
  map_mem : ∀ x, f x ∈ m
  map_id : ∀ x ∈ m, f x = x
#align linear_map.is_proj LinearMap.IsProj

theorem isProj_iff_idempotent (f : M →ₗ[S] M) : (∃ p : Submodule S M, IsProj p f) ↔ f ∘ₗ f = f := by
  constructor
  -- ⊢ (∃ p, IsProj p f) → comp f f = f
  · intro h
    -- ⊢ comp f f = f
    obtain ⟨p, hp⟩ := h
    -- ⊢ comp f f = f
    ext x
    -- ⊢ ↑(comp f f) x = ↑f x
    rw [comp_apply]
    -- ⊢ ↑f (↑f x) = ↑f x
    exact hp.map_id (f x) (hp.map_mem x)
    -- 🎉 no goals
  · intro h
    -- ⊢ ∃ p, IsProj p f
    use range f
    -- ⊢ IsProj (range f) f
    constructor
    -- ⊢ ∀ (x : M), ↑f x ∈ range f
    · intro x
      -- ⊢ ↑f x ∈ range f
      exact mem_range_self f x
      -- 🎉 no goals
    · intro x hx
      -- ⊢ ↑f x = x
      obtain ⟨y, hy⟩ := mem_range.1 hx
      -- ⊢ ↑f x = x
      rw [← hy, ← comp_apply, h]
      -- 🎉 no goals
#align linear_map.is_proj_iff_idempotent LinearMap.isProj_iff_idempotent

namespace IsProj

variable {p m}

/-- Restriction of the codomain of a projection of onto a subspace `p` to `p` instead of the whole
space.
-/
def codRestrict {f : M →ₗ[S] M} (h : IsProj m f) : M →ₗ[S] m :=
  f.codRestrict m h.map_mem
#align linear_map.is_proj.cod_restrict LinearMap.IsProj.codRestrict

@[simp]
theorem codRestrict_apply {f : M →ₗ[S] M} (h : IsProj m f) (x : M) : ↑(h.codRestrict x) = f x :=
  f.codRestrict_apply m x
#align linear_map.is_proj.cod_restrict_apply LinearMap.IsProj.codRestrict_apply

@[simp]
theorem codRestrict_apply_cod {f : M →ₗ[S] M} (h : IsProj m f) (x : m) : h.codRestrict x = x := by
  ext
  -- ⊢ ↑(↑(codRestrict h) ↑x) = ↑x
  rw [codRestrict_apply]
  -- ⊢ ↑f ↑x = ↑x
  exact h.map_id x x.2
  -- 🎉 no goals
#align linear_map.is_proj.cod_restrict_apply_cod LinearMap.IsProj.codRestrict_apply_cod

theorem codRestrict_ker {f : M →ₗ[S] M} (h : IsProj m f) : ker h.codRestrict = ker f :=
  f.ker_codRestrict m _
#align linear_map.is_proj.cod_restrict_ker LinearMap.IsProj.codRestrict_ker

theorem isCompl {f : E →ₗ[R] E} (h : IsProj p f) : IsCompl p (ker f) := by
  rw [← codRestrict_ker]
  exact isCompl_of_proj h.codRestrict_apply_cod
  -- 🎉 no goals
#align linear_map.is_proj.is_compl LinearMap.IsProj.isCompl

theorem eq_conj_prod_map' {f : E →ₗ[R] E} (h : IsProj p f) :
    f = (p.prodEquivOfIsCompl (ker f) h.isCompl).toLinearMap ∘ₗ
        prodMap id 0 ∘ₗ (p.prodEquivOfIsCompl (ker f) h.isCompl).symm.toLinearMap := by
  rw [← LinearMap.comp_assoc, LinearEquiv.eq_comp_toLinearMap_symm]
  -- ⊢ comp f ↑(prodEquivOfIsCompl p (ker f) (_ : IsCompl p (ker f))) = comp (↑(pro …
  ext x
  -- ⊢ ↑(comp (comp f ↑(prodEquivOfIsCompl p (ker f) (_ : IsCompl p (ker f)))) (inl …
  · simp only [coe_prodEquivOfIsCompl, comp_apply, coe_inl, coprod_apply, coeSubtype,
      _root_.map_zero, add_zero, h.map_id x x.2, prodMap_apply, id_apply]
  · simp only [coe_prodEquivOfIsCompl, comp_apply, coe_inr, coprod_apply, _root_.map_zero,
      coeSubtype, zero_add, map_coe_ker, prodMap_apply, zero_apply, add_zero]
#align linear_map.is_proj.eq_conj_prod_map' LinearMap.IsProj.eq_conj_prod_map'

end IsProj

end LinearMap

end Ring

section CommRing

namespace LinearMap

variable {R : Type*} [CommRing R] {E : Type*} [AddCommGroup E] [Module R E] {p : Submodule R E}

theorem IsProj.eq_conj_prodMap {f : E →ₗ[R] E} (h : IsProj p f) :
    f = (p.prodEquivOfIsCompl (ker f) h.isCompl).conj (prodMap id 0) := by
  rw [LinearEquiv.conj_apply]
  -- ⊢ f = comp (comp (↑(Submodule.prodEquivOfIsCompl p (ker f) (_ : IsCompl p (ker …
  exact h.eq_conj_prod_map'
  -- 🎉 no goals
#align linear_map.is_proj.eq_conj_prod_map LinearMap.IsProj.eq_conj_prodMap

end LinearMap

end CommRing
