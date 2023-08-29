/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.LinearAlgebra.FiniteDimensional

#align_import linear_algebra.projective_space.basic from "leanprover-community/mathlib"@"c4658a649d216f57e99621708b09dcb3dcccbd23"

/-!

# Projective Spaces

This file contains the definition of the projectivization of a vector space over a field,
as well as the bijection between said projectivization and the collection of all one
dimensional subspaces of the vector space.

## Notation
`ℙ K V` is notation for `Projectivization K V`, the projectivization of a `K`-vector space `V`.

## Constructing terms of `ℙ K V`.
We have three ways to construct terms of `ℙ K V`:
- `Projectivization.mk K v hv` where `v : V` and `hv : v ≠ 0`.
- `Projectivization.mk' K v` where `v : { w : V // w ≠ 0 }`.
- `Projectivization.mk'' H h` where `H : Submodule K V` and `h : finrank H = 1`.

## Other definitions
- For `v : ℙ K V`, `v.submodule` gives the corresponding submodule of `V`.
- `Projectivization.equivSubmodule` is the equivalence between `ℙ K V`
  and `{ H : Submodule K V // finrank H = 1 }`.
- For `v : ℙ K V`, `v.rep : V` is a representative of `v`.

-/


variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The setoid whose quotient is the projectivization of `V`. -/
def projectivizationSetoid : Setoid { v : V // v ≠ 0 } :=
  (MulAction.orbitRel Kˣ V).comap (↑)
#align projectivization_setoid projectivizationSetoid

/-- The projectivization of the `K`-vector space `V`.
The notation `ℙ K V` is preferred. -/
def Projectivization := Quotient (projectivizationSetoid K V)
#align projectivization Projectivization

notation "ℙ" => Projectivization

namespace Projectivization

variable {V}

/-- Construct an element of the projectivization from a nonzero vector. -/
def mk (v : V) (hv : v ≠ 0) : ℙ K V :=
  Quotient.mk'' ⟨v, hv⟩
#align projectivization.mk Projectivization.mk

/-- A variant of `Projectivization.mk` in terms of a subtype. `mk` is preferred. -/
def mk' (v : { v : V // v ≠ 0 }) : ℙ K V :=
  Quotient.mk'' v
#align projectivization.mk' Projectivization.mk'

@[simp]
theorem mk'_eq_mk (v : { v : V // v ≠ 0 }) : mk' K v = mk K ↑v v.2 := rfl
#align projectivization.mk'_eq_mk Projectivization.mk'_eq_mk

instance [Nontrivial V] : Nonempty (ℙ K V) :=
  let ⟨v, hv⟩ := exists_ne (0 : V)
  ⟨mk K v hv⟩

variable {K}

/-- Choose a representative of `v : Projectivization K V` in `V`. -/
protected noncomputable def rep (v : ℙ K V) : V :=
  v.out'
#align projectivization.rep Projectivization.rep

theorem rep_nonzero (v : ℙ K V) : v.rep ≠ 0 :=
  v.out'.2
#align projectivization.rep_nonzero Projectivization.rep_nonzero

@[simp]
theorem mk_rep (v : ℙ K V) : mk K v.rep v.rep_nonzero = v := Quotient.out_eq' _
#align projectivization.mk_rep Projectivization.mk_rep

open FiniteDimensional

/-- Consider an element of the projectivization as a submodule of `V`. -/
protected def submodule (v : ℙ K V) : Submodule K V :=
  (Quotient.liftOn' v fun v => K ∙ (v : V)) <| by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨x, rfl : x • b = a⟩
    -- ⊢ Submodule.span K {↑{ val := x • b, property := ha }} = Submodule.span K {↑{  …
    exact Submodule.span_singleton_group_smul_eq _ x _
    -- 🎉 no goals
#align projectivization.submodule Projectivization.submodule

variable (K)

theorem mk_eq_mk_iff (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    mk K v hv = mk K w hw ↔ ∃ a : Kˣ, a • w = v :=
  Quotient.eq''
#align projectivization.mk_eq_mk_iff Projectivization.mk_eq_mk_iff

/-- Two nonzero vectors go to the same point in projective space if and only if one is
a scalar multiple of the other. -/
theorem mk_eq_mk_iff' (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    mk K v hv = mk K w hw ↔ ∃ a : K, a • w = v := by
  rw [mk_eq_mk_iff K v w hv hw]
  -- ⊢ (∃ a, a • w = v) ↔ ∃ a, a • w = v
  constructor
  -- ⊢ (∃ a, a • w = v) → ∃ a, a • w = v
  · rintro ⟨a, ha⟩
    -- ⊢ ∃ a, a • w = v
    exact ⟨a, ha⟩
    -- 🎉 no goals
  · rintro ⟨a, ha⟩
    -- ⊢ ∃ a, a • w = v
    refine' ⟨Units.mk0 a fun c => hv.symm _, ha⟩
    -- ⊢ 0 = v
    rwa [c, zero_smul] at ha
    -- 🎉 no goals
#align projectivization.mk_eq_mk_iff' Projectivization.mk_eq_mk_iff'

theorem exists_smul_eq_mk_rep (v : V) (hv : v ≠ 0) : ∃ a : Kˣ, a • v = (mk K v hv).rep :=
  (mk_eq_mk_iff K _ _ (rep_nonzero _) hv).1 (mk_rep _)
#align projectivization.exists_smul_eq_mk_rep Projectivization.exists_smul_eq_mk_rep

variable {K}

/-- An induction principle for `Projectivization`.
Use as `induction v using Projectivization.ind`. -/
@[elab_as_elim]
theorem ind {P : ℙ K V → Prop} (h : ∀ (v : V) (h : v ≠ 0), P (mk K v h)) : ∀ p, P p :=
  Quotient.ind' <| Subtype.rec <| h
#align projectivization.ind Projectivization.ind

@[simp]
theorem submodule_mk (v : V) (hv : v ≠ 0) : (mk K v hv).submodule = K ∙ v :=
  rfl
#align projectivization.submodule_mk Projectivization.submodule_mk

theorem submodule_eq (v : ℙ K V) : v.submodule = K ∙ v.rep := by
  conv_lhs => rw [← v.mk_rep]
  -- 🎉 no goals
#align projectivization.submodule_eq Projectivization.submodule_eq

theorem finrank_submodule (v : ℙ K V) : finrank K v.submodule = 1 := by
  rw [submodule_eq]
  -- ⊢ finrank K { x // x ∈ Submodule.span K {Projectivization.rep v} } = 1
  exact finrank_span_singleton v.rep_nonzero
  -- 🎉 no goals
#align projectivization.finrank_submodule Projectivization.finrank_submodule

instance (v : ℙ K V) : FiniteDimensional K v.submodule := by
  rw [← v.mk_rep]
  -- ⊢ FiniteDimensional K { x // x ∈ Projectivization.submodule (mk K (Projectiviz …
  change FiniteDimensional K (K ∙ v.rep)
  -- ⊢ FiniteDimensional K { x // x ∈ Submodule.span K {Projectivization.rep v} }
  infer_instance
  -- 🎉 no goals

theorem submodule_injective :
    Function.Injective (Projectivization.submodule : ℙ K V → Submodule K V) := fun u v h ↦ by
  induction' u using ind with u hu
  -- ⊢ mk K u hu = v
  induction' v using ind with v hv
  -- ⊢ mk K u hu = mk K v hv
  rw [submodule_mk, submodule_mk, Submodule.span_singleton_eq_span_singleton] at h
  -- ⊢ mk K u hu = mk K v hv
  exact ((mk_eq_mk_iff K v u hv hu).2 h).symm
  -- 🎉 no goals
#align projectivization.submodule_injective Projectivization.submodule_injective

variable (K V)

/-- The equivalence between the projectivization and the
collection of subspaces of dimension 1. -/
noncomputable def equivSubmodule : ℙ K V ≃ { H : Submodule K V // finrank K H = 1 } :=
  (Equiv.ofInjective _ submodule_injective).trans <| .subtypeEquiv (.refl _) fun H ↦ by
    refine ⟨fun ⟨v, hv⟩ ↦ hv ▸ v.finrank_submodule, fun h ↦ ?_⟩
    -- ⊢ H ∈ Set.range Projectivization.submodule
    rcases finrank_eq_one_iff'.1 h with ⟨v : H, hv₀, hv : ∀ w : H, _⟩
    -- ⊢ H ∈ Set.range Projectivization.submodule
    use mk K (v : V) (Subtype.coe_injective.ne hv₀)
    -- ⊢ Projectivization.submodule (mk K ↑v (_ : ↑v ≠ ↑0)) = H
    rw [submodule_mk, SetLike.ext'_iff, Submodule.span_singleton_eq_range]
    -- ⊢ (Set.range fun x => x • ↑v) = ↑H
    refine (Set.range_subset_iff.2 fun _ ↦ H.smul_mem _ v.2).antisymm fun x hx ↦ ?_
    -- ⊢ x ∈ Set.range fun x => x • ↑v
    rcases hv ⟨x, hx⟩ with ⟨c, hc⟩
    -- ⊢ x ∈ Set.range fun x => x • ↑v
    exact ⟨c, congr_arg Subtype.val hc⟩
    -- 🎉 no goals
#align projectivization.equiv_submodule Projectivization.equivSubmodule

variable {K V}

/-- Construct an element of the projectivization from a subspace of dimension 1. -/
noncomputable def mk'' (H : Submodule K V) (h : finrank K H = 1) : ℙ K V :=
  (equivSubmodule K V).symm ⟨H, h⟩
#align projectivization.mk'' Projectivization.mk''

@[simp]
theorem submodule_mk'' (H : Submodule K V) (h : finrank K H = 1) : (mk'' H h).submodule = H :=
  congr_arg Subtype.val <| (equivSubmodule K V).apply_symm_apply ⟨H, h⟩
#align projectivization.submodule_mk'' Projectivization.submodule_mk''

@[simp]
theorem mk''_submodule (v : ℙ K V) : mk'' v.submodule v.finrank_submodule = v :=
  (equivSubmodule K V).symm_apply_apply v
#align projectivization.mk''_submodule Projectivization.mk''_submodule

section Map

variable {L W : Type*} [DivisionRing L] [AddCommGroup W] [Module L W]

/-- An injective semilinear map of vector spaces induces a map on projective spaces. -/
def map {σ : K →+* L} (f : V →ₛₗ[σ] W) (hf : Function.Injective f) : ℙ K V → ℙ L W :=
  Quotient.map' (fun v => ⟨f v, fun c => v.2 (hf (by simp [c]))⟩)
                                                     -- 🎉 no goals
    (by
      rintro ⟨u, hu⟩ ⟨v, hv⟩ ⟨a, ha⟩
      -- ⊢ Setoid.r ((fun v => { val := ↑f ↑v, property := (_ : ↑f ↑v = 0 → False) }) { …
      use Units.map σ.toMonoidHom a
      -- ⊢ (fun m => m • ↑((fun v => { val := ↑f ↑v, property := (_ : ↑f ↑v = 0 → False …
      dsimp at ha ⊢
      -- ⊢ ↑(Units.map ↑σ) a • ↑f v = ↑f u
      erw [← f.map_smulₛₗ, ha])
      -- 🎉 no goals
#align projectivization.map Projectivization.map

theorem map_mk {σ : K →+* L} (f : V →ₛₗ[σ] W) (hf : Function.Injective f) (v : V) (hv : v ≠ 0) :
    map f hf (mk K v hv) = mk L (f v) (map_zero f ▸ hf.ne hv) :=
  rfl

/-- Mapping with respect to a semilinear map over an isomorphism of fields yields
an injective map on projective spaces. -/
theorem map_injective {σ : K →+* L} {τ : L →+* K} [RingHomInvPair σ τ] (f : V →ₛₗ[σ] W)
    (hf : Function.Injective f) : Function.Injective (map f hf) := fun u v h ↦ by
  induction' u using ind with u hu; induction' v using ind with v hv
  -- ⊢ mk K u hu = v
                                    -- ⊢ mk K u hu = mk K v hv
  simp only [map_mk, mk_eq_mk_iff'] at h ⊢
  -- ⊢ ∃ a, a • v = u
  rcases h with ⟨a, ha⟩
  -- ⊢ ∃ a, a • v = u
  refine ⟨τ a, hf ?_⟩
  -- ⊢ ↑f (↑τ a • v) = ↑f u
  rwa [f.map_smulₛₗ, RingHomInvPair.comp_apply_eq₂]
  -- 🎉 no goals
#align projectivization.map_injective Projectivization.map_injective

@[simp]
theorem map_id : map (LinearMap.id : V →ₗ[K] V) (LinearEquiv.refl K V).injective = id := by
  ext ⟨v⟩
  -- ⊢ map LinearMap.id (_ : Function.Injective ↑(LinearEquiv.refl K V)) (Quot.mk S …
  rfl
  -- 🎉 no goals
#align projectivization.map_id Projectivization.map_id

-- porting note: removed `@[simp]` because of unusable `hg.comp hf` in the LHS
theorem map_comp {F U : Type*} [Field F] [AddCommGroup U] [Module F U] {σ : K →+* L} {τ : L →+* F}
    {γ : K →+* F} [RingHomCompTriple σ τ γ] (f : V →ₛₗ[σ] W) (hf : Function.Injective f)
    (g : W →ₛₗ[τ] U) (hg : Function.Injective g) :
    map (g.comp f) (hg.comp hf) = map g hg ∘ map f hf := by
  ext ⟨v⟩
  -- ⊢ map (LinearMap.comp g f) (_ : Function.Injective (↑g ∘ fun x => ↑f x)) (Quot …
  rfl
  -- 🎉 no goals
#align projectivization.map_comp Projectivization.map_comp

end Map

end Projectivization
