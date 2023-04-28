/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz

! This file was ported from Lean 3 source module linear_algebra.projective_space.basic
! leanprover-community/mathlib commit c4658a649d216f57e99621708b09dcb3dcccbd23
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.FiniteDimensional

/-!

# Projective Spaces

This file contains the definition of the projectivization of a vector space over a field,
as well as the bijection between said projectivization and the collection of all one
dimensional subspaces of the vector space.

## Notation
`ℙ K V` is notation for `projectivization K V`, the projectivization of a `K`-vector space `V`.

## Constructing terms of `ℙ K V`.
We have three ways to construct terms of `ℙ K V`:
- `projectivization.mk K v hv` where `v : V` and `hv : v ≠ 0`.
- `projectivization.mk' K v` where `v : { w : V // w ≠ 0 }`.
- `projectivization.mk'' H h` where `H : submodule K V` and `h : finrank H = 1`.

## Other definitions
- For `v : ℙ K V`, `v.submodule` gives the corresponding submodule of `V`.
- `projectivization.equiv_submodule` is the equivalence between `ℙ K V`
  and `{ H : submodule K V // finrank H = 1 }`.
- For `v : ℙ K V`, `v.rep : V` is a representative of `v`.

-/


variable (K V : Type _) [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The setoid whose quotient is the projectivization of `V`. -/
def projectivizationSetoid : Setoid { v : V // v ≠ 0 } :=
  (MulAction.orbitRel Kˣ V).comap coe
#align projectivization_setoid projectivizationSetoid

/-- The projectivization of the `K`-vector space `V`.
The notation `ℙ K V` is preferred. -/
@[nolint has_nonempty_instance]
def Projectivization :=
  Quotient (projectivizationSetoid K V)
#align projectivization Projectivization

-- mathport name: exprℙ
notation "ℙ" => Projectivization

namespace Projectivization

variable {V}

/-- Construct an element of the projectivization from a nonzero vector. -/
def mk (v : V) (hv : v ≠ 0) : ℙ K V :=
  Quotient.mk'' ⟨v, hv⟩
#align projectivization.mk Projectivization.mk

/-- A variant of `projectivization.mk` in terms of a subtype. `mk` is preferred. -/
def mk' (v : { v : V // v ≠ 0 }) : ℙ K V :=
  Quotient.mk'' v
#align projectivization.mk' Projectivization.mk'

@[simp]
theorem mk'_eq_mk (v : { v : V // v ≠ 0 }) : mk' K v = mk K v v.2 :=
  by
  dsimp [mk, mk']
  congr 1
  simp
#align projectivization.mk'_eq_mk Projectivization.mk'_eq_mk

instance [Nontrivial V] : Nonempty (ℙ K V) :=
  let ⟨v, hv⟩ := exists_ne (0 : V)
  ⟨mk K v hv⟩

variable {K}

/-- Choose a representative of `v : projectivization K V` in `V`. -/
protected noncomputable def rep (v : ℙ K V) : V :=
  v.out'
#align projectivization.rep Projectivization.rep

theorem rep_nonzero (v : ℙ K V) : v.rep ≠ 0 :=
  v.out'.2
#align projectivization.rep_nonzero Projectivization.rep_nonzero

@[simp]
theorem mk_rep (v : ℙ K V) : mk K v.rep v.rep_nonzero = v :=
  by
  dsimp [mk, Projectivization.rep]
  simp
#align projectivization.mk_rep Projectivization.mk_rep

open FiniteDimensional

/-- Consider an element of the projectivization as a submodule of `V`. -/
protected def submodule (v : ℙ K V) : Submodule K V :=
  (Quotient.liftOn' v fun v => K ∙ (v : V)) <|
    by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨x, rfl : x • b = a⟩
    exact Submodule.span_singleton_group_smul_eq _ x _
#align projectivization.submodule Projectivization.submodule

variable (K)

theorem mk_eq_mk_iff (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    mk K v hv = mk K w hw ↔ ∃ a : Kˣ, a • w = v :=
  Quotient.eq''
#align projectivization.mk_eq_mk_iff Projectivization.mk_eq_mk_iff

/-- Two nonzero vectors go to the same point in projective space if and only if one is
a scalar multiple of the other. -/
theorem mk_eq_mk_iff' (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    mk K v hv = mk K w hw ↔ ∃ a : K, a • w = v :=
  by
  rw [mk_eq_mk_iff K v w hv hw]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    refine' ⟨Units.mk0 a fun c => hv.symm _, ha⟩
    rwa [c, zero_smul] at ha
#align projectivization.mk_eq_mk_iff' Projectivization.mk_eq_mk_iff'

theorem exists_smul_eq_mk_rep (v : V) (hv : v ≠ 0) : ∃ a : Kˣ, a • v = (mk K v hv).rep :=
  show (projectivizationSetoid K V).Rel _ _ from Quotient.mk_out' ⟨v, hv⟩
#align projectivization.exists_smul_eq_mk_rep Projectivization.exists_smul_eq_mk_rep

variable {K}

/-- An induction principle for `projectivization`.
Use as `induction v using projectivization.ind`. -/
@[elab_as_elim]
theorem ind {P : ℙ K V → Prop} (h : ∀ (v : V) (h : v ≠ 0), P (mk K v h)) : ∀ p, P p :=
  Quotient.ind' <| Subtype.rec <| h
#align projectivization.ind Projectivization.ind

@[simp]
theorem submodule_mk (v : V) (hv : v ≠ 0) : (mk K v hv).Submodule = K ∙ v :=
  rfl
#align projectivization.submodule_mk Projectivization.submodule_mk

theorem submodule_eq (v : ℙ K V) : v.Submodule = K ∙ v.rep :=
  by
  conv_lhs => rw [← v.mk_rep]
  rfl
#align projectivization.submodule_eq Projectivization.submodule_eq

theorem finrank_submodule (v : ℙ K V) : finrank K v.Submodule = 1 :=
  by
  rw [submodule_eq]
  exact finrank_span_singleton v.rep_nonzero
#align projectivization.finrank_submodule Projectivization.finrank_submodule

instance (v : ℙ K V) : FiniteDimensional K v.Submodule :=
  by
  rw [← v.mk_rep]
  change FiniteDimensional K (K ∙ v.rep)
  infer_instance

theorem submodule_injective :
    Function.Injective (Projectivization.submodule : ℙ K V → Submodule K V) :=
  by
  intro u v h; replace h := le_of_eq h
  simp only [submodule_eq] at h
  rw [Submodule.le_span_singleton_iff] at h
  rw [← mk_rep v, ← mk_rep u]
  apply Quotient.sound'
  obtain ⟨a, ha⟩ := h u.rep (Submodule.mem_span_singleton_self _)
  have : a ≠ 0 := fun c => u.rep_nonzero (by simpa [c] using ha.symm)
  use Units.mk0 a this, ha
#align projectivization.submodule_injective Projectivization.submodule_injective

variable (K V)

/-- The equivalence between the projectivization and the
collection of subspaces of dimension 1. -/
noncomputable def equivSubmodule : ℙ K V ≃ { H : Submodule K V // finrank K H = 1 } :=
  Equiv.ofBijective (fun v => ⟨v.Submodule, v.finrank_submodule⟩)
    (by
      constructor
      · intro u v h
        apply_fun fun e => e.val  at h
        apply submodule_injective h
      · rintro ⟨H, h⟩
        rw [finrank_eq_one_iff'] at h
        obtain ⟨v, hv, h⟩ := h
        have : (v : V) ≠ 0 := fun c => hv (Subtype.coe_injective c)
        use mk K v this
        symm
        ext x
        revert x
        erw [← Set.ext_iff]
        ext x
        dsimp [-SetLike.mem_coe]
        rw [Submodule.span_singleton_eq_range]
        refine' ⟨fun hh => _, _⟩
        · obtain ⟨c, hc⟩ := h ⟨x, hh⟩
          exact ⟨c, congr_arg coe hc⟩
        · rintro ⟨c, rfl⟩
          refine' Submodule.smul_mem _ _ v.2)
#align projectivization.equiv_submodule Projectivization.equivSubmodule

variable {K V}

/-- Construct an element of the projectivization from a subspace of dimension 1. -/
noncomputable def mk'' (H : Submodule K V) (h : finrank K H = 1) : ℙ K V :=
  (equivSubmodule K V).symm ⟨H, h⟩
#align projectivization.mk'' Projectivization.mk''

@[simp]
theorem submodule_mk'' (H : Submodule K V) (h : finrank K H = 1) : (mk'' H h).Submodule = H :=
  by
  suffices (equiv_submodule K V) (mk'' H h) = ⟨H, h⟩ by exact congr_arg coe this
  dsimp [mk'']
  simp
#align projectivization.submodule_mk'' Projectivization.submodule_mk''

@[simp]
theorem mk''_submodule (v : ℙ K V) : mk'' v.Submodule v.finrank_submodule = v :=
  show (equivSubmodule K V).symm (equivSubmodule K V _) = _ by simp
#align projectivization.mk''_submodule Projectivization.mk''_submodule

section Map

variable {L W : Type _} [DivisionRing L] [AddCommGroup W] [Module L W]

/-- An injective semilinear map of vector spaces induces a map on projective spaces. -/
def map {σ : K →+* L} (f : V →ₛₗ[σ] W) (hf : Function.Injective f) : ℙ K V → ℙ L W :=
  Quotient.map' (fun v => ⟨f v, fun c => v.2 (hf (by simp [c]))⟩)
    (by
      rintro ⟨u, hu⟩ ⟨v, hv⟩ ⟨a, ha⟩
      use Units.map σ.to_monoid_hom a
      dsimp at ha⊢
      erw [← f.map_smulₛₗ, ha])
#align projectivization.map Projectivization.map

/-- Mapping with respect to a semilinear map over an isomorphism of fields yields
an injective map on projective spaces. -/
theorem map_injective {σ : K →+* L} {τ : L →+* K} [RingHomInvPair σ τ] (f : V →ₛₗ[σ] W)
    (hf : Function.Injective f) : Function.Injective (map f hf) :=
  by
  intro u v h
  rw [← u.mk_rep, ← v.mk_rep] at *
  apply Quotient.sound'
  dsimp [map, mk] at h
  simp only [Quotient.eq''] at h
  obtain ⟨a, ha⟩ := h
  use Units.map τ.to_monoid_hom a
  dsimp at ha⊢
  have : (a : L) = σ (τ a) := by rw [RingHomInvPair.comp_apply_eq₂]
  change (a : L) • f v.rep = f u.rep at ha
  rw [this, ← f.map_smulₛₗ] at ha
  exact hf ha
#align projectivization.map_injective Projectivization.map_injective

@[simp]
theorem map_id : map (LinearMap.id : V →ₗ[K] V) (LinearEquiv.refl K V).Injective = id :=
  by
  ext v
  induction v using Projectivization.ind
  rfl
#align projectivization.map_id Projectivization.map_id

@[simp]
theorem map_comp {F U : Type _} [Field F] [AddCommGroup U] [Module F U] {σ : K →+* L} {τ : L →+* F}
    {γ : K →+* F} [RingHomCompTriple σ τ γ] (f : V →ₛₗ[σ] W) (hf : Function.Injective f)
    (g : W →ₛₗ[τ] U) (hg : Function.Injective g) :
    map (g.comp f) (hg.comp hf) = map g hg ∘ map f hf :=
  by
  ext v
  induction v using Projectivization.ind
  rfl
#align projectivization.map_comp Projectivization.map_comp

end Map

end Projectivization

