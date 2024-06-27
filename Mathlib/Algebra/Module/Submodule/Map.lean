/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/

import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.LinearMap

/-!
# `map` and `comap` for `Submodule`s

## Main declarations

* `Submodule.map`: The pushforward of a submodule `p ⊆ M` by `f : M → M₂`
* `Submodule.comap`: The pullback of a submodule `p ⊆ M₂` along `f : M → M₂`
* `Submodule.giMapComap`: `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective.
* `Submodule.gciMapComap`: `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective.

## Tags

submodule, subspace, linear map, pushforward, pullback
-/

open Function Pointwise Set

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

namespace Submodule

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable (p p' : Submodule R M) (q q' : Submodule R₂ M₂)
variable {x : M}

section

variable [RingHomSurjective σ₁₂] {F : Type*} [FunLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂]

/-- The pushforward of a submodule `p ⊆ M` by `f : M → M₂` -/
def map (f : F) (p : Submodule R M) : Submodule R₂ M₂ :=
  { p.toAddSubmonoid.map f with
    carrier := f '' p
    smul_mem' := by
      rintro c x ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := σ₁₂.surjective c
      exact ⟨_, p.smul_mem a hy, map_smulₛₗ f _ _⟩ }
#align submodule.map Submodule.map

@[simp]
theorem map_coe (f : F) (p : Submodule R M) : (map f p : Set M₂) = f '' p :=
  rfl
#align submodule.map_coe Submodule.map_coe

theorem map_toAddSubmonoid (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    (p.map f).toAddSubmonoid = p.toAddSubmonoid.map (f : M →+ M₂) :=
  SetLike.coe_injective rfl
#align submodule.map_to_add_submonoid Submodule.map_toAddSubmonoid

theorem map_toAddSubmonoid' (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    (p.map f).toAddSubmonoid = p.toAddSubmonoid.map f :=
  SetLike.coe_injective rfl
#align submodule.map_to_add_submonoid' Submodule.map_toAddSubmonoid'

@[simp]
theorem _root_.AddMonoidHom.coe_toIntLinearMap_map {A A₂ : Type*} [AddCommGroup A] [AddCommGroup A₂]
    (f : A →+ A₂) (s : AddSubgroup A) :
    (AddSubgroup.toIntSubmodule s).map f.toIntLinearMap =
      AddSubgroup.toIntSubmodule (s.map f) := rfl

@[simp]
theorem _root_.MonoidHom.coe_toAdditive_map {G G₂ : Type*} [Group G] [Group G₂] (f : G →* G₂)
    (s : Subgroup G) :
    s.toAddSubgroup.map (MonoidHom.toAdditive f) = Subgroup.toAddSubgroup (s.map f) := rfl

@[simp]
theorem _root_.AddMonoidHom.coe_toMultiplicative_map {G G₂ : Type*} [AddGroup G] [AddGroup G₂]
    (f : G →+ G₂) (s : AddSubgroup G) :
    s.toSubgroup.map (AddMonoidHom.toMultiplicative f) = AddSubgroup.toSubgroup (s.map f) := rfl

@[simp]
theorem mem_map {f : F} {p : Submodule R M} {x : M₂} : x ∈ map f p ↔ ∃ y, y ∈ p ∧ f y = x :=
  Iff.rfl
#align submodule.mem_map Submodule.mem_map

theorem mem_map_of_mem {f : F} {p : Submodule R M} {r} (h : r ∈ p) : f r ∈ map f p :=
  Set.mem_image_of_mem _ h
#align submodule.mem_map_of_mem Submodule.mem_map_of_mem

theorem apply_coe_mem_map (f : F) {p : Submodule R M} (r : p) : f r ∈ map f p :=
  mem_map_of_mem r.prop
#align submodule.apply_coe_mem_map Submodule.apply_coe_mem_map

@[simp]
theorem map_id : map (LinearMap.id : M →ₗ[R] M) p = p :=
  Submodule.ext fun a => by simp
#align submodule.map_id Submodule.map_id

theorem map_comp [RingHomSurjective σ₂₃] [RingHomSurjective σ₁₃] (f : M →ₛₗ[σ₁₂] M₂)
    (g : M₂ →ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.comp f : M →ₛₗ[σ₁₃] M₃) p = map g (map f p) :=
  SetLike.coe_injective <| by simp only [← image_comp, map_coe, LinearMap.coe_comp, comp_apply]
#align submodule.map_comp Submodule.map_comp

theorem map_mono {f : F} {p p' : Submodule R M} : p ≤ p' → map f p ≤ map f p' :=
  image_subset _
#align submodule.map_mono Submodule.map_mono

@[simp]
theorem map_zero : map (0 : M →ₛₗ[σ₁₂] M₂) p = ⊥ :=
  have : ∃ x : M, x ∈ p := ⟨0, p.zero_mem⟩
  ext <| by simp [this, eq_comm]
#align submodule.map_zero Submodule.map_zero

theorem map_add_le (f g : M →ₛₗ[σ₁₂] M₂) : map (f + g) p ≤ map f p ⊔ map g p := by
  rintro x ⟨m, hm, rfl⟩
  exact add_mem_sup (mem_map_of_mem hm) (mem_map_of_mem hm)
#align submodule.map_add_le Submodule.map_add_le

theorem map_inf_le (f : F) {p q : Submodule R M} :
    (p ⊓ q).map f ≤ p.map f ⊓ q.map f :=
  image_inter_subset f p q

theorem map_inf (f : F) {p q : Submodule R M} (hf : Injective f) :
    (p ⊓ q).map f = p.map f ⊓ q.map f :=
  SetLike.coe_injective <| Set.image_inter hf

theorem range_map_nonempty (N : Submodule R M) :
    (Set.range (fun ϕ => Submodule.map ϕ N : (M →ₛₗ[σ₁₂] M₂) → Submodule R₂ M₂)).Nonempty :=
  ⟨_, Set.mem_range.mpr ⟨0, rfl⟩⟩
#align submodule.range_map_nonempty Submodule.range_map_nonempty

end

section SemilinearMap

variable {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂]

/-- The pushforward of a submodule by an injective linear map is
linearly equivalent to the original submodule. See also `LinearEquiv.submoduleMap` for a
computable version when `f` has an explicit inverse. -/
noncomputable def equivMapOfInjective (f : F) (i : Injective f) (p : Submodule R M) :
    p ≃ₛₗ[σ₁₂] p.map f :=
  { Equiv.Set.image f p i with
    map_add' := by
      intros
      simp only [coe_add, map_add, Equiv.toFun_as_coe, Equiv.Set.image_apply]
      rfl
    map_smul' := by
      intros
      -- Note: #8386 changed `map_smulₛₗ` into `map_smulₛₗ _`
      simp only [coe_smul_of_tower, map_smulₛₗ _, Equiv.toFun_as_coe, Equiv.Set.image_apply]
      rfl }
#align submodule.equiv_map_of_injective Submodule.equivMapOfInjective

@[simp]
theorem coe_equivMapOfInjective_apply (f : F) (i : Injective f) (p : Submodule R M) (x : p) :
    (equivMapOfInjective f i p x : M₂) = f x :=
  rfl
#align submodule.coe_equiv_map_of_injective_apply Submodule.coe_equivMapOfInjective_apply

@[simp]
theorem map_equivMapOfInjective_symm_apply (f : F) (i : Injective f) (p : Submodule R M)
    (x : p.map f) : f ((equivMapOfInjective f i p).symm x) = x := by
  rw [← LinearEquiv.apply_symm_apply (equivMapOfInjective f i p) x, coe_equivMapOfInjective_apply,
    i.eq_iff, LinearEquiv.apply_symm_apply]

/-- The pullback of a submodule `p ⊆ M₂` along `f : M → M₂` -/
def comap (f : F) (p : Submodule R₂ M₂) : Submodule R M :=
  { p.toAddSubmonoid.comap f with
    carrier := f ⁻¹' p
    -- Note: #8386 added `map_smulₛₗ _`
    smul_mem' := fun a x h => by simp [p.smul_mem (σ₁₂ a) h, map_smulₛₗ _] }
#align submodule.comap Submodule.comap

@[simp]
theorem comap_coe (f : F) (p : Submodule R₂ M₂) : (comap f p : Set M) = f ⁻¹' p :=
  rfl
#align submodule.comap_coe Submodule.comap_coe

@[simp]
theorem AddMonoidHom.coe_toIntLinearMap_comap {A A₂ : Type*} [AddCommGroup A] [AddCommGroup A₂]
    (f : A →+ A₂) (s : AddSubgroup A₂) :
    (AddSubgroup.toIntSubmodule s).comap f.toIntLinearMap =
      AddSubgroup.toIntSubmodule (s.comap f) := rfl

@[simp]
theorem mem_comap {f : F} {p : Submodule R₂ M₂} : x ∈ comap f p ↔ f x ∈ p :=
  Iff.rfl
#align submodule.mem_comap Submodule.mem_comap

@[simp]
theorem comap_id : comap (LinearMap.id : M →ₗ[R] M) p = p :=
  SetLike.coe_injective rfl
#align submodule.comap_id Submodule.comap_id

theorem comap_comp (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃) (p : Submodule R₃ M₃) :
    comap (g.comp f : M →ₛₗ[σ₁₃] M₃) p = comap f (comap g p) :=
  rfl
#align submodule.comap_comp Submodule.comap_comp

theorem comap_mono {f : F} {q q' : Submodule R₂ M₂} : q ≤ q' → comap f q ≤ comap f q' :=
  preimage_mono
#align submodule.comap_mono Submodule.comap_mono

theorem le_comap_pow_of_le_comap (p : Submodule R M) {f : M →ₗ[R] M} (h : p ≤ p.comap f) (k : ℕ) :
    p ≤ p.comap (f ^ k) := by
  induction' k with k ih
  · simp [LinearMap.one_eq_id]
  · simp [LinearMap.iterate_succ, comap_comp, h.trans (comap_mono ih)]
#align submodule.le_comap_pow_of_le_comap Submodule.le_comap_pow_of_le_comap

section

variable [RingHomSurjective σ₁₂]

theorem map_le_iff_le_comap {f : F} {p : Submodule R M} {q : Submodule R₂ M₂} :
    map f p ≤ q ↔ p ≤ comap f q :=
  image_subset_iff
#align submodule.map_le_iff_le_comap Submodule.map_le_iff_le_comap

theorem gc_map_comap (f : F) : GaloisConnection (map f) (comap f)
  | _, _ => map_le_iff_le_comap
#align submodule.gc_map_comap Submodule.gc_map_comap

@[simp]
theorem map_bot (f : F) : map f ⊥ = ⊥ :=
  (gc_map_comap f).l_bot
#align submodule.map_bot Submodule.map_bot

@[simp]
theorem map_sup (f : F) : map f (p ⊔ p') = map f p ⊔ map f p' :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup
#align submodule.map_sup Submodule.map_sup

@[simp]
theorem map_iSup {ι : Sort*} (f : F) (p : ι → Submodule R M) :
    map f (⨆ i, p i) = ⨆ i, map f (p i) :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup
#align submodule.map_supr Submodule.map_iSup

end

@[simp]
theorem comap_top (f : F) : comap f ⊤ = ⊤ :=
  rfl
#align submodule.comap_top Submodule.comap_top

@[simp]
theorem comap_inf (f : F) : comap f (q ⊓ q') = comap f q ⊓ comap f q' :=
  rfl
#align submodule.comap_inf Submodule.comap_inf

@[simp]
theorem comap_iInf [RingHomSurjective σ₁₂] {ι : Sort*} (f : F) (p : ι → Submodule R₂ M₂) :
    comap f (⨅ i, p i) = ⨅ i, comap f (p i) :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_iInf
#align submodule.comap_infi Submodule.comap_iInf

@[simp]
theorem comap_zero : comap (0 : M →ₛₗ[σ₁₂] M₂) q = ⊤ :=
  ext <| by simp
#align submodule.comap_zero Submodule.comap_zero

theorem map_comap_le [RingHomSurjective σ₁₂] (f : F) (q : Submodule R₂ M₂) :
    map f (comap f q) ≤ q :=
  (gc_map_comap f).l_u_le _
#align submodule.map_comap_le Submodule.map_comap_le

theorem le_comap_map [RingHomSurjective σ₁₂] (f : F) (p : Submodule R M) : p ≤ comap f (map f p) :=
  (gc_map_comap f).le_u_l _
#align submodule.le_comap_map Submodule.le_comap_map

section GaloisInsertion

variable {f : F} (hf : Surjective f)
variable [RingHomSurjective σ₁₂]

/-- `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective. -/
def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x hx => by
    rcases hf x with ⟨y, rfl⟩
    simp only [mem_map, mem_comap]
    exact ⟨y, hx, rfl⟩
#align submodule.gi_map_comap Submodule.giMapComap

theorem map_comap_eq_of_surjective (p : Submodule R₂ M₂) : (p.comap f).map f = p :=
  (giMapComap hf).l_u_eq _
#align submodule.map_comap_eq_of_surjective Submodule.map_comap_eq_of_surjective

theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective
#align submodule.map_surjective_of_surjective Submodule.map_surjective_of_surjective

theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective
#align submodule.comap_injective_of_surjective Submodule.comap_injective_of_surjective

theorem map_sup_comap_of_surjective (p q : Submodule R₂ M₂) :
    (p.comap f ⊔ q.comap f).map f = p ⊔ q :=
  (giMapComap hf).l_sup_u _ _
#align submodule.map_sup_comap_of_surjective Submodule.map_sup_comap_of_surjective

theorem map_iSup_comap_of_sujective {ι : Sort*} (S : ι → Submodule R₂ M₂) :
    (⨆ i, (S i).comap f).map f = iSup S :=
  (giMapComap hf).l_iSup_u _
#align submodule.map_supr_comap_of_sujective Submodule.map_iSup_comap_of_sujective

theorem map_inf_comap_of_surjective (p q : Submodule R₂ M₂) :
    (p.comap f ⊓ q.comap f).map f = p ⊓ q :=
  (giMapComap hf).l_inf_u _ _
#align submodule.map_inf_comap_of_surjective Submodule.map_inf_comap_of_surjective

theorem map_iInf_comap_of_surjective {ι : Sort*} (S : ι → Submodule R₂ M₂) :
    (⨅ i, (S i).comap f).map f = iInf S :=
  (giMapComap hf).l_iInf_u _
#align submodule.map_infi_comap_of_surjective Submodule.map_iInf_comap_of_surjective

theorem comap_le_comap_iff_of_surjective (p q : Submodule R₂ M₂) : p.comap f ≤ q.comap f ↔ p ≤ q :=
  (giMapComap hf).u_le_u_iff
#align submodule.comap_le_comap_iff_of_surjective Submodule.comap_le_comap_iff_of_surjective

theorem comap_strictMono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strictMono_u
#align submodule.comap_strict_mono_of_surjective Submodule.comap_strictMono_of_surjective

end GaloisInsertion

section GaloisCoinsertion

variable [RingHomSurjective σ₁₂] {f : F} (hf : Injective f)

/-- `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective. -/
def gciMapComap : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by
    simp [mem_comap, mem_map, forall_exists_index, and_imp]
    intro y hy hxy
    rw [hf.eq_iff] at hxy
    rwa [← hxy]
#align submodule.gci_map_comap Submodule.gciMapComap

theorem comap_map_eq_of_injective (p : Submodule R M) : (p.map f).comap f = p :=
  (gciMapComap hf).u_l_eq _
#align submodule.comap_map_eq_of_injective Submodule.comap_map_eq_of_injective

theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective
#align submodule.comap_surjective_of_injective Submodule.comap_surjective_of_injective

theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective
#align submodule.map_injective_of_injective Submodule.map_injective_of_injective

theorem comap_inf_map_of_injective (p q : Submodule R M) : (p.map f ⊓ q.map f).comap f = p ⊓ q :=
  (gciMapComap hf).u_inf_l _ _
#align submodule.comap_inf_map_of_injective Submodule.comap_inf_map_of_injective

theorem comap_iInf_map_of_injective {ι : Sort*} (S : ι → Submodule R M) :
    (⨅ i, (S i).map f).comap f = iInf S :=
  (gciMapComap hf).u_iInf_l _
#align submodule.comap_infi_map_of_injective Submodule.comap_iInf_map_of_injective

theorem comap_sup_map_of_injective (p q : Submodule R M) : (p.map f ⊔ q.map f).comap f = p ⊔ q :=
  (gciMapComap hf).u_sup_l _ _
#align submodule.comap_sup_map_of_injective Submodule.comap_sup_map_of_injective

theorem comap_iSup_map_of_injective {ι : Sort*} (S : ι → Submodule R M) :
    (⨆ i, (S i).map f).comap f = iSup S :=
  (gciMapComap hf).u_iSup_l _
#align submodule.comap_supr_map_of_injective Submodule.comap_iSup_map_of_injective

theorem map_le_map_iff_of_injective (p q : Submodule R M) : p.map f ≤ q.map f ↔ p ≤ q :=
  (gciMapComap hf).l_le_l_iff
#align submodule.map_le_map_iff_of_injective Submodule.map_le_map_iff_of_injective

theorem map_strictMono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strictMono_l
#align submodule.map_strict_mono_of_injective Submodule.map_strictMono_of_injective

end GaloisCoinsertion

end SemilinearMap

section OrderIso

variable [RingHomSurjective σ₁₂] {F : Type*}

/-- A linear isomorphism induces an order isomorphism of submodules. -/
@[simps symm_apply apply]
def orderIsoMapComapOfBijective [FunLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂]
    (f : F) (hf : Bijective f) : Submodule R M ≃o Submodule R₂ M₂ where
  toFun := map f
  invFun := comap f
  left_inv := comap_map_eq_of_injective hf.injective
  right_inv := map_comap_eq_of_surjective hf.surjective
  map_rel_iff' := map_le_map_iff_of_injective hf.injective _ _

/-- A linear isomorphism induces an order isomorphism of submodules. -/
@[simps! symm_apply apply]
def orderIsoMapComap [EquivLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂] (f : F) :
    Submodule R M ≃o Submodule R₂ M₂ := orderIsoMapComapOfBijective f (EquivLike.bijective f)
#align submodule.order_iso_map_comap Submodule.orderIsoMapComap

end OrderIso

variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂]

--TODO(Mario): is there a way to prove this from order properties?
theorem map_inf_eq_map_inf_comap [RingHomSurjective σ₁₂] {f : F} {p : Submodule R M}
    {p' : Submodule R₂ M₂} : map f p ⊓ p' = map f (p ⊓ comap f p') :=
  le_antisymm (by rintro _ ⟨⟨x, h₁, rfl⟩, h₂⟩; exact ⟨_, ⟨h₁, h₂⟩, rfl⟩)
    (le_inf (map_mono inf_le_left) (map_le_iff_le_comap.2 inf_le_right))
#align submodule.map_inf_eq_map_inf_comap Submodule.map_inf_eq_map_inf_comap

@[simp]
theorem map_comap_subtype : map p.subtype (comap p.subtype p') = p ⊓ p' :=
  ext fun x => ⟨by rintro ⟨⟨_, h₁⟩, h₂, rfl⟩; exact ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨⟨_, h₁⟩, h₂, rfl⟩⟩
#align submodule.map_comap_subtype Submodule.map_comap_subtype

theorem eq_zero_of_bot_submodule : ∀ b : (⊥ : Submodule R M), b = 0
  | ⟨b', hb⟩ => Subtype.eq <| show b' = 0 from (mem_bot R).1 hb
#align submodule.eq_zero_of_bot_submodule Submodule.eq_zero_of_bot_submodule

/-- The infimum of a family of invariant submodule of an endomorphism is also an invariant
submodule. -/
theorem _root_.LinearMap.iInf_invariant {σ : R →+* R} [RingHomSurjective σ] {ι : Sort*}
    (f : M →ₛₗ[σ] M) {p : ι → Submodule R M} (hf : ∀ i, ∀ v ∈ p i, f v ∈ p i) :
    ∀ v ∈ iInf p, f v ∈ iInf p := by
  have : ∀ i, (p i).map f ≤ p i := by
    rintro i - ⟨v, hv, rfl⟩
    exact hf i v hv
  suffices (iInf p).map f ≤ iInf p by exact fun v hv => this ⟨v, hv, rfl⟩
  exact le_iInf fun i => (Submodule.map_mono (iInf_le p i)).trans (this i)
#align linear_map.infi_invariant LinearMap.iInf_invariant

theorem disjoint_iff_comap_eq_bot {p q : Submodule R M} : Disjoint p q ↔ comap p.subtype q = ⊥ := by
  rw [← (map_injective_of_injective (show Injective p.subtype from Subtype.coe_injective)).eq_iff,
    map_comap_subtype, map_bot, disjoint_iff]
#align submodule.disjoint_iff_comap_eq_bot Submodule.disjoint_iff_comap_eq_bot

end AddCommMonoid

section AddCommGroup

variable [Ring R] [AddCommGroup M] [Module R M] (p : Submodule R M)
variable [AddCommGroup M₂] [Module R M₂]

@[simp]
protected theorem map_neg (f : M →ₗ[R] M₂) : map (-f) p = map f p :=
  ext fun _ =>
    ⟨fun ⟨x, hx, hy⟩ => hy ▸ ⟨-x, show -x ∈ p from neg_mem hx, map_neg f x⟩, fun ⟨x, hx, hy⟩ =>
      hy ▸ ⟨-x, show -x ∈ p from neg_mem hx, (map_neg (-f) _).trans (neg_neg (f x))⟩⟩
#align submodule.map_neg Submodule.map_neg

@[simp]
lemma comap_neg {f : M →ₗ[R] M₂} {p : Submodule R M₂} :
    p.comap (-f) = p.comap f := by
  ext; simp

end AddCommGroup

end Submodule

namespace Submodule

variable {K : Type*} {V : Type*} {V₂ : Type*}
variable [Semifield K]
variable [AddCommMonoid V] [Module K V]
variable [AddCommMonoid V₂] [Module K V₂]

theorem comap_smul (f : V →ₗ[K] V₂) (p : Submodule K V₂) (a : K) (h : a ≠ 0) :
    p.comap (a • f) = p.comap f := by
  ext b; simp only [Submodule.mem_comap, p.smul_mem_iff h, LinearMap.smul_apply]
#align submodule.comap_smul Submodule.comap_smul

protected theorem map_smul (f : V →ₗ[K] V₂) (p : Submodule K V) (a : K) (h : a ≠ 0) :
    p.map (a • f) = p.map f :=
  le_antisymm (by rw [map_le_iff_le_comap, comap_smul f _ a h, ← map_le_iff_le_comap])
    (by rw [map_le_iff_le_comap, ← comap_smul f _ a h, ← map_le_iff_le_comap])
#align submodule.map_smul Submodule.map_smul

theorem comap_smul' (f : V →ₗ[K] V₂) (p : Submodule K V₂) (a : K) :
    p.comap (a • f) = ⨅ _ : a ≠ 0, p.comap f := by
  classical by_cases h : a = 0 <;> simp [h, comap_smul]
#align submodule.comap_smul' Submodule.comap_smul'

theorem map_smul' (f : V →ₗ[K] V₂) (p : Submodule K V) (a : K) :
    p.map (a • f) = ⨆ _ : a ≠ 0, map f p := by
  classical by_cases h : a = 0 <;> simp [h, Submodule.map_smul]
#align submodule.map_smul' Submodule.map_smul'

end Submodule

namespace Submodule

section Module

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- If `s ≤ t`, then we can view `s` as a submodule of `t` by taking the comap
of `t.subtype`. -/
@[simps symm_apply]
def comapSubtypeEquivOfLe {p q : Submodule R M} (hpq : p ≤ q) : comap q.subtype p ≃ₗ[R] p where
  toFun x := ⟨x, x.2⟩
  invFun x := ⟨⟨x, hpq x.2⟩, x.2⟩
  left_inv x := by simp only [coe_mk, SetLike.eta, LinearEquiv.coe_coe]
  right_inv x := by simp only [Subtype.coe_mk, SetLike.eta, LinearEquiv.coe_coe]
  map_add' x y := rfl
  map_smul' c x := rfl
#align submodule.comap_subtype_equiv_of_le Submodule.comapSubtypeEquivOfLe
#align submodule.comap_subtype_equiv_of_le_symm_apply_coe_coe Submodule.comapSubtypeEquivOfLe_symm_apply

-- Porting note: The original theorem generated by `simps` was using `LinearEquiv.toLinearMap`,
-- different from the theorem on Lean 3, and not simp-normal form.
@[simp]
theorem comapSubtypeEquivOfLe_apply_coe {p q : Submodule R M} (hpq : p ≤ q)
    (x : comap q.subtype p) :
    (comapSubtypeEquivOfLe hpq x : M) = (x : M) :=
  rfl
#align submodule.comap_subtype_equiv_of_le_apply_coe Submodule.comapSubtypeEquivOfLe_apply_coe

end Module

end Submodule

namespace Submodule

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂} {τ₂₁ : R₂ →+* R}
variable [RingHomInvPair τ₁₂ τ₂₁] [RingHomInvPair τ₂₁ τ₁₂]
variable (p : Submodule R M) (q : Submodule R₂ M₂)

-- Porting note: Was `@[simp]`.
@[simp high]
theorem mem_map_equiv {e : M ≃ₛₗ[τ₁₂] M₂} {x : M₂} :
    x ∈ p.map (e : M →ₛₗ[τ₁₂] M₂) ↔ e.symm x ∈ p := by
  rw [Submodule.mem_map]; constructor
  · rintro ⟨y, hy, hx⟩
    simp [← hx, hy]
  · intro hx
    exact ⟨e.symm x, hx, by simp⟩
#align submodule.mem_map_equiv Submodule.mem_map_equiv

theorem map_equiv_eq_comap_symm (e : M ≃ₛₗ[τ₁₂] M₂) (K : Submodule R M) :
    K.map (e : M →ₛₗ[τ₁₂] M₂) = K.comap (e.symm : M₂ →ₛₗ[τ₂₁] M) :=
  Submodule.ext fun _ => by rw [mem_map_equiv, mem_comap, LinearEquiv.coe_coe]
#align submodule.map_equiv_eq_comap_symm Submodule.map_equiv_eq_comap_symm

theorem comap_equiv_eq_map_symm (e : M ≃ₛₗ[τ₁₂] M₂) (K : Submodule R₂ M₂) :
    K.comap (e : M →ₛₗ[τ₁₂] M₂) = K.map (e.symm : M₂ →ₛₗ[τ₂₁] M) :=
  (map_equiv_eq_comap_symm e.symm K).symm
#align submodule.comap_equiv_eq_map_symm Submodule.comap_equiv_eq_map_symm

variable {p}

theorem map_symm_eq_iff (e : M ≃ₛₗ[τ₁₂] M₂) {K : Submodule R₂ M₂} :
    K.map e.symm = p ↔ p.map e = K := by
  constructor <;> rintro rfl
  · calc
      map e (map e.symm K) = comap e.symm (map e.symm K) := map_equiv_eq_comap_symm _ _
      _ = K := comap_map_eq_of_injective e.symm.injective _
  · calc
      map e.symm (map e p) = comap e (map e p) := (comap_equiv_eq_map_symm _ _).symm
      _ = p := comap_map_eq_of_injective e.injective _
#align submodule.map_symm_eq_iff Submodule.map_symm_eq_iff

theorem orderIsoMapComap_apply' (e : M ≃ₛₗ[τ₁₂] M₂) (p : Submodule R M) :
    orderIsoMapComap e p = comap e.symm p :=
  p.map_equiv_eq_comap_symm _
#align submodule.order_iso_map_comap_apply' Submodule.orderIsoMapComap_apply'

theorem orderIsoMapComap_symm_apply' (e : M ≃ₛₗ[τ₁₂] M₂) (p : Submodule R₂ M₂) :
    (orderIsoMapComap e).symm p = map e.symm p :=
  p.comap_equiv_eq_map_symm _
#align submodule.order_iso_map_comap_symm_apply' Submodule.orderIsoMapComap_symm_apply'

theorem inf_comap_le_comap_add (f₁ f₂ : M →ₛₗ[τ₁₂] M₂) :
    comap f₁ q ⊓ comap f₂ q ≤ comap (f₁ + f₂) q := by
  rw [SetLike.le_def]
  intro m h
  change f₁ m + f₂ m ∈ q
  change f₁ m ∈ q ∧ f₂ m ∈ q at h
  apply q.add_mem h.1 h.2
#align submodule.inf_comap_le_comap_add Submodule.inf_comap_le_comap_add

end Submodule

namespace Submodule

variable {N N₂ : Type*}
variable [CommSemiring R] [CommSemiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]
variable [AddCommMonoid N] [AddCommMonoid N₂] [Module R N] [Module R N₂]
variable {τ₁₂ : R →+* R₂} {τ₂₁ : R₂ →+* R}
variable [RingHomInvPair τ₁₂ τ₂₁] [RingHomInvPair τ₂₁ τ₁₂]
variable (p : Submodule R M) (q : Submodule R₂ M₂)
variable (pₗ : Submodule R N) (qₗ : Submodule R N₂)

theorem comap_le_comap_smul (fₗ : N →ₗ[R] N₂) (c : R) : comap fₗ qₗ ≤ comap (c • fₗ) qₗ := by
  rw [SetLike.le_def]
  intro m h
  change c • fₗ m ∈ qₗ
  change fₗ m ∈ qₗ at h
  apply qₗ.smul_mem _ h
#align submodule.comap_le_comap_smul Submodule.comap_le_comap_smul

/-- Given modules `M`, `M₂` over a commutative ring, together with submodules `p ⊆ M`, `q ⊆ M₂`,
the set of maps $\{f ∈ Hom(M, M₂) | f(p) ⊆ q \}$ is a submodule of `Hom(M, M₂)`. -/
def compatibleMaps : Submodule R (N →ₗ[R] N₂) where
  carrier := { fₗ | pₗ ≤ comap fₗ qₗ }
  zero_mem' := by
    change pₗ ≤ comap (0 : N →ₗ[R] N₂) qₗ
    rw [comap_zero]
    exact le_top
  add_mem' {f₁ f₂} h₁ h₂ := by
    apply le_trans _ (inf_comap_le_comap_add qₗ f₁ f₂)
    rw [le_inf_iff]
    exact ⟨h₁, h₂⟩
  smul_mem' c fₗ h := by
    dsimp at h
    exact le_trans h (comap_le_comap_smul qₗ fₗ c)
#align submodule.compatible_maps Submodule.compatibleMaps

end Submodule

namespace LinearMap

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₁] [Module R M] [Module R M₁]

/-- A linear map between two modules restricts to a linear map from any submodule p of the
domain onto the image of that submodule.

This is the linear version of `AddMonoidHom.addSubmonoidMap` and `AddMonoidHom.addSubgroupMap`. -/
def submoduleMap (f : M →ₗ[R] M₁) (p : Submodule R M) : p →ₗ[R] p.map f :=
  f.restrict fun x hx ↦ Submodule.mem_map.mpr ⟨x, hx, rfl⟩

@[simp]
theorem submoduleMap_coe_apply (f : M →ₗ[R] M₁) {p : Submodule R M} (x : p) :
    ↑(f.submoduleMap p x) = f x := rfl

theorem submoduleMap_surjective (f : M →ₗ[R] M₁) (p : Submodule R M) :
    Function.Surjective (f.submoduleMap p) := f.toAddMonoidHom.addSubmonoidMap_surjective _

variable [Semiring R₂] [AddCommMonoid M₂] [Module R₂ M₂] {σ₂₁ : R₂ →+* R}

open Submodule

theorem map_codRestrict [RingHomSurjective σ₂₁] (p : Submodule R M) (f : M₂ →ₛₗ[σ₂₁] M) (h p') :
    Submodule.map (codRestrict p f h) p' = comap p.subtype (p'.map f) :=
  Submodule.ext fun ⟨x, hx⟩ => by simp [Subtype.ext_iff_val]
#align linear_map.map_cod_restrict LinearMap.map_codRestrict

theorem comap_codRestrict (p : Submodule R M) (f : M₂ →ₛₗ[σ₂₁] M) (hf p') :
    Submodule.comap (codRestrict p f hf) p' = Submodule.comap f (map p.subtype p') :=
  Submodule.ext fun x => ⟨fun h => ⟨⟨_, hf x⟩, h, rfl⟩, by rintro ⟨⟨_, _⟩, h, ⟨⟩⟩; exact h⟩
#align linear_map.comap_cod_restrict LinearMap.comap_codRestrict

end LinearMap

/-! ### Linear equivalences -/

namespace LinearEquiv

section AddCommMonoid

section

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable {module_M : Module R M} {module_M₂ : Module R₂ M₂}
variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
variable (e : M ≃ₛₗ[σ₁₂] M₂)

theorem map_eq_comap {p : Submodule R M} :
    (p.map (e : M →ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂) = p.comap (e.symm : M₂ →ₛₗ[σ₂₁] M) :=
  SetLike.coe_injective <| by simp [e.image_eq_preimage]
#align linear_equiv.map_eq_comap LinearEquiv.map_eq_comap

/-- A linear equivalence of two modules restricts to a linear equivalence from any submodule
`p` of the domain onto the image of that submodule.

This is the linear version of `AddEquiv.submonoidMap` and `AddEquiv.subgroupMap`.

This is `LinearEquiv.ofSubmodule'` but with `map` on the right instead of `comap` on the left. -/
def submoduleMap (p : Submodule R M) : p ≃ₛₗ[σ₁₂] ↥(p.map (e : M →ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂) :=
  { ((e : M →ₛₗ[σ₁₂] M₂).domRestrict p).codRestrict (p.map (e : M →ₛₗ[σ₁₂] M₂)) fun x =>
      ⟨x, by
        simp only [LinearMap.domRestrict_apply, eq_self_iff_true, and_true_iff, SetLike.coe_mem,
          SetLike.mem_coe]⟩ with
    invFun := fun y =>
      ⟨(e.symm : M₂ →ₛₗ[σ₂₁] M) y, by
        rcases y with ⟨y', hy⟩
        rw [Submodule.mem_map] at hy
        rcases hy with ⟨x, hx, hxy⟩
        subst hxy
        simp only [symm_apply_apply, Submodule.coe_mk, coe_coe, hx]⟩
    left_inv := fun x => by
      simp only [LinearMap.domRestrict_apply, LinearMap.codRestrict_apply, LinearMap.toFun_eq_coe,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, SetLike.eta]
    right_inv := fun y => by
      apply SetCoe.ext
      simp only [LinearMap.domRestrict_apply, LinearMap.codRestrict_apply, LinearMap.toFun_eq_coe,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] }
#align linear_equiv.submodule_map LinearEquiv.submoduleMap

@[simp]
theorem submoduleMap_apply (p : Submodule R M) (x : p) : ↑(e.submoduleMap p x) = e x :=
  rfl
#align linear_equiv.submodule_map_apply LinearEquiv.submoduleMap_apply

@[simp]
theorem submoduleMap_symm_apply (p : Submodule R M)
    (x : (p.map (e : M →ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂)) : ↑((e.submoduleMap p).symm x) = e.symm x :=
  rfl
#align linear_equiv.submodule_map_symm_apply LinearEquiv.submoduleMap_symm_apply

end

end AddCommMonoid

end LinearEquiv
