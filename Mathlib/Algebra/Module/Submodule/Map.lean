/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap

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

@[expose] public section

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

variable [RingHomSurjective σ₁₂]

/-- The pushforward of a submodule `p ⊆ M` by `f : M → M₂` -/
def map (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) : Submodule R₂ M₂ :=
  { p.toAddSubmonoid.map f with
    carrier := f '' p
    smul_mem' := by
      rintro c x ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := σ₁₂.surjective c
      exact ⟨_, p.smul_mem a hy, map_smulₛₗ f _ _⟩ }

@[simp]
theorem map_coe (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) : (map f p : Set M₂) = f '' p :=
  rfl

theorem map_toAddSubmonoid (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    (p.map f).toAddSubmonoid = p.toAddSubmonoid.map (f : M →+ M₂) :=
  SetLike.coe_injective rfl

theorem map_toAddSubmonoid' (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    (p.map f).toAddSubmonoid = p.toAddSubmonoid.map f :=
  SetLike.coe_injective rfl

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
theorem mem_map {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x : M₂} :
    x ∈ map f p ↔ ∃ y, y ∈ p ∧ f y = x :=
  Iff.rfl

theorem mem_map_of_mem {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R M} {r} (h : r ∈ p) : f r ∈ map f p :=
  Set.mem_image_of_mem _ h

theorem apply_coe_mem_map (f : M →ₛₗ[σ₁₂] M₂) {p : Submodule R M} (r : p) : f r ∈ map f p :=
  mem_map_of_mem r.prop

@[simp]
theorem map_id : map (LinearMap.id : M →ₗ[R] M) p = p :=
  Submodule.ext fun a => by simp

theorem map_comp [RingHomSurjective σ₂₃] [RingHomSurjective σ₁₃] (f : M →ₛₗ[σ₁₂] M₂)
    (g : M₂ →ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.comp f : M →ₛₗ[σ₁₃] M₃) p = map g (map f p) :=
  SetLike.coe_injective <| by simp only [← image_comp, map_coe, LinearMap.coe_comp, comp_apply]

@[gcongr]
theorem map_mono {f : M →ₛₗ[σ₁₂] M₂} {p p' : Submodule R M} : p ≤ p' → map f p ≤ map f p' :=
  image_mono

@[simp]
protected theorem map_zero : map (0 : M →ₛₗ[σ₁₂] M₂) p = ⊥ :=
  have : ∃ x : M, x ∈ p := ⟨0, p.zero_mem⟩
  ext <| by simp [this, eq_comm]

theorem map_add_le (f g : M →ₛₗ[σ₁₂] M₂) : map (f + g) p ≤ map f p ⊔ map g p := by
  rintro x ⟨m, hm, rfl⟩
  exact add_mem_sup (mem_map_of_mem hm) (mem_map_of_mem hm)

theorem map_inf_le (f : M →ₛₗ[σ₁₂] M₂) {p q : Submodule R M} :
    (p ⊓ q).map f ≤ p.map f ⊓ q.map f :=
  image_inter_subset f p q

theorem map_inf (f : M →ₛₗ[σ₁₂] M₂) {p q : Submodule R M} (hf : Injective f) :
    (p ⊓ q).map f = p.map f ⊓ q.map f :=
  SetLike.coe_injective <| Set.image_inter hf

lemma map_iInf {ι : Sort*} [Nonempty ι] {p : ι → Submodule R M} (f : M →ₛₗ[σ₁₂] M₂)
    (hf : Injective f) : (⨅ i, p i).map f = ⨅ i, (p i).map f :=
  SetLike.coe_injective <| by simpa only [map_coe, coe_iInf] using hf.injOn.image_iInter_eq

theorem range_map_nonempty (N : Submodule R M) :
    (Set.range (fun ϕ => Submodule.map ϕ N : (M →ₛₗ[σ₁₂] M₂) → Submodule R₂ M₂)).Nonempty :=
  ⟨_, Set.mem_range.mpr ⟨0, rfl⟩⟩

end

section SemilinearMap

variable {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/-- The pushforward of a submodule by an injective linear map is
linearly equivalent to the original submodule. See also `LinearEquiv.submoduleMap` for a
computable version when `f` has an explicit inverse. -/
noncomputable def equivMapOfInjective (f : M →ₛₗ[σ₁₂] M₂) (i : Injective f) (p : Submodule R M) :
    p ≃ₛₗ[σ₁₂] p.map f :=
  { Equiv.Set.image f p i with
    map_add' := by
      intros
      simp only [coe_add, map_add, Equiv.toFun_as_coe, Equiv.Set.image_apply]
      rfl
    map_smul' := by
      intros
      -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`
      simp only [coe_smul_of_tower, map_smulₛₗ _, Equiv.toFun_as_coe, Equiv.Set.image_apply]
      rfl }

@[simp]
theorem coe_equivMapOfInjective_apply (f : M →ₛₗ[σ₁₂] M₂) (i : Injective f) (p : Submodule R M)
    (x : p) : (equivMapOfInjective f i p x : M₂) = f x :=
  rfl

@[simp]
theorem map_equivMapOfInjective_symm_apply (f : M →ₛₗ[σ₁₂] M₂) (i : Injective f) (p : Submodule R M)
    (x : p.map f) : f ((equivMapOfInjective f i p).symm x) = x := by
  rw [← LinearEquiv.apply_symm_apply (equivMapOfInjective f i p) x, coe_equivMapOfInjective_apply,
    i.eq_iff, LinearEquiv.apply_symm_apply]

/-- The pullback of a submodule `p ⊆ M₂` along `f : M → M₂` -/
@[implicit_reducible]
def comap (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) : Submodule R M :=
  { p.toAddSubmonoid.comap f with
    carrier := f ⁻¹' p
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 added `map_smulₛₗ _`
    smul_mem' := fun a x h => by simp [p.smul_mem (σ₁₂ a) h, map_smulₛₗ _] }

@[simp]
theorem comap_coe (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) : (comap f p : Set M) = f ⁻¹' p :=
  rfl

@[simp]
theorem AddMonoidHom.coe_toIntLinearMap_comap {A A₂ : Type*} [AddCommGroup A] [AddCommGroup A₂]
    (f : A →+ A₂) (s : AddSubgroup A₂) :
    (AddSubgroup.toIntSubmodule s).comap f.toIntLinearMap =
      AddSubgroup.toIntSubmodule (s.comap f) := rfl

@[simp]
theorem mem_comap {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂} : x ∈ comap f p ↔ f x ∈ p :=
  Iff.rfl

@[simp]
theorem comap_id : comap (LinearMap.id : M →ₗ[R] M) p = p :=
  SetLike.coe_injective rfl

theorem comap_comp (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃) (p : Submodule R₃ M₃) :
    comap (g.comp f : M →ₛₗ[σ₁₃] M₃) p = comap f (comap g p) :=
  rfl

@[gcongr]
theorem comap_mono {f : M →ₛₗ[σ₁₂] M₂} {q q' : Submodule R₂ M₂} : q ≤ q' → comap f q ≤ comap f q' :=
  preimage_mono

theorem le_comap_pow_of_le_comap (p : Submodule R M) {f : M →ₗ[R] M}
    (h : p ≤ p.comap f) (k : ℕ) : p ≤ p.comap (f ^ k) := by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih => simp [Module.End.iterate_succ, comap_comp, h.trans (comap_mono ih)]

section

variable [RingHomSurjective σ₁₂]

theorem map_le_iff_le_comap {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂} :
    map f p ≤ q ↔ p ≤ comap f q :=
  image_subset_iff

theorem gc_map_comap (f : M →ₛₗ[σ₁₂] M₂) : GaloisConnection (map f) (comap f)
  | _, _ => map_le_iff_le_comap

@[simp]
theorem map_bot (f : M →ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
theorem map_sup (f : M →ₛₗ[σ₁₂] M₂) : map f (p ⊔ p') = map f p ⊔ map f p' :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup

@[simp]
theorem map_iSup {ι : Sort*} (f : M →ₛₗ[σ₁₂] M₂) (p : ι → Submodule R M) :
    map f (⨆ i, p i) = ⨆ i, map f (p i) :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup

lemma disjoint_map {f : M →ₛₗ[σ₁₂] M₂} (hf : Function.Injective f) {p q : Submodule R M}
    (hpq : Disjoint p q) : Disjoint (p.map f) (q.map f) := by
  rw [disjoint_iff, ← map_inf f hf, disjoint_iff.mp hpq, map_bot]

end

@[simp]
theorem comap_top (f : M →ₛₗ[σ₁₂] M₂) : comap f ⊤ = ⊤ :=
  rfl

@[simp]
theorem comap_inf (f : M →ₛₗ[σ₁₂] M₂) : comap f (q ⊓ q') = comap f q ⊓ comap f q' :=
  rfl

@[simp]
theorem comap_iInf {ι : Sort*} (f : M →ₛₗ[σ₁₂] M₂)
    (p : ι → Submodule R₂ M₂) : comap f (⨅ i, p i) = ⨅ i, comap f (p i) := by
  ext
  simp

@[simp]
theorem comap_finsetInf {ι : Type*} (f : M →ₛₗ[σ₁₂] M₂)
    (s : Finset ι) (p : ι → Submodule R₂ M₂) : comap f (s.inf p) = s.inf fun i ↦ comap f (p i) := by
  simp [Finset.inf_eq_iInf]

@[simp]
theorem comap_zero : comap (0 : M →ₛₗ[σ₁₂] M₂) q = ⊤ :=
  ext <| by simp

theorem map_comap_le [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (q : Submodule R₂ M₂) :
    map f (comap f q) ≤ q :=
  (gc_map_comap f).l_u_le _

theorem le_comap_map [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    p ≤ comap f (map f p) :=
  (gc_map_comap f).le_u_l _

section submoduleOf

/-- For any `R` submodules `p` and `q`, `p ⊓ q` as a submodule of `q`. -/
def submoduleOf (p q : Submodule R M) : Submodule R q :=
  Submodule.comap q.subtype p

/-- If `p ≤ q`, then `p` as a subgroup of `q` is isomorphic to `p`. -/
def submoduleOfEquivOfLe {p q : Submodule R M} (h : p ≤ q) : p.submoduleOf q ≃ₗ[R] p where
  toFun m := ⟨m.1, m.2⟩
  invFun m := ⟨⟨m.1, h m.2⟩, m.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end submoduleOf

section GaloisInsertion

variable [RingHomSurjective σ₁₂] {f : M →ₛₗ[σ₁₂] M₂}

/-- `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective. -/
def giMapComap (hf : Surjective f) : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x hx => by
    rcases hf x with ⟨y, rfl⟩
    simp only [mem_map, mem_comap]
    exact ⟨y, hx, rfl⟩

variable (hf : Surjective f)
include hf

theorem map_comap_eq_of_surjective (p : Submodule R₂ M₂) : (p.comap f).map f = p :=
  (giMapComap hf).l_u_eq _

theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective

theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective

theorem map_sup_comap_of_surjective (p q : Submodule R₂ M₂) :
    (p.comap f ⊔ q.comap f).map f = p ⊔ q :=
  (giMapComap hf).l_sup_u _ _

theorem map_iSup_comap_of_surjective {ι : Sort*} (S : ι → Submodule R₂ M₂) :
    (⨆ i, (S i).comap f).map f = iSup S :=
  (giMapComap hf).l_iSup_u _

theorem map_inf_comap_of_surjective (p q : Submodule R₂ M₂) :
    (p.comap f ⊓ q.comap f).map f = p ⊓ q :=
  (giMapComap hf).l_inf_u _ _

theorem map_iInf_comap_of_surjective {ι : Sort*} (S : ι → Submodule R₂ M₂) :
    (⨅ i, (S i).comap f).map f = iInf S :=
  (giMapComap hf).l_iInf_u _

theorem comap_le_comap_iff_of_surjective {p q : Submodule R₂ M₂} : p.comap f ≤ q.comap f ↔ p ≤ q :=
  (giMapComap hf).u_le_u_iff

lemma comap_lt_comap_iff_of_surjective {p q : Submodule R₂ M₂} : p.comap f < q.comap f ↔ p < q := by
  apply lt_iff_lt_of_le_iff_le' <;> exact comap_le_comap_iff_of_surjective hf

theorem comap_strictMono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strictMono_u

variable {p q}

theorem le_map_of_comap_le_of_surjective (h : q.comap f ≤ p) : q ≤ p.map f :=
  map_comap_eq_of_surjective hf q ▸ map_mono h

theorem lt_map_of_comap_lt_of_surjective (h : q.comap f < p) : q < p.map f := by
  rw [lt_iff_le_not_ge] at h ⊢; rw [map_le_iff_le_comap]
  exact h.imp_left (le_map_of_comap_le_of_surjective hf)

end GaloisInsertion

section GaloisCoinsertion

variable [RingHomSurjective σ₁₂] {f : M →ₛₗ[σ₁₂] M₂}

/-- `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective. -/
def gciMapComap (hf : Injective f) : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by
    simp only [mem_comap, mem_map, forall_exists_index, and_imp]
    intro y hy hxy
    rw [hf.eq_iff] at hxy
    rwa [← hxy]

variable (hf : Injective f)
include hf

theorem comap_map_eq_of_injective (p : Submodule R M) : (p.map f).comap f = p :=
  (gciMapComap hf).u_l_eq _

theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective

theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective

theorem comap_inf_map_of_injective (p q : Submodule R M) : (p.map f ⊓ q.map f).comap f = p ⊓ q :=
  (gciMapComap hf).u_inf_l _ _

theorem comap_iInf_map_of_injective {ι : Sort*} (S : ι → Submodule R M) :
    (⨅ i, (S i).map f).comap f = iInf S :=
  (gciMapComap hf).u_iInf_l _

theorem comap_sup_map_of_injective (p q : Submodule R M) : (p.map f ⊔ q.map f).comap f = p ⊔ q :=
  (gciMapComap hf).u_sup_l _ _

theorem comap_iSup_map_of_injective {ι : Sort*} (S : ι → Submodule R M) :
    (⨆ i, (S i).map f).comap f = iSup S :=
  (gciMapComap hf).u_iSup_l _

theorem map_le_map_iff_of_injective (p q : Submodule R M) : p.map f ≤ q.map f ↔ p ≤ q :=
  (gciMapComap hf).l_le_l_iff

theorem map_strictMono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strictMono_l

lemma map_lt_map_iff_of_injective {p q : Submodule R M} :
    p.map f < q.map f ↔ p < q := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, map_le_map_iff_of_injective hf,
    (map_injective_of_injective hf).ne_iff]

lemma comap_lt_of_lt_map_of_injective {p : Submodule R M} {q : Submodule R₂ M₂}
    (h : q < p.map f) : q.comap f < p := by
  rw [← map_lt_map_iff_of_injective hf]
  exact (map_comap_le _ _).trans_lt h

lemma map_covBy_of_injective {p q : Submodule R M} (h : p ⋖ q) :
    p.map f ⋖ q.map f := by
  refine ⟨lt_of_le_of_ne (map_mono h.1.le) ((map_injective_of_injective hf).ne h.1.ne), ?_⟩
  intro P h₁ h₂
  refine h.2 ?_ (Submodule.comap_lt_of_lt_map_of_injective hf h₂)
  rw [← Submodule.map_lt_map_iff_of_injective hf]
  refine h₁.trans_le ?_
  exact (Set.image_preimage_eq_of_subset (.trans h₂.le (Set.image_subset_range _ _))).superset

end GaloisCoinsertion

end SemilinearMap

section OrderIso

variable [RingHomSurjective σ₁₂]

/-- A linear isomorphism induces an order isomorphism of submodules. -/
@[simps symm_apply apply]
def orderIsoMapComapOfBijective (f : M →ₛₗ[σ₁₂] M₂) (hf : Bijective f) :
    Submodule R M ≃o Submodule R₂ M₂ where
  toFun := map f
  invFun := comap f
  left_inv := comap_map_eq_of_injective hf.injective
  right_inv := map_comap_eq_of_surjective hf.surjective
  map_rel_iff' := map_le_map_iff_of_injective hf.injective _ _

variable {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/-- A linear isomorphism induces an order isomorphism of submodules. -/
@[simps! apply]
def orderIsoMapComap (f : M ≃ₛₗ[σ₁₂] M₂) :
    Submodule R M ≃o Submodule R₂ M₂ := orderIsoMapComapOfBijective (f : M →ₛₗ[σ₁₂] M₂) f.bijective

@[simp]
lemma orderIsoMapComap_symm_apply (f : M ≃ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) :
    (orderIsoMapComap f).symm p = comap (f : M →ₛₗ[σ₁₂] M₂) p :=
  rfl

variable {e : M ≃ₛₗ[σ₁₂] M₂}
variable {p}

@[simp] protected lemma map_eq_bot_iff : p.map (e : M →ₛₗ[σ₁₂] M₂) = ⊥ ↔ p = ⊥ :=
  map_eq_bot_iff (orderIsoMapComap e)

@[simp] protected lemma map_eq_top_iff : p.map (e : M →ₛₗ[σ₁₂] M₂) = ⊤ ↔ p = ⊤ :=
  map_eq_top_iff (orderIsoMapComap e)

protected lemma map_ne_bot_iff : p.map (e : M →ₛₗ[σ₁₂] M₂) ≠ ⊥ ↔ p ≠ ⊥ := by simp

protected lemma map_ne_top_iff : p.map (e : M →ₛₗ[σ₁₂] M₂) ≠ ⊤ ↔ p ≠ ⊤ := by simp

end OrderIso

--TODO(Mario): is there a way to prove this from order properties?
theorem map_inf_eq_map_inf_comap [RingHomSurjective σ₁₂] {f : M →ₛₗ[σ₁₂] M₂} {p : Submodule R M}
    {p' : Submodule R₂ M₂} : map f p ⊓ p' = map f (p ⊓ comap f p') :=
  le_antisymm (by rintro _ ⟨⟨x, h₁, rfl⟩, h₂⟩; exact ⟨_, ⟨h₁, h₂⟩, rfl⟩)
    (le_inf (map_mono inf_le_left) (map_le_iff_le_comap.2 inf_le_right))

@[simp]
theorem map_comap_subtype : map p.subtype (comap p.subtype p') = p ⊓ p' :=
  ext fun x => ⟨by rintro ⟨⟨_, h₁⟩, h₂, rfl⟩; exact ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨⟨_, h₁⟩, h₂, rfl⟩⟩

theorem eq_zero_of_bot_submodule : ∀ b : (⊥ : Submodule R M), b = 0
  | ⟨b', hb⟩ => Subtype.ext <| show b' = 0 from (mem_bot R).1 hb

/-- The infimum of a family of invariant submodule of an endomorphism is also an invariant
submodule. -/
theorem _root_.LinearMap.iInf_invariant {σ : R →+* R} {ι : Sort*}
    (f : M →ₛₗ[σ] M) {p : ι → Submodule R M} (hf : ∀ i, ∀ v ∈ p i, f v ∈ p i) :
    ∀ v ∈ iInf p, f v ∈ iInf p := by
  simp only [mem_iInf]
  exact fun v a i ↦ hf i v (a i)

theorem disjoint_iff_comap_eq_bot {p q : Submodule R M} : Disjoint p q ↔ comap p.subtype q = ⊥ := by
  rw [← (map_injective_of_injective (show Injective p.subtype from Subtype.coe_injective)).eq_iff,
    map_comap_subtype, map_bot, disjoint_iff]

end AddCommMonoid

section AddCommGroup

variable [Ring R] [AddCommGroup M] [Module R M] (p : Submodule R M)
variable [AddCommGroup M₂] [Module R M₂]

@[simp]
protected theorem map_neg (f : M →ₗ[R] M₂) : map (-f) p = map f p :=
  ext fun _ =>
    ⟨fun ⟨x, hx, hy⟩ => hy ▸ ⟨-x, show -x ∈ p from neg_mem hx, map_neg f x⟩, fun ⟨x, hx, hy⟩ =>
      hy ▸ ⟨-x, show -x ∈ p from neg_mem hx, (map_neg (-f) _).trans (neg_neg (f x))⟩⟩

@[simp]
lemma comap_neg {f : M →ₗ[R] M₂} {p : Submodule R M₂} :
    p.comap (-f) = p.comap f := by
  ext; simp

lemma map_toAddSubgroup (f : M →ₗ[R] M₂) (p : Submodule R M) :
    (p.map f).toAddSubgroup = p.toAddSubgroup.map (f : M →+ M₂) :=
  rfl

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

protected theorem map_smul (f : V →ₗ[K] V₂) (p : Submodule K V) (a : K) (h : a ≠ 0) :
    p.map (a • f) = p.map f :=
  le_antisymm (by rw [map_le_iff_le_comap, comap_smul f _ a h, ← map_le_iff_le_comap])
    (by rw [map_le_iff_le_comap, ← comap_smul f _ a h, ← map_le_iff_le_comap])

theorem comap_smul' (f : V →ₗ[K] V₂) (p : Submodule K V₂) (a : K) :
    p.comap (a • f) = ⨅ _ : a ≠ 0, p.comap f := by
  classical by_cases h : a = 0 <;> simp [h, comap_smul]

theorem map_smul' (f : V →ₗ[K] V₂) (p : Submodule K V) (a : K) :
    p.map (a • f) = ⨆ _ : a ≠ 0, map f p := by
  classical by_cases h : a = 0 <;> simp [h, Submodule.map_smul]

end Submodule

namespace Submodule

section Module

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- If `s ≤ t`, then we can view `s` as a submodule of `t` by taking the comap
of `t.subtype`. -/
@[simps apply_coe symm_apply]
def comapSubtypeEquivOfLe {p q : Submodule R M} (hpq : p ≤ q) : comap q.subtype p ≃ₗ[R] p where
  toFun x := ⟨x, x.2⟩
  invFun x := ⟨⟨x, hpq x.2⟩, x.2⟩
  left_inv x := by simp
  right_inv x := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Module

end Submodule

namespace Submodule

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂} {τ₂₁ : R₂ →+* R}
variable [RingHomInvPair τ₁₂ τ₂₁] [RingHomInvPair τ₂₁ τ₁₂]
variable (p : Submodule R M) (q : Submodule R₂ M₂)

@[simp high]
theorem mem_map_equiv {e : M ≃ₛₗ[τ₁₂] M₂} {x : M₂} :
    x ∈ p.map (e : M →ₛₗ[τ₁₂] M₂) ↔ e.symm x ∈ p := by
  rw [Submodule.mem_map]; constructor
  · rintro ⟨y, hy, hx⟩
    simp [← hx, hy]
  · intro hx
    exact ⟨e.symm x, hx, by simp⟩

theorem map_equiv_eq_comap_symm (e : M ≃ₛₗ[τ₁₂] M₂) (K : Submodule R M) :
    K.map (e : M →ₛₗ[τ₁₂] M₂) = K.comap (e.symm : M₂ →ₛₗ[τ₂₁] M) :=
  Submodule.ext fun _ => by rw [mem_map_equiv, mem_comap, LinearEquiv.coe_coe]

theorem comap_equiv_eq_map_symm (e : M ≃ₛₗ[τ₁₂] M₂) (K : Submodule R₂ M₂) :
    K.comap (e : M →ₛₗ[τ₁₂] M₂) = K.map (e.symm : M₂ →ₛₗ[τ₂₁] M) :=
  (map_equiv_eq_comap_symm e.symm K).symm

variable {p}

theorem map_symm_eq_iff (e : M ≃ₛₗ[τ₁₂] M₂) {K : Submodule R₂ M₂} :
    K.map (e.symm : M₂ →ₛₗ[τ₂₁] M) = p ↔ p.map (e : M →ₛₗ[τ₁₂] M₂) = K := by
  rw [map_equiv_eq_comap_symm]
  exact (orderIsoMapComap e).symm_apply_eq.trans eq_comm

theorem orderIsoMapComap_apply' (e : M ≃ₛₗ[τ₁₂] M₂) (p : Submodule R M) :
    orderIsoMapComap e p = comap (e.symm : M₂ →ₛₗ[τ₂₁] M) p :=
  p.map_equiv_eq_comap_symm _

theorem orderIsoMapComap_symm_apply' (e : M ≃ₛₗ[τ₁₂] M₂) (p : Submodule R₂ M₂) :
    (orderIsoMapComap e).symm p = map (e.symm : M₂ →ₛₗ[τ₂₁] M) p :=
  p.comap_equiv_eq_map_symm _

theorem inf_comap_le_comap_add (f₁ f₂ : M →ₛₗ[τ₁₂] M₂) :
    comap f₁ q ⊓ comap f₂ q ≤ comap (f₁ + f₂) q := by
  simp only [SetLike.le_def, mem_comap, mem_inf, LinearMap.add_apply]
  exact fun _ h ↦ add_mem h.1 h.2

lemma surjOn_iff_le_map [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {p : Submodule R M}
    {q : Submodule R₂ M₂} : Set.SurjOn f p q ↔ q ≤ p.map f :=
  Iff.rfl

end Submodule

namespace Submodule

variable {S N N₂ : Type*}
variable [CommSemiring S] [Semiring R] [CommSemiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]
variable [AddCommMonoid N] [AddCommMonoid N₂] [Module S N] [Module S N₂]
variable {τ₁₂ : R →+* R₂}
variable (p : Submodule R M) (q : Submodule R₂ M₂)
variable (pₗ : Submodule S N) (qₗ : Submodule S N₂)

theorem comap_le_comap_smul (f : M →ₛₗ[τ₁₂] M₂) (c : R₂) : comap f q ≤ comap (c • f) q := by
  simp only [SetLike.le_def, mem_comap, LinearMap.smul_apply]
  exact fun _ h ↦ smul_mem _ _ h

theorem map_smul_le_map [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) (c : R₂) :
    map (c • f) p ≤ map f p := by
  grw [map_le_iff_le_comap, ← comap_le_comap_smul (map f p) f c, ← map_le_iff_le_comap]

/-- Given modules `M`, `M₂` over a commutative ring, together with submodules `p ⊆ M`, `q ⊆ M₂`,
the set of maps $\{f ∈ Hom(M, M₂) | f(p) ⊆ q \}$ is a submodule of `Hom(M, M₂)`. -/
def compatibleMaps : Submodule S (N →ₗ[S] N₂) where
  carrier := { fₗ | pₗ ≤ comap fₗ qₗ }
  zero_mem' := by simp
  add_mem' {f₁ f₂} h₁ h₂ := by
    apply le_trans _ (inf_comap_le_comap_add qₗ f₁ f₂)
    rw [le_inf_iff]
    exact ⟨h₁, h₂⟩
  smul_mem' c fₗ h := by
    dsimp at h
    exact le_trans h (comap_le_comap_smul qₗ fₗ c)

end Submodule

namespace LinearMap

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]
variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}

/-- The `LinearMap` from the preimage of a submodule to itself.

This is the linear version of `AddMonoidHom.addSubmonoidComap`
and `AddMonoidHom.addSubgroupComap`. -/
@[simps!]
def submoduleComap (f : M →ₛₗ[σ₁₂] M₂) (q : Submodule R₂ M₂) : q.comap f →ₛₗ[σ₁₂] q :=
  f.restrict fun _ ↦ Submodule.mem_comap.1

theorem submoduleComap_surjective_of_surjective (f : M →ₛₗ[σ₁₂] M₂) (q : Submodule R₂ M₂)
    (hf : Surjective f) : Surjective (f.submoduleComap q) := fun y ↦ by
  obtain ⟨x, hx⟩ := hf y
  use ⟨x, Submodule.mem_comap.mpr (hx ▸ y.2)⟩
  apply Subtype.val_injective
  simp [hx]

/-- A linear map between two modules restricts to a linear map from any submodule p of the
domain onto the image of that submodule.

This is the linear version of `AddMonoidHom.addSubmonoidMap` and `AddMonoidHom.addSubgroupMap`.

TODO: Consider making this an `abbrev`, dropping its API, and renaming to something like
`restrictSubmodule`. -/
def submoduleMap [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    p →ₛₗ[σ₁₂] p.map f :=
  f.restrict fun x hx ↦ Submodule.mem_map.mpr ⟨x, hx, rfl⟩

@[simp]
theorem submoduleMap_coe_apply [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) {p : Submodule R M}
    (x : p) : ↑(f.submoduleMap p x) = f x := rfl

theorem submoduleMap_surjective [RingHomSurjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    Function.Surjective (f.submoduleMap p) := f.toAddMonoidHom.addSubmonoidMap_surjective _

@[grind inj]
theorem submoduleMap_injective [RingHomSurjective σ₁₂] {f : M →ₛₗ[σ₁₂] M₂} (hf : Injective f)
    (p : Submodule R M) : Injective (f.submoduleMap p) :=
  f.toAddMonoidHom.addSubmonoidMap_injective hf _

open Submodule

theorem map_codRestrict [RingHomSurjective σ₂₁] (p : Submodule R M) (f : M₂ →ₛₗ[σ₂₁] M) (h p') :
    map (codRestrict p f h) p' = comap p.subtype (p'.map f) :=
  Submodule.ext fun ⟨x, hx⟩ => by simp [Subtype.ext_iff]

theorem comap_codRestrict (p : Submodule R M) (f : M₂ →ₛₗ[σ₂₁] M) (hf p') :
    comap (codRestrict p f hf) p' = comap f (map p.subtype p') :=
  Submodule.ext fun x => ⟨fun h => ⟨⟨_, hf x⟩, h, rfl⟩, by rintro ⟨⟨_, _⟩, h, ⟨⟩⟩; exact h⟩

theorem map_domRestrict [RingHomSurjective σ₂₁] (p : Submodule R₂ M₂) (f : M₂ →ₛₗ[σ₂₁] M) (p') :
    map (domRestrict f p) p' = map f (map p.subtype p') :=
  map_comp p.subtype f p'

theorem comap_domRestrict (p : Submodule R₂ M₂) (f : M₂ →ₛₗ[σ₂₁] M) (p') :
    comap (domRestrict f p) p' = comap p.subtype (comap f p') :=
  comap_comp p.subtype f p'

set_option backward.isDefEq.respectTransparency.types false in
theorem map_restrict [RingHomSurjective σ₂₁] {p : Submodule R₂ M₂} {q : Submodule R M}
    {f : M₂ →ₛₗ[σ₂₁] M} (h : ∀ x ∈ p, f x ∈ q) (p') :
    map (f.restrict h) p' = comap q.subtype (map f (map p.subtype p')) := by
  rw [restrict_eq_codRestrict_domRestrict, map_codRestrict, map_domRestrict]

set_option backward.isDefEq.respectTransparency.types false in
theorem comap_restrict {p : Submodule R₂ M₂} {q : Submodule R M} {f : M₂ →ₛₗ[σ₂₁] M}
    (h : ∀ x ∈ p, f x ∈ q) (p') :
    comap (f.restrict h) p' = comap p.subtype (comap f (map q.subtype p')) := by
  rw [restrict_eq_codRestrict_domRestrict, comap_codRestrict, comap_domRestrict]

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

set_option backward.isDefEq.respectTransparency false in
/-- A linear equivalence of two modules restricts to a linear equivalence from any submodule
`p` of the domain onto the image of that submodule.

This is the linear version of `AddEquiv.submonoidMap` and `AddEquiv.subgroupMap`.

This is `LinearEquiv.ofSubmodule'` but with `map` on the right instead of `comap` on the left. -/
def submoduleMap (p : Submodule R M) : p ≃ₛₗ[σ₁₂] ↥(p.map (e : M →ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂) :=
  { ((e : M →ₛₗ[σ₁₂] M₂).domRestrict p).codRestrict (p.map (e : M →ₛₗ[σ₁₂] M₂)) fun x =>
      ⟨x, by
        simp only [LinearMap.domRestrict_apply, and_true, SetLike.coe_mem,
          SetLike.mem_coe]⟩ with
    invFun := fun y =>
      ⟨(e.symm : M₂ →ₛₗ[σ₂₁] M) y, by
        rcases y with ⟨y', hy⟩
        rw [Submodule.mem_map] at hy
        rcases hy with ⟨x, hx, hxy⟩
        subst hxy
        simp only [symm_apply_apply, coe_coe, hx]⟩
    left_inv := fun x => by
      simp only [LinearMap.domRestrict_apply, LinearMap.codRestrict_apply, LinearMap.toFun_eq_coe,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, SetLike.eta]
    right_inv := fun y => by
      apply SetCoe.ext
      simp only [LinearMap.domRestrict_apply, LinearMap.codRestrict_apply, LinearMap.toFun_eq_coe,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] }

@[simp]
theorem submoduleMap_apply (p : Submodule R M) (x : p) : ↑(e.submoduleMap p x) = e x :=
  rfl

@[simp]
theorem submoduleMap_symm_apply (p : Submodule R M)
    (x : (p.map (e : M →ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂)) : ↑((e.submoduleMap p).symm x) = e.symm x :=
  rfl

end

end AddCommMonoid

end LinearEquiv
