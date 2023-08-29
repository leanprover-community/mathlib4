/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.RingTheory.Noetherian

#align_import algebra.lie.submodule from "leanprover-community/mathlib"@"9822b65bfc4ac74537d77ae318d27df1df662471"

/-!
# Lie submodules of a Lie algebra

In this file we define Lie submodules and Lie ideals, we construct the lattice structure on Lie
submodules and we use it to define various important operations, notably the Lie span of a subset
of a Lie module.

## Main definitions

  * `LieSubmodule`
  * `LieSubmodule.wellFounded_of_noetherian`
  * `LieSubmodule.lieSpan`
  * `LieSubmodule.map`
  * `LieSubmodule.comap`
  * `LieIdeal`
  * `LieIdeal.map`
  * `LieIdeal.comap`

## Tags

lie algebra, lie submodule, lie ideal, lattice structure
-/


universe u v w w₁ w₂

section LieSubmodule

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

/-- A Lie submodule of a Lie module is a submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie module. -/
structure LieSubmodule extends Submodule R M where
  lie_mem : ∀ {x : L} {m : M}, m ∈ carrier → ⁅x, m⁆ ∈ carrier
#align lie_submodule LieSubmodule

attribute [nolint docBlame] LieSubmodule.toSubmodule
attribute [coe] LieSubmodule.toSubmodule

namespace LieSubmodule

variable {R L M}
variable (N N' : LieSubmodule R L M)

instance : SetLike (LieSubmodule R L M) M where
  coe s := s.carrier
  coe_injective' N O h := by cases N; cases O; congr; exact SetLike.coe_injective' h
                             -- ⊢ { toSubmodule := toSubmodule✝, lie_mem := lie_mem✝ } = O
                                      -- ⊢ { toSubmodule := toSubmodule✝¹, lie_mem := lie_mem✝¹ } = { toSubmodule := to …
                                               -- ⊢ toSubmodule✝¹ = toSubmodule✝
                                                      -- 🎉 no goals

instance : AddSubgroupClass (LieSubmodule R L M) M where
  add_mem {N} _ _ := N.add_mem'
  zero_mem N := N.zero_mem'
  neg_mem {N} x hx := show -x ∈ N.toSubmodule from neg_mem hx

/-- The zero module is a Lie submodule of any Lie module. -/
instance : Zero (LieSubmodule R L M) :=
  ⟨{ (0 : Submodule R M) with
      lie_mem := fun {x m} h ↦ by rw [(Submodule.mem_bot R).1 h]; apply lie_zero }⟩
                                  -- ⊢ ⁅x, 0⁆ ∈ { toAddSubmonoid := src✝.toAddSubmonoid, smul_mem' := (_ : ∀ (c : R …
                                                                  -- 🎉 no goals

instance : Inhabited (LieSubmodule R L M) :=
  ⟨0⟩

instance coeSubmodule : CoeOut (LieSubmodule R L M) (Submodule R M) :=
  ⟨toSubmodule⟩
#align lie_submodule.coe_submodule LieSubmodule.coeSubmodule

-- Syntactic tautology
#noalign lie_submodule.to_submodule_eq_coe

@[norm_cast]
theorem coe_toSubmodule : ((N : Submodule R M) : Set M) = N :=
  rfl
#align lie_submodule.coe_to_submodule LieSubmodule.coe_toSubmodule

-- Porting note: `simp` can prove this after `mem_coeSubmodule` is added to the simp set,
-- but `dsimp` can't.
@[simp, nolint simpNF]
theorem mem_carrier {x : M} : x ∈ N.carrier ↔ x ∈ (N : Set M) :=
  Iff.rfl
#align lie_submodule.mem_carrier LieSubmodule.mem_carrier

@[simp]
theorem mem_mk_iff (S : Set M) (h₁ h₂ h₃ h₄) {x : M} :
    x ∈ (⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieSubmodule R L M) ↔ x ∈ S :=
  Iff.rfl
#align lie_submodule.mem_mk_iff LieSubmodule.mem_mk_iff

@[simp]
theorem mem_coeSubmodule {x : M} : x ∈ (N : Submodule R M) ↔ x ∈ N :=
  Iff.rfl
#align lie_submodule.mem_coe_submodule LieSubmodule.mem_coeSubmodule

theorem mem_coe {x : M} : x ∈ (N : Set M) ↔ x ∈ N :=
  Iff.rfl
#align lie_submodule.mem_coe LieSubmodule.mem_coe

@[simp]
protected theorem zero_mem : (0 : M) ∈ N :=
  zero_mem N
#align lie_submodule.zero_mem LieSubmodule.zero_mem

-- Porting note: @[simp] can prove this
theorem mk_eq_zero {x} (h : x ∈ N) : (⟨x, h⟩ : N) = 0 ↔ x = 0 :=
  Subtype.ext_iff_val
#align lie_submodule.mk_eq_zero LieSubmodule.mk_eq_zero

@[simp]
theorem coe_toSet_mk (S : Set M) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieSubmodule R L M) : Set M) = S :=
  rfl
#align lie_submodule.coe_to_set_mk LieSubmodule.coe_toSet_mk

@[simp]
theorem coe_toSubmodule_mk (p : Submodule R M) (h) :
    (({ p with lie_mem := h } : LieSubmodule R L M) : Submodule R M) = p := by cases p; rfl
                                                                               -- ⊢ ↑{ toSubmodule := { toAddSubmonoid := { toAddSubmonoid := toAddSubmonoid✝, s …
                                                                                        -- 🎉 no goals
#align lie_submodule.coe_to_submodule_mk LieSubmodule.coe_toSubmodule_mk

theorem coeSubmodule_injective :
    Function.Injective (toSubmodule : LieSubmodule R L M → Submodule R M) := fun x y h ↦ by
  cases x; cases y; congr
  -- ⊢ { toSubmodule := toSubmodule✝, lie_mem := lie_mem✝ } = y
           -- ⊢ { toSubmodule := toSubmodule✝¹, lie_mem := lie_mem✝¹ } = { toSubmodule := to …
                    -- 🎉 no goals
#align lie_submodule.coe_submodule_injective LieSubmodule.coeSubmodule_injective

@[ext]
theorem ext (h : ∀ m, m ∈ N ↔ m ∈ N') : N = N' :=
  SetLike.ext h
#align lie_submodule.ext LieSubmodule.ext

@[simp]
theorem coe_toSubmodule_eq_iff : (N : Submodule R M) = (N' : Submodule R M) ↔ N = N' :=
  coeSubmodule_injective.eq_iff
#align lie_submodule.coe_to_submodule_eq_iff LieSubmodule.coe_toSubmodule_eq_iff

/-- Copy of a `LieSubmodule` with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (s : Set M) (hs : s = ↑N) : LieSubmodule R L M where
  carrier := s
  -- Porting note: all the proofs below were in term mode
  zero_mem' := by exact hs.symm ▸ N.zero_mem'
                  -- 🎉 no goals
                     -- ⊢ a✝ + b✝ ∈ ↑N
                                       -- 🎉 no goals
  add_mem' x y := by rw [hs] at x y ⊢; exact N.add_mem' x y
  smul_mem' := by exact hs.symm ▸ N.smul_mem'
                  -- 🎉 no goals
  lie_mem := by exact hs.symm ▸ N.lie_mem
                -- 🎉 no goals
#align lie_submodule.copy LieSubmodule.copy

@[simp]
theorem coe_copy (S : LieSubmodule R L M) (s : Set M) (hs : s = ↑S) : (S.copy s hs : Set M) = s :=
  rfl
#align lie_submodule.coe_copy LieSubmodule.coe_copy

theorem copy_eq (S : LieSubmodule R L M) (s : Set M) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align lie_submodule.copy_eq LieSubmodule.copy_eq

instance : LieRingModule L N where
  bracket (x : L) (m : N) := ⟨⁅x, m.val⁆, N.lie_mem m.property⟩
  add_lie := by intro x y m; apply SetCoe.ext; apply add_lie
                -- ⊢ ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
                             -- ⊢ ↑⁅x + y, m⁆ = ↑(⁅x, m⁆ + ⁅y, m⁆)
                                               -- 🎉 no goals
  lie_add := by intro x m n; apply SetCoe.ext; apply lie_add
                -- ⊢ ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
                             -- ⊢ ↑⁅x, m + n⁆ = ↑(⁅x, m⁆ + ⁅x, n⁆)
                                               -- 🎉 no goals
  leibniz_lie := by intro x y m; apply SetCoe.ext; apply leibniz_lie
                    -- ⊢ ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆
                                 -- ⊢ ↑⁅x, ⁅y, m⁆⁆ = ↑(⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆)
                                                   -- 🎉 no goals

instance module' {S : Type*} [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] :
    Module S N :=
  N.toSubmodule.module'
#align lie_submodule.module' LieSubmodule.module'

instance : Module R N :=
  N.toSubmodule.module

instance {S : Type*} [Semiring S] [SMul S R] [SMul Sᵐᵒᵖ R] [Module S M] [Module Sᵐᵒᵖ M]
    [IsScalarTower S R M] [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] : IsCentralScalar S N :=
  N.toSubmodule.isCentralScalar

instance : LieModule R L N where
  lie_smul := by intro t x y; apply SetCoe.ext; apply lie_smul
                 -- ⊢ ⁅x, t • y⁆ = t • ⁅x, y⁆
                 -- ⊢ ⁅t • x, y⁆ = t • ⁅x, y⁆
                              -- ⊢ ↑⁅t • x, y⁆ = ↑(t • ⁅x, y⁆)
                                                -- 🎉 no goals
                              -- ⊢ ↑⁅x, t • y⁆ = ↑(t • ⁅x, y⁆)
                                                -- 🎉 no goals
  smul_lie := by intro t x y; apply SetCoe.ext; apply smul_lie

@[simp, norm_cast]
theorem coe_zero : ((0 : N) : M) = (0 : M) :=
  rfl
#align lie_submodule.coe_zero LieSubmodule.coe_zero

@[simp, norm_cast]
theorem coe_add (m m' : N) : (↑(m + m') : M) = (m : M) + (m' : M) :=
  rfl
#align lie_submodule.coe_add LieSubmodule.coe_add

@[simp, norm_cast]
theorem coe_neg (m : N) : (↑(-m) : M) = -(m : M) :=
  rfl
#align lie_submodule.coe_neg LieSubmodule.coe_neg

@[simp, norm_cast]
theorem coe_sub (m m' : N) : (↑(m - m') : M) = (m : M) - (m' : M) :=
  rfl
#align lie_submodule.coe_sub LieSubmodule.coe_sub

@[simp, norm_cast]
theorem coe_smul (t : R) (m : N) : (↑(t • m) : M) = t • (m : M) :=
  rfl
#align lie_submodule.coe_smul LieSubmodule.coe_smul

@[simp, norm_cast]
theorem coe_bracket (x : L) (m : N) : (↑⁅x, m⁆ : M) = ⁅x, ↑m⁆ :=
  rfl
#align lie_submodule.coe_bracket LieSubmodule.coe_bracket

end LieSubmodule

section LieIdeal

/-- An ideal of a Lie algebra is a Lie submodule of the Lie algebra as a Lie module over itself. -/
abbrev LieIdeal :=
  LieSubmodule R L L
#align lie_ideal LieIdeal

theorem lie_mem_right (I : LieIdeal R L) (x y : L) (h : y ∈ I) : ⁅x, y⁆ ∈ I :=
  I.lie_mem h
#align lie_mem_right lie_mem_right

theorem lie_mem_left (I : LieIdeal R L) (x y : L) (h : x ∈ I) : ⁅x, y⁆ ∈ I := by
  rw [← lie_skew, ← neg_lie]; apply lie_mem_right; assumption
  -- ⊢ ⁅-y, x⁆ ∈ I
                              -- ⊢ x ∈ I
                                                   -- 🎉 no goals
#align lie_mem_left lie_mem_left

/-- An ideal of a Lie algebra is a Lie subalgebra. -/
-- Porting note: added `@[coe]` to fix `norm_cast` issues, but this causes bad pretty-printing:
-- `(I : LieSubalgebra R L)` becomes `(↑R L I)`
@[coe]
def lieIdealSubalgebra (I : LieIdeal R L) : LieSubalgebra R L :=
  { I.toSubmodule with lie_mem' := by intro x y _ hy; apply lie_mem_right; exact hy }
                                      -- ⊢ ⁅x, y⁆ ∈ { toAddSubmonoid := src✝.toAddSubmonoid, smul_mem' := (_ : ∀ (c : R …
                                                      -- ⊢ y ∈ I
                                                                           -- 🎉 no goals
#align lie_ideal_subalgebra lieIdealSubalgebra

instance : Coe (LieIdeal R L) (LieSubalgebra R L) :=
  ⟨lieIdealSubalgebra R L⟩

@[norm_cast]
theorem LieIdeal.coe_toSubalgebra (I : LieIdeal R L) : ((I : LieSubalgebra R L) : Set L) = I :=
  rfl
#align lie_ideal.coe_to_subalgebra LieIdeal.coe_toSubalgebra

-- Porting note: here and below, used `LieSubmodule.toSubmodule` rather than coercions, because
-- those are treated like `((I : LieSubalgebra R L) : Submodule R L)` instead.
@[norm_cast]
theorem LieIdeal.coe_to_lieSubalgebra_to_submodule (I : LieIdeal R L) :
    ((I : LieSubalgebra R L) : Submodule R L) = LieSubmodule.toSubmodule I :=
  rfl
#align lie_ideal.coe_to_lie_subalgebra_to_submodule LieIdeal.coe_to_lieSubalgebra_to_submodule

/-- An ideal of `L` is a Lie subalgebra of `L`, so it is a Lie ring. -/
instance LieIdeal.lieRing (I : LieIdeal R L) : LieRing I :=
  LieSubalgebra.lieRing R L ↑I
#align lie_ideal.lie_ring LieIdeal.lieRing

/-- Transfer the `LieAlgebra` instance from the coercion `LieIdeal → LieSubalgebra`. -/
instance LieIdeal.lieAlgebra (I : LieIdeal R L) : LieAlgebra R I :=
  LieSubalgebra.lieAlgebra R L ↑I
#align lie_ideal.lie_algebra LieIdeal.lieAlgebra

/-- Transfer the `LieRingModule` instance from the coercion `LieIdeal → LieSubalgebra`. -/
instance LieIdeal.lieRingModule {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (I : LieIdeal R L) [LieRingModule L M] : LieRingModule I M :=
  LieSubalgebra.lieRingModule (I : LieSubalgebra R L)
#align lie_ideal.lie_ring_module LieIdeal.lieRingModule

@[simp]
theorem LieIdeal.coe_bracket_of_module {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (I : LieIdeal R L) [LieRingModule L M] (x : I) (m : M) : ⁅x, m⁆ = ⁅(↑x : L), m⁆ :=
  LieSubalgebra.coe_bracket_of_module (I : LieSubalgebra R L) x m
#align lie_ideal.coe_bracket_of_module LieIdeal.coe_bracket_of_module

/-- Transfer the `LieModule` instance from the coercion `LieIdeal → LieSubalgebra`. -/
instance LieIdeal.lieModule (I : LieIdeal R L) : LieModule R I M :=
  LieSubalgebra.lieModule (I : LieSubalgebra R L)
#align lie_ideal.lie_module LieIdeal.lieModule

end LieIdeal

variable {R M}

theorem Submodule.exists_lieSubmodule_coe_eq_iff (p : Submodule R M) :
    (∃ N : LieSubmodule R L M, ↑N = p) ↔ ∀ (x : L) (m : M), m ∈ p → ⁅x, m⁆ ∈ p := by
  constructor
  -- ⊢ (∃ N, ↑N = p) → ∀ (x : L) (m : M), m ∈ p → ⁅x, m⁆ ∈ p
  · rintro ⟨N, rfl⟩ _ _; exact N.lie_mem
    -- ⊢ m✝ ∈ ↑N → ⁅x✝, m✝⁆ ∈ ↑N
                         -- 🎉 no goals
  · intro h; use { p with lie_mem := @h }
    -- ⊢ ∃ N, ↑N = p
             -- 🎉 no goals
#align submodule.exists_lie_submodule_coe_eq_iff Submodule.exists_lieSubmodule_coe_eq_iff

namespace LieSubalgebra

variable {L}
variable (K : LieSubalgebra R L)

/-- Given a Lie subalgebra `K ⊆ L`, if we view `L` as a `K`-module by restriction, it contains
a distinguished Lie submodule for the action of `K`, namely `K` itself. -/
def toLieSubmodule : LieSubmodule R K L :=
  { (K : Submodule R L) with lie_mem := fun {x _} hy ↦ K.lie_mem x.property hy }
#align lie_subalgebra.to_lie_submodule LieSubalgebra.toLieSubmodule

@[simp]
theorem coe_toLieSubmodule : (K.toLieSubmodule : Submodule R L) = K := rfl
#align lie_subalgebra.coe_to_lie_submodule LieSubalgebra.coe_toLieSubmodule

variable {K}

@[simp]
theorem mem_toLieSubmodule (x : L) : x ∈ K.toLieSubmodule ↔ x ∈ K :=
  Iff.rfl
#align lie_subalgebra.mem_to_lie_submodule LieSubalgebra.mem_toLieSubmodule

theorem exists_lieIdeal_coe_eq_iff :
    (∃ I : LieIdeal R L, ↑I = K) ↔ ∀ x y : L, y ∈ K → ⁅x, y⁆ ∈ K := by
  simp only [← coe_to_submodule_eq_iff, LieIdeal.coe_to_lieSubalgebra_to_submodule,
    Submodule.exists_lieSubmodule_coe_eq_iff L]
  -- Porting note: was `exact Iff.rfl`
  simp only [mem_coe_submodule]
  -- 🎉 no goals
#align lie_subalgebra.exists_lie_ideal_coe_eq_iff LieSubalgebra.exists_lieIdeal_coe_eq_iff

theorem exists_nested_lieIdeal_coe_eq_iff {K' : LieSubalgebra R L} (h : K ≤ K') :
    (∃ I : LieIdeal R K', ↑I = ofLe h) ↔ ∀ x y : L, x ∈ K' → y ∈ K → ⁅x, y⁆ ∈ K := by
  simp only [exists_lieIdeal_coe_eq_iff, coe_bracket, mem_ofLe]
  -- ⊢ (∀ (x y : { x // x ∈ K' }), ↑y ∈ K → ⁅↑x, ↑y⁆ ∈ K) ↔ ∀ (x y : L), x ∈ K' → y …
  constructor
  -- ⊢ (∀ (x y : { x // x ∈ K' }), ↑y ∈ K → ⁅↑x, ↑y⁆ ∈ K) → ∀ (x y : L), x ∈ K' → y …
  · intro h' x y hx hy; exact h' ⟨x, hx⟩ ⟨y, h hy⟩ hy
    -- ⊢ ⁅x, y⁆ ∈ K
                        -- 🎉 no goals
  · rintro h' ⟨x, hx⟩ ⟨y, hy⟩ hy'; exact h' x y hx hy'
    -- ⊢ ⁅↑{ val := x, property := hx }, ↑{ val := y, property := hy }⁆ ∈ K
                                   -- 🎉 no goals
#align lie_subalgebra.exists_nested_lie_ideal_coe_eq_iff LieSubalgebra.exists_nested_lieIdeal_coe_eq_iff

end LieSubalgebra

end LieSubmodule

namespace LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

variable (N N' : LieSubmodule R L M) (I J : LieIdeal R L)

section LatticeStructure

open Set

theorem coe_injective : Function.Injective ((↑) : LieSubmodule R L M → Set M) :=
  SetLike.coe_injective
#align lie_submodule.coe_injective LieSubmodule.coe_injective

@[simp, norm_cast]
theorem coeSubmodule_le_coeSubmodule : (N : Submodule R M) ≤ N' ↔ N ≤ N' :=
  Iff.rfl
#align lie_submodule.coe_submodule_le_coe_submodule LieSubmodule.coeSubmodule_le_coeSubmodule

instance : Bot (LieSubmodule R L M) :=
  ⟨0⟩

@[simp]
theorem bot_coe : ((⊥ : LieSubmodule R L M) : Set M) = {0} :=
  rfl
#align lie_submodule.bot_coe LieSubmodule.bot_coe

@[simp]
theorem bot_coeSubmodule : ((⊥ : LieSubmodule R L M) : Submodule R M) = ⊥ :=
  rfl
#align lie_submodule.bot_coe_submodule LieSubmodule.bot_coeSubmodule

@[simp]
theorem mem_bot (x : M) : x ∈ (⊥ : LieSubmodule R L M) ↔ x = 0 :=
  mem_singleton_iff
#align lie_submodule.mem_bot LieSubmodule.mem_bot

instance : Top (LieSubmodule R L M) :=
  ⟨{ (⊤ : Submodule R M) with lie_mem := fun {x m} _ ↦ mem_univ ⁅x, m⁆ }⟩

@[simp]
theorem top_coe : ((⊤ : LieSubmodule R L M) : Set M) = univ :=
  rfl
#align lie_submodule.top_coe LieSubmodule.top_coe

@[simp]
theorem top_coeSubmodule : ((⊤ : LieSubmodule R L M) : Submodule R M) = ⊤ :=
  rfl
#align lie_submodule.top_coe_submodule LieSubmodule.top_coeSubmodule

@[simp]
theorem mem_top (x : M) : x ∈ (⊤ : LieSubmodule R L M) :=
  mem_univ x
#align lie_submodule.mem_top LieSubmodule.mem_top

instance : Inf (LieSubmodule R L M) :=
  ⟨fun N N' ↦
    { (N ⊓ N' : Submodule R M) with
      lie_mem := fun h ↦ mem_inter (N.lie_mem h.1) (N'.lie_mem h.2) }⟩

instance : InfSet (LieSubmodule R L M) :=
  ⟨fun S ↦
    { sInf {((s : Submodule R M)) | s ∈ S} with
      lie_mem := fun {x m} h ↦ by
        simp only [Submodule.mem_carrier, mem_iInter, Submodule.sInf_coe, mem_setOf_eq,
          forall_apply_eq_imp_iff₂, forall_exists_index, and_imp] at h ⊢
        intro N hN; apply N.lie_mem (h N hN) }⟩
        -- ⊢ ⁅x, m⁆ ∈ ↑↑N
                    -- 🎉 no goals

@[simp]
theorem inf_coe : (↑(N ⊓ N') : Set M) = ↑N ∩ ↑N' :=
  rfl
#align lie_submodule.inf_coe LieSubmodule.inf_coe

@[simp]
theorem sInf_coe_toSubmodule (S : Set (LieSubmodule R L M)) :
    (↑(sInf S) : Submodule R M) = sInf {((s : Submodule R M)) | s ∈ S} :=
  rfl
#align lie_submodule.Inf_coe_to_submodule LieSubmodule.sInf_coe_toSubmodule

@[simp]
theorem sInf_coe (S : Set (LieSubmodule R L M)) : (↑(sInf S) : Set M) = ⋂ s ∈ S, (s : Set M) := by
  rw [← LieSubmodule.coe_toSubmodule, sInf_coe_toSubmodule, Submodule.sInf_coe]
  -- ⊢ ⋂ (p : Submodule R M) (_ : p ∈ {x | ∃ s, s ∈ S ∧ ↑s = x}), ↑p = ⋂ (s : LieSu …
  ext m
  -- ⊢ m ∈ ⋂ (p : Submodule R M) (_ : p ∈ {x | ∃ s, s ∈ S ∧ ↑s = x}), ↑p ↔ m ∈ ⋂ (s …
  simp only [mem_iInter, mem_setOf_eq, forall_apply_eq_imp_iff₂, exists_imp,
    and_imp, SetLike.mem_coe, mem_coeSubmodule]
#align lie_submodule.Inf_coe LieSubmodule.sInf_coe

theorem sInf_glb (S : Set (LieSubmodule R L M)) : IsGLB S (sInf S) := by
  have h : ∀ {N N' : LieSubmodule R L M}, (N : Set M) ≤ N' ↔ N ≤ N' := fun {_ _} ↦ Iff.rfl
  -- ⊢ IsGLB S (sInf S)
  apply IsGLB.of_image h
  -- ⊢ IsGLB ((fun {x} => ↑x) '' S) ↑(sInf S)
  simp only [sInf_coe]
  -- ⊢ IsGLB ((fun {x} => ↑x) '' S) (⋂ (s : LieSubmodule R L M) (_ : s ∈ S), ↑s)
  exact isGLB_biInf
  -- 🎉 no goals
#align lie_submodule.Inf_glb LieSubmodule.sInf_glb

/-- The set of Lie submodules of a Lie module form a complete lattice.

We provide explicit values for the fields `bot`, `top`, `inf` to get more convenient definitions
than we would otherwise obtain from `completeLatticeOfInf`. -/
instance : CompleteLattice (LieSubmodule R L M) :=
  { SetLike.instPartialOrder,
    completeLatticeOfInf _ sInf_glb with
    le := (· ≤ ·)
    lt := (· < ·)
    bot := ⊥
    bot_le := fun N _ h ↦ by rw [mem_bot] at h; rw [h]; exact N.zero_mem'
                             -- ⊢ x✝ ∈ N
                                                -- ⊢ 0 ∈ N
                                                        -- 🎉 no goals
    top := ⊤
    le_top := fun _ _ _ ↦ trivial
    inf := (· ⊓ ·)
    le_inf := fun N₁ N₂ N₃ h₁₂ h₁₃ m hm ↦ ⟨h₁₂ hm, h₁₃ hm⟩
    inf_le_left := fun _ _ _ ↦ And.left
    inf_le_right := fun _ _ _ ↦ And.right }

instance : AddCommMonoid (LieSubmodule R L M) where
  add := (· ⊔ ·)
  add_assoc _ _ _ := sup_assoc
  zero := ⊥
  zero_add _ := bot_sup_eq
  add_zero _ := sup_bot_eq
  add_comm _ _ := sup_comm

@[simp]
theorem add_eq_sup : N + N' = N ⊔ N' :=
  rfl
#align lie_submodule.add_eq_sup LieSubmodule.add_eq_sup

@[norm_cast, simp]
theorem sup_coe_toSubmodule :
    (↑(N ⊔ N') : Submodule R M) = (N : Submodule R M) ⊔ (N' : Submodule R M) := by
  have aux : ∀ {x : L} {m}, m ∈ (N ⊔ N' : Submodule R M) → ⁅x, m⁆ ∈ (N ⊔ N' : Submodule R M) := by
    simp only [Submodule.mem_sup]
    rintro x m ⟨y, hy, z, hz, rfl⟩
    refine' ⟨⁅x, y⁆, N.lie_mem hy, ⁅x, z⁆, N'.lie_mem hz, (lie_add _ _ _).symm⟩
  refine' le_antisymm (sInf_le ⟨{ (N ⊔ N' : Submodule R M) with lie_mem := aux }, _⟩) _
  -- ⊢ (let src := ↑N ⊔ ↑N';
  -- Porting note: rewrote proof
  · simp only [← coeSubmodule_le_coeSubmodule, mem_setOf_eq, and_true_iff]
    -- ⊢ ↑N ≤ { toAddSubmonoid := (↑N ⊔ ↑N').toAddSubmonoid, smul_mem' := (_ : ∀ (c : …
    constructor <;> intro x hx <;> simp [Submodule.mem_sup_left hx, hx, Submodule.mem_sup_right hx]
    -- ⊢ ↑N ≤ { toAddSubmonoid := (↑N ⊔ ↑N').toAddSubmonoid, smul_mem' := (_ : ∀ (c : …
                    -- ⊢ x ∈ { toAddSubmonoid := (↑N ⊔ ↑N').toAddSubmonoid, smul_mem' := (_ : ∀ (c :  …
                    -- ⊢ x ∈ { toAddSubmonoid := (↑N ⊔ ↑N').toAddSubmonoid, smul_mem' := (_ : ∀ (c :  …
                                   -- 🎉 no goals
                                   -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align lie_submodule.sup_coe_to_submodule LieSubmodule.sup_coe_toSubmodule

@[norm_cast, simp]
theorem inf_coe_toSubmodule :
    (↑(N ⊓ N') : Submodule R M) = (N : Submodule R M) ⊓ (N' : Submodule R M) :=
  rfl
#align lie_submodule.inf_coe_to_submodule LieSubmodule.inf_coe_toSubmodule

@[simp]
theorem mem_inf (x : M) : x ∈ N ⊓ N' ↔ x ∈ N ∧ x ∈ N' := by
  rw [← mem_coeSubmodule, ← mem_coeSubmodule, ← mem_coeSubmodule, inf_coe_toSubmodule,
    Submodule.mem_inf]
#align lie_submodule.mem_inf LieSubmodule.mem_inf

theorem mem_sup (x : M) : x ∈ N ⊔ N' ↔ ∃ y ∈ N, ∃ z ∈ N', y + z = x := by
  rw [← mem_coeSubmodule, sup_coe_toSubmodule, Submodule.mem_sup]; exact Iff.rfl
  -- ⊢ (∃ y, y ∈ ↑N ∧ ∃ z, z ∈ ↑N' ∧ y + z = x) ↔ ∃ y, y ∈ N ∧ ∃ z, z ∈ N' ∧ y + z  …
                                                                   -- 🎉 no goals
#align lie_submodule.mem_sup LieSubmodule.mem_sup

nonrec theorem eq_bot_iff : N = ⊥ ↔ ∀ m : M, m ∈ N → m = 0 := by rw [eq_bot_iff]; exact Iff.rfl
                                                                 -- ⊢ N ≤ ⊥ ↔ ∀ (m : M), m ∈ N → m = 0
                                                                                  -- 🎉 no goals
#align lie_submodule.eq_bot_iff LieSubmodule.eq_bot_iff

instance subsingleton_of_bot : Subsingleton (LieSubmodule R L ↑(⊥ : LieSubmodule R L M)) := by
  apply subsingleton_of_bot_eq_top
  -- ⊢ ⊥ = ⊤
  ext ⟨x, hx⟩; change x ∈ ⊥ at hx; rw [Submodule.mem_bot] at hx; subst hx
  -- ⊢ { val := x, property := hx } ∈ ⊥ ↔ { val := x, property := hx } ∈ ⊤
               -- ⊢ { val := x, property := hx } ∈ ⊥ ↔ { val := x, property := hx } ∈ ⊤
                                   -- ⊢ { val := x, property := hx✝ } ∈ ⊥ ↔ { val := x, property := hx✝ } ∈ ⊤
                                                                 -- ⊢ { val := 0, property := hx } ∈ ⊥ ↔ { val := 0, property := hx } ∈ ⊤
  simp only [true_iff_iff, eq_self_iff_true, Submodule.mk_eq_zero, LieSubmodule.mem_bot, mem_top]
  -- 🎉 no goals
#align lie_submodule.subsingleton_of_bot LieSubmodule.subsingleton_of_bot

instance : IsModularLattice (LieSubmodule R L M) where
  sup_inf_le_assoc_of_le _ _ := by
    simp only [← coeSubmodule_le_coeSubmodule, sup_coe_toSubmodule, inf_coe_toSubmodule]
    -- ⊢ ↑x✝² ≤ ↑x✝ → (↑x✝² ⊔ ↑x✝¹) ⊓ ↑x✝ ≤ ↑x✝² ⊔ ↑x✝¹ ⊓ ↑x✝
    exact IsModularLattice.sup_inf_le_assoc_of_le _
    -- 🎉 no goals

variable (R L M)

theorem wellFounded_of_noetherian [IsNoetherian R M] :
    WellFounded ((· > ·) : LieSubmodule R L M → LieSubmodule R L M → Prop) :=
  let f :
    ((· > ·) : LieSubmodule R L M → LieSubmodule R L M → Prop) →r
      ((· > ·) : Submodule R M → Submodule R M → Prop) :=
    { toFun := (↑)
      map_rel' := fun h ↦ h }
  RelHomClass.wellFounded f (isNoetherian_iff_wellFounded.mp inferInstance)
#align lie_submodule.well_founded_of_noetherian LieSubmodule.wellFounded_of_noetherian

@[simp]
theorem subsingleton_iff : Subsingleton (LieSubmodule R L M) ↔ Subsingleton M :=
  have h : Subsingleton (LieSubmodule R L M) ↔ Subsingleton (Submodule R M) := by
    rw [← subsingleton_iff_bot_eq_top, ← subsingleton_iff_bot_eq_top, ← coe_toSubmodule_eq_iff,
      top_coeSubmodule, bot_coeSubmodule]
  h.trans <| Submodule.subsingleton_iff R
#align lie_submodule.subsingleton_iff LieSubmodule.subsingleton_iff

@[simp]
theorem nontrivial_iff : Nontrivial (LieSubmodule R L M) ↔ Nontrivial M :=
  not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans <| subsingleton_iff R L M).trans
      not_nontrivial_iff_subsingleton.symm)
#align lie_submodule.nontrivial_iff LieSubmodule.nontrivial_iff

instance [Nontrivial M] : Nontrivial (LieSubmodule R L M) :=
  (nontrivial_iff R L M).mpr ‹_›

theorem nontrivial_iff_ne_bot {N : LieSubmodule R L M} : Nontrivial N ↔ N ≠ ⊥ := by
  constructor <;> contrapose!
  -- ⊢ Nontrivial { x // x ∈ ↑N } → N ≠ ⊥
                  -- ⊢ N = ⊥ → ¬Nontrivial { x // x ∈ ↑N }
                  -- ⊢ ¬Nontrivial { x // x ∈ ↑N } → N = ⊥
  · rintro rfl
      ⟨⟨m₁, h₁ : m₁ ∈ (⊥ : LieSubmodule R L M)⟩, ⟨m₂, h₂ : m₂ ∈ (⊥ : LieSubmodule R L M)⟩, h₁₂⟩
    simp [(LieSubmodule.mem_bot _).mp h₁, (LieSubmodule.mem_bot _).mp h₂] at h₁₂
    -- 🎉 no goals
  · rw [not_nontrivial_iff_subsingleton, LieSubmodule.eq_bot_iff]
    -- ⊢ Subsingleton { x // x ∈ ↑N } → ∀ (m : M), m ∈ N → m = 0
    rintro ⟨h⟩ m hm
    -- ⊢ m = 0
    simpa using h ⟨m, hm⟩ ⟨_, N.zero_mem⟩
    -- 🎉 no goals
#align lie_submodule.nontrivial_iff_ne_bot LieSubmodule.nontrivial_iff_ne_bot

variable {R L M}

section InclusionMaps

/-- The inclusion of a Lie submodule into its ambient space is a morphism of Lie modules. -/
def incl : N →ₗ⁅R,L⁆ M :=
  { Submodule.subtype (N : Submodule R M) with map_lie' := fun {_ _} ↦ rfl }
#align lie_submodule.incl LieSubmodule.incl

@[simp]
theorem incl_coe : (N.incl : N →ₗ[R] M) = (N : Submodule R M).subtype :=
  rfl
#align lie_submodule.incl_coe LieSubmodule.incl_coe

@[simp]
theorem incl_apply (m : N) : N.incl m = m :=
  rfl
#align lie_submodule.incl_apply LieSubmodule.incl_apply

theorem incl_eq_val : (N.incl : N → M) = Subtype.val :=
  rfl
#align lie_submodule.incl_eq_val LieSubmodule.incl_eq_val

variable {N N'} (h : N ≤ N')

/-- Given two nested Lie submodules `N ⊆ N'`, the inclusion `N ↪ N'` is a morphism of Lie modules.-/
def homOfLe : N →ₗ⁅R,L⁆ N' :=
  { Submodule.ofLe (show N.toSubmodule ≤ N'.toSubmodule from h) with map_lie' := fun {_ _} ↦ rfl }
#align lie_submodule.hom_of_le LieSubmodule.homOfLe

@[simp]
theorem coe_homOfLe (m : N) : (homOfLe h m : M) = m :=
  rfl
#align lie_submodule.coe_hom_of_le LieSubmodule.coe_homOfLe

theorem homOfLe_apply (m : N) : homOfLe h m = ⟨m.1, h m.2⟩ :=
  rfl
#align lie_submodule.hom_of_le_apply LieSubmodule.homOfLe_apply

theorem homOfLe_injective : Function.Injective (homOfLe h) := fun x y ↦ by
  simp only [homOfLe_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe]
  -- 🎉 no goals
#align lie_submodule.hom_of_le_injective LieSubmodule.homOfLe_injective

end InclusionMaps

section LieSpan

variable (R L) (s : Set M)

/-- The `lieSpan` of a set `s ⊆ M` is the smallest Lie submodule of `M` that contains `s`. -/
def lieSpan : LieSubmodule R L M :=
  sInf { N | s ⊆ N }
#align lie_submodule.lie_span LieSubmodule.lieSpan

variable {R L s}

theorem mem_lieSpan {x : M} : x ∈ lieSpan R L s ↔ ∀ N : LieSubmodule R L M, s ⊆ N → x ∈ N := by
  change x ∈ (lieSpan R L s : Set M) ↔ _; erw [sInf_coe]; exact mem_iInter₂
  -- ⊢ x ∈ ↑(lieSpan R L s) ↔ ∀ (N : LieSubmodule R L M), s ⊆ ↑N → x ∈ N
                                          -- ⊢ x ∈ ⋂ (s_1 : LieSubmodule R L M) (_ : s_1 ∈ {N | s ⊆ ↑N}), ↑s_1 ↔ ∀ (N : Lie …
                                                          -- 🎉 no goals
#align lie_submodule.mem_lie_span LieSubmodule.mem_lieSpan

theorem subset_lieSpan : s ⊆ lieSpan R L s := by
  intro m hm
  -- ⊢ m ∈ ↑(lieSpan R L s)
  erw [mem_lieSpan]
  -- ⊢ ∀ (N : LieSubmodule R L M), s ⊆ ↑N → m ∈ N
  intro N hN
  -- ⊢ m ∈ N
  exact hN hm
  -- 🎉 no goals
#align lie_submodule.subset_lie_span LieSubmodule.subset_lieSpan

theorem submodule_span_le_lieSpan : Submodule.span R s ≤ lieSpan R L s := by
  rw [Submodule.span_le]
  -- ⊢ s ⊆ ↑↑(lieSpan R L s)
  apply subset_lieSpan
  -- 🎉 no goals
#align lie_submodule.submodule_span_le_lie_span LieSubmodule.submodule_span_le_lieSpan

theorem lieSpan_le {N} : lieSpan R L s ≤ N ↔ s ⊆ N := by
  constructor
  -- ⊢ lieSpan R L s ≤ N → s ⊆ ↑N
  · exact Subset.trans subset_lieSpan
    -- 🎉 no goals
  · intro hs m hm; rw [mem_lieSpan] at hm; exact hm _ hs
    -- ⊢ m ∈ N
                   -- ⊢ m ∈ N
                                           -- 🎉 no goals
#align lie_submodule.lie_span_le LieSubmodule.lieSpan_le

theorem lieSpan_mono {t : Set M} (h : s ⊆ t) : lieSpan R L s ≤ lieSpan R L t := by
  rw [lieSpan_le]
  -- ⊢ s ⊆ ↑(lieSpan R L t)
  exact Subset.trans h subset_lieSpan
  -- 🎉 no goals
#align lie_submodule.lie_span_mono LieSubmodule.lieSpan_mono

theorem lieSpan_eq : lieSpan R L (N : Set M) = N :=
  le_antisymm (lieSpan_le.mpr rfl.subset) subset_lieSpan
#align lie_submodule.lie_span_eq LieSubmodule.lieSpan_eq

theorem coe_lieSpan_submodule_eq_iff {p : Submodule R M} :
    (lieSpan R L (p : Set M) : Submodule R M) = p ↔ ∃ N : LieSubmodule R L M, ↑N = p := by
  rw [p.exists_lieSubmodule_coe_eq_iff L]; constructor <;> intro h
  -- ⊢ ↑(lieSpan R L ↑p) = p ↔ ∀ (x : L) (m : M), m ∈ p → ⁅x, m⁆ ∈ p
                                           -- ⊢ ↑(lieSpan R L ↑p) = p → ∀ (x : L) (m : M), m ∈ p → ⁅x, m⁆ ∈ p
                                                           -- ⊢ ∀ (x : L) (m : M), m ∈ p → ⁅x, m⁆ ∈ p
                                                           -- ⊢ ↑(lieSpan R L ↑p) = p
  · intro x m hm; rw [← h, mem_coeSubmodule]; exact lie_mem _ (subset_lieSpan hm)
    -- ⊢ ⁅x, m⁆ ∈ p
                  -- ⊢ ⁅x, m⁆ ∈ lieSpan R L ↑p
                                              -- 🎉 no goals
  · rw [← coe_toSubmodule_mk p @h, coe_toSubmodule, coe_toSubmodule_eq_iff, lieSpan_eq]
    -- 🎉 no goals
#align lie_submodule.coe_lie_span_submodule_eq_iff LieSubmodule.coe_lieSpan_submodule_eq_iff

variable (R L M)

/-- `lieSpan` forms a Galois insertion with the coercion from `LieSubmodule` to `Set`. -/
protected def gi : GaloisInsertion (lieSpan R L : Set M → LieSubmodule R L M) (↑) where
  choice s _ := lieSpan R L s
  gc _ _ := lieSpan_le
  le_l_u _ := subset_lieSpan
  choice_eq _ _ := rfl
#align lie_submodule.gi LieSubmodule.gi

@[simp]
theorem span_empty : lieSpan R L (∅ : Set M) = ⊥ :=
  (LieSubmodule.gi R L M).gc.l_bot
#align lie_submodule.span_empty LieSubmodule.span_empty

@[simp]
theorem span_univ : lieSpan R L (Set.univ : Set M) = ⊤ :=
  eq_top_iff.2 <| SetLike.le_def.2 <| subset_lieSpan
#align lie_submodule.span_univ LieSubmodule.span_univ

theorem lieSpan_eq_bot_iff : lieSpan R L s = ⊥ ↔ ∀ m ∈ s, m = (0 : M) := by
  rw [_root_.eq_bot_iff, lieSpan_le, bot_coe, subset_singleton_iff]
  -- 🎉 no goals
#align lie_submodule.lie_span_eq_bot_iff LieSubmodule.lieSpan_eq_bot_iff

variable {M}

theorem span_union (s t : Set M) : lieSpan R L (s ∪ t) = lieSpan R L s ⊔ lieSpan R L t :=
  (LieSubmodule.gi R L M).gc.l_sup
#align lie_submodule.span_union LieSubmodule.span_union

theorem span_iUnion {ι} (s : ι → Set M) : lieSpan R L (⋃ i, s i) = ⨆ i, lieSpan R L (s i) :=
  (LieSubmodule.gi R L M).gc.l_iSup
#align lie_submodule.span_Union LieSubmodule.span_iUnion

end LieSpan

end LatticeStructure

end LieSubmodule

section LieSubmoduleMapAndComap

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']

namespace LieSubmodule

variable (f : M →ₗ⁅R,L⁆ M') (N N₂ : LieSubmodule R L M) (N' : LieSubmodule R L M')

/-- A morphism of Lie modules `f : M → M'` pushes forward Lie submodules of `M` to Lie submodules
of `M'`. -/
def map : LieSubmodule R L M' :=
  { (N : Submodule R M).map (f : M →ₗ[R] M') with
    lie_mem := fun {x m'} h ↦ by
      rcases h with ⟨m, hm, hfm⟩; use ⁅x, m⁆; constructor
      -- ⊢ ⁅x, m'⁆ ∈ { toAddSubmonoid := src✝.toAddSubmonoid, smul_mem' := (_ : ∀ (c :  …
                                  -- ⊢ ⁅x, m⁆ ∈ ↑↑N ∧ ↑↑f ⁅x, m⁆ = ⁅x, m'⁆
                                              -- ⊢ ⁅x, m⁆ ∈ ↑↑N
      · apply N.lie_mem hm
        -- 🎉 no goals
      · norm_cast at hfm; simp [hfm] }
        -- ⊢ ↑↑f ⁅x, m⁆ = ⁅x, m'⁆
                          -- 🎉 no goals
#align lie_submodule.map LieSubmodule.map

@[simp]
theorem coeSubmodule_map : (N.map f : Submodule R M') = (N : Submodule R M).map (f : M →ₗ[R] M') :=
  rfl
#align lie_submodule.coe_submodule_map LieSubmodule.coeSubmodule_map

/-- A morphism of Lie modules `f : M → M'` pulls back Lie submodules of `M'` to Lie submodules of
`M`. -/
def comap : LieSubmodule R L M :=
  { (N' : Submodule R M').comap (f : M →ₗ[R] M') with
    lie_mem := fun {x m} h ↦ by
      suffices ⁅x, f m⁆ ∈ N' by simp [this]
      -- ⊢ ⁅x, ↑f m⁆ ∈ N'
      apply N'.lie_mem h }
      -- 🎉 no goals
#align lie_submodule.comap LieSubmodule.comap

@[simp]
theorem coeSubmodule_comap :
    (N'.comap f : Submodule R M) = (N' : Submodule R M').comap (f : M →ₗ[R] M') :=
  rfl
#align lie_submodule.coe_submodule_comap LieSubmodule.coeSubmodule_comap

variable {f N N₂ N'}

theorem map_le_iff_le_comap : map f N ≤ N' ↔ N ≤ comap f N' :=
  Set.image_subset_iff
#align lie_submodule.map_le_iff_le_comap LieSubmodule.map_le_iff_le_comap

variable (f)

theorem gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ ↦ map_le_iff_le_comap
#align lie_submodule.gc_map_comap LieSubmodule.gc_map_comap

variable {f}

@[simp]
theorem map_sup : (N ⊔ N₂).map f = N.map f ⊔ N₂.map f :=
  (gc_map_comap f).l_sup
#align lie_submodule.map_sup LieSubmodule.map_sup

@[simp]
theorem mem_map (m' : M') : m' ∈ N.map f ↔ ∃ m, m ∈ N ∧ f m = m' :=
  Submodule.mem_map
#align lie_submodule.mem_map LieSubmodule.mem_map

@[simp]
theorem mem_comap {m : M} : m ∈ comap f N' ↔ f m ∈ N' :=
  Iff.rfl
#align lie_submodule.mem_comap LieSubmodule.mem_comap

theorem comap_incl_eq_top : N₂.comap N.incl = ⊤ ↔ N ≤ N₂ := by
  rw [← LieSubmodule.coe_toSubmodule_eq_iff, LieSubmodule.coeSubmodule_comap, LieSubmodule.incl_coe,
    LieSubmodule.top_coeSubmodule, Submodule.comap_subtype_eq_top, coeSubmodule_le_coeSubmodule]
#align lie_submodule.comap_incl_eq_top LieSubmodule.comap_incl_eq_top

theorem comap_incl_eq_bot : N₂.comap N.incl = ⊥ ↔ N ⊓ N₂ = ⊥ := by
  simp only [← LieSubmodule.coe_toSubmodule_eq_iff, LieSubmodule.coeSubmodule_comap,
    LieSubmodule.incl_coe, LieSubmodule.bot_coeSubmodule, ← Submodule.disjoint_iff_comap_eq_bot,
    disjoint_iff, inf_coe_toSubmodule]
#align lie_submodule.comap_incl_eq_bot LieSubmodule.comap_incl_eq_bot

end LieSubmodule

namespace LieIdeal

variable (f : L →ₗ⁅R⁆ L') (I I₂ : LieIdeal R L) (J : LieIdeal R L')

@[simp]
theorem top_coe_lieSubalgebra : ((⊤ : LieIdeal R L) : LieSubalgebra R L) = ⊤ :=
  rfl
#align lie_ideal.top_coe_lie_subalgebra LieIdeal.top_coe_lieSubalgebra

/-- A morphism of Lie algebras `f : L → L'` pushes forward Lie ideals of `L` to Lie ideals of `L'`.

Note that unlike `LieSubmodule.map`, we must take the `lieSpan` of the image. Mathematically
this is because although `f` makes `L'` into a Lie module over `L`, in general the `L` submodules of
`L'` are not the same as the ideals of `L'`. -/
def map : LieIdeal R L' :=
  LieSubmodule.lieSpan R L' <| (I : Submodule R L).map (f : L →ₗ[R] L')
#align lie_ideal.map LieIdeal.map

/-- A morphism of Lie algebras `f : L → L'` pulls back Lie ideals of `L'` to Lie ideals of `L`.

Note that `f` makes `L'` into a Lie module over `L` (turning `f` into a morphism of Lie modules)
and so this is a special case of `LieSubmodule.comap` but we do not exploit this fact. -/
def comap : LieIdeal R L :=
  { (J : Submodule R L').comap (f : L →ₗ[R] L') with
    lie_mem := fun {x y} h ↦ by
      suffices ⁅f x, f y⁆ ∈ J by
        simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
          Submodule.mem_toAddSubmonoid, Submodule.mem_comap, LieHom.coe_toLinearMap, LieHom.map_lie,
          LieSubalgebra.mem_coe_submodule]
        exact this
      apply J.lie_mem h }
      -- 🎉 no goals
#align lie_ideal.comap LieIdeal.comap

@[simp]
theorem map_coeSubmodule (h : ↑(map f I) = f '' I) :
    LieSubmodule.toSubmodule (map f I) = (LieSubmodule.toSubmodule I).map (f : L →ₗ[R] L') := by
  rw [SetLike.ext'_iff, LieSubmodule.coe_toSubmodule, h, Submodule.map_coe]; rfl
  -- ⊢ ↑f '' ↑I = ↑↑f '' ↑↑I
                                                                             -- 🎉 no goals
#align lie_ideal.map_coe_submodule LieIdeal.map_coeSubmodule

@[simp]
theorem comap_coeSubmodule :
    (LieSubmodule.toSubmodule (comap f J)) = (LieSubmodule.toSubmodule J).comap (f : L →ₗ[R] L') :=
  rfl
#align lie_ideal.comap_coe_submodule LieIdeal.comap_coeSubmodule

theorem map_le : map f I ≤ J ↔ f '' I ⊆ J :=
  LieSubmodule.lieSpan_le
#align lie_ideal.map_le LieIdeal.map_le

variable {f I I₂ J}

theorem mem_map {x : L} (hx : x ∈ I) : f x ∈ map f I := by
  apply LieSubmodule.subset_lieSpan
  -- ⊢ ↑f x ∈ ↑(Submodule.map (↑f) (↑R L I).toSubmodule)
  use x
  -- ⊢ x ∈ ↑(↑R L I).toSubmodule ∧ ↑↑f x = ↑f x
  exact ⟨hx, rfl⟩
  -- 🎉 no goals
#align lie_ideal.mem_map LieIdeal.mem_map

@[simp]
theorem mem_comap {x : L} : x ∈ comap f J ↔ f x ∈ J :=
  Iff.rfl
#align lie_ideal.mem_comap LieIdeal.mem_comap

theorem map_le_iff_le_comap : map f I ≤ J ↔ I ≤ comap f J := by
  rw [map_le]
  -- ⊢ ↑f '' ↑I ⊆ ↑J ↔ I ≤ comap f J
  exact Set.image_subset_iff
  -- 🎉 no goals
#align lie_ideal.map_le_iff_le_comap LieIdeal.map_le_iff_le_comap

variable (f)

theorem gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ ↦ map_le_iff_le_comap
#align lie_ideal.gc_map_comap LieIdeal.gc_map_comap

variable {f}

@[simp]
theorem map_sup : (I ⊔ I₂).map f = I.map f ⊔ I₂.map f :=
  (gc_map_comap f).l_sup
#align lie_ideal.map_sup LieIdeal.map_sup

theorem map_comap_le : map f (comap f J) ≤ J := by rw [map_le_iff_le_comap]
                                                   -- 🎉 no goals
#align lie_ideal.map_comap_le LieIdeal.map_comap_le

/-- See also `LieIdeal.map_comap_eq`. -/
theorem comap_map_le : I ≤ comap f (map f I) := by rw [← map_le_iff_le_comap]
                                                   -- 🎉 no goals
#align lie_ideal.comap_map_le LieIdeal.comap_map_le

@[mono]
theorem map_mono : Monotone (map f) := fun I₁ I₂ h ↦ by
  rw [SetLike.le_def] at h
  -- ⊢ map f I₁ ≤ map f I₂
  apply LieSubmodule.lieSpan_mono (Set.image_subset (⇑f) h)
  -- 🎉 no goals
#align lie_ideal.map_mono LieIdeal.map_mono

@[mono]
theorem comap_mono : Monotone (comap f) := fun J₁ J₂ h ↦ by
  rw [← SetLike.coe_subset_coe] at h ⊢
  -- ⊢ ↑(comap f J₁) ⊆ ↑(comap f J₂)
  dsimp only [SetLike.coe]
  -- ⊢ (↑(comap f J₁)).toAddSubmonoid.toAddSubsemigroup.carrier ⊆ (↑(comap f J₂)).t …
  exact Set.preimage_mono h
  -- 🎉 no goals
#align lie_ideal.comap_mono LieIdeal.comap_mono

theorem map_of_image (h : f '' I = J) : I.map f = J := by
  apply le_antisymm
  -- ⊢ map f I ≤ J
  · erw [LieSubmodule.lieSpan_le, Submodule.map_coe, h]
    -- 🎉 no goals
  · rw [← SetLike.coe_subset_coe, ← h]; exact LieSubmodule.subset_lieSpan
    -- ⊢ ↑f '' ↑I ⊆ ↑(map f I)
                                        -- 🎉 no goals
#align lie_ideal.map_of_image LieIdeal.map_of_image

/-- Note that this is not a special case of `LieSubmodule.subsingleton_of_bot`. Indeed, given
`I : LieIdeal R L`, in general the two lattices `LieIdeal R I` and `LieSubmodule R L I` are
different (though the latter does naturally inject into the former).

In other words, in general, ideals of `I`, regarded as a Lie algebra in its own right, are not the
same as ideals of `L` contained in `I`. -/
instance subsingleton_of_bot : Subsingleton (LieIdeal R (⊥ : LieIdeal R L)) := by
  apply subsingleton_of_bot_eq_top
  -- ⊢ ⊥ = ⊤
  ext ⟨x, hx⟩
  -- ⊢ { val := x, property := hx } ∈ ⊥ ↔ { val := x, property := hx } ∈ ⊤
  rw [LieSubmodule.bot_coeSubmodule, Submodule.mem_bot] at hx
  -- ⊢ { val := x, property := hx✝ } ∈ ⊥ ↔ { val := x, property := hx✝ } ∈ ⊤
  subst hx
  -- ⊢ { val := 0, property := hx } ∈ ⊥ ↔ { val := 0, property := hx } ∈ ⊤
  simp only [Submodule.mk_eq_zero, LieSubmodule.mem_bot, LieSubmodule.mem_top]
  -- 🎉 no goals
#align lie_ideal.subsingleton_of_bot LieIdeal.subsingleton_of_bot

end LieIdeal

namespace LieHom

variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

/-- The kernel of a morphism of Lie algebras, as an ideal in the domain. -/
def ker : LieIdeal R L :=
  LieIdeal.comap f ⊥
#align lie_hom.ker LieHom.ker

/-- The range of a morphism of Lie algebras as an ideal in the codomain. -/
def idealRange : LieIdeal R L' :=
  LieSubmodule.lieSpan R L' f.range
#align lie_hom.ideal_range LieHom.idealRange

theorem idealRange_eq_lieSpan_range : f.idealRange = LieSubmodule.lieSpan R L' f.range :=
  rfl
#align lie_hom.ideal_range_eq_lie_span_range LieHom.idealRange_eq_lieSpan_range

theorem idealRange_eq_map : f.idealRange = LieIdeal.map f ⊤ := by
  ext
  -- ⊢ m✝ ∈ idealRange f ↔ m✝ ∈ LieIdeal.map f ⊤
  simp only [idealRange, range_eq_map]
  -- ⊢ m✝ ∈ LieSubmodule.lieSpan R L' ↑(LieSubalgebra.map f ⊤) ↔ m✝ ∈ LieIdeal.map  …
  rfl
  -- 🎉 no goals
#align lie_hom.ideal_range_eq_map LieHom.idealRange_eq_map

/-- The condition that the image of a morphism of Lie algebras is an ideal. -/
def IsIdealMorphism : Prop :=
  (f.idealRange : LieSubalgebra R L') = f.range
#align lie_hom.is_ideal_morphism LieHom.IsIdealMorphism

@[simp]
theorem isIdealMorphism_def : f.IsIdealMorphism ↔ (f.idealRange : LieSubalgebra R L') = f.range :=
  Iff.rfl
#align lie_hom.is_ideal_morphism_def LieHom.isIdealMorphism_def

theorem isIdealMorphism_iff : f.IsIdealMorphism ↔ ∀ (x : L') (y : L), ∃ z : L, ⁅x, f y⁆ = f z := by
  simp only [isIdealMorphism_def, idealRange_eq_lieSpan_range, ←
    LieSubalgebra.coe_to_submodule_eq_iff, ← f.range.coe_to_submodule,
    LieIdeal.coe_to_lieSubalgebra_to_submodule, LieSubmodule.coe_lieSpan_submodule_eq_iff,
    LieSubalgebra.mem_coe_submodule, mem_range, exists_imp,
    Submodule.exists_lieSubmodule_coe_eq_iff]
  constructor
  -- ⊢ (∀ (x m : L') (x_1 : L), ↑f x_1 = m → ∃ y, ↑f y = ⁅x, m⁆) → ∀ (x : L') (y :  …
  · intro h x y; obtain ⟨z, hz⟩ := h x (f y) y rfl; use z; exact hz.symm
    -- ⊢ ∃ z, ⁅x, ↑f y⁆ = ↑f z
                 -- ⊢ ∃ z, ⁅x, ↑f y⁆ = ↑f z
                                                    -- ⊢ ⁅x, ↑f y⁆ = ↑f z
                                                           -- 🎉 no goals
  · intro h x y z hz; obtain ⟨w, hw⟩ := h x z; use w; rw [← hw, hz]
    -- ⊢ ∃ y_1, ↑f y_1 = ⁅x, y⁆
                      -- ⊢ ∃ y_1, ↑f y_1 = ⁅x, y⁆
                                               -- ⊢ ↑f w = ⁅x, y⁆
                                                      -- 🎉 no goals
#align lie_hom.is_ideal_morphism_iff LieHom.isIdealMorphism_iff

theorem range_subset_idealRange : (f.range : Set L') ⊆ f.idealRange :=
  LieSubmodule.subset_lieSpan
#align lie_hom.range_subset_ideal_range LieHom.range_subset_idealRange

theorem map_le_idealRange : I.map f ≤ f.idealRange := by
  rw [f.idealRange_eq_map]
  -- ⊢ LieIdeal.map f I ≤ LieIdeal.map f ⊤
  exact LieIdeal.map_mono le_top
  -- 🎉 no goals
#align lie_hom.map_le_ideal_range LieHom.map_le_idealRange

theorem ker_le_comap : f.ker ≤ J.comap f :=
  LieIdeal.comap_mono bot_le
#align lie_hom.ker_le_comap LieHom.ker_le_comap

@[simp]
theorem ker_coeSubmodule : LieSubmodule.toSubmodule (ker f) = LinearMap.ker (f : L →ₗ[R] L') :=
  rfl
#align lie_hom.ker_coe_submodule LieHom.ker_coeSubmodule

@[simp]
theorem mem_ker {x : L} : x ∈ ker f ↔ f x = 0 :=
  show x ∈ LieSubmodule.toSubmodule (f.ker) ↔ _ by
    simp only [ker_coeSubmodule, LinearMap.mem_ker, coe_toLinearMap]
    -- 🎉 no goals
#align lie_hom.mem_ker LieHom.mem_ker

theorem mem_idealRange {x : L} : f x ∈ idealRange f := by
  rw [idealRange_eq_map]
  -- ⊢ ↑f x ∈ LieIdeal.map f ⊤
  exact LieIdeal.mem_map (LieSubmodule.mem_top x)
  -- 🎉 no goals
#align lie_hom.mem_ideal_range LieHom.mem_idealRange

@[simp]
theorem mem_idealRange_iff (h : IsIdealMorphism f) {y : L'} :
    y ∈ idealRange f ↔ ∃ x : L, f x = y := by
  rw [f.isIdealMorphism_def] at h
  -- ⊢ y ∈ idealRange f ↔ ∃ x, ↑f x = y
  rw [← LieSubmodule.mem_coe, ← LieIdeal.coe_toSubalgebra, h, f.range_coe, Set.mem_range]
  -- 🎉 no goals
#align lie_hom.mem_ideal_range_iff LieHom.mem_idealRange_iff

theorem le_ker_iff : I ≤ f.ker ↔ ∀ x, x ∈ I → f x = 0 := by
  constructor <;> intro h x hx
  -- ⊢ I ≤ ker f → ∀ (x : L), x ∈ I → ↑f x = 0
                  -- ⊢ ↑f x = 0
                  -- ⊢ x ∈ ker f
  · specialize h hx; rw [mem_ker] at h; exact h
    -- ⊢ ↑f x = 0
                     -- ⊢ ↑f x = 0
                                        -- 🎉 no goals
  · rw [mem_ker]; apply h x hx
    -- ⊢ ↑f x = 0
                  -- 🎉 no goals
#align lie_hom.le_ker_iff LieHom.le_ker_iff

theorem ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f := by
  rw [← LieSubmodule.coe_toSubmodule_eq_iff, ker_coeSubmodule, LieSubmodule.bot_coeSubmodule,
    LinearMap.ker_eq_bot, coe_toLinearMap]
#align lie_hom.ker_eq_bot LieHom.ker_eq_bot

@[simp]
theorem range_coeSubmodule : (f.range : Submodule R L') = LinearMap.range (f : L →ₗ[R] L') :=
  rfl
#align lie_hom.range_coe_submodule LieHom.range_coeSubmodule

theorem range_eq_top : f.range = ⊤ ↔ Function.Surjective f := by
  rw [← LieSubalgebra.coe_to_submodule_eq_iff, range_coeSubmodule, LieSubalgebra.top_coe_submodule]
  -- ⊢ LinearMap.range ↑f = ⊤ ↔ Function.Surjective ↑f
  exact LinearMap.range_eq_top
  -- 🎉 no goals
#align lie_hom.range_eq_top LieHom.range_eq_top

@[simp]
theorem idealRange_eq_top_of_surjective (h : Function.Surjective f) : f.idealRange = ⊤ := by
  rw [← f.range_eq_top] at h
  -- ⊢ idealRange f = ⊤
  rw [idealRange_eq_lieSpan_range, h, ← LieSubalgebra.coe_to_submodule, ←
    LieSubmodule.coe_toSubmodule_eq_iff, LieSubmodule.top_coeSubmodule,
    LieSubalgebra.top_coe_submodule, LieSubmodule.coe_lieSpan_submodule_eq_iff]
  use ⊤
  -- ⊢ ↑⊤ = ⊤
  exact LieSubmodule.top_coeSubmodule
  -- 🎉 no goals
#align lie_hom.ideal_range_eq_top_of_surjective LieHom.idealRange_eq_top_of_surjective

theorem isIdealMorphism_of_surjective (h : Function.Surjective f) : f.IsIdealMorphism := by
  rw [isIdealMorphism_def, f.idealRange_eq_top_of_surjective h, f.range_eq_top.mpr h,
    LieIdeal.top_coe_lieSubalgebra]
#align lie_hom.is_ideal_morphism_of_surjective LieHom.isIdealMorphism_of_surjective

end LieHom

namespace LieIdeal

variable {f : L →ₗ⁅R⁆ L'} {I : LieIdeal R L} {J : LieIdeal R L'}

@[simp]
theorem map_eq_bot_iff : I.map f = ⊥ ↔ I ≤ f.ker := by
  rw [← le_bot_iff]
  -- ⊢ map f I ≤ ⊥ ↔ I ≤ LieHom.ker f
  exact LieIdeal.map_le_iff_le_comap
  -- 🎉 no goals
#align lie_ideal.map_eq_bot_iff LieIdeal.map_eq_bot_iff

theorem coe_map_of_surjective (h : Function.Surjective f) :
    LieSubmodule.toSubmodule (I.map f) = (LieSubmodule.toSubmodule I).map (f : L →ₗ[R] L') := by
  let J : LieIdeal R L' :=
    { (I : Submodule R L).map (f : L →ₗ[R] L') with
      lie_mem := fun {x y} hy ↦ by
        have hy' : ∃ x : L, x ∈ I ∧ f x = y := by simpa [hy]
        obtain ⟨z₂, hz₂, rfl⟩ := hy'
        obtain ⟨z₁, rfl⟩ := h x
        simp only [LieHom.coe_toLinearMap, SetLike.mem_coe, Set.mem_image,
          LieSubmodule.mem_coeSubmodule, Submodule.mem_carrier, Submodule.map_coe]
        use ⁅z₁, z₂⁆
        exact ⟨I.lie_mem hz₂, f.map_lie z₁ z₂⟩ }
  erw [LieSubmodule.coe_lieSpan_submodule_eq_iff]
  -- ⊢ ∃ N, ↑N = Submodule.map (↑f) (↑R L I).toSubmodule
  use J
  -- 🎉 no goals
#align lie_ideal.coe_map_of_surjective LieIdeal.coe_map_of_surjective

theorem mem_map_of_surjective {y : L'} (h₁ : Function.Surjective f) (h₂ : y ∈ I.map f) :
    ∃ x : I, f x = y := by
  rw [← LieSubmodule.mem_coeSubmodule, coe_map_of_surjective h₁, Submodule.mem_map] at h₂
  -- ⊢ ∃ x, ↑f ↑x = y
  obtain ⟨x, hx, rfl⟩ := h₂
  -- ⊢ ∃ x_1, ↑f ↑x_1 = ↑↑f x
  use ⟨x, hx⟩
  -- ⊢ ↑f ↑{ val := x, property := hx } = ↑↑f x
  rw [LieHom.coe_toLinearMap]
  -- 🎉 no goals
#align lie_ideal.mem_map_of_surjective LieIdeal.mem_map_of_surjective

theorem bot_of_map_eq_bot {I : LieIdeal R L} (h₁ : Function.Injective f) (h₂ : I.map f = ⊥) :
    I = ⊥ := by
  rw [← f.ker_eq_bot, LieHom.ker] at h₁
  -- ⊢ I = ⊥
  rw [eq_bot_iff, map_le_iff_le_comap, h₁] at h₂
  -- ⊢ I = ⊥
  rw [eq_bot_iff]; exact h₂
  -- ⊢ I ≤ ⊥
                   -- 🎉 no goals
#align lie_ideal.bot_of_map_eq_bot LieIdeal.bot_of_map_eq_bot

/-- Given two nested Lie ideals `I₁ ⊆ I₂`, the inclusion `I₁ ↪ I₂` is a morphism of Lie algebras. -/
def homOfLe {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) : I₁ →ₗ⁅R⁆ I₂ :=
  { Submodule.ofLe (show I₁.toSubmodule ≤ I₂.toSubmodule from h) with map_lie' := fun {_ _} ↦ rfl }
#align lie_ideal.hom_of_le LieIdeal.homOfLe

@[simp]
theorem coe_homOfLe {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) (x : I₁) : (homOfLe h x : L) = x :=
  rfl
#align lie_ideal.coe_hom_of_le LieIdeal.coe_homOfLe

theorem homOfLe_apply {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) (x : I₁) : homOfLe h x = ⟨x.1, h x.2⟩ :=
  rfl
#align lie_ideal.hom_of_le_apply LieIdeal.homOfLe_apply

theorem homOfLe_injective {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) : Function.Injective (homOfLe h) :=
  fun x y ↦ by
  simp only [homOfLe_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe]
  -- 🎉 no goals
#align lie_ideal.hom_of_le_injective LieIdeal.homOfLe_injective

-- Porting note: LHS simplifies, so moved @[simp] to new theorem `map_sup_ker_eq_map'`
theorem map_sup_ker_eq_map : LieIdeal.map f (I ⊔ f.ker) = LieIdeal.map f I := by
  suffices LieIdeal.map f (I ⊔ f.ker) ≤ LieIdeal.map f I by
    exact le_antisymm this (LieIdeal.map_mono le_sup_left)
  apply LieSubmodule.lieSpan_mono
  -- ⊢ ↑(Submodule.map (↑f) (↑R L (I ⊔ LieHom.ker f)).toSubmodule) ⊆ ↑(Submodule.ma …
  rintro x ⟨y, hy₁, hy₂⟩; rw [← hy₂]
  -- ⊢ x ∈ ↑(Submodule.map (↑f) (↑R L I).toSubmodule)
                          -- ⊢ ↑↑f y ∈ ↑(Submodule.map (↑f) (↑R L I).toSubmodule)
  erw [LieSubmodule.mem_sup] at hy₁;obtain ⟨z₁, hz₁, z₂, hz₂, hy⟩ := hy₁; rw [← hy]
  -- ⊢ ↑↑f y ∈ ↑(Submodule.map (↑f) (↑R L I).toSubmodule)
                                    -- ⊢ ↑↑f y ∈ ↑(Submodule.map (↑f) (↑R L I).toSubmodule)
                                                                          -- ⊢ ↑↑f (z₁ + z₂) ∈ ↑(Submodule.map (↑f) (↑R L I).toSubmodule)
  rw [f.coe_toLinearMap, f.map_add, f.mem_ker.mp hz₂, add_zero]; exact ⟨z₁, hz₁, rfl⟩
  -- ⊢ ↑f z₁ ∈ ↑(Submodule.map (↑f) (↑R L I).toSubmodule)
                                                                 -- 🎉 no goals
#align lie_ideal.map_sup_ker_eq_map LieIdeal.map_sup_ker_eq_map

@[simp]
theorem map_sup_ker_eq_map' :
    LieIdeal.map f I ⊔ LieIdeal.map f (LieHom.ker f) = LieIdeal.map f I := by
  simpa using map_sup_ker_eq_map (f := f)
  -- 🎉 no goals

@[simp]
theorem map_comap_eq (h : f.IsIdealMorphism) : map f (comap f J) = f.idealRange ⊓ J := by
  apply le_antisymm
  -- ⊢ map f (comap f J) ≤ LieHom.idealRange f ⊓ J
  · rw [le_inf_iff]; exact ⟨f.map_le_idealRange _, map_comap_le⟩
    -- ⊢ map f (comap f J) ≤ LieHom.idealRange f ∧ map f (comap f J) ≤ J
                     -- 🎉 no goals
  · rw [f.isIdealMorphism_def] at h
    -- ⊢ LieHom.idealRange f ⊓ J ≤ map f (comap f J)
    rw [← SetLike.coe_subset_coe, LieSubmodule.inf_coe, ← coe_toSubalgebra, h]
    -- ⊢ ↑(LieHom.range f) ∩ ↑J ⊆ ↑(map f (comap f J))
    rintro y ⟨⟨x, h₁⟩, h₂⟩; rw [← h₁] at h₂ ⊢; exact mem_map h₂
    -- ⊢ y ∈ ↑(map f (comap f J))
                            -- ⊢ ↑↑f x ∈ ↑(map f (comap f J))
                                               -- 🎉 no goals
#align lie_ideal.map_comap_eq LieIdeal.map_comap_eq

@[simp]
theorem comap_map_eq (h : ↑(map f I) = f '' I) : comap f (map f I) = I ⊔ f.ker := by
  rw [← LieSubmodule.coe_toSubmodule_eq_iff, comap_coeSubmodule, I.map_coeSubmodule f h,
    LieSubmodule.sup_coe_toSubmodule, f.ker_coeSubmodule, Submodule.comap_map_eq]
#align lie_ideal.comap_map_eq LieIdeal.comap_map_eq

variable (f I J)

/-- Regarding an ideal `I` as a subalgebra, the inclusion map into its ambient space is a morphism
of Lie algebras. -/
def incl : I →ₗ⁅R⁆ L :=
  (I : LieSubalgebra R L).incl
#align lie_ideal.incl LieIdeal.incl

@[simp]
theorem incl_range : I.incl.range = I :=
  (I : LieSubalgebra R L).incl_range
#align lie_ideal.incl_range LieIdeal.incl_range

@[simp]
theorem incl_apply (x : I) : I.incl x = x :=
  rfl
#align lie_ideal.incl_apply LieIdeal.incl_apply

@[simp]
theorem incl_coe : (I.incl.toLinearMap : I →ₗ[R] L) = (I : Submodule R L).subtype :=
  rfl
#align lie_ideal.incl_coe LieIdeal.incl_coe

@[simp]
theorem comap_incl_self : comap I.incl I = ⊤ := by ext; simp
                                                   -- ⊢ m✝ ∈ comap (incl I) I ↔ m✝ ∈ ⊤
                                                        -- 🎉 no goals
  --  porting note: `ext; simp` works also in mathlib3, though the proof used to be
  --  rw [← LieSubmodule.coe_toSubmodule_eq_iff, LieSubmodule.top_coeSubmodule,
  --    LieIdeal.comap_coeSubmodule, LieIdeal.incl_coe, Submodule.comap_subtype_self]
#align lie_ideal.comap_incl_self LieIdeal.comap_incl_self

@[simp]
theorem ker_incl : I.incl.ker = ⊥ := by ext; simp
                                        -- ⊢ m✝ ∈ LieHom.ker (incl I) ↔ m✝ ∈ ⊥
                                             -- 🎉 no goals
  --  porting note: `ext; simp` works also in mathlib3, though the proof used to be
  --  rw [← LieSubmodule.coe_toSubmodule_eq_iff, I.incl.ker_coeSubmodule,
  --    LieSubmodule.bot_coeSubmodule, incl_coe, Submodule.ker_subtype]
#align lie_ideal.ker_incl LieIdeal.ker_incl

@[simp]
theorem incl_idealRange : I.incl.idealRange = I := by
  rw [LieHom.idealRange_eq_lieSpan_range, ← LieSubalgebra.coe_to_submodule, ←
    LieSubmodule.coe_toSubmodule_eq_iff, incl_range, coe_to_lieSubalgebra_to_submodule,
    LieSubmodule.coe_lieSpan_submodule_eq_iff]
  use I
  -- 🎉 no goals
#align lie_ideal.incl_ideal_range LieIdeal.incl_idealRange

theorem incl_isIdealMorphism : I.incl.IsIdealMorphism := by
  rw [I.incl.isIdealMorphism_def, incl_idealRange]
  -- ⊢ ↑R L I = LieHom.range (incl I)
  exact (I : LieSubalgebra R L).incl_range.symm
  -- 🎉 no goals
#align lie_ideal.incl_is_ideal_morphism LieIdeal.incl_isIdealMorphism

end LieIdeal

end LieSubmoduleMapAndComap

namespace LieModuleHom

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable (f : M →ₗ⁅R,L⁆ N)

/-- The kernel of a morphism of Lie algebras, as an ideal in the domain. -/
def ker : LieSubmodule R L M :=
  LieSubmodule.comap f ⊥
#align lie_module_hom.ker LieModuleHom.ker

@[simp]
theorem ker_coeSubmodule : (f.ker : Submodule R M) = LinearMap.ker (f : M →ₗ[R] N) :=
  rfl
#align lie_module_hom.ker_coe_submodule LieModuleHom.ker_coeSubmodule

theorem ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f := by
  rw [← LieSubmodule.coe_toSubmodule_eq_iff, ker_coeSubmodule, LieSubmodule.bot_coeSubmodule,
    LinearMap.ker_eq_bot, coe_toLinearMap]
#align lie_module_hom.ker_eq_bot LieModuleHom.ker_eq_bot

variable {f}

@[simp]
theorem mem_ker (m : M) : m ∈ f.ker ↔ f m = 0 :=
  Iff.rfl
#align lie_module_hom.mem_ker LieModuleHom.mem_ker

@[simp]
theorem ker_id : (LieModuleHom.id : M →ₗ⁅R,L⁆ M).ker = ⊥ :=
  rfl
#align lie_module_hom.ker_id LieModuleHom.ker_id

@[simp]
theorem comp_ker_incl : f.comp f.ker.incl = 0 := by ext ⟨m, hm⟩; exact (mem_ker m).mp hm
                                                    -- ⊢ ↑(comp f (LieSubmodule.incl (ker f))) { val := m, property := hm } = ↑0 { va …
                                                                 -- 🎉 no goals
#align lie_module_hom.comp_ker_incl LieModuleHom.comp_ker_incl

theorem le_ker_iff_map (M' : LieSubmodule R L M) : M' ≤ f.ker ↔ LieSubmodule.map f M' = ⊥ := by
  rw [ker, eq_bot_iff, LieSubmodule.map_le_iff_le_comap]
  -- 🎉 no goals
#align lie_module_hom.le_ker_iff_map LieModuleHom.le_ker_iff_map

variable (f)

/-- The range of a morphism of Lie modules `f : M → N` is a Lie submodule of `N`.
See Note [range copy pattern]. -/
def range : LieSubmodule R L N :=
  (LieSubmodule.map f ⊤).copy (Set.range f) Set.image_univ.symm
#align lie_module_hom.range LieModuleHom.range

@[simp]
theorem coe_range : (f.range : Set N) = Set.range f :=
  rfl
#align lie_module_hom.coe_range LieModuleHom.coe_range

@[simp]
theorem coeSubmodule_range : (f.range : Submodule R N) = LinearMap.range (f : M →ₗ[R] N) :=
  rfl
#align lie_module_hom.coe_submodule_range LieModuleHom.coeSubmodule_range

@[simp]
theorem mem_range (n : N) : n ∈ f.range ↔ ∃ m, f m = n :=
  Iff.rfl
#align lie_module_hom.mem_range LieModuleHom.mem_range

theorem map_top : LieSubmodule.map f ⊤ = f.range := by ext; simp [LieSubmodule.mem_map]
                                                       -- ⊢ m✝ ∈ LieSubmodule.map f ⊤ ↔ m✝ ∈ range f
                                                            -- 🎉 no goals
#align lie_module_hom.map_top LieModuleHom.map_top

end LieModuleHom

namespace LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (N : LieSubmodule R L M)

@[simp]
theorem ker_incl : N.incl.ker = ⊥ := by simp [← LieSubmodule.coe_toSubmodule_eq_iff]
                                        -- 🎉 no goals
#align lie_submodule.ker_incl LieSubmodule.ker_incl

@[simp]
theorem range_incl : N.incl.range = N := by simp [← LieSubmodule.coe_toSubmodule_eq_iff]
                                            -- 🎉 no goals
#align lie_submodule.range_incl LieSubmodule.range_incl

@[simp]
theorem comap_incl_self : comap N.incl N = ⊤ := by simp [← LieSubmodule.coe_toSubmodule_eq_iff]
                                                   -- 🎉 no goals
#align lie_submodule.comap_incl_self LieSubmodule.comap_incl_self

end LieSubmodule

section TopEquiv

variable {R : Type u} {L : Type v}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The natural equivalence between the 'top' Lie subalgebra and the enclosing Lie algebra.

This is the Lie subalgebra version of `Submodule.topEquiv`. -/
def LieSubalgebra.topEquiv : (⊤ : LieSubalgebra R L) ≃ₗ⁅R⁆ L :=
  { (⊤ : LieSubalgebra R L).incl with
    invFun := fun x ↦ ⟨x, Set.mem_univ x⟩
    left_inv := fun x ↦ by ext; rfl
                           -- ⊢ ↑((fun x => { val := x, property := (_ : x ∈ Set.univ) }) (AddHom.toFun (↑{  …
                                -- 🎉 no goals
    right_inv := fun x ↦ rfl }
#align lie_subalgebra.top_equiv LieSubalgebra.topEquiv

@[simp]
theorem LieSubalgebra.topEquiv_apply (x : (⊤ : LieSubalgebra R L)) : LieSubalgebra.topEquiv x = x :=
  rfl
#align lie_subalgebra.top_equiv_apply LieSubalgebra.topEquiv_apply

/-- The natural equivalence between the 'top' Lie ideal and the enclosing Lie algebra.

This is the Lie ideal version of `Submodule.topEquiv`. -/
def LieIdeal.topEquiv : (⊤ : LieIdeal R L) ≃ₗ⁅R⁆ L :=
  LieSubalgebra.topEquiv
#align lie_ideal.top_equiv LieIdeal.topEquiv

@[simp]
theorem LieIdeal.topEquiv_apply (x : (⊤ : LieIdeal R L)) : LieIdeal.topEquiv x = x :=
  rfl
#align lie_ideal.top_equiv_apply LieIdeal.topEquiv_apply

end TopEquiv
