/-
Copyright (c) 2025 S. Gangloff. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: S. Gangloff
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Instances.Discrete
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# Symbolic dynamics over `ℤ^d`

We set up a minimal API for the full shift over a finite discrete alphabet, cylinders,
patterns, and subshifts defined by forbidden patterns. We also define a language size on
boxes and a (limsup-based) notion of topological entropy.

## Main definitions

* `Zd d` : the lattice `ℤ^d` as functions `Fin d → ℤ`.
* `FullShiftZd A d` : configurations `Zd d → A` with the product topology.
* `FullShiftZd.shift` : the `ℤ^d`-action by translation.
* `cylinder U x` : cylinder set fixing the coordinates in `U ⊆ Zd d` to those of `x`.
* `Pattern A d` : finite patterns (support + values).
* `Pattern.occursIn` : occurrence of a pattern at a position.
* `forbids F` : configurations avoiding every pattern in `F`.
* `Subshift` : closed, shift‑invariant subsets of the full shift.
* `box n` : the cube `[-n,n]^d` as a finset of `Zd d`.
* `languageCard` / `patternCount` : number of patterns seen on a box.
* `limsupAtTop` : `limsup` of a real sequence along `atTop` (infimum of eventual upper bounds).
* `entropy` : limsup language growth per unit volume.

## Notation/Conventions

* The alphabet `A` is assumed finite, discrete, and inhabited throughout. The product topology
  on configurations is used.
* Cylinders are defined by equality on finitely many coordinates, hence are clopen.

-/

open Set Topology
open Filter

namespace SymbolicDynamics


variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
  [TopologicalSpace A] [DiscreteTopology A]

variable {d : ℕ}

/-- The lattice `ℤ^d` as functions `Fin d → ℤ`. -/
def Zd (d : ℕ) := Fin d → ℤ

/-- Decidable equality on `Zd d`. -/
@[instance]
def Zd.decidableEq (d : ℕ) : DecidableEq (Zd d) :=
  inferInstanceAs (DecidableEq (Fin d → ℤ))

/-- Pointwise addition on `ℤ^d`. -/
instance : Add (Zd d) where
  add := fun u v i ↦ u i + v i

/-- `ℤ^d` is an additive commutative group (pointwise). -/
instance : AddCommGroup (Zd d) := Pi.addCommGroup

/-! ## Full shift -/

/-- The full shift over `ℤ^d` with alphabet `A`. -/
@[reducible]
def FullShiftZd (A : Type*) (d : ℕ) := Zd d → A

/-- Product topology on the full shift. -/
instance : TopologicalSpace (FullShiftZd A d) := Pi.topologicalSpace

/-- Default configuration: constantly `default`. -/
instance : Inhabited (FullShiftZd A d) := ⟨fun _ ↦ default⟩

namespace FullShiftZd

/-! ### Shift action -/

/-- Shift by `v`: translate a configuration by `v`. -/
def shift (v : Zd d) (x : FullShiftZd A d) : FullShiftZd A d :=
  fun u ↦ x (u + v)

section
variable {A : Type*} {d : ℕ}

@[simp] lemma shift_zero (x : FullShiftZd A d) :
    shift (0 : Zd d) x = x := by
  ext u; simp [shift]

/-- Compatibility of shifts with addition. -/
lemma shift_add (v w : Zd d) (x : FullShiftZd A d) :
    shift (v + w) x = shift v (shift w x) := by
  ext u; simp [shift, add_assoc]
end

section
variable {A : Type*} [TopologicalSpace A]
variable {d : ℕ}

/-- The shift map is continuous. -/
lemma shift_continuous (v : Zd d) :
  Continuous (shift v : FullShiftZd A d → FullShiftZd A d) := by
  continuity
end

/-! ### Cylinders and clopen basis -/

/-- Cylinder fixing `x` on a finite set `U`. -/
@[reducible]
def cylinder (U : Finset (Zd d)) (x : Zd d → A) : Set (FullShiftZd A d) :=
  { y | ∀ i ∈ U, y i = x i }

section
variable {A : Type*} {d : ℕ}

@[simp] lemma mem_cylinder {U : Finset (Zd d)} {x y : FullShiftZd A d} :
  y ∈ cylinder U x ↔ ∀ i ∈ U, y i = x i := by rfl
end

section
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
variable {d : ℕ}

/-- Cylinders are open. -/
lemma cylinder_is_open (U : Finset (Zd d)) (x : Zd d → A) :
  IsOpen (cylinder U x) := by
  let S : Set (FullShiftZd A d) := ⋂ i ∈ U, { y | y i = x i }
  have : cylinder U x = S := by
    ext y
    rw [cylinder, mem_setOf_eq]
    rw [mem_iInter₂]
    simp only [mem_setOf_eq]
  rw [this]
  apply isOpen_biInter_finset
  intro i _
  have : { y : FullShiftZd A d | y i = x i } = (fun y ↦ y i) ⁻¹' {x i} := rfl
  rw [this]
  apply Continuous.isOpen_preimage
  · exact continuous_apply i
  · exact isOpen_discrete ({x i} : Set A)
end

section
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
variable [Fintype A] [DecidableEq A]
variable {d : ℕ}

/-- Cylinders are closed (hence clopen). -/
lemma cylinder_is_closed (d : ℕ) (U : Finset (Zd d)) (x : Zd d → A) :
    IsClosed (cylinder U x) := by
  have h : (cylinder U x)ᶜ = ⋃ (i ∈ U) (a ∈ (Finset.univ \ {x i} : Finset A)),
      cylinder {i} (Function.update x i a) := by
    · ext y
      simp only [mem_compl_iff]
      simp only [mem_iUnion]
      simp only [mem_cylinder]
      simp only [Finset.mem_univ, Finset.mem_sdiff]
      simp only [not_forall]
      simp only [exists_prop]
      constructor
      · intro hy
        push_neg at hy
        obtain ⟨i, hiU, hiy⟩ := hy
        use i, hiU, y i
        constructor
        · simp [hiy]
        · simp [Function.update_apply]
      · rintro ⟨i, hiU, a, ha, hy⟩
        simp only [true_and] at ha
        use i, hiU
        rw [hy]
        simp only [Function.update_apply]
        have hne : a ≠ x i := by
          intro h
          apply ha
          rw [h]
          exact Finset.mem_singleton_self _
        exact hne
        exact Finset.mem_singleton_self i
  have : IsOpen ((cylinder U x)ᶜ) := by
    rw [h]
    apply isOpen_iUnion; intro i
    apply isOpen_iUnion; intro hi
    apply isOpen_iUnion; intro a
    apply isOpen_iUnion; intro ha
    exact cylinder_is_open {i} (Function.update x i a)
  exact isOpen_compl_iff.mp this
end

/-! ## Subshifts and patterns -/

/-- A subshift is a closed, shift‑invariant subset of the full shift. -/
structure Subshift (A : Type*) [TopologicalSpace A] [Inhabited A] (d : ℕ) where
  /-- The underlying set. -/
  carrier : Set (FullShiftZd A d)
  /-- Closedness of the carrier. -/
  is_closed : IsClosed carrier
  /-- Shift invariance. -/
  shift_invariant : ∀ v : Zd d, ∀ x ∈ carrier, shift v x ∈ carrier

/-- The full shift is a subshift. -/
example : Subshift A d :=
{ carrier := Set.univ,
  is_closed := isClosed_univ,
  shift_invariant := by intro _ _ _; simp }

/-- A finite pattern: a finite support `U` together with values on `U`. -/
structure Pattern (A : Type*) (d : ℕ) where
  support : Finset (Zd d)
  data : support → A

/-- The domino supported on `{i,j}` with values `ai`,`aj`. -/
def domino {A : Type*} {d : ℕ}
    (i j : Zd d) (ai aj : A) : Pattern A d := by
  refine
  { support := ({i, j} : Finset (Zd d))
  , data := fun ⟨z, hz⟩ => if z = i then ai else aj }

/-- `p` occurs in `x` at position `v`. -/
def Pattern.occursIn (p : Pattern A d) (x : FullShiftZd A d) (v : Zd d) : Prop :=
  ∀ u (hu : u ∈ p.support), x (u + v) = p.data ⟨u, hu⟩

/-! ### Forbidden patterns -/

/-- Configurations avoiding all patterns of `F`. -/
def forbids (F : Set (Pattern A d)) : Set (FullShiftZd A d) :=
  { x | ∀ p ∈ F, ∀ v : Zd d, ¬ p.occursIn x v }

section
variable {A : Type*} {d : ℕ}

lemma occurs_shift (p : Pattern A d) (x : FullShiftZd A d) (v w : Zd d) :
  Pattern.occursIn p (shift w x) v ↔ Pattern.occursIn p x (v + w) := by
  constructor
  · intro h u hu; simpa [← add_assoc] using h u hu
  · intro h u hu; simpa [shift, add_assoc] using h u hu

/-- `forbids F` is shift invariant. -/
lemma forbids_shift_invariant (F : Set (Pattern A d)) :
    ∀ v : Zd d, ∀ x ∈ forbids F, shift v x ∈ forbids F := by
  intro w x hx p hp v; specialize hx p hp (v + w); contrapose! hx; rwa [← occurs_shift]
end

/-- Extend a pattern by `default` away from its support (anchored at the origin). -/
def patternToOriginConfig (p : Pattern A d) : FullShiftZd A d :=
  fun i ↦ if h : i ∈ p.support then p.data ⟨i, h⟩ else default

/-- Translate a pattern to occur at `v`. -/
def patternToConfig (p : Pattern A d) (v : Zd d) : FullShiftZd A d :=
  shift (-v) (patternToOriginConfig p)

/-- Restrict a configuration to a finite support, seen as a pattern. -/
def patternFromConfig (x : Zd d → A) (U : Finset (Zd d)) : Pattern A d :=
  { support := U,
    data := fun i => x i.1 }

set_option linter.unusedSectionVars false
/-- Occurrences are cylinders translated by `v`. -/
lemma occursAt_eq_cylinder (p : Pattern A d) (v : Zd d) :
  { x | p.occursIn x v }
    = cylinder (p.support.image (· + v)) (patternToConfig p v) := by
  ext x
  constructor
  · intro H u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    dsimp [patternToConfig, patternToOriginConfig, shift]
    simp [add_neg_cancel_right, dif_pos hw, H w hw]
  · intro H u hu
    have := H (u + v) (Finset.mem_image_of_mem _ hu)
    dsimp [patternToConfig, patternToOriginConfig, shift] at this
    simpa [add_neg_cancel_right, dif_pos hu] using this

/-- Occurrence sets are closed. -/
lemma occursAt_closed (p : Pattern A d) (v : Zd d) :
    IsClosed { x | p.occursIn x v } := by
  rw [occursAt_eq_cylinder]; exact cylinder_is_closed d _ _

/-- Occurrence sets are open. -/
lemma occursAt_open (p : Pattern A d) (v : Zd d) :
    IsOpen { x | p.occursIn x v } := by
  rw [occursAt_eq_cylinder]; exact cylinder_is_open _ _

/-- Avoiding a fixed set of patterns is a closed condition. -/
lemma forbids_closed (F : Set (Pattern A d)) :
  IsClosed (forbids F) := by
  rw [forbids]
  have : {x | ∀ p ∈ F, ∀ v : Zd d, ¬ p.occursIn x v}
       = ⋂ (p : Pattern A d) (h : p ∈ F), ⋂ (v : Zd d), {x | ¬ p.occursIn x v} := by
    ext x; simp
  rw [this]
  refine isClosed_iInter ?_;
  intro p; refine isClosed_iInter ?_;
  intro _; refine isClosed_iInter ?_;
  intro v; have : {x | ¬p.occursIn x v} = {x | p.occursIn x v}ᶜ := by ext x; simp
  simpa [this, isClosed_compl_iff] using occursAt_open p v

/-- Subshift defined by forbidden patterns. -/
def X_F (F : Set (Pattern A d)) : Subshift A d :=
{ carrier := forbids F,
  is_closed := forbids_closed F,
  shift_invariant := forbids_shift_invariant F }

/-- Subshift of finite type defined by a finite family of forbidden patterns. -/
def SFT (F : Finset (Pattern A d)) : Subshift A d :=
  X_F (F : Set (Pattern A d))

/-! ## Boxes, language, and entropy -/

/-- The box `[-n,n]^d` as a finset of `Zd d`. -/
def box (n : ℕ) : Finset (Zd d) :=
  Fintype.piFinset (fun _ ↦ Finset.Icc (-↑n : ℤ) ↑n)

/-- Language on the box `[-n,n]^d`: patterns obtained by restricting some `x ∈ X`. -/
def language_box (X : Set (Zd d → A)) (n : ℕ) : Set (Pattern A d) :=
  { p | ∃ x ∈ X, patternFromConfig x (box n) = p }

/-- Patterns with fixed support `U`. -/
def FixedSupport (A : Type*) (d : ℕ) (U : Finset (Zd d)) :=
  { p : Pattern A d // p.support = U }

set_option linter.unnecessarySimpa false
/-- Equivalence `FixedSupport A d U ≃ (U → A)`. -/
def equivFun {U : Finset (Zd d)} : FixedSupport A d U ≃ (U → A) where
  toFun := fun p => fun i =>
    p.val.data ⟨i.1, by simpa [p.property] using i.2⟩
  invFun := fun f => ⟨{ support := U, data := f }, rfl⟩
  left_inv := by
    rintro ⟨p, hp⟩; apply Subtype.ext; cases hp; rfl
  right_inv := by intro f; rfl

/-- Finiteness of `FixedSupport A d U`. -/
instance fintypeFixedSupport (U : Finset (Zd d)) :
    Fintype (FixedSupport A d U) := by
  classical
  exact Fintype.ofEquiv (U → A) (equivFun (A:=A) (d:=d) (U:=U)).symm

/-- Cardinality of the box language (as a finite set), defined via images into
`FixedSupport`. This version is `noncomputable` since it goes through `Set.finite_univ`. -/
noncomputable def languageCard (X : Set (Zd d → A)) (n : ℕ) : ℕ := by
  classical
  let U : Finset (Zd d) := box (d:=d) n
  let f : {x : Zd d → A // x ∈ X} → FixedSupport A d U :=
    fun x => ⟨patternFromConfig (A:=A) (d:=d) x.1 U, rfl⟩
  have hfin_univ : (Set.univ : Set (FixedSupport A d U)).Finite := Set.finite_univ
  have hfin : (Set.range f).Finite := hfin_univ.subset (by intro y hy; simp)
  exact hfin.toFinset.card

/-- Number of patterns of a subshift on the box of size `n`. -/
noncomputable def patternCount (Y : Subshift A d) (n : ℕ) : ℕ :=
  languageCard (A:=A) (d:=d) Y.carrier n

/-- The box `[-n,n]^d` is nonempty. -/
@[simp] lemma box_card_pos (d n : ℕ) : 0 < (box (d:=d) n).card := by
  classical
  have hcoord :
      ∀ i : Fin d, (0 : ℤ) ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
    intro i
    have h0n : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (Nat.zero_le n)
    have hneg : -(n : ℤ) ≤ 0 := neg_nonpos.mpr h0n
    simp [Finset.mem_Icc, hneg]
  have hmem : (0 : Zd d) ∈ box (d:=d) n :=
    Fintype.mem_piFinset.mpr hcoord
  exact Finset.card_pos.mpr ⟨0, hmem⟩

/-- `limsup` along `atTop` as the infimum of eventual upper bounds. -/
noncomputable def limsupAtTop (u : ℕ → ℝ) : ℝ :=
  sInf { L : ℝ | ∀ᶠ n in Filter.atTop, u n ≤ L }

/-- Topological entropy via limsup language growth on cubes.
We use `+ 1` inside the logarithm to avoid `log 0`. -/
noncomputable def entropy (Y : Subshift A d) : ℝ :=
  limsupAtTop (fun n =>
    (Real.log ((patternCount (A:=A) (d:=d) Y n + 1 : ℕ))) /
    ((box (d:=d) n).card : ℝ))

end FullShiftZd

end SymbolicDynamics
