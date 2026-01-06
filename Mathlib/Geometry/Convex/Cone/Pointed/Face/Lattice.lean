/-
Copyright (c) 2025 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed.Face.Basic

/-!
## Face

This file defines the notion of face of a pointed cone as a bundled object and establishes the
complete lattice structure thereon. The type `Face C` therefore also represents the face lattice
of a pointed cone `C`.

## Main definitions

* `Face C`: the face lattice of `C`.
* `inf` and `sup`: infimum and supremum operations on `Face C`.
* `CompleteLattice` instance: the face lattice of a pointed cone using `inf` and `sup`.
* `prod`: the product of two faces of pointed cones, together with projections `prod_left` and
  `prod_right`.
* `prod_orderIso`: proves that the face lattices of a product cone is the product of the face
  lattices of the individual cones.

-/

@[expose] public section

namespace PointedCone

variable {R M N : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M] in
/-- A face of a pointed cone `C`. Represents the face lattice of `C`. -/
structure Face (C : PointedCone R M) extends PointedCone R M where
  isFaceOf : IsFaceOf toSubmodule C

namespace Face

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
variable {C C₁ C₂ : PointedCone R M} {F F₁ F₂ : Face C}

/-- A pointed cone `C` as a face of itself. -/
@[coe]
def self (C : PointedCone R M) : Face C := ⟨C, IsFaceOf.refl _⟩

instance {C : PointedCone R M} : CoeDep (PointedCone R M) C (Face C) := ⟨self C⟩

/-- Converts a face of a pointed cone into a pointed cone. -/
@[coe, simp]
def toPointedCone {C : PointedCone R M} (F : Face C) : PointedCone R M := F.toSubmodule

instance : CoeOut (Face (C : PointedCone R M)) (PointedCone R M) := ⟨toPointedCone⟩

instance : SetLike (Face C) M where
  coe C := C.toPointedCone
  coe_injective' := SetLike.coe_injective.comp <| by rintro ⟨_, _⟩ ⟨_, _⟩ _; congr

@[ext]
theorem ext (h : ∀ x, x ∈ F₁ ↔ x ∈ F₂) : F₁ = F₂ := SetLike.ext h

@[simp]
theorem coe_le_iff {F₁ F₂ : Face C} : F₁ ≤ F₂ ↔ F₁.toPointedCone ≤ F₂.toPointedCone := by
  constructor <;> intro h x xF₁ <;> exact h xF₁

@[simp]
theorem mem_coe {F : Face C} (x : M) : x ∈ F ↔ x ∈ F.toPointedCone := .rfl

/-!
### Infimum, supremum and lattice
-/

/-- The infimum of two faces `F₁`, `F₂` of `C` is the intersection of the cones `F₁` and `F₂`. -/
instance : Min (Face C) where
  min F₁ F₂ := ⟨F₁ ⊓ F₂, F₁.isFaceOf.inf_left F₂.isFaceOf⟩

instance : InfSet (Face C) where
 sInf S :=
  { toSubmodule := C ⊓ sInf {s.1 | s ∈ S}
    isFaceOf := by
      constructor
      · exact fun _ sm => sm.1
      · simp only [Submodule.mem_inf, Submodule.mem_sInf, Set.mem_setOf_eq, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂]
        intros _ _ a xc yc a0 _ h
        simp only [xc, true_and]; intros F Fs
        exact F.isFaceOf.mem_of_smul_add_mem xc yc a0 (h F Fs)
  }

instance : SemilatticeInf (Face C) where
  inf_le_left _ _ _ xi := xi.1
  inf_le_right _ _ _ xi := xi.2
  le_inf _ _ _ h₁₂ h₂₃ _ xi := ⟨h₁₂ xi, h₂₃ xi⟩

instance : CompleteSemilatticeInf (Face C) where
  __ := instSemilatticeInf
  sInf_le S f fS := by
    rw [coe_le_iff]
    refine inf_le_of_right_le ?_
    simpa [LE.le] using fun _ xs => xs f fS
  le_sInf S f fS := by
    simp only [sInf, Set.mem_setOf_eq, Set.iInter_exists, Set.biInter_and',
      Set.iInter_iInter_eq_right, coe_le_iff, toPointedCone, le_inf_iff]
    refine ⟨f.isFaceOf.le, ?_⟩
    simpa [LE.le] using fun _ xf s sm => fS s sm xf

/-- The supremum of two faces `F₁`, `F₂` of `C` is the smallest face of `C` that contains both `F₁`
  and `F₂`. -/
instance : Max (Face C) where
  max F₁ F₂ := sInf {F : Face C | F₁ ≤ F ∧ F₂ ≤ F}

instance : SemilatticeSup (Face C) where
  sup := max
  le_sup_left _ _ := le_sInf (fun _ Fs => Fs.1)
  le_sup_right _ _ := le_sInf (fun _ Fs => Fs.2)
  sup_le _ _ _ h₁₂ h₂₃ := sInf_le (Set.mem_sep h₁₂ h₂₃)

/-- The supremum of a set `S` of faces of `C` is the smallest face of `C` that contains all
  members of `S`. -/
instance : SupSet (Face C) where sSup S := sInf { F : Face C | ∀ F' ∈ S, F' ≤ F }

instance : CompleteSemilatticeSup (Face C) where
  __ := instSemilatticeSup
  sSup := sSup
  sSup_le _ _ fS := sInf_le_of_le fS le_rfl
  le_sSup _ f fS := le_sInf_iff.mpr <| fun _ a ↦ a f fS

instance : Lattice (Face C) where

/-- The top face of `C` is `C` itself. -/
instance : OrderTop (Face C) where
  top := C
  le_top F := F.isFaceOf.le

instance : Inhabited (Face C) := ⟨⊤⟩

instance : Nonempty (Face C) := ⟨⊤⟩

end Semiring

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {C C₁ : PointedCone R M} {C₂ : PointedCone R N}

/-- The lineality space of a pointed cone `C` as a face of `C`.
  It is contained in all faces of `C`. -/
def lineal : Face C := ⟨_, IsFaceOf.lineal C⟩

lemma lineal_le {C : PointedCone R M} (F : Face C) : lineal ≤ F := F.isFaceOf.lineal_le

/-- The bottom face of `C` is its lineality space. -/
instance : OrderBot (Face C) where
  bot := lineal
  bot_le F := F.lineal_le

instance : BoundedOrder (Face C) where

instance : CompleteLattice (Face C) where

/-!
### Product
-/
section Prod

open Submodule

/-- The face of `C₁ × C₂` obtained by taking the (submodule) product of faces `F₁ ≤ C₁` and
`F₂ ≤ C₂`. -/
def prod (F₁ : Face C₁) (F₂ : Face C₂) : Face (C₁.prod C₂) := ⟨_, F₁.isFaceOf.prod F₂.isFaceOf⟩

/-- The face of `C₁` obtained by projecting to the first component of a face `F ≤ C₁ × C₂`. -/
def projFst (F : Face (C₁.prod C₂)) : Face C₁ := ⟨_, F.isFaceOf.fst⟩

/-- The face of `C₁` obtained by projecting to the second component of a face `F ≤ C₁ × C₂`. -/
def projSnd (F : Face (C₁.prod C₂)) : Face C₂ := ⟨_, F.isFaceOf.snd⟩

@[simp]
theorem prod_projFst (F₁ : Face C₁) (F₂ : Face C₂) : (F₁.prod F₂).projFst = F₁ := by
  ext
  simpa [projFst, prod] using fun _ => ⟨0, F₂.toSubmodule.zero_mem⟩

@[simp]
theorem prod_projSnd (F₁ : Face C₁) (F₂ : Face C₂) : (F₁.prod F₂).projSnd = F₂ := by
  ext
  simpa [projSnd, prod] using fun _ => ⟨0, F₁.toSubmodule.zero_mem⟩

theorem projFst_prod_projSnd (G : Face (C₁.prod C₂)) : G.projFst.prod G.projSnd = G := by
  ext x
  simp only [prod, toPointedCone, projFst, projSnd, mem_coe, mem_prod, mem_map,
    LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right, LinearMap.snd_apply]
  constructor
  · simp only [and_imp, forall_exists_index]
    intro y yn z zm
    have := add_mem zm yn
    simp only [Prod.mk_add_mk, add_comm] at this
    rw [← Prod.mk_add_mk, add_comm] at this
    refine G.isFaceOf.mem_of_add_mem ?_ ?_ this
    · exact ⟨(mem_prod.mp (G.isFaceOf.le yn)).1, (mem_prod.mp (G.isFaceOf.le zm)).2⟩
    · exact ⟨(mem_prod.mp (G.isFaceOf.le zm)).1, (mem_prod.mp (G.isFaceOf.le yn)).2⟩
  · intro h; exact ⟨⟨x.2, h⟩, ⟨x.1, h⟩⟩

theorem prod_mono {F₁ F₁' : Face C₁} {F₂ F₂' : Face C₂} :
    F₁ ≤ F₁' → F₂ ≤ F₂' → prod F₁ F₂ ≤ prod F₁' F₂' := Submodule.prod_mono

/-- The face lattice of the product of two cones is isomorphic to the product of their face
lattices. -/
def prod_orderIso (C : PointedCone R M) (D : PointedCone R N) :
    Face (C.prod D) ≃o Face C × Face D where
  toFun G := ⟨projFst G, projSnd G⟩
  invFun G := G.1.prod G.2
  left_inv G := by simp [projFst_prod_projSnd]
  right_inv G := by simp
  map_rel_iff' := by
    simp only [Equiv.coe_fn_mk, ge_iff_le, Prod.mk_le_mk, coe_le_iff]
    intro F₁ F₂; constructor <;> intro a
    · simpa [projFst_prod_projSnd, coe_le_iff] using Face.prod_mono a.1 a.2
    · constructor; all_goals
      try simpa only [prod_left, prod_right]
      exact fun _ d => Submodule.map_mono a d

end Prod

end Field

end Face

end PointedCone
