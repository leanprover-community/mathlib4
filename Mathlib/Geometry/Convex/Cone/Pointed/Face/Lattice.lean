/-
Copyright (c) 2025 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed.Face.Basic

/-!
## Face

This file defines a bundled object for a face of a pointed cone and a complete lattice structure on
them.

## Main definitions

* `Face C`: a bundled structure for a face of the pointed cone `C`.
* `inf` and `sup`: infimum and supremum operations on `Face C`
* `CompleteLattice` instance: the face lattice of a pointed cone using `inf` and `sup`.
* `prod`: the product of two faces of pointed cones, together with projections `prod_left` and
  `prod_right`.
* `prod_orderIso`: the order isomorphism defined by `prod`.

-/

@[expose] public section

namespace PointedCone

variable {R M N : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M] in
/-- A face of a pointed cone `C`, as a bundled structure. -/
structure Face (C : PointedCone R M) extends PointedCone R M where
  isFaceOf : IsFaceOf toSubmodule C

namespace Face

section Semiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
variable {C C₁ C₂ : PointedCone R M} {F F₁ F₂ : Face C}

/-- A pointed cone `C` as a face of itself. -/
def self (C : PointedCone R M) : Face C := ⟨C, IsFaceOf.refl _⟩

instance {C : PointedCone R M} : CoeDep (PointedCone R M) C (Face C) := ⟨self C⟩

/- Convert a face of a pointed cone into a pointed cone. -/
@[coe, simp]
def toPointedCone {C : PointedCone R M} (F : Face C) : PointedCone R M := F.toSubmodule

instance : CoeOut (Face (C : PointedCone R M)) (PointedCone R M) where
  coe := toPointedCone

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
def inf (F₁ F₂ : Face C) : Face C := ⟨F₁ ⊓ F₂, F₁.isFaceOf.inf_left F₂.isFaceOf⟩

instance : InfSet (Face C) :=
⟨fun S =>
  { toSubmodule := C ⊓ sInf {s.1 | s ∈ S}
    isFaceOf := by
      constructor
      · exact fun _ sm => sm.1
      · simp only [Submodule.mem_inf, Submodule.mem_sInf, Set.mem_setOf_eq, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂]
        intros _ _ a xc yc a0 _ h
        simp only [xc, true_and]; intros F Fs
        exact F.isFaceOf.mem_of_smul_add_mem xc yc a0 (h F Fs)
}⟩

instance : SemilatticeInf (Face C) where
  inf := inf
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
def sup (F₁ F₂ : Face C) : Face C := sInf {F : Face C | F₁ ≤ F ∧ F₂ ≤ F}

instance : SemilatticeSup (Face C) where
  sup := sup
  le_sup_left _ _ := le_sInf (fun _ Fs => Fs.1)
  le_sup_right _ _ := le_sInf (fun _ Fs => Fs.2)
  sup_le _ _ _ h₁₂ h₂₃ := sInf_le (Set.mem_sep h₁₂ h₂₃)

/-- The supremum of a set `S` of faces of `C` is the smallest face of `C` that comtains all
  members of `S`. -/
instance : SupSet (Face C) where sSup S := sInf { F : Face C | ∀ F' ∈ S, F' ≤ F }

instance : CompleteSemilatticeSup (Face C) where
  __ := instSemilatticeSup
  sSup := sSup
  sSup_le _ _ fS := sInf_le_of_le fS le_rfl
  le_sSup _ f fS := le_sInf_iff.mpr <| fun _ a ↦ a f fS

instance : Lattice (Face C) where

/-- The top element of the partial order on faces of `C` is `C` itself. -/
instance : OrderTop (Face C) where
  top := C
  le_top F := F.isFaceOf.le

instance : Inhabited (Face C) := ⟨⊤⟩

instance : Nonempty (Face C) := ⟨⊤⟩

/-!
### `OrderHom` for some operations
-/

/-- The order homomorphism mapping a face `F₁` of `C₁` to the face `F₁ ⊓ F₂ ≤ C₁ ⊓ C₂` for
  some face `F₂` of `C₂`. -/
def inf_face_orderHom (F₂ : Face C₂) : Face C₁ →o Face (C₁ ⊓ C₂) where
  toFun F := ⟨_, F.isFaceOf.inf F₂.isFaceOf⟩
  monotone' F₁ F₂ h x := by
    simp only [mem_coe, toPointedCone, Submodule.mem_inf, and_imp]
    exact fun xF₁ xC₂ => ⟨h.subset xF₁, xC₂⟩

/-- The order homomorphism mapping a face `F` of `C₁` to the face `F ⊓ C₂ ≤ C₁ ⊓ C₂`. -/
def inf_orderHom (C₂ : PointedCone R M) : Face C₁ →o Face (C₁ ⊓ C₂) :=
  inf_face_orderHom (self C₂)

/-- The order homomorphism mapping the product of faces `F₁ ≤ C₁` and `F₂ ≤ C₂` to
  the face `F₁ ⊓ F₂ ≤ C₁ ⊓ C₂`. -/
def prod_inf_face_orderHom : Face C₁ × Face C₂ →o Face (C₁ ⊓ C₂) where
  toFun F := ⟨_, F.1.isFaceOf.inf F.2.isFaceOf⟩
  monotone' F₁ F₂ h x := by
    simp only [mem_coe, toPointedCone, Submodule.mem_inf, and_imp]
    intros xF₁ xF₂
    simp only [LE.le, mem_coe] at h
    exact ⟨h.1 xF₁, h.2 xF₂⟩

end Semiring

section Field

variable [Field R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {C C₁ : PointedCone R M} {C₂ : PointedCone R N}

/-- The face of a pointed cone `C` that is its lineal space. It is contained in all faces of `C`. -/
def lineal : Face C := ⟨_, IsFaceOf.lineal C⟩

lemma lineal_le {C : PointedCone R M} (F : Face C) : lineal ≤ F := F.isFaceOf.lineal_le

/-- The bottom element of the partial order on faces of `C` is `C.lineal`. -/
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

/-- The face of `C₁` obtained by projecting to the left component of a face `F ≤ C₁ × C₂`. -/
def proj_fst (F : Face (C₁.prod C₂)) : Face C₁ := ⟨_, F.isFaceOf.fst⟩

/-- The face of `C₁` obtained by projecting to the left component of a face `F ≤ C₁ × C₂`. -/
def proj_snd (F : Face (C₁.prod C₂)) : Face C₂ := ⟨_, F.isFaceOf.snd⟩

@[simp]
theorem prod_proj_fst (F₁ : Face C₁) (F₂ : Face C₂) : (F₁.prod F₂).proj_fst = F₁ := by
  ext
  simpa [proj_fst, prod] using fun _ => ⟨0, F₂.toSubmodule.zero_mem⟩

@[simp]
theorem prod_proj_snd (F₁ : Face C₁) (F₂ : Face C₂) : (F₁.prod F₂).proj_snd = F₂ := by
  ext
  simpa [proj_snd, prod] using fun _ => ⟨0, F₁.toSubmodule.zero_mem⟩

theorem proj_fst_prod_proj_snd (G : Face (C₁.prod C₂)) : G.proj_fst.prod G.proj_snd = G := by
  ext x
  simp only [prod, toPointedCone, proj_fst, proj_snd, mem_coe, mem_prod, mem_map,
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
  F₁ ≤ F₁' → F₂ ≤ F₂' → prod F₁ F₂ ≤ prod F₁' F₂' :=
  Submodule.prod_mono

/- The face lattice of the product of two cones is isomorphic to the product of their face
lattices. -/
def prod_orderIso (C : PointedCone R M) (D : PointedCone R N) :
    Face (C.prod D) ≃o Face C × Face D where
  toFun G := ⟨proj_fst G, proj_snd G⟩
  invFun G := G.1.prod G.2
  left_inv G := by simp [proj_fst_prod_proj_snd]
  right_inv G := by simp
  map_rel_iff' := by
    simp only [Equiv.coe_fn_mk, ge_iff_le, Prod.mk_le_mk, coe_le_iff]
    intro F₁ F₂; constructor <;> intro a
    · simpa [proj_fst_prod_proj_snd, coe_le_iff] using Face.prod_mono a.1 a.2
    · constructor; all_goals
      try simpa only [prod_left, prod_right]
      exact fun _ d => Submodule.map_mono a d

end Prod

end Field

end Face

end PointedCone
