/-
Copyright (c) Hang Lu Su 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Fabrizio Barroero, Stefano Francaviglia,
  Francesco Milizia, Valerio Proietti, Hang Lu Su, Lawrence Wu
-/

import Mathlib

/-!
# Finitely Presented Groups

This file defines when a group is finitely presented and proves their basic properties.
The formal definition of when a group is (finitely) presented is when there exists an isomorphism
between G and F_S / << R >> where S is the generating set and R are the relations.
Here, we define a `Is(Finitely)Presented` directly in terms of the existence of F_S / << R >>
for ease, ignoring the isomorphism.

TODO : maybe just define FinitelyPresentedGroup, then IsFinitelyPresented should be in terms of
the isomorphism? And you can define that FinitelyPresentedGroup IsFinitelyPresented!
OR: look at Group.FG and how that package works.

## Main definitions

## Main results

## Tags
finitely presented group, normal closure finitely generated,
-/

universe u v
-- TODO not sure if this is the right abstraction / right name for this.
/-- The kernel of a homomorphism composed with an isomorphism is equal to the kernel of
the homomorphism mapped by the inverse isomorphism. -/
@[simp]
lemma MonoidHom.ker_comp_mulEquiv {G H K : Type*} [Group G] [Group H] [Group K]
    (f : H →* K) (e : G ≃* H) : (f.comp e).ker = (Subgroup.map (e.symm.toMonoidHom) f.ker) := by
  rw [← MonoidHom.comap_ker, Subgroup.comap_equiv_eq_map_symm]
  rfl

def FinitelyPresentedGroup {n : ℕ} (rels : Set (FreeGroup (Fin n)))
(_h : rels.Finite) := PresentedGroup (rels)
  -- FreeGroup (Fin n) ⧸ Subgroup.normalClosure rels

def FinitelyPresentedGroup' {α : Type} [Finite α] (rels : Set (FreeGroup α))
(_h : rels.Finite) := PresentedGroup (rels)

namespace FinitelyPresentedGroup

instance (n : ℕ) (rels : Set (FreeGroup (Fin n))) (h : rels.Finite) :
Group (FinitelyPresentedGroup rels h) :=
  QuotientGroup.Quotient.group _

instance (α : Type) [Finite α] (rels : Set (FreeGroup α)) (h : rels.Finite) :
Group (FinitelyPresentedGroup' rels h) :=
  QuotientGroup.Quotient.group _

open Subgroup

/-- Definition of subgroup that is given by the normal closure of finitely many elements. -/
def IsNormalClosureFG {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ S : Set G, S.Finite ∧ Subgroup.normalClosure S = H

/-- `IsNormalClosureFG` is invariant under surjective homomorphism. -/
lemma IsNormalClosureFG.invariant_surj_hom {G H : Type*} [Group G] [Group H]
  (f : G →* H) (hf : Function.Surjective f) (K : Subgroup G) (hK : IsNormalClosureFG K)
  : IsNormalClosureFG (K.map f) := by
  obtain ⟨ S, hSfinite, hSclosure ⟩ := hK
  use f '' S
  constructor
  · exact hSfinite.image _
  · rw [ ← hSclosure, Subgroup.map_normalClosure _ _ hf]

/-- A finitely presented group is given by a surjective homomorphism from a free group on n
elements whose normal closure of its kernel is finitely generated. -/
class IsFinitelyPresented (G : Type*) [Group G] : Prop where
  out : ∃ (n : ℕ) (f : (FreeGroup (Fin n)) →* G),
    Function.Surjective f ∧ IsNormalClosureFG (MonoidHom.ker f)

class IsFinitelyPresented' (G : Type*) [Group G] : Prop where
  out: ∃ (n : ℕ) (rels : Set (FreeGroup (Fin n))) (h : rels.Finite),
  Nonempty (G ≃* FinitelyPresentedGroup rels h)

class IsFinitelyPresented'' (G : Type*) [Group G] : Prop where
  out: ∃ (α : Type) (_: Finite α) (rels : Set (FreeGroup α)) (h : rels.Finite),
  Nonempty (G ≃* (FinitelyPresentedGroup' rels h))
-- TODO calls to IsNormalClosureFG.map could be simplified? Like maybe using the iso functions.
  -- seems like we apply a lot of `MonoidHom.ker_comp_mulEquiv + IsNormalClosureFG.map`.
lemma isFinitelyPresented_iff_fintype {G : Type u} [Group G] :
    IsFinitelyPresented G ↔ ∃ (α : Type u) (_ : Fintype α) (f : FreeGroup α →* G),
    Function.Surjective f ∧ IsNormalClosureFG (f.ker) := by
  constructor
  · intro ⟨n, f, hfsurj, hfker⟩
    let iso : FreeGroup (ULift (Fin n)) ≃* FreeGroup (Fin n) :=
      FreeGroup.freeGroupCongr Equiv.ulift
    refine ⟨ULift (Fin n), inferInstance, f.comp iso, hfsurj.comp iso.surjective, ?_⟩
    simp only [MonoidHom.ker_comp_mulEquiv]
    exact IsNormalClosureFG.invariant_surj_hom
      iso.symm.toMonoidHom iso.symm.surjective f.ker hfker
  · intro ⟨α, _, f, hfsurj, hfker⟩
    let iso : FreeGroup (Fin (Fintype.card α)) ≃* FreeGroup α :=
      FreeGroup.freeGroupCongr (Fintype.equivFin α).symm
    refine ⟨Fintype.card α, f.comp iso, hfsurj.comp iso.surjective, ?_⟩
    simp only [MonoidHom.ker_comp_mulEquiv]
    exact IsNormalClosureFG.invariant_surj_hom
      iso.symm.toMonoidHom iso.symm.surjective f.ker hfker
-- TODO same code as above. Keep one?
lemma isFinitelyPresented_iff_finite {G : Type u} [Group G] :
    IsFinitelyPresented G ↔ ∃ (α : Type u) (_ : Finite α) (f : FreeGroup α →* G),
    Function.Surjective f ∧ IsNormalClosureFG (f.ker) := by
    constructor
    · intro ⟨n, f, hfsurj, hfker⟩
      let iso : FreeGroup (ULift (Fin n)) ≃* FreeGroup (Fin n) :=
      FreeGroup.freeGroupCongr Equiv.ulift
      refine ⟨ULift (Fin n), inferInstance, f.comp iso, hfsurj.comp iso.surjective, ?_⟩
      simp only [MonoidHom.ker_comp_mulEquiv]
      exact IsNormalClosureFG.invariant_surj_hom
        iso.symm.toMonoidHom iso.symm.surjective f.ker hfker
    · intro ⟨α, _, f, hfsurj, hfker⟩
      let n := Nat.card α
      let iso : FreeGroup (Fin (Nat.card α)) ≃* FreeGroup α :=
        FreeGroup.freeGroupCongr (Finite.equivFin α).symm
      refine ⟨Nat.card α, f.comp iso, hfsurj.comp iso.surjective, ?_⟩
      simp only [MonoidHom.ker_comp_mulEquiv]
      exact IsNormalClosureFG.invariant_surj_hom
        iso.symm.toMonoidHom iso.symm.surjective f.ker hfker

lemma isFP_iff_finite' {G : Type*} [Group G] :
  IsFinitelyPresented' G ↔ ∃ (α : Type) (_ : Finite α) (rels : Set (FreeGroup α)) (h : rels.Finite),
  Nonempty (G ≃* PresentedGroup rels) := by
  constructor
  · intro ⟨n, rels, hrels, ⟨iso⟩⟩
    unfold FinitelyPresentedGroup at iso
    exact ⟨Fin n, inferInstance, rels, hrels, ⟨iso⟩⟩
  · intro ⟨α, _, rels, hrels, ⟨iso⟩⟩
    let n := Nat.card α
    let e : FreeGroup (Fin (Nat.card α)) ≃* FreeGroup α :=
        FreeGroup.freeGroupCongr (Finite.equivFin α).symm
    -- let rels' := e '' rels
    sorry

theorem Group.fg_iff_exists_freeGroup_hom_surjective_fintype_ARISTOTLE1 {G : Type*} [Group G] :
    Group.FG G ↔ ∃ (α : Type) (_ : Fintype α) (φ : FreeGroup α →* G), Function.Surjective φ := by
      constructor <;> intro h;
      · obtain ⟨S, hS⟩ : ∃ S : Set G, S.Finite ∧ Subgroup.closure S = ⊤ := by
          obtain ⟨ S, hS ⟩ := h;
          exact ⟨ S, S.finite_toSet, hS ⟩;
        -- Let α be the finite set S.
        obtain ⟨α, hα⟩ : ∃ α : Type, ∃ (x : Fintype α), Nonempty (α ≃ S) := by
          have := hS.1.exists_finset_coe;
          obtain ⟨ s', rfl ⟩ := this; exact ⟨ Fin s'.card, inferInstance, ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩ ⟩ ;
        obtain ⟨ x, ⟨ e ⟩ ⟩ := hα;
        refine' ⟨ α, x, FreeGroup.lift ( fun a => ( e a : G ) ), _ ⟩;
        intro g
        have h_closure : g ∈ Subgroup.closure S := by
          aesop;
        refine' Subgroup.closure_induction ( fun g hg => _ ) _ _ _ h_closure;
        · exact ⟨ FreeGroup.of ( e.symm ⟨ g, hg ⟩ ), by simp +decide ⟩;
        · exact ⟨ 1, map_one _ ⟩;
        · rintro x y hx hy ⟨ a, rfl ⟩ ⟨ b, rfl ⟩ ; exact ⟨ a * b, by simp +decide ⟩;
        · rintro x hx ⟨ a, rfl ⟩ ; exact ⟨ a⁻¹, by simp +decide ⟩ ;
      · obtain ⟨ α, hα, φ, hφ ⟩ := h
        -- Since α is finite, the image of α under φ is also finite. Therefore, the image of α generates G, proving that G is finitely generated.
        have h_image_finite : Set.Finite (Set.range (fun a : α => φ (FreeGroup.of a))) := by
          exact Set.toFinite _;
        refine' ⟨ h_image_finite.toFinset, _ ⟩;
        refine' eq_top_iff.mpr fun g hg => _;
        obtain ⟨ x, rfl ⟩ := hφ g;
        induction x using FreeGroup.induction_on <;> aesop

theorem Group.fg_iff_exists_freeGroup_hom_surjective_fintype_ARISTOTLE2 {G : Type*} [Group G] :
    Group.FG G ↔ ∃ (α : Type*) (_ : Fintype α) (φ : FreeGroup α →* G), Function.Surjective φ := by
      ·
        constructor <;> intro hG
        all_goals generalize_proofs at *;
        · obtain ⟨ S, hS ⟩ := hG;
          -- Let $T$ be the set of elements in $S$.
          set T : Set G := S.toSet;
          -- Let $α$ be the set of elements in $T$.
          obtain ⟨α, hα⟩ : ∃ α : Type, ∃ (x : Fintype α), Nonempty (α ≃ T) := by
            -- Since $T$ is finite, we can use the fact that any finite set is equivalent to a finite type.
            use Fin (Finset.card S);
            -- Since $S$ is a finset, there exists an equivalence between $Fin (Finset.card S)$ and $S$.
            have h_equiv : Nonempty (Fin (Finset.card S) ≃ S) := by
              exact ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩;
            exact ⟨ inferInstance, h_equiv ⟩;
          obtain ⟨ hα, ⟨ e ⟩ ⟩ := hα;
          -- Define the homomorphism φ by mapping each generator in α to the corresponding element in T.
          use ULift α, inferInstance, FreeGroup.lift (fun a => (e (ULift.down a)).val);
          intro g
          have h_mem : g ∈ Subgroup.closure T := by
            aesop
          generalize_proofs at *;
          refine' Subgroup.closure_induction _ _ _ _ h_mem;
          · intro x hx
            obtain ⟨ a, ha ⟩ := e.surjective ⟨ x, hx ⟩
            use FreeGroup.of (ULift.up a)
            simp [ha];
          · exact ⟨ 1, map_one _ ⟩;
          · rintro x y hx hy ⟨ a, rfl ⟩ ⟨ b, rfl ⟩ ; exact ⟨ a * b, by simp +decide ⟩ ;
          · rintro x hx ⟨ a, rfl ⟩ ; exact ⟨ a⁻¹, by simp +decide ⟩ ;
        · -- To prove the forward direction, assume there exists a finite type α and a surjective homomorphism φ from the free group on α to G. We can use the fact that the image of a finite set under a surjective homomorphism is finite.
          obtain ⟨α, hα, φ, hφ⟩ := hG;
          have h_gen : ∃ (S : Set G), S.Finite ∧ Subgroup.closure S = ⊤ := by
            refine' ⟨ Set.range ( fun x : α => φ ( FreeGroup.of x ) ), Set.toFinite _, _ ⟩;
            rw [ eq_top_iff ];
            rintro g -;
            obtain ⟨ x, rfl ⟩ := hφ g;
            induction x using FreeGroup.induction_on <;> aesop;
          obtain ⟨ S, hS_finite, hS_gen ⟩ := h_gen; exact ⟨ hS_finite.toFinset, by simpa [ Subgroup.closure ] using hS_gen ⟩ ;

theorem Group.fg_iff_exists_freeGroup_hom_surjective_finite {G : Type*} [Group G] :
    Group.FG G ↔ ∃ (α : Type) (_ : Finite α) (φ : FreeGroup α →* G), Function.Surjective φ := by
      constructor
      · rw [Group.fg_iff_exists_freeGroup_hom_surjective]
        intro ⟨S, hS, φ⟩
        sorry
      · sorry

/- instance {G : Type*} [Group G] [h : IsFinitelyPresented G] : Group.FG G := by
  rw [Group.fg_iff_exists_freeGroup_hom_surjective_finite]
  rw [isFinitelyPresented_iff_finite] at h
  obtain ⟨S, hSfinite, f, hfsurj, hkernel⟩ := h
  use S, hSfinite, f, hfsurj -/

instance {G : Type*} [Group G] [h : IsFinitelyPresented' G] : Group.FG G := by
  rw [Group.fg_iff_exists_freeGroup_hom_surjective]
  rw [isFP_iff_finite'] at h
  obtain ⟨S, hSfinite, f, hfsurj, hkernel⟩ := h
  sorry

instance {G : Type*} [Group G] [h : IsFinitelyPresented'' G] : Group.FG G := by
  rw [Group.fg_iff_exists_freeGroup_hom_surjective_finite]
  obtain ⟨α, hα, rels, hrels, ⟨iso⟩⟩ := h
  unfold FinitelyPresentedGroup' at iso
  unfold PresentedGroup at iso
  use α, hα
  -- TODO probably a nicer way to do this.
  let iso' := iso.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.normalClosure rels))
  use iso'
  simpa [iso'] using
    (Function.Surjective.comp iso.symm.surjective (QuotientGroup.mk'_surjective (Subgroup.normalClosure rels)))

/-   -- # Proof 2
  obtain ⟨α, hα, rels, hrels, ⟨iso⟩⟩ := h
  unfold FinitelyPresentedGroup' at iso
  unfold PresentedGroup at iso
  rw [Group.fg_iff]
  let _ : Fintype α := Fintype.ofFinite α
  have S : Set α := (Finset.univ : Finset α)
  let f : α → G := fun a => iso.symm (PresentedGroup.of (rels := rels) a)
  have sG : Set G := S.image f
  use sG
  sorry -/

/-  `u` is chosen as the universe as otw creates problems with other FP group def.
 `PresentedGroup` is defined as having the same type as its generators in #PresentedGroup. -/
def IsPresented (G : Type u) [Group G] : Prop :=
  ∃ (α : Type u) (rels : Set (FreeGroup α)) (f : FreeGroup α →* G),
  Function.Surjective f ∧ (normalClosure rels = f.ker)

def IsPresented' (G : Type*) [Group G] : Prop :=
 ∃ (α : Type*) (rels : Set (FreeGroup α)), Nonempty (G ≃* PresentedGroup rels)

/- If we use `α : Type for isFinitelyPresented_iff_finite` then creates type incompatibility
with def of `IsPresentedGroup`. -/
instance {G : Type*} [Group G] [h : IsFinitelyPresented G] : IsPresented G := by
  rw [isFinitelyPresented_iff_finite] at h
  obtain ⟨α, _, f, hfsurj, hfker⟩ := h
  obtain ⟨S, hSfinite, hSclosure⟩ := hfker
  exact ⟨α, S, f, hfsurj, hSclosure⟩

instance {G : Type*} [Group G] [h : IsFinitelyPresented' G] : IsPresented' G := by
  rw [isFP_iff_finite'] at h
  obtain ⟨α, hα, rels, hrels, ⟨iso⟩⟩ := h
  use ULift α, Set.image (FreeGroup.map ULift.up) rels
  let e : ULift α ≃ α := Equiv.ulift
  refine ⟨iso.trans (PresentedGroup.equivPresentedGroup rels e.symm)⟩

instance {G : Type*} [Group G] [h : IsFinitelyPresented'' G] : IsPresented' G := by
  obtain ⟨α, hα, rels, hrels, ⟨iso⟩⟩ := h
  use ULift α, Set.image (FreeGroup.map ULift.up) rels
  let e : ULift α ≃ α := Equiv.ulift
  refine ⟨iso.trans (PresentedGroup.equivPresentedGroup rels e.symm)⟩


-- TODO? every group is isomorphic to a `PresentedGroup`!


lemma isFinitelyPresented''_of_finitelyPresentedGroup'
  {α : Type} [Finite α] (rels : Set (FreeGroup α)) (h : rels.Finite) :
  IsFinitelyPresented'' (FinitelyPresentedGroup' rels h) := by
  refine ⟨α, inferInstance, rels, h, ?_⟩
  exact ⟨MulEquiv.refl _⟩


lemma FinitelyPresentedGroup.is_FP {α : Type} [Finite α] (rels : Set (FreeGroup α)),
(IsFinitelyPresented''(FinitelyPresentedGroup(rels)))
/- namespace IsFinitelyPresented

variable {G H : Type*} [Group G] [Group H]

-- Finitely presented groups are closed under isomorphism
lemma of_equiv (e : G ≃* H) (h : IsFinitelyPresented G) :
    IsFinitelyPresented H := by
  sorry

-- Direct products of finitely presented groups are finitely presented
instance instProd [IsFinitelyPresented G] [IsFinitelyPresented H] :
    IsFinitelyPresented (G × H) := by
  sorry

-- Quotients of finitely presented groups by finitely generated normal subgroups
lemma quotient_of_fg_normal (N : Subgroup G) [N.Normal]
    [IsFinitelyPresented G] (hN : IsNormalClosureFG N) :
    IsFinitelyPresented (G ⧸ N) := by
  sorry

-- Trivial group is finitely presented
instance instTrivial : IsFinitelyPresented (Unit) := by
  sorry

-- Finite groups are finitely presented
instance instFinite [Finite G] : IsFinitelyPresented G := by
  sorry

end IsFinitelyPresented -/

/- -- Finitely generated free groups are finitely presented
instance FreeGroup.instFinitelyPresented (α : Type*) [Fintype α] :
    IsFinitelyPresented (FreeGroup α) := by
  sorry

-- Cyclic groups are finitely presented
instance Int.instFinitelyPresented : IsFinitelyPresented ℤ := by
  sorry

instance ZMod.instFinitelyPresented (n : ℕ) : IsFinitelyPresented (ZMod n) := by
  sorry -/
