/-
Copyright (c) Hang Lu Su 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Fabrizio Barroero, Stefano Francaviglia,
  Francesco Milizia, Valerio Proietti, Hang Lu Su, Lawrence Wu
-/

import Mathlib

/-!
# Finitely Presented Groups

This file defines finitely presented groups and proves their basic properties.

## Main definitions

## Main results

## Tags
finitely presented group, normal closure finitely generated,
-/
-- TODO not sure if this is the right abstraction / right name for this.
/-- The kernel of a homomorphism composed with an isomorphism is equal to the kernel of
the homomorphism mapped by the inverse isomorphism. -/
@[simp]
lemma MonoidHom.ker_comp_mulEquiv {G H K : Type*} [Group G] [Group H] [Group K]
    (f : H →* K) (e : G ≃* H) : (f.comp e).ker = (Subgroup.map (e.symm.toMonoidHom) f.ker) := by
  rw [← MonoidHom.comap_ker, Subgroup.comap_equiv_eq_map_symm]
  rfl

def FinitelyPresentedGroup (n : ℕ) (rels : Set (FreeGroup (Fin n))) (_h : rels.Finite) : Type :=
  FreeGroup (Fin n) ⧸ Subgroup.normalClosure (rels : Set (FreeGroup (Fin n)))

open Subgroup
#check @QuotientGroup.Quotient.group

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

universe u

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

theorem Group.fg_iff_exists_freeGroup_hom_surjective_finite {G : Type u} [Group G] :
    Group.FG G ↔ ∃ (α : Type u) (_ : Finite α) (φ : FreeGroup α →* G), Function.Surjective φ := by
      · sorry

instance {G : Type*} [Group G] [h : IsFinitelyPresented G] : Group.FG G := by
  rw [Group.fg_iff_exists_freeGroup_hom_surjective_finite]
  rw [isFinitelyPresented_iff_finite] at h
  obtain ⟨S, hSfinite, f, hfsurj, hkernel⟩ := h
  use S, hSfinite, f, hfsurj

-- TODO this uses `(α : Type)` not `(α : Type*)` as was defined in `PresentedGroup.lean`.
def IsPresentedGroup (G : Type u) [Group G] : Prop :=
  ∃ (α : Type u) (rels : Set (FreeGroup α)), Nonempty (G ≃* PresentedGroup rels)

-- TODO shorten this.
instance {G : Type*} [Group G] [h : IsFinitelyPresented G] : IsPresentedGroup G := by
  rw [isFinitelyPresented_iff_finite] at h
  obtain ⟨α, _, f, hfsurj, hfkernel⟩ := h
  obtain ⟨S, hSfinite, hSclosure⟩ := hfkernel
  unfold IsPresentedGroup
  use α, S
  let iso := (QuotientGroup.quotientKerEquivOfSurjective f hfsurj).symm
  refine ⟨?_⟩
  unfold PresentedGroup
  let hSclosure_equiv := QuotientGroup.quotientMulEquivOfEq hSclosure
  let iso' := iso.trans hSclosure_equiv.symm
  exact iso'


/-   lemma fpGroup_is_fgGroup (G: Type*) [Group G] (h: IsFinitelyPresented G) : Group.FG G := by
  rw [Group.fg_iff_exists_freeGroup_hom_surjective]
  apply isFinitelyPresented_iff at G
  --constructor
  sorry -/

/- lemma isFinitelyPresented_stupid (α : Type) [Finite α] (s : Finset (FreeGroup α)) :
    IsFinitelyPresented ((FreeGroup α) ⧸ normalClosure s) := by
    rw [isFinitelyPresented_iff]
    constructor
    sorry -/

/- namespace IsFinitelyPresented

variable {G H : Type*} [Group G] [Group H]

-- Finitely presented groups are closed under isomorphism
lemma of_equiv (e : G ≃* H) (h : IsFinitelyPresented G) :
    IsFinitelyPresented H := by
  sorry

-- Trivial group is finitely presented
instance instTrivial : IsFinitelyPresented (Unit) := by
  sorry

-- Finite groups are finitely presented
instance instFinite [Finite G] : IsFinitelyPresented G := by
  sorry

end IsFinitelyPresented -/

/- -- Free groups are finitely presented
instance FreeGroup.instFinitelyPresented (α : Type*) [Fintype α] :
    IsFinitelyPresented (FreeGroup α) := by
  sorry

-- Cyclic groups are finitely presented
instance Int.instFinitelyPresented : IsFinitelyPresented ℤ := by
  sorry

instance ZMod.instFinitelyPresented (n : ℕ) : IsFinitelyPresented (ZMod n) := by
  sorry -/
