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

universe u

-- Start of suggested additions to #Monoid.ker

-- TODO not sure if this is the right abstraction / right name for this.
/-- The kernel of a homomorphism composed with an isomorphism is equal to the kernel of
the homomorphism mapped by the inverse isomorphism. -/
@[simp]
lemma MonoidHom.ker_comp_mulEquiv {G H K : Type*} [Group G] [Group H] [Group K]
  (f : H →* K) (iso : G ≃* H) : (f.comp iso).ker = (Subgroup.map (iso.symm.toMonoidHom) f.ker) := by
  rw [← MonoidHom.comap_ker, Subgroup.comap_equiv_eq_map_symm]
  rfl

-- End of suggested additions to #Monoid.ker

-- Start of suggested additions to #FreeGroup
-- TODO review this
def FreeGroup.freeGroupEmptyMulEquivUnit : FreeGroup Empty ≃* Unit :=
{ toEquiv := FreeGroup.freeGroupEmptyEquivUnit
  map_mul' := by intro x y; rfl }

-- TODO review this
def FreeGroup.freeGroupUnitMulEquivInt :
    FreeGroup Unit ≃* Multiplicative ℤ := by
  refine
    { toFun := fun x => Multiplicative.ofAdd (FreeGroup.freeGroupUnitEquivInt x)
      invFun := fun z => FreeGroup.freeGroupUnitEquivInt.symm z.toAdd
      left_inv := by
        intro x
        simp
      right_inv := by
        intro z
        simp
      map_mul' := by
        intro x y
        ext
        simp [FreeGroup.freeGroupUnitEquivInt] }
-- end of addition to #FreeGroup

-- Start of suggested additions to #Group.FG
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

-- End of suggested additions to #Group.FG

-- Start of suggestion additions to #PresentedGroup

class IsPresented (G : Type*) [Group G] : Prop where
 out: ∃ (α : Type*) (rels : Set (FreeGroup α)), Nonempty (G ≃* PresentedGroup rels)

namespace IsPresented

/- When a FinitelyPresentedGroup G is defined as a PresentedGroup G, it naturally acquires the type
\α since `G = FreeGroup α / normalClosure rels` where `rels : Set (FreeGroup α)`.
On the other hand, when we write IsFinitelyPresented as `∃ α: Type` and a surjective map
`f: FreeGroup α →* G` such that `f.ker = normalClosure rels,`
since `MonoidHom` allows `FreeGroup α` and `G` to be different types,
we have to specify that `α` and `G` live in the same type universe to get the same result. -/
lemma iff_hom_surj {G : Type u} [Group G] : IsPresented G ↔
  ∃ (α : Type u) (rels : Set (FreeGroup α)) (f : FreeGroup α →* G),
  Function.Surjective f ∧ f.ker = Subgroup.normalClosure rels := by
    constructor
    · intro ⟨α, rels, ⟨iso⟩⟩
      -- TODO `use α` returns a type mismatch.
      sorry
    · sorry

end IsPresented
-- End of suggested additions to #PresentedGroup

-- Start of NormalClosureFG statements
open Subgroup

/- The normal closure of an empty set is the trivial subgroup. -/
lemma normalClosure_empty {G : Type*} [Group G] :
    Subgroup.normalClosure (∅ : Set G) = (⊥ : Subgroup G) := by
  apply le_antisymm
  · exact Subgroup.normalClosure_le_normal (N := (⊥ : Subgroup G)) (by simp)
  · exact bot_le

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

-- End of NormalClosureFG statements

def FinitelyPresentedGroup {α : Type} [Finite α] (rels : Set (FreeGroup α))
(_h : rels.Finite) := PresentedGroup (rels)

namespace FinitelyPresentedGroup

instance (α : Type) [Finite α] (rels : Set (FreeGroup α)) (h : rels.Finite) :
Group (FinitelyPresentedGroup rels h) :=
  QuotientGroup.Quotient.group _

end FinitelyPresentedGroup

class IsFinitelyPresented (G : Type*) [Group G] : Prop where
  out: ∃ (α : Type) (_: Finite α) (rels : Set (FreeGroup α)) (h : rels.Finite),
  Nonempty (G ≃* (FinitelyPresentedGroup rels h))

class IsOneRelator (G : Type*) [Group G] : Prop where
  out : ∃ (α : Type*) (rels : Set (FreeGroup α)) (hrels : rels.Finite),
      Nonempty (G ≃* PresentedGroup rels) ∧
      hrels.toFinset.card = 1

-- TODO calls to IsNormalClosureFG.map could be simplified? Like maybe using the iso functions.
  -- seems like we apply a lot of `MonoidHom.ker_comp_mulEquiv + IsNormalClosureFG.map`.

/- Every FP group is FG -/
instance isFP_isFG {G : Type*} [Group G] [h : IsFinitelyPresented G] : Group.FG G := by
  rw [Group.fg_iff_exists_freeGroup_hom_surjective_finite]
  obtain ⟨α, hα, rels, hrels, ⟨iso⟩⟩ := h
  unfold FinitelyPresentedGroup at iso
  unfold PresentedGroup at iso
  use α, hα
  -- TODO probably a nicer way to do this.
  let iso' := iso.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.normalClosure rels))
  use iso'
  simpa [iso'] using
    (Function.Surjective.comp iso.symm.surjective (QuotientGroup.mk'_surjective (Subgroup.normalClosure rels)))

instance isFP_isPresented {G : Type*} [Group G] [h : IsFinitelyPresented G] : IsPresented G := by
  obtain ⟨α, hα, rels, hrels, ⟨iso⟩⟩ := h
  use ULift α, Set.image (FreeGroup.map ULift.up) rels
  let e : ULift α ≃ α := Equiv.ulift
  refine ⟨iso.trans (PresentedGroup.equivPresentedGroup rels e.symm)⟩

-- TODO? every group is isomorphic to a `PresentedGroup`

namespace IsFinitelyPresented

/- Every FP group is FP -/
lemma FPgroup {α : Type} [Finite α] (rels : Set (FreeGroup α)) (h : rels.Finite) :
  IsFinitelyPresented (FinitelyPresentedGroup rels h) := by
  refine ⟨α, inferInstance, rels, h, ?_⟩
  exact ⟨MulEquiv.refl _⟩

theorem iff_hom_surj_finite {G : Type*} [Group G] :
IsFinitelyPresented G ↔ ∃ (α : Type) (_ : Finite α) (f : (FreeGroup α) →* G),
  Function.Surjective f ∧ IsNormalClosureFG (MonoidHom.ker f)  := by
  constructor
  · intro ⟨α, hα, rels, hrels, ⟨iso⟩⟩
    unfold FinitelyPresentedGroup at iso
    unfold PresentedGroup at iso
    let f : FreeGroup α →* G :=
      iso.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.normalClosure rels))
    have hfsurj : Function.Surjective f := by
      simpa [f] using
      (iso.symm.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.normalClosure rels)))
    have hfker : IsNormalClosureFG f.ker := by
      use rels, hrels
      ext x
      simp [f]
    exact ⟨α, hα, f, hfsurj, hfker⟩
  · intro ⟨α, hα, f, hfsurj, hfker⟩
    obtain ⟨S, hSfinite, hSnormalClosure⟩ := hfker
    use α, hα, S, hSfinite
    refine ⟨?_⟩
    unfold FinitelyPresentedGroup
    unfold PresentedGroup
    let iso1 : FreeGroup α ⧸ f.ker ≃* G :=
      QuotientGroup.quotientKerEquivOfSurjective (φ := f) hfsurj
    have iso2 : FreeGroup α ⧸ normalClosure S ≃* FreeGroup α ⧸ f.ker :=
      QuotientGroup.quotientMulEquivOfEq hSnormalClosure
    exact iso1.symm.trans iso2.symm

theorem iff_hom_surj_fin_n {G : Type*} [Group G] :
IsFinitelyPresented G ↔ ∃ (n : ℕ) (f : (FreeGroup (Fin n)) →* G),
  Function.Surjective f ∧ IsNormalClosureFG (MonoidHom.ker f)  := by
  rw [iff_hom_surj_finite]
  constructor
  · intro ⟨α, hα, f, hfsurj, hfker⟩
    let n := Nat.card α
    let iso : FreeGroup (Fin n) ≃* FreeGroup α :=
    FreeGroup.freeGroupCongr (Finite.equivFin α).symm
    let f' : FreeGroup (Fin n) →* G := f.comp iso
    let hf'surj := hfsurj.comp iso.surjective
    have hf'ker : IsNormalClosureFG f'.ker := by
      unfold f'
      simp only [MonoidHom.ker_comp_mulEquiv]
      exact
      IsNormalClosureFG.invariant_surj_hom iso.symm.toMonoidHom iso.symm.surjective f.ker hfker
    exact ⟨n, f', hf'surj, hf'ker⟩
  · intro ⟨n, f, hfsurj, hfker⟩
    let α := Fin n
    use α, inferInstance, f



-- TODO I think this needs to work for any presented group.
/- If you FreeGroup α by an empty set, you get the original group -/
def quotient_normalClosure_empty_mulEquiv (α : Type*) :
    FreeGroup α ⧸ Subgroup.normalClosure (∅ : Set (FreeGroup α)) ≃* FreeGroup α := by
  have hbot :
      Subgroup.normalClosure (∅ : Set (FreeGroup α)) = (⊥ : Subgroup (FreeGroup α)) := by
    simpa using (normalClosure_empty (G := FreeGroup α))
  exact (QuotientGroup.quotientMulEquivOfEq hbot).trans
    (QuotientGroup.quotientBot (G := FreeGroup α))

/- FreeGroup on finitely many generators is FP -/
/- instance {α : Type} [Finite α] IsFinitelyPresented (FreeGroup α) := by
  sorry -/

/- Trivial group is FP -/
instance instTrivial : IsFinitelyPresented (Unit) := by
  let α := Empty
  let rels := (∅ : Set (FreeGroup Empty))
  have hrels : rels.Finite := by
    simp [rels]
  use α, inferInstance, rels, hrels
  let iso := FreeGroup.freeGroupEmptyMulEquivUnit
  unfold FinitelyPresentedGroup
  unfold PresentedGroup
  refine ⟨?_⟩
  have qiso : FreeGroup α ⧸ Subgroup.normalClosure rels ≃* FreeGroup α := by
    simpa [rels] using quotient_normalClosure_empty_mulEquiv (α := α)
  unfold α at qiso
  exact iso.symm.trans qiso.symm

/- ℤ is finitely presented -/
instance Int.instFinitelyPresented : IsFinitelyPresented (Multiplicative ℤ) := by
  let α := Unit
  let rels := (∅ : Set (FreeGroup α))
  have hrels : rels.Finite := by
    simp [rels]
  use α, inferInstance, rels, hrels
  unfold FinitelyPresentedGroup
  unfold PresentedGroup
  refine ⟨?_⟩
  have qiso : FreeGroup α ⧸ Subgroup.normalClosure rels ≃* FreeGroup α := by
    simpa [rels] using quotient_normalClosure_empty_mulEquiv (α := α)
  let iso := FreeGroup.freeGroupUnitMulEquivInt
  unfold α at qiso
  exact iso.symm.trans qiso.symm

variable {G H : Type*} [Group G] [Group H]

/- FP groups are closed under isomorphism -/
lemma of_mulEquiv {G H : Type*} [Group G] [Group H]
(iso : G ≃* H) (h : IsFinitelyPresented G) :
    IsFinitelyPresented H := by
    obtain ⟨α, hα, rels, hrels, ⟨iso'⟩⟩ := h
    exact ⟨α, hα, rels, hrels, ⟨ iso.symm.trans iso' ⟩⟩

-- TODO: it makes more sense to write this for PresentedGroup first and then unfold.
/- Direct products of finitely presented groups are finitely presented -/
instance instProd [hG : IsFinitelyPresented G] [hH : IsFinitelyPresented H] :
  IsFinitelyPresented (G × H) := by
  obtain ⟨α, hα, Grels, hGrels, ⟨Giso⟩⟩ := hG
  obtain ⟨β, hβ, Hrels, hHrels, ⟨Hiso⟩⟩ := hH
  simp only [FinitelyPresentedGroup] at Giso Hiso
  use α ⊕ β, inferInstance
  let Grels_prod : Set (FreeGroup (α ⊕ β)) := FreeGroup.map Sum.inl '' Grels
  let Hrels_prod : Set (FreeGroup (α ⊕ β)) := FreeGroup.map Sum.inr '' Hrels
  have hGrels_prod : Grels_prod.Finite := by
    simpa [Grels_prod] using hGrels.image (FreeGroup.map Sum.inl)
  have hHrels_prod : Hrels_prod.Finite := by
    simpa [Hrels_prod] using hHrels.image (FreeGroup.map Sum.inr)
  -- TODO this should be refactored.
  let comms : Set (FreeGroup (α ⊕ β)) :=
  (fun p => ⁅p.1, p.2⁆) '' (Grels_prod ×ˢ Hrels_prod)
  have hcomm : comms.Finite := by
  -- comms = image of commutator on Grels_prod ×ˢ Hrels_prod
    simpa [comms] using (Set.Finite.image (fun p => ⁅p.1, p.2⁆) (hGrels_prod.prod hHrels_prod))
  let rels_prod : Set (FreeGroup (α ⊕ β)) :=
  Grels_prod ∪ Hrels_prod ∪ comms
  have hrels_prod : rels_prod.Finite := by
  -- assuming hGrels_prod : Grels_prod.Finite, hHrels_prod : Hrels_prod.Finite
    simpa [rels_prod] using (hGrels_prod.union hHrels_prod).union hcomm
  refine ⟨rels_prod, hrels_prod, ?_⟩
  refine ⟨?_iso⟩
  have e₁ : G × H ≃* PresentedGroup Grels × PresentedGroup Hrels :=
    MulEquiv.prodCongr Giso Hiso
  sorry

lemma quotient_of_normalClosureFG (N : Subgroup G) [N.Normal]
    [hG : IsFinitelyPresented G] (hN : IsNormalClosureFG N) :
    IsFinitelyPresented (G ⧸ N) := by
    obtain ⟨α, hα, rels, hrels, ⟨iso⟩⟩ := hG
    unfold FinitelyPresentedGroup at iso
    unfold PresentedGroup at iso
    let N' := N.map iso.toMonoidHom
    have hN'normal : N'.Normal :=
     Subgroup.Normal.map (H := N) (h := inferInstance) (f := iso.toMonoidHom) iso.surjective
    have hN'closureFG : IsNormalClosureFG N' := by
      simpa [N'] using
    (IsNormalClosureFG.invariant_surj_hom (f := iso.toMonoidHom)
      (hf := iso.surjective) (K := N) hN)
    have he : Subgroup.map (↑iso) N = N' := by
      rfl
    have qiso : G ⧸ N ≃* (FreeGroup α ⧸ Subgroup.normalClosure rels) ⧸ N' :=
      QuotientGroup.congr N N' iso he
    obtain ⟨S, hS, hSClosure⟩ := hN'closureFG
    -- TODO show isomorphism (FreeGroup α ⧸ normalClosure rels) ⧸ N' with (FreeGroup α ⧸ normalClosure (rels ∪ S))
    sorry

end IsFinitelyPresented

/- namespace IsFinitelyPresented

variable {G H : Type*} [Group G] [Group H]

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
