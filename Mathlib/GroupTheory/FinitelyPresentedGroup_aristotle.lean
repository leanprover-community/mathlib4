/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7cacf65b-61e4-4470-9402-e1d71fabcc98

The following was proved by Aristotle:

- lemma isFinitelyPresented_iff_fintype {G : Type*} [Group G] :
    IsFinitelyPresented G ↔ ∃ (α : Type*) (_ : Fintype α) (f : FreeGroup α →* G),
    Function.Surjective f ∧ IsNormalClosureFG (f.ker)
-/

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

/-- The kernel of a homomorphism composed with an isomorphism is equal to the kernel of
the homomorphism mapped by the inverse isomorphism. -/
@[simp]
lemma MonoidHom.ker_comp_mulEquiv {G H K : Type*} [Group G] [Group H] [Group K]
    (f : H →* K) (e : G ≃* H) : (f.comp e.toMonoidHom).ker = (Subgroup.map (↑e.symm) f.ker) := by
  rw [← MonoidHom.comap_ker, Subgroup.comap_equiv_eq_map_symm']
  rfl

def FinitelyPresentedGroup (n : ℕ) (rels : Set (FreeGroup (Fin n))) (_h : rels.Finite) : Type :=
  FreeGroup (Fin n) ⧸ Subgroup.normalClosure (rels : Set (FreeGroup (Fin n)))

open Subgroup

/-- Definition of subgroup that is given by the normal closure of finitely many elements. -/
def IsNormalClosureFG {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ S : Set G, S.Finite ∧ Subgroup.normalClosure S = H

/-- The above property is invariant under surjective homomorphism. -/
lemma IsNormalClosureFG.map {G H : Type*} [Group G] [Group H]
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

lemma isFinitelyPresented_iff_fintype' {G : Type*} [Group G] :
    IsFinitelyPresented G ↔ ∃ (α : Type*) (_ : Fintype α) (f : FreeGroup α →* G),
    Function.Surjective f ∧ IsNormalClosureFG (f.ker) := by
    constructor <;> intro h;
    · obtain ⟨ n, f, hf₁, hf₂ ⟩ := h.out;
      refine' ⟨ ULift ( Fin n ), inferInstance, _, _, _ ⟩;
      exact f.comp ( FreeGroup.map fun x => x.down );
      · intro g;
        obtain ⟨ x, rfl ⟩ := hf₁ g;
        refine' ⟨ FreeGroup.map ( fun x => ⟨ x ⟩ ) x, _ ⟩;
        induction x using FreeGroup.induction_on <;> aesop;
      · obtain ⟨ S, hS₁, hS₂ ⟩ := hf₂;
        refine' ⟨ S.image ( FreeGroup.map fun x => ULift.up x ), _, _ ⟩;
        · exact hS₁.image _;
        · convert congr_arg ( Subgroup.map ( FreeGroup.map fun x => ULift.up x ) ) hS₂ using 1;
          · refine' le_antisymm _ _;
            · simp +decide [ Subgroup.normalClosure ];
              simp +decide [ Set.subset_def, Group.conjugatesOfSet ];
              simp +decide [ conjugatesOf ];
              rintro x y hy z rfl;
              refine' ⟨ FreeGroup.map ( fun x => x.down ) z * y * ( FreeGroup.map ( fun x => x.down ) z ) ⁻¹, _, _ ⟩ <;> simp +decide [ Subgroup.mem_closure ];
              · exact fun K hK => hK y hy ⟨ FreeGroup.map ( fun x => x.down ) z, rfl ⟩;
              · congr! 1;
                · refine' FreeGroup.induction_on z _ _ _ _ <;> aesop;
                · refine' FreeGroup.induction_on z _ _ _ _ <;> aesop;
            · simp +decide [ Subgroup.map_le_iff_le_comap, Subgroup.normalClosure ];
              simp +decide [ Set.subset_def, Group.conjugatesOfSet ];
              simp +decide [ conjugatesOf ];
              rintro x y hy z rfl;
              exact Subgroup.subset_closure ( Set.mem_iUnion₂.2 ⟨ y, hy, ⟨ FreeGroup.map ( fun x => ULift.up x ) z, by simp +decide ⟩ ⟩ );
          · ext; simp +decide [ MonoidHom.mem_ker ] ;
            constructor;
            · rename_i x;
              refine' fun hx => ⟨ FreeGroup.map ( fun x => x.down ) x, hx, _ ⟩;
              refine' FreeGroup.induction_on x _ _ _ _ <;> aesop;
            · rintro ⟨ x, hx₁, rfl ⟩;
              convert hx₁;
              refine' FreeGroup.induction_on x _ _ _ _ <;> aesop;
    · obtain ⟨ α, _hα, f, hf_surj, hf_ker ⟩ := h
      have h_finite : ∃ (n : ℕ) (g : (FreeGroup (Fin n)) →* G),
        Function.Surjective g ∧ IsNormalClosureFG (MonoidHom.ker g) := by
          obtain ⟨n, g, hg⟩ : ∃ n : ℕ, ∃ g : FreeGroup (Fin n) ≃* FreeGroup α, True := by
            refine' ⟨ Fintype.card α, _, trivial ⟩;
            exact FreeGroup.freeGroupCongr ( Fintype.equivOfCardEq ( by simp +decide ) );
          refine' ⟨ n, f.comp g.toMonoidHom, _, _ ⟩;
          · exact hf_surj.comp g.surjective;
          · convert hf_ker.map g.symm.toMonoidHom _;
            · ext; simp +decide [ MonoidHom.mem_ker ] ; aesop;
            · exact g.symm.surjective
      exact ⟨ h_finite ⟩

lemma isFinitelyPresented_iff_fintype {G : Type*} [Group G] :
    IsFinitelyPresented G ↔ ∃ (α : Type*) (_ : Fintype α) (f : FreeGroup α →* G),
    Function.Surjective f ∧ IsNormalClosureFG (f.ker) := by
  constructor
  · intro ⟨n, f, hfsurj, hfkernel⟩
    refine ⟨ULift (Fin n), inferInstance, f.comp (FreeGroup.map ULift.down), ?_, ?_⟩
    ·
      -- Since $f$ is surjective and the inclusion map is surjective, their composition is also surjective.
      apply Function.Surjective.comp hfsurj;
      -- Since ULift.down is the identity function, the map FreeGroup.map ULift.down is also the identity function on the free group. Therefore, for any b in the free group of Fin n, we can take a = b.
      intro b
      use FreeGroup.map (fun x => ULift.up x) b;
      induction b using FreeGroup.induction_on <;> aesop
    ·
      convert hfkernel.map _ _;
      rotate_left;
      -- Define the homomorphism from the free group on Fin n to the free group on ULift (Fin n) by mapping each generator to the corresponding generator in ULift (Fin n).
      let g : FreeGroup (Fin n) →* FreeGroup (ULift (Fin n)) := FreeGroup.map ULift.up;
      exact g;
      · intro x;
        refine' FreeGroup.induction_on x _ _ _ _;
        · exact ⟨ 1, by simp +decide ⟩;
        · exact fun x => ⟨ FreeGroup.of x.down, by simp +decide ⟩;
        · exact fun x hx => ⟨ hx.choose⁻¹, by simp +decide [ hx.choose_spec ] ⟩;
        · rintro x y ⟨ a, rfl ⟩ ⟨ b, rfl ⟩ ; exact ⟨ a * b, by simp +decide ⟩;
      · -- The kernel of the composition is the preimage of the kernel of $f$ under the map $g$.
        ext; simp [MonoidHom.mem_ker, Function.comp];
        constructor;
        · rename_i x;
          refine' fun hx => ⟨ FreeGroup.map ULift.down x, hx, _ ⟩;
          refine' FreeGroup.induction_on x _ _ _ _ <;> aesop;
        · rintro ⟨ x, hx, rfl ⟩;
          convert hx;
          refine' FreeGroup.induction_on x _ _ _ _ <;> aesop
  · intro ⟨α, _, f, hfsurj, hfkernel⟩
    let iso : FreeGroup (Fin (Fintype.card α)) ≃* FreeGroup α :=
      FreeGroup.freeGroupCongr (Fintype.equivFin α).symm
    refine ⟨Fintype.card α, f.comp iso.toMonoidHom, hfsurj.comp iso.surjective, ?_⟩
    simp only [MonoidHom.ker_comp_mulEquiv] -- this could further be factored as a lemma I feel.
    exact IsNormalClosureFG.map iso.symm.toMonoidHom iso.symm.surjective f.ker hfkernel

/- lemma isFinitelyPresented_iff_set_finite {G : Type*} [Group G] :
    IsFinitelyPresented G ↔ ∃ (S : Set G), ∃ (_ : S.Finite) (f : FreeGroup S →* G),
    Function.Surjective f ∧ IsNormalClosureFG (f.ker) := by
    constructor
    · intro ⟨n, f, hfsurj, hfkernel⟩
      let S : Set G := Set.range (fun i : Fin n => f (FreeGroup.of i))
      have hSfinite : S.Finite := Set.finite_range _
      refine ⟨S, hSfinite, ?_⟩
      let g : S → G := fun ⟨x, hx⟩ => x  -- Inclusion map
      let φ : FreeGroup S →* G := FreeGroup.lift g
      sorry
    · sorry -/

variable (G : Type*) [Group G] (g : G)

theorem Group.fg_iff_exists_freeGroup_hom_surjective' :
    Group.FG G ↔ ∃ (S : Set G) (_ : S.Finite) (φ : FreeGroup S →* G), Function.Surjective φ := by
  refine ⟨fun ⟨S, hS⟩ ↦ ⟨S, S.finite_toSet, FreeGroup.lift Subtype.val, ?_⟩, ?_⟩
  · rwa [← MonoidHom.range_eq_top, ← FreeGroup.closure_eq_range]
  · rintro ⟨S, hfin : Finite S, φ, hφ⟩
    refine fg_iff.mpr ⟨φ '' Set.range FreeGroup.of, ?_, Set.toFinite _⟩
    simp [← MonoidHom.map_closure, hφ, FreeGroup.closure_range_of, ← MonoidHom.range_eq_map]

theorem Group.fg_iff_exists_freeGroup_hom_surjective_fintype {G : Type*} [Group G] :
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

instance [h : IsFinitelyPresented G] : Group.FG G := by
  rw [Group.fg_iff_exists_freeGroup_hom_surjective_fintype]
  rw [isFinitelyPresented_iff_fintype] at h
  obtain ⟨S, hSfinite, f, hfsurj, hkernel⟩ := h
  use S, hSfinite, f, hfsurj

def IsPresentedGroup (G : Type*) [Group G] : Prop :=
  ∃ (α : Type*) (rels : Set (FreeGroup α)), Nonempty (G ≃* PresentedGroup rels)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

unsolved goals
case h.e'_4.e'_2.e'_2.e'_2.e'_2.e'_2
G : Type u_1
inst✝ : Group G
g : G
h : IsFinitelyPresented G
α : Type u_2
instα : Fintype α
f : FreeGroup α →* G
hfsurj : Function.Surjective (⇑f : FreeGroup α → G)
S : Set (FreeGroup α)
hSfinite : S.Finite
hSclosure : Subgroup.normalClosure S = f.ker
iso : G ≃* FreeGroup α ⧸ f.ker := (QuotientGroup.quotientKerEquivOfSurjective f hfsurj).symm
e_2✝ : PresentedGroup S = (FreeGroup α ⧸ f.ker)
⊢ PresentedGroup.instGroup S ≍ QuotientGroup.Quotient.group f.ker-/
instance [h : IsFinitelyPresented G] : IsPresentedGroup G := by
  obtain ⟨α, instα, f, hfsurj, hfkernel⟩ := isFinitelyPresented_iff_fintype.mp h
  obtain ⟨S, hSfinite, hSclosure⟩ := hfkernel
  use α, S
  let iso := (QuotientGroup.quotientKerEquivOfSurjective f hfsurj).symm
  refine ⟨?_⟩
  convert iso
  sorry