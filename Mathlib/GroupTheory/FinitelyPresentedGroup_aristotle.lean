/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7338c39c-1304-43e9-882d-add99ff908d0

The following was proved by Aristotle:

- lemma isFinitelyPresented_iff_fintype {G : Type*} [Group G] :
  IsFinitelyPresented G ↔ ∃ (α : Type) (_ : Fintype α) (f : FreeGroup α →* G),
  Function.Surjective f ∧ IsNormalClosureOfFiniteSet (MonoidHom.ker f)

- lemma of_equiv (e : G ≃* H) (h : IsFinitelyPresented G) :
    IsFinitelyPresented H

- instance instTrivial : IsFinitelyPresented (Unit)

- instance instFinite [Finite G] : IsFinitelyPresented G
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

open Subgroup

def IsNormalClosureOfFiniteSet {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ S : Set G, S.Finite ∧ Subgroup.normalClosure S = H

class IsFinitelyPresented (G : Type*) [Group G] : Prop where
  out : ∃ (n : ℕ) (f : (FreeGroup (Fin n)) →* G),
    Function.Surjective f ∧ IsNormalClosureOfFiniteSet (MonoidHom.ker f)

/- lemma isFinitelyPresented_iff_finite_set {G : Type*} [Group G] :
  IsFinitelyPresented G ↔ ∃ (S : Set G) (f : FreeGroup S →* G), S.Finite ∧
  Function.Surjective f ∧ IsNormalClosureOfFiniteSet (MonoidHom.ker f) := by
    constructor
    · -- mp
      intro ⟨n, f', hfsurj, hkernel⟩
      let S : Set G := Set.range (fun i : Fin n => f' (FreeGroup.of i))
      have hSfinite : S.Finite := Set.finite_range (fun i : Fin n => f' (FreeGroup.of i))
      use S
      sorry
    · -- mpr
      sorry -/

noncomputable section AristotleLemmas

/-
The image of a finitely generated normal subgroup under a surjective homomorphism is also a finitely generated normal subgroup.
-/
lemma IsNormalClosureOfFiniteSet_map {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f) (K : Subgroup G) (hK : IsNormalClosureOfFiniteSet K) : IsNormalClosureOfFiniteSet (K.map f) := by
  obtain ⟨ S, hSf, hS ⟩ := hK;
  refine' ⟨ f '' S, hSf.image _, _ ⟩;
  rw [ ← hS, Subgroup.map_normalClosure ];
  exact hf

/-
The kernel of the map between free groups induced by a surjective map of finite sets is the normal closure of a finite set.
-/
lemma ker_map_of_surjective_isNormalClosureOfFiniteSet {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) (hf : Function.Surjective f) : IsNormalClosureOfFiniteSet (MonoidHom.ker (FreeGroup.map f)) := by
  -- Let $S = \{ \text{of } x \cdot (\text{of } y)^{-1} \mid x, y \in \alpha, f(x) = f(y) \}$. This set is finite.
  set S : Set (FreeGroup α) := {g | ∃ x y : α, g = FreeGroup.of x * (FreeGroup.of y)⁻¹ ∧ f x = f y} with hS_def;
  -- Clearly $S \subseteq \ker(\text{map } f)$, so $N \le \ker(\text{map } f)$.
  have hN_le : Subgroup.normalClosure S ≤ MonoidHom.ker (FreeGroup.map f) := by
    refine' Subgroup.normalClosure_le_normal _;
    rintro _ ⟨ x, y, rfl, hxy ⟩ ; simp +decide [ hxy ];
  -- To show the reverse inclusion, consider the quotient $Q = \text{FreeGroup } \alpha / N$.
  set Q := FreeGroup α ⧸ Subgroup.normalClosure S with hQ_def;
  -- We can define a map $g: \text{FreeGroup } \beta \to Q$ by mapping each $b \in \beta$ to the class of some $x \in f^{-1}(b)$.
  obtain ⟨g, hg⟩ : ∃ g : FreeGroup β →* Q, ∀ b : β, ∀ x : α, f x = b → g (FreeGroup.of b) = QuotientGroup.mk (FreeGroup.of x) := by
    choose g hg using hf;
    refine' ⟨ FreeGroup.lift ( fun b => QuotientGroup.mk ( FreeGroup.of ( g b ) ) ), fun b x hx => _ ⟩;
    -- Since $f x = b$, we have $FreeGroup.of x * (FreeGroup.of (g b))⁻¹ \in S$.
    have h_mem_S : FreeGroup.of x * (FreeGroup.of (g b))⁻¹ ∈ Subgroup.normalClosure S := by
      exact Subgroup.subset_normalClosure ⟨ x, g b, rfl, by aesop ⟩;
    erw [ QuotientGroup.eq ];
    simpa [ mul_assoc ] using Subgroup.normalClosure_normal.conj_mem _ h_mem_S ( FreeGroup.of ( g b ) ) ⁻¹;
  -- The composition $\text{FreeGroup } \alpha \to \text{FreeGroup } \beta \to Q$ is the canonical projection, so the kernel of $\text{FreeGroup } \alpha \to \text{FreeGroup } \beta$ is contained in $N$.
  have h_comp : ∀ x : FreeGroup α, g (FreeGroup.map f x) = QuotientGroup.mk x := by
    intro x;
    induction x using FreeGroup.induction_on <;> aesop;
  -- Therefore, the kernel of $\text{FreeGroup } \alpha \to \text{FreeGroup } \beta$ is contained in $N$.
  have h_ker_le : MonoidHom.ker (FreeGroup.map f) ≤ Subgroup.normalClosure S := by
    intro x hx;
    specialize h_comp x;
    simp_all +decide [ QuotientGroup.eq ];
    rw [ eq_comm, QuotientGroup.eq_one_iff ] at h_comp ; aesop;
  refine' ⟨ S, _, _ ⟩;
  · exact Set.Finite.subset ( Set.toFinite ( Set.range fun p : α × α => FreeGroup.of p.1 * ( FreeGroup.of p.2 ) ⁻¹ ) ) fun x hx => by aesop;
  · exact le_antisymm hN_le h_ker_le

end AristotleLemmas

lemma isFinitelyPresented_iff_fintype {G : Type*} [Group G] :
  IsFinitelyPresented G ↔ ∃ (α : Type) (_ : Fintype α) (f : FreeGroup α →* G),
  Function.Surjective f ∧ IsNormalClosureOfFiniteSet (MonoidHom.ker f) := by
    constructor
    · -- mp
      intro ⟨n, f, hfsurj, hkernel⟩
      use Fin n, inferInstance, f
    · -- mpr
      intro ⟨α, instα, f, hfsurj, hkernel⟩
      haveI := instα  -- Register the Fintype instance
      let n := Fintype.card α
      let e := Fintype.equivFin α
      let e' := FreeGroup.map e.invFun
      let f' := f.comp (e')
      use n, f'
      constructor
      · have he'surj : Function.Surjective e' := by
          -- Since `e` is an equivalence, its inverse is also a bijection, and thus the image of `e'` is all of `FreeGroup α`.
          have he'_surj : Function.Surjective (FreeGroup.map e.invFun) := by
            intro x
            exact ⟨FreeGroup.map e x, by
              induction x using FreeGroup.induction_on <;> aesop⟩;
          exact he'_surj
        -- Since $e'$ is surjective and $f$ is surjective, their composition $f'$ is also surjective.
        apply Function.Surjective.comp hfsurj he'surj
      ·
        -- Since `e'` is surjective, `ker f'` is the normal closure of a finite set.
        have hker_surj : Function.Surjective e' := by
          -- Since `e` is an equivalence, its inverse is also a bijection, and thus the image of `e'` is all of `FreeGroup α`.
          have he'_surj : Function.Surjective (FreeGroup.map e.invFun) := by
            intro x
            exact ⟨FreeGroup.map e x, by
              induction x using FreeGroup.induction_on <;> aesop⟩;
          exact he'_surj;
        convert IsNormalClosureOfFiniteSet_map _ _ _ hkernel using 1;
        rotate_left;
        exact FreeGroup.map e;
        · intro x;
          refine' ⟨ FreeGroup.map ( e.symm ) x, _ ⟩;
          induction x using FreeGroup.induction_on <;> aesop;
        · ext; simp [f'];
          constructor;
          · intro hx;
            rename_i x;
            refine' ⟨ e' x, hx, _ ⟩;
            refine' FreeGroup.induction_on x _ _ _ _ <;> aesop;
          · rintro ⟨ x, hx, rfl ⟩;
            convert hx;
            refine' FreeGroup.induction_on x _ _ _ _ <;> aesop

variable (G : Type) [Group G] (g : G)

/- instance [h : IsFinitelyPresented G] : Group.FG G := by
  rw [isFinitelyPresented_iff'] at h
  rw [Group.fg_iff_exists_freeGroup_hom_surjective]
  obtain ⟨S, f, hfsurj, hkernel⟩ := h
  use S
  constructor
  · use f
    exact hfsurj
  · exact Finset.finite_toSet S -/

/- instance [h : IsFinitelyPresented G] : PresentedGroup G := by
  sorry
-/

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

namespace IsFinitelyPresented

variable {G H : Type*} [Group G] [Group H]

-- Finitely presented groups are closed under isomorphism
lemma of_equiv (e : G ≃* H) (h : IsFinitelyPresented G) :
    IsFinitelyPresented H := by
  obtain ⟨ n, f, hf₁, hf₂ ⟩ := h;
  -- Let $f' = e \circ f$. We need to show that $f'$ is surjective and its kernel is finitely generated.
  use n, e.toMonoidHom.comp f;
  simp +zetaDelta at *;
  unfold IsNormalClosureOfFiniteSet at *; aesop;

-- Trivial group is finitely presented
instance instTrivial : IsFinitelyPresented (Unit) := by
  -- The trivial group is finitely presented because it can be presented with no generators and no relations.
  use 0, (1 : FreeGroup (Fin 0) →* Unit), by
    exact fun _ => ⟨ 1, rfl ⟩;
  -- The trivial subgroup is generated by the empty set, which is finite.
  use ∅; simp;
  simp +decide [ Subgroup.normalClosure ]

-- Finite groups are finitely presented
noncomputable section AristotleLemmas

/-
A finitely generated normal subgroup is the normal closure of a finite set.
-/
lemma normalClosure_of_fg_normal_subgroup {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (h : N.FG) : IsNormalClosureOfFiniteSet N := by
  obtain ⟨ S, hS ⟩ := h;
  refine' ⟨ S, _, _ ⟩;
  · exact S.finite_toSet;
  · refine' le_antisymm _ _;
    · simp +decide [ ← hS, Subgroup.normalClosure ];
      simp +decide [ Set.subset_def, Group.conjugatesOfSet ];
      simp +decide [ conjugatesOf ];
      -- Since $N$ is normal, conjugating any element of $N$ by any element of $G$ keeps it in $N$.
      have h_normal : ∀ x : G, ∀ n : G, n ∈ N → x * n * x⁻¹ ∈ N := by
        exact fun x n hn => Subgroup.Normal.mem_comm inferInstance ( by simpa using hn );
      aesop;
    · exact hS ▸ Subgroup.closure_le_normalClosure

/-
The free group on a finite type is finitely generated.
-/
instance freeGroup_fg_of_fintype {α : Type*} [Fintype α] : Group.FG (FreeGroup α) := by
  exact ⟨ Set.Finite.toFinset ( Set.toFinite ( Set.range FreeGroup.of ) ), by simpa ⟩

end AristotleLemmas

instance instFinite [Finite G] : IsFinitelyPresented G := by
  have h_finite_quotient : ∃ (n : ℕ) (f : FreeGroup (Fin n) →* G), Function.Surjective f ∧ (MonoidHom.ker f).FiniteIndex := by
    obtain ⟨f, hf⟩ : ∃ (n : ℕ) (f : FreeGroup (Fin n) →* G), Function.Surjective f := by
      -- Since $G$ is finite, we can take $n$ to be the cardinality of $G$ and define $f$ by mapping each generator to an element of $G$.
      obtain ⟨n, hn⟩ : ∃ n : ℕ, Nonempty (Fin n ≃ G) := by
        haveI := Fintype.ofFinite G; exact ⟨ Fintype.card G, ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩ ⟩ ;
      obtain ⟨ e ⟩ := hn;
      refine' ⟨ n, FreeGroup.lift ( fun i => e i ), _ ⟩;
      intro x; use FreeGroup.of ( e.symm x ) ; aesop;
    obtain ⟨ f, hf ⟩ := hf;
    exact ⟨ _, f, hf, Subgroup.finiteIndex_of_finite_quotient ⟩;
  choose n f hf using h_finite_quotient;
  have h_finite_quotient : (MonoidHom.ker f).FG := by
    have h_finite_quotient : Group.FG (FreeGroup (Fin n)) := by
      infer_instance;
    convert Subgroup.fg_of_index_ne_zero _;
    rotate_left;
    exact FreeGroup ( Fin n );
    exact inferInstance;
    exact f.ker;
    · exact h_finite_quotient;
    · exact hf.2;
    · exact?;
  have := @normalClosure_of_fg_normal_subgroup;
  exact ⟨ n, f, hf.1, this _ h_finite_quotient ⟩

end IsFinitelyPresented