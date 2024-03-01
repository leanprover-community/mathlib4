/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Shapes.CombinedProducts

/-!
# Decomposition of objects into connected components and applications

We show that in a Galois category every object is the (finite) coproduct of connected subobjects.
This has many useful corollaries, in particular that the fiber of every object
is represented by a Galois object (TODO).

## Main results

* `has_decomp_connected_components`: Every object is the sum of its (finitely many) connected
  components.
* `fiber_in_connected_component`: An element of the fiber of `X` lies in the fiber of some
  connected component.
* `connected_component_unique`: Up to isomorphism, for each element `x` in the fiber of `X` there
  is only one connected component whose fiber contains `x`.

-/

universe u₁ u₂ w

namespace CategoryTheory

open Limits Functor

variable {C : Type u₁} [Category.{u₂} C]

namespace PreGaloisCategory

variable [GaloisCategory C]

section Decomposition

/-! ### Decomposition in connected components

To show that an object `X` of a Galois category admits a decomposition into connected objects,
we proceed by induction on the cardinality of the fiber under an arbitrary fiber functor.

If `X` is connected, there is nothing to show. If not, we can write `X` as the sum of two
non-trivial subobjects which have strictly smaller fiber and conclude by the induction hypothesis.

-/

/- The trivial case if `X` is connected. -/
private lemma has_decomp_connected_components_aux_conn (X : C) [IsConnected X] :
    ∃ (ι : Type) (f : ι → C) (g : (i : ι) → (f i) ⟶ X) (_ : IsColimit (Cofan.mk X g)),
    (∀ i, IsConnected (f i)) ∧ Finite ι := by
  refine ⟨Unit, fun _ ↦ X, fun _ ↦ 𝟙 X, mkCofanColimit _ (fun s ↦ s.inj ()), ?_⟩
  exact ⟨fun _ ↦ inferInstance, inferInstance⟩

/- The trivial case if `X` is initial. -/
private lemma has_decomp_connected_components_aux_initial (X : C) (h : IsInitial X) :
    ∃ (ι : Type) (f : ι → C) (g : (i : ι) → (f i) ⟶ X) (_ : IsColimit (Cofan.mk X g)),
    (∀ i, IsConnected (f i)) ∧ Finite ι := by
  refine ⟨Empty, fun _ ↦ X, fun _ ↦ 𝟙 X, ?_⟩
  use mkCofanColimit _ (fun s ↦ IsInitial.to h s.pt) (fun s ↦ by aesop)
    (fun s m _ ↦ IsInitial.hom_ext h m _)
  exact ⟨by simp only [IsEmpty.forall_iff], inferInstance⟩

/- Show decomposition by inducting on `Nat.card (F.obj X)`. -/
private lemma has_decomp_connected_components_aux (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (n : ℕ) : ∀ (X : C), n = Nat.card (F.obj X) → ∃ (ι : Type) (f : ι → C)
    (g : (i : ι) → (f i) ⟶ X) (_ : IsColimit (Cofan.mk X g)),
    (∀ i, IsConnected (f i)) ∧ Finite ι := by
  induction' n using Nat.strongRecOn with n hi
  intro X hn
  by_cases h : IsConnected X
  exact has_decomp_connected_components_aux_conn X
  by_cases nhi : (IsInitial X → False)
  · obtain ⟨Y, v, hni, hvmono, hvnoiso⟩ :=
      has_non_trivial_subobject_of_not_isConnected_of_not_initial X h nhi
    obtain ⟨Z, u, ⟨c⟩⟩ := PreGaloisCategory.monoInducesIsoOnDirectSummand v
    let t : ColimitCocone (pair Y Z) := { cocone := BinaryCofan.mk v u, isColimit := c }
    have hn1 : Nat.card (F.obj Y) < n := by
      rw [hn]
      exact ltCardFiber_of_mono_of_notIso F v hvnoiso
    have i : X ≅ Y ⨿ Z := (colimit.isoColimitCocone t).symm
    have hnn : Nat.card (F.obj X) = Nat.card (F.obj Y) + Nat.card (F.obj Z) := by
      rw [cardFiber_eq_of_iso F i]
      exact cardFiber_coprod_eq_sum F Y Z
    have hn2 : Nat.card (F.obj Z) < n := by
      rw [hn, hnn, lt_add_iff_pos_left]
      exact Nat.pos_of_ne_zero (non_zero_card_fiber_of_not_initial F Y hni)
    let ⟨ι₁, f₁, g₁, hc₁, hf₁, he₁⟩ := hi (Nat.card (F.obj Y)) hn1 Y rfl
    let ⟨ι₂, f₂, g₂, hc₂, hf₂, he₂⟩ := hi (Nat.card (F.obj Z)) hn2 Z rfl
    refine ⟨ι₁ ⊕ ι₂, Sum.elim f₁ f₂,
      Cofan.combPairHoms (Cofan.mk Y g₁) (Cofan.mk Z g₂) (BinaryCofan.mk v u), ?_⟩
    use Cofan.combPairIsColimit hc₁ hc₂ c
    refine ⟨fun i ↦ ?_, inferInstance⟩
    cases i; exact hf₁ _; exact hf₂ _
  · simp at nhi
    obtain ⟨hi⟩ := nhi
    exact has_decomp_connected_components_aux_initial X hi

/-- In a Galois category, every object is the sum of connected objects. -/
theorem has_decomp_connected_components (X : C) :
    ∃ (ι : Type) (f : ι → C)
    (g : (i : ι) → f i ⟶ X)
    (_ : IsColimit (Cofan.mk X g)),
    (∀ i, IsConnected (f i)) ∧ Finite ι := by
  let F := GaloisCategory.getFiberFunctor C
  exact has_decomp_connected_components_aux F (Nat.card <| F.obj X) X rfl

/-- In a Galois category, every object is the sum of connected objects. -/
theorem has_decomp_connected_components' (X : C) :
    ∃ (ι : Type) (_ : Finite ι) (f : ι → C) (_ : ∐ f ≅ X), ∀ i, IsConnected (f i) := by
  obtain ⟨ι, f, g, hl, hc, hf⟩ := has_decomp_connected_components X
  exact ⟨ι, hf, f, colimit.isoColimitCocone ⟨Cofan.mk X g, hl⟩, hc⟩

variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- Every element in the fiber of `X` lies in some connected component of `X`. -/
lemma fiber_in_connected_component (X : C) (x : F.obj X) : ∃ (Y : C) (i : Y ⟶ X) (y : F.obj Y),
    F.map i y = x ∧ IsConnected Y ∧ Mono i := by
  obtain ⟨ι, f, g, hl, hc, he⟩ := has_decomp_connected_components X
  have : Fintype ι := Fintype.ofFinite ι
  let s : Cocone (Discrete.functor f ⋙ F) := F.mapCocone (Cofan.mk X g)
  let s' : IsColimit s := isColimitOfPreserves F hl
  obtain ⟨⟨j⟩, z, h⟩ := Concrete.isColimit_exists_rep _ s' x
  refine ⟨f j, g j, z, ⟨?_, hc j, MonoCoprod.mono_inj _ (Cofan.mk X g) hl j⟩⟩
  subst h
  rfl

/-- Up to isomorphism an element of the fiber of `X` only lies in one connected component. -/
lemma connected_component_unique {X A B : C} [IsConnected A] [IsConnected B] (a : F.obj A)
    (b : F.obj B) (i : A ⟶ X) (j : B ⟶ X) (h : F.map i a = F.map j b) [Mono i] [Mono j] :
    ∃ (f : A ≅ B), F.map f.hom a = b := by
  /- We consider the fiber product of A and B over X. This is a non-empty (because of `h`)
  subobject of `A` and `B` and hence isomorphic to `A` and `B` by connectedness. -/
  let Y : C := pullback i j
  let u : Y ⟶ A := pullback.fst
  let v : Y ⟶ B := pullback.snd
  let G := F ⋙ FintypeCat.incl
  let e : F.obj Y ≃ { p : F.obj A × F.obj B // F.map i p.1 = F.map j p.2 } :=
    fiberPullbackEquiv F i j
  let y : F.obj Y := e.symm ⟨(a, b), h⟩
  have hn : IsInitial Y → False := not_initial_of_inhabited F y
  have : IsIso u := IsConnected.noTrivialComponent Y u hn
  have : IsIso v := IsConnected.noTrivialComponent Y v hn
  use ((asIso u).symm ≪≫ asIso v)
  have hu : G.map u y = a := by
    simp only [y, e, ← PreservesPullback.iso_hom_fst G, fiberPullbackEquiv, Iso.toEquiv_comp,
      Equiv.symm_trans_apply, Iso.toEquiv_symm_fun, types_comp_apply, inv_hom_id_apply]
    rw [Types.pullbackIsoPullback_inv_fst_apply (F.map i) (F.map j)]
  have hv : G.map v y = b := by
    simp only [y, e, ← PreservesPullback.iso_hom_snd G, fiberPullbackEquiv, Iso.toEquiv_comp,
      Equiv.symm_trans_apply, Iso.toEquiv_symm_fun, types_comp_apply, inv_hom_id_apply]
    rw [Types.pullbackIsoPullback_inv_snd_apply (F.map i) (F.map j)]
  rw [← hu, ← hv]
  show (F.toPrefunctor.map u ≫ F.toPrefunctor.map _) y = F.toPrefunctor.map v y
  simp only [← F.map_comp, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom,
    IsIso.hom_inv_id_assoc]

end Decomposition

end PreGaloisCategory

end CategoryTheory
