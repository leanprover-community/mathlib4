/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.GaloisObjects
public import Mathlib.CategoryTheory.Limits.Shapes.CombinedProducts
public import Mathlib.Data.Finite.Sum

/-!
# Decomposition of objects into connected components and applications

We show that in a Galois category every object is the (finite) coproduct of connected subobjects.
This has many useful corollaries, in particular that the fiber of every object
is represented by a Galois object.

## Main results

* `has_decomp_connected_components`: Every object is the sum of its (finitely many) connected
  components.
* `fiber_in_connected_component`: An element of the fiber of `X` lies in the fiber of some
  connected component.
* `connected_component_unique`: Up to isomorphism, for each element `x` in the fiber of `X` there
  is only one connected component whose fiber contains `x`.
* `exists_galois_representative`: The fiber of `X` is represented by some Galois object `A`:
  Evaluation at some `a` in the fiber of `A` induces a bijection `A ⟶ X` to `F.obj X`.

## References

* [lenstraGSchemes]: H. W. Lenstra. Galois theory for schemes.

-/

public section

universe u₁ u₂ w

namespace CategoryTheory

open Limits Functor

variable {C : Type u₁} [Category.{u₂} C]

namespace PreGaloisCategory


section Decomposition

/-! ### Decomposition in connected components

To show that an object `X` of a Galois category admits a decomposition into connected objects,
we proceed by induction on the cardinality of the fiber under an arbitrary fiber functor.

If `X` is connected, there is nothing to show. If not, we can write `X` as the sum of two
non-trivial subobjects which have strictly smaller fiber and conclude by the induction hypothesis.

-/

/-- The trivial case if `X` is connected. -/
private lemma has_decomp_connected_components_aux_conn (X : C) [IsConnected X] :
    ∃ (ι : Type) (f : ι → C) (g : (i : ι) → (f i) ⟶ X) (_ : IsColimit (Cofan.mk X g)),
    (∀ i, IsConnected (f i)) ∧ Finite ι := by
  refine ⟨Unit, fun _ ↦ X, fun _ ↦ 𝟙 X, mkCofanColimit _ (fun s ↦ s.inj ()), ?_⟩
  exact ⟨fun _ ↦ inferInstance, inferInstance⟩

/-- The trivial case if `X` is initial. -/
private lemma has_decomp_connected_components_aux_initial (X : C) (h : IsInitial X) :
    ∃ (ι : Type) (f : ι → C) (g : (i : ι) → (f i) ⟶ X) (_ : IsColimit (Cofan.mk X g)),
    (∀ i, IsConnected (f i)) ∧ Finite ι := by
  refine ⟨Empty, fun _ ↦ X, fun _ ↦ 𝟙 X, ?_⟩
  use mkCofanColimit _ (fun s ↦ IsInitial.to h s.pt) (fun s ↦ by simp)
    (fun s m _ ↦ IsInitial.hom_ext h m _)
  exact ⟨by simp only [IsEmpty.forall_iff], inferInstance⟩

variable [GaloisCategory C]

/- Show decomposition by inducting on `Nat.card (F.obj X)`. -/
private lemma has_decomp_connected_components_aux (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (n : ℕ) : ∀ (X : C), n = Nat.card (F.obj X) → ∃ (ι : Type) (f : ι → C)
    (g : (i : ι) → (f i) ⟶ X) (_ : IsColimit (Cofan.mk X g)),
    (∀ i, IsConnected (f i)) ∧ Finite ι := by
  induction n using Nat.strongRecOn with | _ n hi
  intro X hn
  by_cases h : IsConnected X
  · exact has_decomp_connected_components_aux_conn X
  by_cases nhi : IsInitial X → False
  · obtain ⟨Y, v, hni, hvmono, hvnoiso⟩ :=
      has_non_trivial_subobject_of_not_isConnected_of_not_initial X h nhi
    obtain ⟨Z, u, ⟨c⟩⟩ := PreGaloisCategory.monoInducesIsoOnDirectSummand v
    let t : ColimitCocone (pair Y Z) := { cocone := BinaryCofan.mk v u, isColimit := c }
    have hn1 : Nat.card (F.obj Y) < n := by
      rw [hn]
      exact lt_card_fiber_of_mono_of_notIso F v hvnoiso
    have i : X ≅ Y ⨿ Z := (colimit.isoColimitCocone t).symm
    have hnn : Nat.card (F.obj X) = Nat.card (F.obj Y) + Nat.card (F.obj Z) := by
      rw [card_fiber_eq_of_iso F i]
      exact card_fiber_coprod_eq_sum F Y Z
    have hn2 : Nat.card (F.obj Z) < n := by
      rw [hn, hnn, lt_add_iff_pos_left]
      exact Nat.pos_of_ne_zero (non_zero_card_fiber_of_not_initial F Y hni)
    let ⟨ι₁, f₁, g₁, hc₁, hf₁, he₁⟩ := hi (Nat.card (F.obj Y)) hn1 Y rfl
    let ⟨ι₂, f₂, g₂, hc₂, hf₂, he₂⟩ := hi (Nat.card (F.obj Z)) hn2 Z rfl
    refine ⟨ι₁ ⊕ ι₂, Sum.elim f₁ f₂,
      Cofan.combPairHoms (Cofan.mk Y g₁) (Cofan.mk Z g₂) (BinaryCofan.mk v u), ?_⟩
    use Cofan.combPairIsColimit hc₁ hc₂ c
    refine ⟨fun i ↦ ?_, inferInstance⟩
    cases i
    · exact hf₁ _
    · exact hf₂ _
  · simp only [not_forall, not_false_eq_true] at nhi
    obtain ⟨hi⟩ := nhi
    exact has_decomp_connected_components_aux_initial X hi

/-- In a Galois category, every object is the sum of connected objects. -/
theorem has_decomp_connected_components (X : C) :
    ∃ (ι : Type) (f : ι → C) (g : (i : ι) → f i ⟶ X) (_ : IsColimit (Cofan.mk X g)),
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
  let u : Y ⟶ A := pullback.fst i j
  let v : Y ⟶ B := pullback.snd i j
  let G := F ⋙ FintypeCat.incl
  let e : F.obj Y ≃ { p : F.obj A × F.obj B // F.map i p.1 = F.map j p.2 } :=
    fiberPullbackEquiv F i j
  let y : F.obj Y := e.symm ⟨(a, b), h⟩
  have hn : IsInitial Y → False := not_initial_of_inhabited F y
  have : IsIso u := IsConnected.noTrivialComponent Y u hn
  have : IsIso v := IsConnected.noTrivialComponent Y v hn
  use (asIso u).symm ≪≫ asIso v
  have hu : G.map u y = a := fiberPullbackEquiv_symm_fst_apply _ _ _ h
  have hv : G.map v y = b := fiberPullbackEquiv_symm_snd_apply _ _ _ h
  rw [← hu, ← hv]
  change (F.map u ≫ F.map _) y = F.map v y
  simp only [← F.map_comp, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom,
    IsIso.hom_inv_id_assoc]

end Decomposition

section GaloisRep

/-! ### Galois representative of fiber

If `X` is any object, then its fiber is represented by some Galois object: There exists
a Galois object `A` and an element `a` in the fiber of `A` such that the
evaluation at `a` from `A ⟶ X` to `F.obj X` is bijective.

To show this we consider the product `∏ᶜ (fun _ : F.obj X ↦ X)` and let `A`
be the connected component whose fiber contains the element `a` in the fiber of the self product
that has at each index `x : F.obj X` the element `x`.

This `A` is Galois and evaluation at `a` is bijective.

Reference: [lenstraGSchemes, 3.14]

-/

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

section GaloisRepAux

variable (X : C)

set_option backward.privateInPublic true in
/-- The self product of `X` indexed by its fiber. -/
@[simp]
private noncomputable def selfProd : C := ∏ᶜ (fun _ : F.obj X ↦ X)

set_option backward.privateInPublic true in
/-- The element in the fiber of the self product whose value at index `x : F.obj X` is `x`. -/
private noncomputable def mkSelfProdFib : F.obj (selfProd F X) :=
  (PreservesProduct.iso F _).inv ((Concrete.productEquiv (fun _ : F.obj X ↦ F.obj X)).symm id)

set_option backward.privateInPublic true in
@[simp]
private lemma mkSelfProdFib_map_π (t : F.obj X) : F.map (Pi.π _ t) (mkSelfProdFib F X) = t := by
  rw [← piComparison_comp_π]
  simp [← PreservesProduct.iso_hom, mkSelfProdFib]

variable {X} {A : C} (u : A ⟶ selfProd F X)
  (a : F.obj A) (h : F.map u a = mkSelfProdFib F X) {F}
include h

set_option backward.privateInPublic true in
/-- For each `x : F.obj X`, this is the composition of `u` with the projection at `x`. -/
@[simp]
private noncomputable def selfProdProj (x : F.obj X) : A ⟶ X := u ≫ Pi.π _ x

variable {u a}

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
private lemma selfProdProj_fiber (x : F.obj X) :
    F.map (selfProdProj u x) a = x := by
  simp_all

variable [IsConnected A]

set_option backward.privateInPublic true in
/-- An element `b : F.obj A` defines a permutation of the fiber of `X` by projecting
`F.map u b` to each factor of the self product. -/
private noncomputable def fiberPerm (b : F.obj A) : F.obj X ≃ F.obj X := by
  let σ (t : F.obj X) : F.obj X := F.map (selfProdProj u t) b
  apply Equiv.ofBijective σ
  apply Finite.injective_iff_bijective.mp
  intro t s (hs : F.map (selfProdProj u t) b = F.map (selfProdProj u s) b)
  change id t = id s
  have h' : selfProdProj u t = selfProdProj u s := evaluation_injective_of_isConnected F A X b hs
  rw [← selfProdProj_fiber h s, ← selfProdProj_fiber h t, h']

set_option backward.privateInPublic true in
/-- Twisting `u` by `fiberPerm h b` yields an inclusion of `A` into `selfProd F X`. -/
private noncomputable def selfProdPermIncl (b : F.obj A) : A ⟶ selfProd F X :=
  u ≫ (Pi.whiskerEquiv (fiberPerm h b) (fun _ => Iso.refl X)).inv

set_option backward.privateInPublic true in
private instance [Mono u] (b : F.obj A) : Mono (selfProdPermIncl h b) := mono_comp _ _

set_option backward.privateInPublic true in
/-- Key technical lemma: the twisted inclusion `selfProdPermIncl h b` maps `a` to `F.map u b`. -/
private lemma selfProdTermIncl_fib_eq (b : F.obj A) :
    F.map u b = F.map (selfProdPermIncl h b) a := by
  apply Concrete.Pi.map_ext _ F
  intro (t : F.obj X)
  convert_to F.map (selfProdProj u t) b = _
  · simp only [selfProdProj, map_comp, FintypeCat.comp_apply]; rfl
  · dsimp only [selfProdPermIncl, Pi.whiskerEquiv]
    rw [map_comp, FintypeCat.comp_apply, h]
    convert_to F.map (selfProdProj u t) b =
      (F.map (Pi.map' (fiberPerm h b) fun _ ↦ 𝟙 X) ≫
      F.map (Pi.π (fun _ ↦ X) t)) (mkSelfProdFib F X)
    rw [← map_comp, Pi.map'_comp_π, Category.comp_id, mkSelfProdFib_map_π F X (fiberPerm h b t)]
    rfl

set_option backward.privateInPublic true in
/-- There exists an automorphism `f` of `A` that maps `b` to `a`.
`f` is obtained by considering `u` and `selfProdPermIncl h b`.
Both are inclusions of `A` into `selfProd F X` mapping `b` respectively `a` to the same element
in the fiber of `selfProd F X`. Applying `connected_component_unique` yields the result. -/
private lemma subobj_selfProd_trans [Mono u] (b : F.obj A) : ∃ (f : A ≅ A), F.map f.hom b = a := by
  apply connected_component_unique F b a u (selfProdPermIncl h b)
  exact selfProdTermIncl_fib_eq h b

end GaloisRepAux

/-- The fiber of any object in a Galois category is represented by a Galois object. -/
lemma exists_galois_representative (X : C) : ∃ (A : C) (a : F.obj A),
    IsGalois A ∧ Function.Bijective (fun (f : A ⟶ X) ↦ F.map f a) := by
  obtain ⟨A, u, a, h1, h2, h3⟩ := fiber_in_connected_component F (selfProd F X)
    (mkSelfProdFib F X)
  use A
  use a
  constructor
  · refine (isGalois_iff_pretransitive F A).mpr ⟨fun x y ↦ ?_⟩
    obtain ⟨fi1, hfi1⟩ := subobj_selfProd_trans h1 x
    obtain ⟨fi2, hfi2⟩ := subobj_selfProd_trans h1 y
    use fi1 ≪≫ fi2.symm
    change F.map (fi1.hom ≫ fi2.inv) x = y
    simp only [map_comp, FintypeCat.comp_apply]
    rw [hfi1, ← hfi2]
    exact ConcreteCategory.congr_hom (F.mapIso fi2).hom_inv_id y
  · refine ⟨evaluation_injective_of_isConnected F A X a, ?_⟩
    intro x
    use u ≫ Pi.π _ x
    exact (selfProdProj_fiber h1) x

/-- Any element in the fiber of an object `X` is the evaluation of a morphism from a
Galois object. -/
lemma exists_hom_from_galois_of_fiber (X : C) (x : F.obj X) :
    ∃ (A : C) (f : A ⟶ X) (a : F.obj A), IsGalois A ∧ F.map f a = x := by
  obtain ⟨A, a, h1, h2⟩ := exists_galois_representative F X
  obtain ⟨f, hf⟩ := h2.surjective x
  exact ⟨A, f, a, h1, hf⟩

/-- Any object with non-empty fiber admits a hom from a Galois object. -/
lemma exists_hom_from_galois_of_fiber_nonempty (X : C) (h : Nonempty (F.obj X)) :
    ∃ (A : C) (_ : A ⟶ X), IsGalois A := by
  obtain ⟨x⟩ := h
  obtain ⟨A, f, a, h1, _⟩ := exists_hom_from_galois_of_fiber F X x
  exact ⟨A, f, h1⟩

include F in
/-- Any connected object admits a hom from a Galois object. -/
lemma exists_hom_from_galois_of_connected (X : C) [IsConnected X] :
    ∃ (A : C) (_ : A ⟶ X), IsGalois A :=
  exists_hom_from_galois_of_fiber_nonempty F X inferInstance

/-- To check equality of natural transformations `F ⟶ G`, it suffices to check it on
Galois objects. -/
lemma natTrans_ext_of_isGalois {G : C ⥤ FintypeCat.{w}} {t s : F ⟶ G}
    (h : ∀ (X : C) [IsGalois X], t.app X = s.app X) :
    t = s := by
  ext X x
  obtain ⟨A, f, a, _, rfl⟩ := exists_hom_from_galois_of_fiber F X x
  rw [FunctorToFintypeCat.naturality, FunctorToFintypeCat.naturality, h A]

end GaloisRep

end PreGaloisCategory

end CategoryTheory
