/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Galois.Topology
import Mathlib.CategoryTheory.Galois.Prorepresentability
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Universal property of fundamental group

-/
universe u₁ u₂ v₁ v₂ v w

namespace CategoryTheory

namespace PreGaloisCategory

open Limits Functor

variable {C : Type u₁} [Category.{u₂, u₁} C] [GaloisCategory C] (F : C ⥤ FintypeCat.{u₂})
  [FiberFunctor F]

variable {G : Type*} [Group G] [∀ X, MulAction G (F.obj X)]
  (hnat : ∀ (g : G) {X Y : C} (f : X ⟶ Y) (x : F.obj X), F.map f (g • x) = g • F.map f x)

@[simps!]
private def isoOnObj (g : G) (X : C) : F.obj X ≅ F.obj X :=
  FintypeCat.equivEquivIso <| {
    toFun := fun x ↦ g • x
    invFun := fun x ↦ g⁻¹ • x
    left_inv := fun x ↦ by simp
    right_inv := fun x ↦ by simp
  }

/-- If `G` acts naturally on `F.obj X` for each `X : C`, this is the canonical
group homomorphism into the automorphism group of `F`. -/
@[simps]
def toAutomorphisms : G →* Aut F where
  toFun g := NatIso.ofComponents (isoOnObj F g) <| by
    intro X Y f
    ext
    simp [hnat]
  map_one' := by
    ext
    simp only [NatIso.ofComponents_hom_app, isoOnObj_hom, one_smul]
    rfl
  map_mul' := by
    intro g h
    ext X x
    simp only [NatIso.ofComponents_hom_app, isoOnObj_hom, mul_smul]
    rfl

lemma action_ext_of_isGalois
    (hnat : ∀ (g : G) {X Y : C} (f : X ⟶ Y) (x : F.obj X), F.map f (g • x) = g • F.map f x)
    {t : F ⟶ F} {X : C} [IsGalois X] {g : G} {x : F.obj X} (hg : g • x = t.app X x) (y : F.obj X) :
    g • y = t.app X y := by
  obtain ⟨φ, (rfl : F.map φ.hom y = x)⟩ := MulAction.exists_smul_eq (Aut X) y x
  have : Function.Injective (F.map φ.hom) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback (F.map φ.hom)
  apply this
  rw [hnat, hg, FunctorToFintypeCat.naturality]

lemma toAutomorphisms_surjective_isGalois
    (hnat : ∀ (g : G) {X Y : C} (f : X ⟶ Y) (x : F.obj X), F.map f (g • x) = g • F.map f x)
    (t : Aut F) (X : C) [IsGalois X]
    [MulAction.IsPretransitive G (F.obj X)] :
    ∃ (g : G), ∀ (x : F.obj X), g • x = t.hom.app X x := by
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F X
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a (t.hom.app X a)
  use g
  exact action_ext_of_isGalois F hnat hg

lemma toAutomorphisms_surjective_isGalois_finite_family
    (hnat : ∀ (g : G) {X Y : C} (f : X ⟶ Y) (x : F.obj X), F.map f (g • x) = g • F.map f x)
    (t : Aut F) {ι : Type*} [Finite ι] (X : ι → C) [∀ i, IsGalois (X i)]
    [∀ (X : C) [IsGalois X], MulAction.IsPretransitive G (F.obj X)] :
    ∃ (g : G), ∀ (i : ι) (x : F.obj (X i)), g • x = t.hom.app (X i) x := by
  let x (i : ι) : F.obj (X i) := (nonempty_fiber_of_isConnected F (X i)).some
  let P : C := ∏ᶜ X
  letI : Fintype ι := Fintype.ofFinite ι
  let is₁ : F.obj P ≅ ∏ᶜ fun i ↦ (F.obj (X i)) := PreservesProduct.iso F X
  let is₂ : (∏ᶜ fun i ↦ F.obj (X i) : FintypeCat) ≃ ∀ i, F.obj (X i) :=
    Limits.FintypeCat.productEquiv (fun i ↦ (F.obj (X i)))
  let px : F.obj P := is₁.inv (is₂.symm x)
  have hpx (i : ι) : F.map (Pi.π X i) px = x i := by
    simp only [px, is₁, is₂, ← piComparison_comp_π, ← PreservesProduct.iso_hom]
    simp only [FintypeCat.comp_apply, FintypeCat.inv_hom_id_apply,
      FintypeCat.productEquiv_symm_comp_π_apply]
  obtain ⟨A, f, a, _, hfa⟩ := exists_hom_from_galois_of_fiber F P px
  obtain ⟨g, hg⟩ := toAutomorphisms_surjective_isGalois F hnat t A
  use g
  intro i y
  apply action_ext_of_isGalois F hnat
  show g • x i = _
  rw [← hpx i, ← hnat, FunctorToFintypeCat.naturality, ← hfa, FunctorToFintypeCat.naturality,
    ← hnat, hg]

lemma natTrans_ext_of_isGalois {t s : F ⟶ F}
    (h : ∀ (X : C) [IsGalois X], t.app X = s.app X) : t = s := by
  ext X x
  obtain ⟨A, f, a, _, rfl⟩ := exists_hom_from_galois_of_fiber F X x
  rw [FunctorToFintypeCat.naturality, FunctorToFintypeCat.naturality, h A]

open Pointwise

lemma toAutomorphisms_surjective [TopologicalSpace G] [TopologicalGroup G] [CompactSpace G]
    [∀ (X : C), ContinuousSMul G (F.obj X)]
    [∀ (X : C) [IsGalois X], MulAction.IsPretransitive G (F.obj X)] :
    Function.Surjective (toAutomorphisms F hnat) := by
  intro t
  have (X : PointedGaloisObject F) : ∃ (g : G), ∀ (x : F.obj X.obj), g • x = t.hom.app X.obj x :=
    toAutomorphisms_surjective_isGalois F hnat t X
  choose gi hgi using this
  let cl (X : PointedGaloisObject F) : Set G := gi X • MulAction.stabilizer G X.pt
  let c : Set G := ⋂ i, cl i
  have hne : c.Nonempty := by
    rw [← Set.univ_inter c]
    apply CompactSpace.isCompact_univ.inter_iInter_nonempty
    · intro X
      apply IsClosed.leftCoset
      exact Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen G X.pt)
    · intro s
      rw [Set.univ_inter]
      have inst (X : C) [IsGalois X] : MulAction.IsPretransitive G (F.obj X) := inferInstance
      obtain ⟨gs, hgs⟩ :=
        @toAutomorphisms_surjective_isGalois_finite_family _ _ _ F _ _ _ _ hnat t
        _ _ (fun X : s ↦ X.val.obj) _ inst
      use gs
      simp only [Set.mem_iInter]
      intro X hXmem
      rw [mem_leftCoset_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul,
        hgs ⟨X, hXmem⟩, ← hgi X, inv_smul_smul]
  obtain ⟨g, hg⟩ := hne
  use g
  apply Iso.ext
  apply natTrans_ext_of_isGalois
  intro X _
  ext x
  simp only [toAutomorphisms_apply, NatIso.ofComponents_hom_app, isoOnObj_hom]
  have : g ∈ (gi ⟨X, x, inferInstance⟩ • MulAction.stabilizer G x : Set G) := by
    simp only [Set.mem_iInter, c] at hg
    exact hg _
  obtain ⟨s, (hsmem : s • x = x), (rfl : gi ⟨X, x, inferInstance⟩ • s = _)⟩ := this
  rw [smul_eq_mul, mul_smul, hsmem]
  exact hgi ⟨X, x, inferInstance⟩ x

end PreGaloisCategory

end CategoryTheory
