/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.Basic
public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.CategoryTheory.Galois.Prorepresentability
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!

# Universal property of fundamental group

Let `C` be a Galois category with fiber functor `F`. While in informal mathematics, we tend to
identify known groups from other contexts (e.g. the absolute Galois group of a field) with
the automorphism group `Aut F` of certain fiber functors `F`, this causes friction in formalization.

Hence, in this file we develop conditions when a topological group `G` is canonically isomorphic to
the automorphism group `Aut F` of `F`. Consequently, the API for Galois categories and their fiber
functors should be stated in terms of an abstract topological group `G` satisfying
`IsFundamentalGroup` in the places where `Aut F` would appear.

## Main definition

Given a compact, topological group `G` with an action on `F.obj X` on each `X`, we say that
`G` is a fundamental group of `F` (`IsFundamentalGroup F G`), if

- `naturality`: the `G`-action on `F.obj X` is compatible with morphisms in `C`
- `transitive_of_isGalois`: `G` acts transitively on `F.obj X` for all Galois objects `X : C`
- `continuous_smul`: the action of `G` on `F.obj X` is continuous if `F.obj X` is equipped with the
  discrete topology for all `X : C`.
- `non_trivial'`: if `g : G` acts trivially on all `F.obj X`, then `g = 1`.

Given this data, we define `toAut F G : G →* Aut F` in the natural way.

## Main results

- `toAut_bijective`: `toAut F G` is a group isomorphism given `IsFundamentalGroup F G`.
- `toAut_isHomeomorph`: `toAut F G` is a homeomorphism given `IsFundamentalGroup F G`.

## TODO

- Develop further equivalent conditions, in particular, relate the condition `non_trivial` with
  `G` being a `T2Space`.

-/

@[expose] public section

universe u₁ u₂ w

namespace CategoryTheory

namespace PreGaloisCategory

open Limits Functor

variable {C : Type u₁} [Category.{u₂} C] (F : C ⥤ FintypeCat.{w})

section

variable (G : Type*) [Group G] [∀ X, MulAction G (F.obj X)]

/-- We say `G` acts naturally on the fibers of `F` if for every `f : X ⟶ Y`, the `G`-actions
on `F.obj X` and `F.obj Y` are compatible with `F.map f`. -/
class IsNaturalSMul : Prop where
  naturality (g : G) {X Y : C} (f : X ⟶ Y) (x : F.obj X) : F.map f (g • x) = g • F.map f x

set_option backward.privateInPublic true in
variable {G} in
@[simps! -isSimp]
private def isoOnObj (g : G) (X : C) : F.obj X ≅ F.obj X :=
  FintypeCat.equivEquivIso <| {
    toFun := fun x ↦ g • x
    invFun := fun x ↦ g⁻¹ • x
    left_inv := fun _ ↦ by simp
    right_inv := fun _ ↦ by simp
  }

variable [IsNaturalSMul F G]

set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If `G` acts naturally on `F.obj X` for each `X : C`, this is the canonical
group homomorphism into the automorphism group of `F`. -/
def toAut : G →* Aut F where
  toFun g := NatIso.ofComponents (isoOnObj F g) <| by
    intro X Y f
    ext
    exact (IsNaturalSMul.naturality _ _ _).symm
  map_one' := by
    ext
    dsimp [isoOnObj]
    cat_disch
  map_mul' := by
    intro g h
    ext X x
    apply mul_smul

variable {G} in
@[simp]
lemma toAut_hom_app_apply (g : G) {X : C} (x : F.obj X) : (toAut F G g).hom.app X x = g • x :=
  rfl

/-- `toAut` is injective, if only the identity acts trivially on every fiber. -/
lemma toAut_injective_of_non_trivial (h : ∀ (g : G), (∀ (X : C) (x : F.obj X), g • x = x) → g = 1) :
    Function.Injective (toAut F G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g (hg : toAut F G g = 1)
  refine h g (fun X x ↦ ?_)
  have : (toAut F G g).hom.app X = 𝟙 (F.obj X) := by
    rw [hg]
    rfl
  rw [← toAut_hom_app_apply, this, FintypeCat.id_apply]

variable [GaloisCategory C] [FiberFunctor F]

lemma toAut_continuous [TopologicalSpace G] [IsTopologicalGroup G]
    [∀ (X : C), ContinuousSMul G (F.obj X)] :
    Continuous (toAut F G) := by
  apply continuous_of_continuousAt_one
  rw [continuousAt_def, map_one]
  intro A hA
  obtain ⟨X, _, hX⟩ := ((nhds_one_has_basis_stabilizers F).mem_iff' A).mp hA
  rw [mem_nhds_iff]
  exact ⟨MulAction.stabilizer G X.pt, Set.preimage_mono (f := toAut F G) hX,
    stabilizer_isOpen G X.pt, one_mem _⟩

variable {G}

lemma action_ext_of_isGalois {t : F ⟶ F} {X : C} [IsGalois X] {g : G} (x : F.obj X)
    (hg : g • x = t.app X x) (y : F.obj X) : g • y = t.app X y := by
  obtain ⟨φ, (rfl : F.map φ.hom y = x)⟩ := MulAction.exists_smul_eq (Aut X) y x
  have : Function.Injective (F.map φ.hom) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback (F.map φ.hom)
  apply this
  rw [IsNaturalSMul.naturality, hg, FunctorToFintypeCat.naturality]

variable (G)

lemma toAut_surjective_isGalois (t : Aut F) (X : C) [IsGalois X]
    [MulAction.IsPretransitive G (F.obj X)] :
    ∃ (g : G), ∀ (x : F.obj X), g • x = t.hom.app X x := by
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F X
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a (t.hom.app X a)
  exact ⟨g, action_ext_of_isGalois F _ hg⟩

lemma toAut_surjective_isGalois_finite_family (t : Aut F) {ι : Type*} [Finite ι] (X : ι → C)
    [∀ i, IsGalois (X i)] (h : ∀ (X : C) [IsGalois X], MulAction.IsPretransitive G (F.obj X)) :
    ∃ (g : G), ∀ (i : ι) (x : F.obj (X i)), g • x = t.hom.app (X i) x := by
  let x (i : ι) : F.obj (X i) := (nonempty_fiber_of_isConnected F (X i)).some
  let P : C := ∏ᶜ X
  let is₁ : F.obj P ≅ ∏ᶜ fun i ↦ (F.obj (X i)) := PreservesProduct.iso F X
  let is₂ : (∏ᶜ fun i ↦ F.obj (X i) : FintypeCat) ≃ ∀ i, F.obj (X i) :=
    Limits.FintypeCat.productEquiv (fun i ↦ (F.obj (X i)))
  let px : F.obj P := is₁.inv (is₂.symm x)
  have hpx (i : ι) : F.map (Pi.π X i) px = x i := by
    simp only [px, is₁, is₂, ← piComparison_comp_π, ← PreservesProduct.iso_hom,
      FintypeCat.comp_apply]
    rw [FintypeCat.inv_hom_id_apply, FintypeCat.productEquiv_symm_comp_π_apply]
  obtain ⟨A, f, a, _, hfa⟩ := exists_hom_from_galois_of_fiber F P px
  obtain ⟨g, hg⟩ := toAut_surjective_isGalois F G t A
  refine ⟨g, fun i y ↦ action_ext_of_isGalois F (x i) ?_ _⟩
  rw [← hpx i, ← IsNaturalSMul.naturality, FunctorToFintypeCat.naturality,
    ← hfa, FunctorToFintypeCat.naturality, ← IsNaturalSMul.naturality, hg]

open scoped Pointwise

/-- If `G` is a compact, topological group that acts continuously and naturally on the
fibers of `F`, `toAut F G` is surjective if and only if it acts transitively on the fibers
of all Galois objects. This is the `if` direction. For the `only if` see
`isPretransitive_of_surjective`. -/
lemma toAut_surjective_of_isPretransitive [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [∀ (X : C), ContinuousSMul G (F.obj X)]
    (h : ∀ (X : C) [IsGalois X], MulAction.IsPretransitive G (F.obj X)) :
    Function.Surjective (toAut F G) := by
  intro t
  choose gi hgi using (fun X : PointedGaloisObject F ↦ toAut_surjective_isGalois F G t X)
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
      obtain ⟨gs, hgs⟩ :=
        toAut_surjective_isGalois_finite_family F G t (fun X : s ↦ X.val.obj) h
      use gs
      simp only [Set.mem_iInter]
      intro X hXmem
      rw [mem_leftCoset_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul,
        hgs ⟨X, hXmem⟩, ← hgi X, inv_smul_smul]
  obtain ⟨g, hg⟩ := hne
  refine ⟨g, Iso.ext <| natTrans_ext_of_isGalois _ <| fun X _ ↦ ?_⟩
  ext x
  simp only [toAut_hom_app_apply]
  have : g ∈ (gi ⟨X, x, inferInstance⟩ • MulAction.stabilizer G x : Set G) := by
    simp only [Set.mem_iInter, c] at hg
    exact hg _
  obtain ⟨s, (hsmem : s • x = x), (rfl : gi ⟨X, x, inferInstance⟩ • s = _)⟩ := this
  rw [smul_eq_mul, mul_smul, hsmem]
  exact hgi ⟨X, x, inferInstance⟩ x

/-- If `toAut F G` is surjective, then `G` acts transitively on the fibers of connected objects.
For a converse see `toAut_surjective`. -/
lemma isPretransitive_of_surjective (h : Function.Surjective (toAut F G)) (X : C)
    [IsConnected X] : MulAction.IsPretransitive G (F.obj X) where
  exists_smul_eq x y := by
    obtain ⟨t, ht⟩ := MulAction.exists_smul_eq (Aut F) x y
    obtain ⟨g, rfl⟩ := h t
    exact ⟨g, ht⟩

end

section

variable [GaloisCategory C]
variable (G : Type*) [Group G] [∀ (X : C), MulAction G (F.obj X)]

/-- A compact, topological group `G` with a natural action on `F.obj X` for each `X : C`
is a fundamental group of `F`, if `G` acts transitively on the fibers of Galois objects,
the action on `F.obj X` is continuous for all `X : C` and the only trivially acting element of `G`
is the identity. -/
class IsFundamentalGroup [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] : Prop
    extends IsNaturalSMul F G where
  transitive_of_isGalois (X : C) [IsGalois X] : MulAction.IsPretransitive G (F.obj X)
  continuous_smul (X : C) : ContinuousSMul G (F.obj X)
  non_trivial' (g : G) : (∀ (X : C) (x : F.obj X), g • x = x) → g = 1

namespace IsFundamentalGroup

attribute [instance] continuous_smul transitive_of_isGalois

variable {G} [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsFundamentalGroup F G]

lemma non_trivial (g : G) (h : ∀ (X : C) (x : F.obj X), g • x = x) : g = 1 :=
  IsFundamentalGroup.non_trivial' g h

end IsFundamentalGroup

variable [FiberFunctor F]

/-- `Aut F` is a fundamental group for `F`. -/
instance : IsFundamentalGroup F (Aut F) where
  naturality g _ _ f x := (FunctorToFintypeCat.naturality F F g.hom f x).symm
  transitive_of_isGalois X := FiberFunctor.isPretransitive_of_isConnected F X
  continuous_smul X := continuousSMul_aut_fiber F X
  non_trivial' g h := by
    ext X x
    exact h X x

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsFundamentalGroup F G]

lemma toAut_bijective : Function.Bijective (toAut F G) where
  left := toAut_injective_of_non_trivial F G IsFundamentalGroup.non_trivial'
  right := toAut_surjective_of_isPretransitive F G IsFundamentalGroup.transitive_of_isGalois

instance (X : C) [IsConnected X] : MulAction.IsPretransitive G (F.obj X) :=
  isPretransitive_of_surjective F G (toAut_bijective F G).surjective X

/-- If `G` is the fundamental group for `F`, it is isomorphic to `Aut F` as groups and
this isomorphism is also a homeomorphism (see `toAutMulEquiv_isHomeomorph`). -/
noncomputable def toAutMulEquiv : G ≃* Aut F :=
  MulEquiv.ofBijective (toAut F G) (toAut_bijective F G)

lemma toAut_isHomeomorph : IsHomeomorph (toAut F G) := by
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨toAut_continuous F G, toAut_bijective F G⟩

lemma toAutMulEquiv_isHomeomorph : IsHomeomorph (toAutMulEquiv F G) :=
  toAut_isHomeomorph F G

/-- If `G` is a fundamental group for `F`, it is canonically homeomorphic to `Aut F`. -/
noncomputable def toAutHomeo : G ≃ₜ Aut F := (toAut_isHomeomorph F G).homeomorph

variable {G}

@[simp]
lemma toAutMulEquiv_apply (g : G) : toAutMulEquiv F G g = toAut F G g := rfl

@[simp]
lemma toAutHomeo_apply (g : G) : toAutHomeo F G g = toAut F G g := rfl

end

end PreGaloisCategory

end CategoryTheory
