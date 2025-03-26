/-
Copyright (c) 2025 Antoine Chambert-Loir, María-Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Maria-Inés de Frutos-Fernandez
-/
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Small.Module

/-! # Tensor products and finitely generated submodules

* `DirectedSystem.Submodule_fg`: the directed system of finitely generated submodules,
with respect to the inclusion maps.

* `Submodules_fg_equiv`: a module is the direct limit
of its finitely generated submodules, with respect to the inclusion maps

* `DirectedSystem.rTensor`: given a directed system `M i`,
the directed system of modules `M i ⊗[R] N`.

* `rTensor_fgEquiv`: a tensor product `M ⊗[R] N` is the direct limit
of the tensor products `P ⊗[R] N`, for finitely generated submodules `P` of `M`.

* `DirectedSystem.lTensor`: given a directed system `N i`,
the directed system of modules `M ⊗[R] N i`.

* `lTensor_fgEquiv`: a tensor product `M ⊗[R] N` is the direct limit
of the tensor products `M ⊗[R] Q`, for finitely generated submodules `Q` of `N`.

* `TensorProduct.exists_rTensor_of_fg`: any element `t:  M ⊗[R] N`  can be lifted
to some `P ⊗[R] N`, for fome finitely generated submodule `P` of `M`.

* `TensorProduct.eq_of_fg_of_subtype_eq`;
given a finitely generated submodule `P` of `M` and `t, t' : P ⊗[R] N`
which have the same image in `M ⊗[R] N`, there exists a finitely generated submodule `Q` of `M`
which contains `P` such that `t` and `t'` have the same image in `Q ⊗[R] N`.

* `TensorProduct.eq_of_fg_of_subtype_eq₂`;
given finitely generated submodules `P` and `P'`of `M`, `t : P ⊗[R] N` and `t' : P' ⊗[R] N`
which have the same image in `M ⊗[R] N`, there exists a finitely generated submodule `Q` of `M`
which contains `P` and `P'` and such that `t` and `t'` have the same image in `Q ⊗[R] N`.

* `TensorProduct.Algebra.exists_of_fg`: any element `t : S ⊗[R] N` can be lifted
to `A ⊗[R] N`, for some finitely generated subalgebra `A` of `S`.

* `TensorProduct.Algebra.eq_of_fg_of_subtype_eq`:
given a finitely generated subalgebra `A` of `S`, `t : A ⊗[R] N` and `t' : A ⊗[R] N`
which have the same image in `S ⊗[R] N`, there exists a finitely generated subalgebra `B` of `S`
which contains `A` and such that `t` and `t'` have the same image in `B ⊗[R] N`.

* `TensorProduct.Algebra.eq_of_fg_of_subtype_eq₂`:
given finitely generated subalgebras `A` and `A'`of `S`, `t : A ⊗[R] N` and `t' : A' ⊗[R] N`
which have the same image in `S ⊗[R] N`, there exists a finitely generated subalgebra `B` of `S`
which contains `A` and `A'` and such that `t` and `t'` have the same image in `B ⊗[R] N`.

* `Submodule.exists_fg_of_baseChange_eq_zero`: if `t : S ⊗[R] M`
mapst to `0` in `S ⊗[R] N`, there exists a finitely generated subalgebra `A` of `S`
and `u : A ⊗[R] M` which maps to `t` in `S ⊗[R] M`, and to `0` in `S ⊗[R] N`.

## TODO

* The results are valid in the context of `AddCommMonoid M` over a `Semiring`.
However,  tensor products in mathlib require commutativity of the scalars,
and direct limits of modules are restricted to modules over rings.

-/

open Submodule LinearMap

open CategoryTheory CategoryTheory.Limits

section Semiring

universe u v v' w

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

open scoped CategoryTheory

example : Category {P : Submodule R M // P.FG } := by
 infer_instance

variable (R M) in
/-- The forgetful functor from the category of finitely generated submodules
to the category of modules -/
def F : {P : Submodule R M // P.FG } ⥤  ModuleCat R where
  obj P := ModuleCat.of R P.val
  map h := ModuleCat.ofHom (inclusion (leOfHom h))

example (P : { P : Submodule R M // P.FG }) : P.val →ₗ[R] (⊤ : Submodule R M) :=
  inclusion le_top

/-- The directed system of finitely generated submodules of `M` -/
theorem DirectedSystem.Submodule_fg :
    DirectedSystem (ι := {P : Submodule R M // P.FG}) (F := fun P ↦ P.val)
    (f := fun ⦃P Q⦄ (h : P ≤ Q) ↦ Submodule.inclusion h) where
  map_self := fun _ _ ↦ rfl
  map_map  := fun _ _ _ _ _ _ ↦ rfl

variable (R M) in
/-- Any module is the direct limit of its finitely generated submodules -/
noncomputable def Submodules_fg_equiv [DecidableEq {P : Submodule R M // P.FG}] :
    Module.DirectLimit (ι := {P : Submodule R M // P.FG})
      (G := fun P ↦ P.val)
      (fun ⦃P Q⦄ (h : P ≤ Q) ↦ Submodule.inclusion h) ≃ₗ[R] M :=
  LinearEquiv.ofBijective
    (Module.DirectLimit.lift _ _ _ _ (fun P ↦ P.val.subtype) (fun _ _ _ _ ↦ rfl))
    ⟨Module.DirectLimit.lift_injective _ _ (fun P ↦ Submodule.injective_subtype P.val),
      fun x ↦ ⟨Module.DirectLimit.of _ {P : Submodule R M // P.FG} _ _
          ⟨Submodule.span R {x}, Submodule.fg_span_singleton x⟩
          ⟨x, Submodule.mem_span_singleton_self x⟩,
         by simp⟩⟩
end Semiring

section TensorProducts

open TensorProduct

universe u v v' w

variable (R : Type u) (M N : Type v)
  [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- Given a directed system of `R`-modules, tensor it on the right gives a directed system -/
theorem DirectedSystem.rTensor {ι : Type*} [Preorder ι] {F : ι → Type*}
    [∀ i, AddCommMonoid (F i)] [∀ i, Module R (F i)] {f : ⦃i j : ι⦄ → i ≤ j → F i →ₗ[R] F j}
    (D : DirectedSystem F (fun _ _ h ↦ f h)) :
    DirectedSystem (fun i ↦ (F i) ⊗[R] N) (fun _ _ h ↦ LinearMap.rTensor N (f h)) where
  map_self i t := by
    rw [← LinearMap.id_apply (R := R) t]
    apply DFunLike.congr_fun
    ext m n
    simp [D.map_self]
  map_map {i j k} h h' t := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    apply DFunLike.congr_fun
    ext p n
    simp [D.map_map]

namespace ModuleCat

open CategoryTheory LinearMap ModuleCat


-- set_option pp.universes true

variable {R : Type u} [CommRing R]

/-- right tensor product with a module gives a functor -/
noncomputable def rTensor (N : ModuleCat R) :
    ModuleCat R ⥤  ModuleCat R where
  obj M := ModuleCat.of R (M ⊗[R] N)
  map {M P} h := ModuleCat.ofHom (LinearMap.rTensor N h.hom)

/-- left tensor product with a module gives a functor -/
noncomputable def lTensor (N : ModuleCat R) :
    ModuleCat R ⥤  ModuleCat R where
  obj M := ModuleCat.of R (N ⊗[R] M)
  map {M P} h := ModuleCat.ofHom (LinearMap.lTensor N h.hom)

/-- hom functor -/
noncomputable def lHom (N : ModuleCat R) :
    ModuleCat R ⥤  ModuleCat R where
  obj P := of R (N →ₗ[R] P)
  map {P Q} h := ofHom (compRight h.hom)


/-- the right tensor product / left hom adjunction :
  Hom (M ⊗ N, P) = Hom (M, Hom (N, P)) -/
noncomputable def rTensor_lHom_adjunction (N : ModuleCat R) :
    N.rTensor ⊣ N.lHom where
  unit := {
    app M := ofHom (curry LinearMap.id)
    naturality {M P} f := hom_ext (LinearMap.ext (fun _ ↦ rfl)) }
  counit := {
    app M := ofHom (lift LinearMap.id)
    naturality {M P} f := hom_ext (TensorProduct.ext (by ext; rfl)) }
  left_triangle_components M := hom_ext (TensorProduct.ext (by ext; rfl))
  right_triangle_components M := hom_ext (LinearMap.ext (fun _ ↦ rfl))

-- Universes don't match because `N.rTensor` and `N.lHom` both increase universes
example (N : ModuleCat R) :
    Functor.IsLeftAdjoint (N.rTensor : ModuleCat R ⥤ ModuleCat R) where
  exists_rightAdjoint := ⟨N.lHom, ⟨N.rTensor_lHom_adjunction⟩⟩

instance instIsLeftAdjointRTensor (N : ModuleCat.{v} R) :
    Functor.IsLeftAdjoint (N.rTensor : ModuleCat.{max v w} R ⥤ ModuleCat.{max v w} R) where
  exists_rightAdjoint := ⟨N.lHom, ⟨N.rTensor_lHom_adjunction⟩⟩

example (N : ModuleCat.{v} R) :
    Functor.IsLeftAdjoint (N.rTensor : ModuleCat.{v} R ⥤ ModuleCat R) :=
  inferInstance

/- this one is not found automatically by `inferInstance`
  but one can apply it explicitly `w = max v' w`  -/
example (N : ModuleCat.{v} R) : Functor.IsLeftAdjoint
    (N.rTensor : ModuleCat.{max v v' w} R ⥤ ModuleCat.{max v v' w} R) := by
  -- inferInstance
  exact instIsLeftAdjointRTensor.{u, v, max v' w} (R := R) N

-- variant
example (N : ModuleCat.{v} R) : Functor.IsLeftAdjoint
    (N.rTensor : ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} R) :=
  instIsLeftAdjointRTensor.{u, v, max u v w} (R := R) N
  -- inferInstance

example (N : ModuleCat.{v} R) {C : Type w} [Category C]
    (K : C ⥤ ModuleCat.{max v w} R) :
    PreservesColimit K N.rTensor := inferInstance

example (N : ModuleCat.{v} R) :
    PreservesColimits (N.rTensor : ModuleCat.{max v w} R ⥤  ModuleCat.{max v w} R) :=
  inferInstance

noncomputable def submoduleFGVal (M : ModuleCat R) :
    {P : Submodule R M // P.FG} ⥤  Submodule R M where
  obj P := P.val
  map h := h

noncomputable def submoduleFGVal_cocone (M : ModuleCat R) :
    Cocone M.submoduleFGVal where
  pt := ⊤
  ι := {
    app _ := LE.le.hom le_top
    naturality {_ _} _ := rfl }

noncomputable def submoduleFGVal_colimit (M : ModuleCat R) :
    IsColimit M.submoduleFGVal_cocone where
  desc c := LE.le.hom (fun m _ ↦ leOfHom (c.ι.app ⟨_, fg_span_singleton m⟩)
    ((span_singleton_le_iff_mem m _).mp fun ⦃x⦄ a ↦ a))

def submodule_emb (M : ModuleCat R) :
    Submodule R M ⥤ ModuleCat R where
  obj P := of R P
  map h := ofHom (inclusion (leOfHom h))

def submodule_emb_cocone (M : ModuleCat R) : Cocone (submodule_emb M) where
  pt := M
  ι := {
    app P := ofHom P.subtype
    naturality {_ _} _ := rfl }

theorem emb_aux {M : ModuleCat R} (c : Cocone M.submodule_emb) (m : M)
    (P Q : Submodule R M) (hP : m ∈ P) (hQ : m ∈ Q) :
    (c.ι.app P).hom ⟨m, hP⟩ = (c.ι.app Q).hom ⟨m, hQ⟩ := by
  rw [← c.w (le_sup_left (a := P) (b := Q)).hom, ← c.w (le_sup_right (a := P) (b := Q)).hom]
  rfl

def submodule_emb_colimit (M : ModuleCat R) :
    IsColimit M.submodule_emb_cocone where
  desc c := ofHom {
    toFun m := (c.ι.app (span R {m})).hom ⟨m, mem_span_singleton_self m⟩
    map_add' m m' := by
      simp only [Functor.const_obj_obj]
      erw [emb_aux c m _ (span R {m, m'})
        (mem_span_singleton_self m) (mem_span_pair.mpr ⟨1, 0, by simp⟩)]
      erw [emb_aux c m' _ (span R {m, m'})
        (mem_span_singleton_self m') (mem_span_pair.mpr ⟨0, 1, by simp⟩)]
      erw [emb_aux c (m + m') _ (span R {m, m'})
        (mem_span_singleton_self _) (mem_span_pair.mpr ⟨1, 1, by simp⟩)]
      rw [← (c.ι.app _).hom.map_add]
      congr
    map_smul' r m := by
      simp only [Functor.const_obj_obj, RingHom.id_apply]
      erw [emb_aux c (r • m) _ (span R {m})
        (mem_span_singleton_self _) (mem_span_singleton.mpr ⟨r, rfl⟩)]
      erw [← (c.ι.app _).hom.map_smul]
      congr }
  fac c P := by
    apply hom_ext
    simp only [Functor.const_obj_obj, ModuleCat.hom_comp, hom_ofHom]
    ext (m : P)
    simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
    have hmP : Submodule.span R {(m : M)} ≤ P := by simp
    erw [← c.w hmP.hom, ModuleCat.comp_apply]
  uniq c F hF := by ext; simp [← hF, ModuleCat.comp_apply]; rfl

noncomputable def submoduleFGVal' (M : ModuleCat R) :
    {P : Submodule R M // P.FG} ⥤ ModuleCat R :=
  (submoduleFGVal M).comp M.submodule_emb

noncomputable def submoduleFGValCat (M : ModuleCat R) :
    {P : Submodule R M // P.FG} ⥤ ModuleCat R where
  obj P := ModuleCat.of R P.val
  map h := ModuleCat.ofHom (inclusion (leOfHom h))

example (X Y : Type u) (f : X → Y) :
      ULift.{max u v} X → ULift Y := ULift.map f


variable {X Y Z : Type v} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module R X] [Module R Y] [Module R Z]

def ULift.linearMap (f : X →ₗ[R] Y) : ULift.{max v w} X →ₗ[R] ULift.{max v w} Y :=
  (ULift.moduleEquiv.symm.toLinearMap.comp f).comp ULift.moduleEquiv.toLinearMap

def ULift.linearMap_id :
    ULift.linearMap.{u, v, w} (LinearMap.id (R := R) (M := X)) = LinearMap.id := by
  simp [ULift.linearMap]

def ULift.linearMap_comp (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) :
    ULift.linearMap.{u, v, w} (g ∘ₗf) = ULift.linearMap g ∘ₗ ULift.linearMap f := by
  simp [ULift.linearMap]; rfl

def ULift.linearMap_add (f : X →ₗ[R] Y) (g : X →ₗ[R] Y) :
    ULift.linearMap.{u, v, w} (f + g) = ULift.linearMap f + ULift.linearMap g := by
  simp [ULift.linearMap]; rfl

noncomputable def submoduleFGValCat' (M : ModuleCat.{v} R) :
    {P : Submodule R M // P.FG} ⥤ ModuleCat.{max v w} R where
  obj P := ModuleCat.of R (ULift P.val) --
  map h := ModuleCat.ofHom (ULift.linearMap  (inclusion (leOfHom h)))

def submoduleFGValCat_cocone (M : ModuleCat R) :
    Cocone M.submoduleFGValCat where
  pt := M
  ι := {
    app P := ofHom P.val.subtype
    naturality {_ _} _ := rfl }

theorem aux {M : ModuleCat R} (c : Cocone M.submoduleFGValCat) (m : M)
    (P Q : {P : Submodule R M // P.FG}) (hP : m ∈ P.val) (hQ : m ∈ Q.val) :
    (c.ι.app P).hom ⟨m, hP⟩ = (c.ι.app Q).hom ⟨m, hQ⟩ := by
  rw [← c.w (le_sup_left (a := P) (b := Q)).hom, ← c.w (le_sup_right (a := P) (b := Q)).hom]
  rfl

set_option maxHeartbeats 250000 in
noncomputable def submoduleFGValCat_colimit (M : ModuleCat R) :
    IsColimit M.submoduleFGValCat_cocone where
  desc c := ofHom {
    toFun m := (c.ι.app (⟨span R {m}, fg_span_singleton _⟩)).hom ⟨m, mem_span_singleton_self m⟩
    map_add' m m' := by
      have h : (span R {m, m'}).FG := fg_span (Set.toFinite {m, m'})
      simp only [Functor.const_obj_obj]
      erw [aux c m _ ⟨span R {m, m'}, h⟩
        (mem_span_singleton_self m) (mem_span_pair.mpr ⟨1, 0, by simp⟩)]
      erw [aux c m' _ ⟨span R {m, m'}, h⟩
        (mem_span_singleton_self m') (mem_span_pair.mpr ⟨0, 1, by simp⟩)]
      erw [aux c (m + m') _ ⟨span R {m, m'}, h⟩
        (mem_span_singleton_self _) (mem_span_pair.mpr ⟨1, 1, by simp⟩)]
      rw [← (c.ι.app _).hom.map_add]
      congr
    map_smul' r m := by
      simp only [Functor.const_obj_obj, RingHom.id_apply]
      erw [aux c (r • m) _ ⟨span R {m}, fg_span_singleton m⟩
        (mem_span_singleton_self _) (mem_span_singleton.mpr ⟨r, rfl⟩)]
      erw [← (c.ι.app _).hom.map_smul]
      congr }
  fac c P := by
    apply hom_ext
    simp only [Functor.const_obj_obj, ModuleCat.hom_comp, hom_ofHom]
    ext (m : ↑P)
    simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
    have hmP : Submodule.span R {(m : M)} ≤ P := by simp
    erw [← c.w hmP.hom, ModuleCat.comp_apply]
  uniq c F hF := by
    ext m
    simp only [← hF, Functor.const_obj_obj, hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk]
    rfl

noncomputable def submoduleFGVal_rTensor (M N : ModuleCat.{v} R) :=
    M.submoduleFGValCat ⋙ N.rTensor

noncomputable def submoduleFGVal_rTensor_cocone (M N : ModuleCat.{v} R) :
    Cocone (M.submoduleFGVal_rTensor N) :=
  N.rTensor.mapCocone M.submoduleFGValCat_cocone

set_option pp.universes true

example (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) :
    Nonempty (IsColimit (submoduleFGVal_rTensor_cocone.{max v w} M N)) :=
  PreservesColimit.preserves M.submoduleFGValCat_colimit

example (M N : ModuleCat R) :
    Nonempty (IsColimit (submoduleFGVal_rTensor_cocone M N)) :=
  PreservesColimit.preserves M.submoduleFGValCat_colimit


noncomputable example (M N : ModuleCat.{v} R) :
    IsColimit (M.submoduleFGVal_rTensor_cocone N) :=
  isColimitOfPreserves N.rTensor M.submoduleFGValCat_colimit

noncomputable example (N : ModuleCat R)
    {C : Type*} [Category C] (F : C ⥤  ModuleCat R) : C ⥤  ModuleCat R :=
    F ⋙ N.rTensor

noncomputable example (N : ModuleCat R) {C : Type*} [Category C]
    (F : C ⥤  ModuleCat R) (c : Cocone F) :
    Cocone (F ⋙ N.rTensor) := N.rTensor.mapCocone c

noncomputable example (N : ModuleCat R) {C : Type*} [Category C]
    (F : C ⥤  ModuleCat R) (c : Cocone F) (l : IsColimit c) :
    IsColimit (N.rTensor.mapCocone c) :=
  isColimitOfPreserves N.rTensor l

-- variable (M : Type v) [AddCommGroup M] [Module R M]


/- noncomputable example : {P : Submodule R M // P.FG} ⥤ ModuleCat.{u} R where
  obj P := by
    have : Small.{u} P.val := small_of_injective P.val.subtype_injective
    exact ModuleCat.of R (Shrink.{u} P.val)
  map {P Q} (h)  := by
    apply ofHom
    have : Small.{u} P.val := small_of_injective P.val.subtype_injective
    have : Small.{u} Q.val := small_of_injective Q.val.subtype_injective
    exact ((linearEquivShrink R Q).toLinearMap.comp (inclusion (leOfHom h))).comp
      (linearEquivShrink R P).symm.toLinearMap
  map_id P := by
    apply hom_ext
    simp only [coe_subtype, ofHom_comp, ModuleCat.hom_comp, hom_ofHom, ModuleCat.hom_id]
    rw [← LinearEquiv.conj_apply]
    exact LinearEquiv.conj_id _ -/

/-
variable (R) in
noncomputable def submodulesFG : {P : Submodule R M // P.FG} ⥤ ModuleCat.{u} R where
  obj P := of R P.val
  map {P Q} (h) := ofHom (inclusion (leOfHom h))

open scoped CategoryTheory

variable (R) in
/-- The cocone of finitely generated submodules to the submodules -/
def cocone_submodulesFG : Cocone (submodulesFG R M) where
  pt := of R M
  ι := {
    app _ := ofHom (Submodule.subtype _)
    naturality {_ _} _ := rfl }

/-- A module is the colimit of its finitely generated submodules -/
noncomputable def colimit_submodulesFG : IsColimit (cocone_submodulesFG R M) where
  desc c := ofHom {
    toFun m := (c.ι.app ⟨_, fg_span_singleton m⟩).hom ⟨m, mem_span_singleton_self m⟩
    map_add' m m' := by
      simp only [Functor.const_obj_obj]
      let P : {P : Submodule R M // P.FG} := ⟨_, fg_span_singleton m⟩
      let P' : {P : Submodule R M // P.FG} := ⟨_, fg_span_singleton m'⟩
      let P'' : {P : Submodule R M // P.FG} := ⟨_, fg_span_singleton (m + m')⟩
      let Q : {P : Submodule R M // P.FG} :=
        ⟨span R {m, m'}, fg_span (Set.toFinite (insert m (singleton m')))⟩
      have hPQ : P ≤ Q := by rw [Subtype.mk_le_mk]; apply Submodule.span_mono; simp
      have hP'Q : P' ≤ Q := by rw [Subtype.mk_le_mk]; apply Submodule.span_mono; simp
      have hP''Q : P'' ≤ Q := by
        rw [Subtype.mk_le_mk, span_singleton_le_iff_mem]
        exact add_mem (subset_span (by simp)) (subset_span (by simp))
      rw [← c.w hPQ.hom, ← c.w hP'Q.hom, ← c.w hP''Q.hom]
      simp only [ModuleCat.comp_apply]
      erw [← (c.ι.app Q).hom.map_add]
      congr
    map_smul' r m := by
      simp only [Functor.const_obj_obj, RingHom.id_apply]
      let P : {P : Submodule R M // P.FG} := ⟨_, fg_span_singleton m⟩
      let Q : {P : Submodule R M // P.FG} := ⟨_, fg_span_singleton (r • m)⟩
      let mP : P.val := ⟨m, mem_span_singleton_self m⟩
      let rmQ : Q.val := ⟨r • m, mem_span_singleton_self _⟩
      have hQP : Q ≤ P := by
        rw [Subtype.mk_le_mk]
        simp only [span_singleton_le_iff_mem]
        apply smul_mem
        exact mem_span_singleton_self m
      rw [← c.w hQP.hom]
      simp only [ModuleCat.comp_apply]
      erw [← (c.ι.app P).hom.map_smul]
      congr }
  fac c P := by
    apply hom_ext
    simp only [Functor.const_obj_obj, ModuleCat.hom_comp, hom_ofHom]
    ext (m : P.val)
    simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
    have hmP : Submodule.span R {(m : M)} ≤ P.val := by simp
    rw [← c.w hmP.hom, ModuleCat.comp_apply]
    congr
  uniq c F hF := by ext; simp [← hF, ModuleCat.comp_apply]; rfl
-/

variable (M N : Type*) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
variable (R)

/-- When `P` ranges over finitely generated submodules of `M`,
  the modules of the form `P ⊗[R] N` form a directed system. -/
theorem rTensor_fg_directedSystem :
    DirectedSystem (ι := {P : Submodule R M // P.FG}) (fun P ↦ P.val ⊗[R] N)
    (fun ⦃_ _⦄ h ↦ LinearMap.rTensor N (Submodule.inclusion h)) :=
  DirectedSystem.rTensor R N DirectedSystem.Submodule_fg

/-- The tensor product `M ⊗[R] N` is the direct limit of the modules `P ⊗[R] N`,
where `P` ranges over all finitely generated submodules of `M`. -/
noncomputable def rTensor_fg_equiv [DecidableEq {P : Submodule R M // P.FG}] :
    Module.DirectLimit (R := R) (ι := {P : Submodule R M // P.FG}) (fun P ↦ P.val ⊗[R] N)
      (fun ⦃P Q⦄ (h : P ≤ Q)  ↦ (Submodule.inclusion h).rTensor N) ≃ₗ[R] M ⊗[R] N :=
  (TensorProduct.directLimitLeft _ N).symm.trans ((Submodules_fg_equiv R M).rTensor N)

theorem rTensor_fgEquiv_of  [DecidableEq {P : Submodule R M // P.FG}]
    {P : {P : Submodule R M // P.FG}} (u : P ⊗[R] N) :
    (rTensor_fg_equiv R M N)
      ((Module.DirectLimit.of R {P : Submodule R M // P.FG} (fun P ↦ P.val ⊗[R] N)
        (fun ⦃_ _⦄ h ↦ (Submodule.inclusion h).rTensor N) P) u)
      = (LinearMap.rTensor N (Submodule.subtype P)) u := by
  suffices (rTensor_fg_equiv R M N).toLinearMap.comp
      (Module.DirectLimit.of R {P : Submodule R M // P.FG} (fun P ↦ P.val ⊗[R] N)
        (fun _ _ hPQ ↦ LinearMap.rTensor N (Submodule.inclusion hPQ)) P)
      = LinearMap.rTensor N (Submodule.subtype P.val) by
    exact DFunLike.congr_fun this u
  ext p n
  simp [rTensor_fg_equiv, Submodules_fg_equiv]
  sorry

theorem rTensor_fgEquiv_of' [DecidableEq {P : Submodule R M // P.FG}]
    (P : Submodule R M) (hP : Submodule.FG P) (u : P ⊗[R] N) :
    (rTensor_fg_equiv R M N)
      ((Module.DirectLimit.of R {P : Submodule R M // P.FG} (fun P ↦ P.val ⊗[R] N)
        (fun ⦃_ _⦄ h ↦ LinearMap.rTensor N (Submodule.inclusion h)) ⟨P, hP⟩) u)
      = (LinearMap.rTensor N (Submodule.subtype P)) u :=
  by apply rTensor_fgEquiv_of

/-- Given a directed system of `R`-modules, tensor it on the left gives a directed system -/
theorem DirectedSystem.lTensor {ι : Type*} [Preorder ι] {F : ι → Type*}
    [∀ i, AddCommMonoid (F i)] [∀ i, Module R (F i)] {f : ⦃i j : ι⦄ → i ≤ j → F i →ₗ[R] F j}
    (D : DirectedSystem F (fun _ _ h ↦ f h)) :
    DirectedSystem (fun i ↦ M ⊗[R] (F i)) (fun _ _ h ↦ LinearMap.lTensor M (f h)) where
  map_self i t := by
    rw [← LinearMap.id_apply (R := R) t]
    apply DFunLike.congr_fun
    ext m n
    simp [D.map_self]
  map_map {i j k} h h' t := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    apply DFunLike.congr_fun
    ext p n
    simp [D.map_map]

/-- When `Q` ranges over finitely generated submodules of `N`,
  the modules of the form `M ⊗[R] Q` form a directed system. -/
theorem lTensor_fg_directedSystem :
    DirectedSystem (ι := {Q : Submodule R N // Q.FG}) (fun Q ↦ M ⊗[R] Q.val)
      (fun _ _ hPQ ↦ LinearMap.lTensor M (Submodule.inclusion hPQ)) :=
  DirectedSystem.lTensor R M DirectedSystem.Submodule_fg

/-- The module `M ⊗[R] N` is the direct limit of the modules `M ⊗[R] Q`,
where `Q` runs over finitely generated submodules of `N`. -/
noncomputable def lTensor_fgEquiv [DecidableEq {Q : Submodule R N // Q.FG}] :
    Module.DirectLimit (R := R) (ι := {Q : Submodule R N // Q.FG}) (fun Q ↦ M ⊗[R] Q.val)
      (fun _ _ hPQ ↦ (Submodule.inclusion hPQ).lTensor M) ≃ₗ[R] M ⊗[R] N :=
  (TensorProduct.directLimitRight _ M).symm.trans ((Submodules_fg_equiv R N).lTensor M)

theorem lTensor_fgEquiv_of [DecidableEq {P : Submodule R N // P.FG}]
    (Q : {Q : Submodule R N // Q.FG}) (u : M ⊗[R] Q.val) :
    (lTensor_fgEquiv R M N)
      ((Module.DirectLimit.of R {Q : Submodule R N // Q.FG} (fun Q ↦ M ⊗[R] Q.val)
        (fun _ _ hPQ ↦ (Submodule.inclusion hPQ).lTensor M) Q) u)
      = (LinearMap.lTensor M (Submodule.subtype Q.val)) u := by
  suffices (lTensor_fgEquiv R M N).toLinearMap.comp
      (Module.DirectLimit.of R {Q : Submodule R N // Q.FG} (fun Q ↦ M ⊗[R] Q.val)
        (fun _ _ hPQ ↦ LinearMap.lTensor M (Submodule.inclusion hPQ)) Q)
      = LinearMap.lTensor M (Submodule.subtype Q.val) by
    exact DFunLike.congr_fun this u
  ext p n
  simp [lTensor_fgEquiv, Submodules_fg_equiv]
  sorry

theorem lTensor_fgEquiv_of' [DecidableEq {Q : Submodule R N // Q.FG}]
    (Q : Submodule R N) (hQ : Q.FG) (u : M ⊗[R] Q) :
    (lTensor_fgEquiv R M N)
      ((Module.DirectLimit.of R {Q : Submodule R N // Q.FG} (fun Q ↦ M ⊗[R] Q.val)
        (fun _ _ hPQ ↦ LinearMap.lTensor M (Submodule.inclusion hPQ)) ⟨Q, hQ⟩) u)
      = (LinearMap.lTensor M (Submodule.subtype Q)) u :=
  lTensor_fgEquiv_of R M N ⟨Q, hQ⟩ u

variable {R M N}

theorem TensorProduct.exists_rTensor_of_fg [DecidableEq {P : Submodule R M // P.FG}]
    (t : M ⊗[R] N) :
    ∃ (P : Submodule R M), P.FG ∧ t ∈ LinearMap.range (LinearMap.rTensor N P.subtype) := by
  let ⟨P, u, hu⟩ := Module.DirectLimit.exists_of ((rTensor_fg_equiv R M N).symm t)
  use P.val, P.property, u
  rw [← rTensor_fgEquiv_of, hu, LinearEquiv.apply_symm_apply]

theorem TensorProduct.eq_of_fg_of_subtype_eq {P : Submodule R M} (hP : P.FG) (t t' : P ⊗[R] N)
    (h : LinearMap.rTensor N P.subtype t = LinearMap.rTensor N P.subtype t') :
    ∃ (Q : Submodule R M) (hPQ : P ≤ Q), Q.FG ∧
      LinearMap.rTensor N (Submodule.inclusion hPQ) t
        = LinearMap.rTensor N (Submodule.inclusion hPQ) t' := by
  have := rTensor_fg_directedSystem R M N -- should this be an instance?
  classical
  simp only [← rTensor_fgEquiv_of' R M N P hP, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨Q, hPQ, h⟩ := Module.DirectLimit.exists_eq_of_of_eq h
  use Q.val, Subtype.coe_le_coe.mpr hPQ, Q.property

theorem TensorProduct.eq_zero_of_fg_of_subtype_eq_zero
    {P : Submodule R M} (hP : P.FG) (t : P ⊗[R] N)
    (h : LinearMap.rTensor N P.subtype t = 0) :
    ∃ (Q : Submodule R M) (hPQ : P ≤ Q), Q.FG ∧
      LinearMap.rTensor N (Submodule.inclusion hPQ) t = 0 := by
  rw [← (LinearMap.rTensor N P.subtype).map_zero] at h
  simpa only [map_zero] using TensorProduct.eq_of_fg_of_subtype_eq hP t _ h

theorem TensorProduct.eq_of_fg_of_subtype_eq₂
    {P : Submodule R M} (hP : Submodule.FG P) (t : P ⊗[R] N)
    {P' : Submodule R M} (hP' : Submodule.FG P') (t' : P' ⊗[R] N)
    (h : LinearMap.rTensor N P.subtype t = LinearMap.rTensor N P'.subtype t') :
    ∃ (Q : Submodule R M) (hPQ : P ≤ Q) (hP'Q : P' ≤ Q), Q.FG ∧
      LinearMap.rTensor N (Submodule.inclusion hPQ) t
        = LinearMap.rTensor N (Submodule.inclusion hP'Q) t' := by
  simp only [← Submodule.subtype_comp_inclusion _ _ (le_sup_left : _ ≤ P ⊔ P'),
    ← Submodule.subtype_comp_inclusion _ _ (le_sup_right : _ ≤ P ⊔ P'),
    LinearMap.rTensor_comp, LinearMap.coe_comp, Function.comp_apply] at h
  let ⟨Q, hQ_le, hQ, h⟩ := TensorProduct.eq_of_fg_of_subtype_eq (hP.sup hP') _ _ h
  use Q, le_trans le_sup_left hQ_le, le_trans le_sup_right hQ_le, hQ
  simpa [← LinearMap.comp_apply, ← LinearMap.rTensor_comp] using h

end TensorProducts

section Algebra

open TensorProduct

variable {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup N] [Module R N]

theorem TensorProduct.Algebra.exists_rTensor_of_fg [DecidableEq {P : Submodule R S // P.FG}]
    (t : S ⊗[R] N) :
    ∃ (A : Subalgebra R S), Subalgebra.FG A ∧
      t ∈ LinearMap.range (LinearMap.rTensor N (Subalgebra.val A).toLinearMap) := by
  obtain ⟨P, hP, ht⟩ := TensorProduct.exists_rTensor_of_fg t
  obtain ⟨s, hs⟩ := hP
  use Algebra.adjoin R s, Subalgebra.fg_adjoin_finset _
  have : P ≤ Subalgebra.toSubmodule (Algebra.adjoin R (s : Set S)) := by
    simp only [← hs, Submodule.span_le, Subalgebra.coe_toSubmodule]
    exact Algebra.subset_adjoin
  rw [← Submodule.subtype_comp_inclusion P _ this, LinearMap.rTensor_comp] at ht
  exact LinearMap.range_comp_le_range _ _ ht

theorem TensorProduct.Algebra.eq_of_fg_of_subtype_eq
    {A : Subalgebra R S} (hA : Subalgebra.FG A) (t t' : A ⊗[R] N)
    (h : LinearMap.rTensor N (Subalgebra.val A).toLinearMap t
      = LinearMap.rTensor N (Subalgebra.val A).toLinearMap t') :
    ∃ (B : Subalgebra R S) (hAB : A ≤ B), Subalgebra.FG B
      ∧ LinearMap.rTensor N (Subalgebra.inclusion hAB).toLinearMap t
        = LinearMap.rTensor N (Subalgebra.inclusion hAB).toLinearMap t' := by
  classical
  let ⟨P, hP, ⟨u, hu⟩⟩ := TensorProduct.exists_rTensor_of_fg t
  let ⟨P', hP', ⟨u', hu'⟩⟩ := TensorProduct.exists_rTensor_of_fg t'
  let P₁ := Submodule.map (Subalgebra.toSubmodule A).subtype (P ⊔ P')
  have hP₁ : Submodule.FG P₁ := Submodule.FG.map _ (Submodule.FG.sup hP hP')
  -- the embeddings from P and P' to P₁
  let j : P →ₗ[R] P₁ := LinearMap.restrict (Subalgebra.toSubmodule A).subtype
      (fun p hp ↦ by
        simp only [Submodule.coe_subtype, Submodule.map_sup, P₁]
        apply Submodule.mem_sup_left
        use p; simp only [SetLike.mem_coe]; exact ⟨hp, rfl⟩)
  let j' : P' →ₗ[R] P₁ := LinearMap.restrict (Subalgebra.toSubmodule A).subtype
      (fun p hp ↦ by
        simp only [Submodule.coe_subtype, Submodule.map_sup, P₁]
        apply Submodule.mem_sup_right
        use p; simp only [SetLike.mem_coe]; exact ⟨hp, rfl⟩)
  -- we map u and u' to P₁ ⊗[R] N, getting u₁ and u'₁
  set u₁ := LinearMap.rTensor N j u with hu₁
  set u'₁ := LinearMap.rTensor N j' u' with hu'₁
  -- u₁ and u'₁ are equal in S ⊗[R] N
  have : LinearMap.rTensor N P₁.subtype u₁ = LinearMap.rTensor N P₁.subtype u'₁ := by
    rw [hu₁, hu'₁]
    simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    have hj₁ : P₁.subtype ∘ₗ j = (Subalgebra.val A).toLinearMap ∘ₗ P.subtype := by ext; rfl
    have hj'₁ : P₁.subtype ∘ₗ j' = (Subalgebra.val A).toLinearMap ∘ₗ P'.subtype := by ext; rfl
    rw [hj₁, hj'₁]
    simp only [LinearMap.rTensor_comp, LinearMap.comp_apply]
    rw [hu, hu', h]
  let ⟨P'₁, hP₁_le, hP'₁, h⟩ := TensorProduct.eq_of_fg_of_subtype_eq hP₁ _ _ this
  let ⟨s, hs⟩ := hP'₁
  let ⟨w, hw⟩ := hA
  let B := Algebra.adjoin R ((s ∪ w : Finset S) : Set S)
  have hBA : A ≤ B := by
    simp only [B, ← hw]
    apply Algebra.adjoin_mono
    simp only [Finset.coe_union, Set.subset_union_right]
  use B, hBA, Subalgebra.fg_adjoin_finset _
  rw [← hu, ← hu']
  simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  have hP'₁_le : P'₁ ≤ Subalgebra.toSubmodule B := by
    simp only [← hs, Finset.coe_union, Submodule.span_le, Subalgebra.coe_toSubmodule, B]
    exact subset_trans Set.subset_union_left Algebra.subset_adjoin
  have k : (Subalgebra.inclusion hBA).toLinearMap ∘ₗ P.subtype
    = Submodule.inclusion hP'₁_le ∘ₗ Submodule.inclusion hP₁_le ∘ₗ j := by ext; rfl
  have k' : (Subalgebra.inclusion hBA).toLinearMap ∘ₗ P'.subtype
    = Submodule.inclusion hP'₁_le ∘ₗ Submodule.inclusion hP₁_le ∘ₗ j' := by ext; rfl
  rw [k, k']
  simp only [LinearMap.rTensor_comp, LinearMap.comp_apply]
  rw [← hu₁, ← hu'₁, h]

theorem TensorProduct.Algebra.eq_of_fg_of_subtype_eq₂
    {A : Subalgebra R S} (hA : Subalgebra.FG A) (t : A ⊗[R] N)
    {A' : Subalgebra R S} (hA' : Subalgebra.FG A') (t' : A' ⊗[R] N)
    (h : LinearMap.rTensor N (Subalgebra.val A).toLinearMap t
      = LinearMap.rTensor N (Subalgebra.val A').toLinearMap t') :
    ∃ (B : Subalgebra R S) (hAB : A ≤ B) (hA'B : A' ≤ B), Subalgebra.FG B
      ∧ LinearMap.rTensor N (Subalgebra.inclusion hAB).toLinearMap t
        = LinearMap.rTensor N (Subalgebra.inclusion hA'B).toLinearMap t' := by
  have hj : (Subalgebra.val (A ⊔ A')).comp (Subalgebra.inclusion le_sup_left)
    = Subalgebra.val A := by ext; rfl
  have hj' : (Subalgebra.val (A ⊔ A')).comp (Subalgebra.inclusion le_sup_right)
    = Subalgebra.val A' := by ext; rfl
  simp only [← hj, ← hj', AlgHom.comp_toLinearMap, LinearMap.rTensor_comp,
    LinearMap.comp_apply] at h
  let ⟨B, hB_le, hB, h⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq
    (Subalgebra.fg_sup hA hA') _ _ h
  use B, le_trans le_sup_left hB_le, le_trans le_sup_right hB_le, hB
  simpa only [← LinearMap.rTensor_comp, ← LinearMap.comp_apply] using h

/-- Lift an element that maps to 0 -/
theorem Submodule.exists_fg_of_baseChange_eq_zero
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (t : S ⊗[R] M) (ht : f.baseChange S t = 0) :
    ∃ (A : Subalgebra R S) (_ : A.FG) (u : A ⊗[R] M),
      f.baseChange A u = 0 ∧ A.val.toLinearMap.rTensor M u = t := by
  classical
  obtain ⟨A, hA, ht_memA⟩ := TensorProduct.Algebra.exists_rTensor_of_fg t
  obtain ⟨u, hu⟩ := _root_.id ht_memA
  have := TensorProduct.Algebra.eq_of_fg_of_subtype_eq hA (f.baseChange _ u) 0
  simp only [map_zero, exists_and_left] at this
  have hu' : (A.val.toLinearMap.rTensor N) (f.baseChange (↥A) u) = 0 := by
    rw [rTensor_comp_baseChange_comm_apply, hu, ht]
  obtain ⟨B, hB, hAB, hu'⟩ := this hu'
  use B, hB, LinearMap.rTensor M (Subalgebra.inclusion hAB).toLinearMap u
  constructor
  · rw [← rTensor_comp_baseChange_comm_apply, hu']
  · rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← hu]
    congr

end Algebra
