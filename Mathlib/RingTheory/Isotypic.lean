import Mathlib.RingTheory.SimpleModule
import Mathlib.Algebra.Module.Equiv
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.DirectSum.Module


/-!
# Isotypic Components

## Main Definitions
  * `isoset R M C` defines the set of all submodules of a module `M` that are isomorphic to module `C`
   (which we shall call a generator).
  * `isotypic R M C` defines the supremum of the isoset. In particular, this should only be used when `C` is a simple module,
   so we use an alternative definition isoset, by taking all possible images of homomorphisms `C →ₗ[R] M` instead.
   (Note: This alternative definition for isoset will make it include `⊥`, but when taking supremum, this won't matter for
   `isotypic R M C`.)
  *

## Main Results
  * `isotypic_mapsTo_isotypic`:
    any module homomorphism keeps isotypic components within isotypic components of the same generator.
  * `IsSemisimpleModule.sSup_isotypics_eq_top`:
    a semisimple module is the supremum of all its isotypic components
  * `iso_semisimple`:
    all isotypic components are semisimple

## TODO
  * Establish that isotypic components are isomorphic to a direct sum of
    a set of isomorphic copies of its generator (and in particular, the
    cardinality of this set is unique)
  * Use the above fact to establish that an isotypic component has a unique generator
    up to isomorphisms
  * Establish that the endomorphism ring of a finite isotypic component is a matrix ring
    over a division ring (namely, over the endomorphism ring of the generator)
  * Establish that a finitely generated semisimple module is a unique finite direct sum of
    finite isotypic components
  * Apply the above for a proof of Wedderburn-Artin by taking the endomorphism ring
    of the semisimple ring, and obtaining the direct product of the endomorphism rings
    of the isotypic components

-/


variable (R) [Ring R] (M C : Type*)
  [AddCommGroup M] [Module R M]
  [AddCommGroup C] [Module R C]


---------------- ISOMORPHISM NOTATION

def isoset' : Set (Submodule R M) :=
  {N : Submodule R M | Nonempty (C ≃ₗ[R] N)}

def isoset :
    Set (Submodule R M) :=
  {LinearMap.range i | (i : C →ₗ[R] M)}

abbrev isotypic' : (Submodule R M) :=
  sSup (isoset' R M C)

/-- We define isotypic to be an indexed supremum to be more compatible
  with other theorems down the line. -/
def isotypic :
    Submodule R M := (⨆ (i : C →ₗ[R] M), LinearMap.range i)

/-- A convenient form to turn isotypic into a non-indexed supremum, for when that is needed. -/
lemma isotypic_eq_sSup_isoset : isotypic R M C = sSup (isoset R M C) := by
  rw[isotypic, isoset, iSup, Set.range]

section DefinitionUnification

variable [IsSimpleModule R C]

lemma isoset_le_insert_zero_isoset' :
    isoset R M C ⊆ isoset' R M C ∪ {0} := by
  rw[isoset, isoset']; intro x hx; rw[Set.mem_setOf] at hx
  obtain ⟨w, hw⟩ := hx
  simp; rw[<-hw]
  exact Or.symm (IsSimpleModule.mapsTo_equiv_or_zero R M C w)

lemma isoset'_le_isoset :
  isoset' R M C ⊆ isoset R M C := by
  rw[isoset, isoset']; intro x f; rw[Set.mem_setOf] at f
  apply Classical.choice at f; rw[Set.mem_setOf]
  use (x.subtype ∘ₗ f)
  rw[LinearMap.range_comp, LinearEquiv.range]
  exact Submodule.map_subtype_top x


theorem isotypic_eq_isotypic' :
  isotypic R M C = isotypic' R M C := by
  rw[isotypic_eq_sSup_isoset,isotypic']
  apply le_antisymm
  · have h : sSup (isoset' R M C) = sSup (isoset' R M C ∪ {0}) := by
      rw[sSup_union]; simp
    rw[h]; apply sSup_le_sSup
    exact isoset_le_insert_zero_isoset' R M C
  · apply sSup_le_sSup
    exact isoset'_le_isoset R M C

end DefinitionUnification

section IndependentOfSimple

theorem isotypic_mapsTo_isotypic (N)
[AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
   Submodule.map f (isotypic R M C) ≤ isotypic R N C := by
  rw[isotypic, isotypic, Submodule.map_iSup, iSup, iSup]
  apply sSup_le_sSup_of_forall_exists_le
  intro x hx; rw[Set.mem_range] at hx; obtain ⟨w, hw⟩ := hx
  simp
  use (LinearMap.comp f w)
  rw[<- hw, LinearMap.range_comp]

end IndependentOfSimple

section DependentOnSimple

/-- The set of all simple submodules. -/
def IsSimpleModule.set_submodule : Set (Submodule R M) :=
  {S : Submodule R M | IsSimpleModule R S}

/-- The set of all atomic submodules. -/
def IsAtom.set_submodule : Set (Submodule R M) :=
  {S : Submodule R M | IsAtom S}

/-- A convenience tool for switching between IsSimpleModule and IsAtom
  within the definition of a set. -/
@[simp]
lemma IsSimpleModule.set_submodule_eq_IsAtom.set_submodule : IsSimpleModule.set_submodule R M = IsAtom.set_submodule R M := by
  rw[IsSimpleModule.set_submodule, IsAtom.set_submodule]
  apply le_antisymm
  · intro x hx; rw[Set.mem_setOf]; rw[Set.mem_setOf] at hx
    exact isSimpleModule_iff_isAtom.mp hx
  · intro x hx; rw[Set.mem_setOf]; rw[Set.mem_setOf] at hx
    exact isSimpleModule_iff_isAtom.mpr hx

/-- The set of all isosets generated by a simple module. -/
def set_submodule_isoset : Set (Set (Submodule R M)) :=
  {isoset R M S | S : IsSimpleModule.set_submodule R M}

/-- The set of all isotypic components generated by a simple module. -/
def set_submodule_isotypic : Set (Submodule R M) :=
  {isotypic R M S | S : IsSimpleModule.set_submodule R M}

lemma sUnion_of_set_submodule_isoset_le_IsSimpleModule.set_submodule :
  ⋃₀ (set_submodule_isoset R M) ⊆ (IsSimpleModule.set_submodule R M) ∪ {0} := by
  rw[Set.sUnion, set_submodule_isoset, IsSimpleModule.set_submodule]
  apply sSup_le
  intro y hy
  simp at hy; obtain ⟨w, hw⟩ := hy
  obtain ⟨hwl, hwr⟩ := hw; rw[isoset] at hwr
  simp; intro a ha; rw[<-hwr] at ha; rw[Set.mem_setOf] at ha; obtain ⟨f, hf⟩ := ha
  have hhf := LinearMap.injective_or_eq_zero f
  simp
  cases hhf with
  | inl h =>
    have hg := LinearMap.surjective_rangeRestrict f
    rw[<-LinearMap.ker_eq_bot,<-LinearMap.ker_rangeRestrict,LinearMap.ker_eq_bot] at h
    have hhg : Function.Bijective f.rangeRestrict := by
      rw[Function.Bijective]
      exact And.intro h hg
    have swa := LinearMap.isSimpleModule_iff_of_bijective f.rangeRestrict hhg
    rw[hf] at swa; rw[<-swa]
    exact Or.inr hwl
  | inr h =>
    rw[h, LinearMap.range_zero] at hf
    symm at hf
    exact Or.inl hf

lemma IsSimpleModule.set_submodule_le_sUnion_of_set_submodule_isoset :
  (IsSimpleModule.set_submodule R M) ⊆ ⋃₀ (set_submodule_isoset R M) := by
  rw[Set.sUnion, set_submodule_isoset, IsSimpleModule.set_submodule]
  simp; intro y hy; rw[Set.mem_setOf] at hy; simp; use y
  apply And.intro; exact hy
  rw[isoset]; rw[Set.mem_setOf]
  use (LinearMap.domRestrict LinearMap.id y)
  apply le_antisymm
  repeat
    intro x; simp

lemma sSup_sUnion_of_set_submodule_isoset_eq_sSup_IsSimpleModule.set_submodule :
  sSup (⋃₀ (set_submodule_isoset R M)) = sSup (IsSimpleModule.set_submodule R M) := by
  apply le_antisymm
  · have h : sSup (IsSimpleModule.set_submodule R M) = sSup (IsSimpleModule.set_submodule R M ∪ {0}) := by
      rw[sSup_union]; simp
    rw[h]
    apply sSup_le_sSup
    exact sUnion_of_set_submodule_isoset_le_IsSimpleModule.set_submodule R M
  · apply sSup_le_sSup
    exact IsSimpleModule.set_submodule_le_sUnion_of_set_submodule_isoset R M

lemma sSup_IsSimpleModule.set_submodule_eq_sSup_set_submodule_isotypic :
  sSup (IsSimpleModule.set_submodule R M) = sSup (set_submodule_isotypic R M) := by
  rw[<- sSup_sUnion_of_set_submodule_isoset_eq_sSup_IsSimpleModule.set_submodule, sSup_sUnion, set_submodule_isotypic]
  apply le_antisymm
  · apply iSup_le
    intro x; apply iSup_le; intro hx; rw[set_submodule_isoset] at hx; simp at hx
    obtain ⟨w, hw⟩ := hx
    rw[<- hw.right, <-isotypic_eq_sSup_isoset]; apply le_sSup; simp
    use w; exact And.intro hw.left rfl
  · apply sSup_le; intro x hx; simp at hx
    obtain ⟨w, hw⟩ := hx
    rw[le_iSup_iff]; simp
    intro b hb
    have hbb := hb (isoset R M w); rw[set_submodule_isoset] at hbb
    simp at hbb; have hww := hbb w hw.left rfl
    rw[<- hw.right, isotypic_eq_sSup_isoset]; exact sSup_le hww

/-- A semisimple module is the supremum of all its isotypic components. -/
theorem IsSemisimpleModule.sSup_isotypics_eq_top
(h : IsSemisimpleModule R M) :
  sSup (set_submodule_isotypic R M) = ⊤ := by
  rw[<-sSup_IsSimpleModule.set_submodule_eq_sSup_set_submodule_isotypic, IsSimpleModule.set_submodule]
  exact IsSemisimpleModule.sSup_simples_eq_top

variable [IsSimpleModule R C]

/-- The isotypic component of an isotypic component using its own generator
  is the top submodule. -/
lemma isotypic_of_isotypic_eq_top :
  isotypic R ((isotypic R M C)) C = ⊤ := by
  let cmap := (⨆ (i : C →ₗ[R] M), LinearMap.range i).subtype
  have hc : Function.Injective cmap := Subtype.coe_injective
  have htop := Submodule.comap_subtype_self (isotypic R M C)
  apply le_antisymm
  · exact le_top
  · rw[<-htop, isotypic, isotypic]
    rw[<-(Submodule.comap_map_eq_of_injective hc (⨆ i, LinearMap.range i))]
    apply Submodule.comap_mono
    simp
    intro f
    rw[le_iSup_iff]
    intro k hk
    have hf : LinearMap.range f ≤ ⨆ (i : C →ₗ[R] M), LinearMap.range i := by
      rw[<-isotypic, isotypic_eq_sSup_isoset, isoset]; apply le_sSup
      use f
    let f_to_iso := (Submodule.inclusion hf) ∘ₗ (f.rangeRestrict)
    have hu := hk f_to_iso
    rw[LinearMap.range_comp, LinearMap.range_rangeRestrict, Submodule.map_top] at hu
    rw[Submodule.range_inclusion] at hu
    rw[Submodule.map_comap_eq_self] at hu
    exact hu
    rw[Submodule.range_subtype]
    exact hf

/-- In particular, a subset of the atoms of `isotypic R M S` have supremum equal to `⊤`. -/
lemma sSup_of_isoset'_of_isotypic_eq_top :
  sSup (isoset' R ((isotypic R M C)) C) = ⊤ := by
  rw[<-isotypic', <-isotypic_eq_isotypic']
  · exact isotypic_of_isotypic_eq_top R M C


/-- Isotypic components are semisimple modules. -/
theorem iso_semisimple :
  IsSemisimpleModule R (isotypic R M C) := by
  rw[<- sSup_simples_eq_top_iff_isSemisimpleModule]
  have hS : isoset R (isotypic R M C) C ⊆ {m | IsSimpleModule R m} ∪ {0} := by
    intro x mx; simp; rw[isoset] at mx; rw[Set.mem_setOf] at mx
    obtain ⟨l, hl⟩ := mx
    rw[<- hl]
    exact Or.symm (IsSimpleModule.mapsTo_simple_or_zero R (isotypic R M C) C l)
  simp at hS; apply sSup_le_sSup_of_subset_insert_bot at hS
  rw[<-isotypic_eq_sSup_isoset, isotypic_of_isotypic_eq_top, top_le_iff] at hS
  exact hS
