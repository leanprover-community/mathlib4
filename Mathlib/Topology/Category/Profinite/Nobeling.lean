/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Category.ModuleCat.Free
import Mathlib.Algebra.Homology.ShortExact.Abelian
import Mathlib.Data.List.MinMax
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Topology.Separation
import Mathlib.Topology.Connected

/-!

# Nöbeling's theorem

This file proves Nöbeling's theorem,

## Main result

- `Nobeling`: For `S : Profinite`, the ℤ-module `LocallyConstant S ℤ` is free.

## Implementation Details

We follow the proof of theorem 5.4 in [scholze2019condensed], ordinal induction, etc.

**TODO:** Write more details here.

## References

- [scholze2019condensed]: *Lectures on Condensed Mathematics*, 2019.

-/

universe u

section ListWellFounded

-- This section is PR #6432

variable {α : Type _} (r : α → α → Prop)

theorem WellFounded.list_chain' (hwf : WellFounded r) :
    @WellFounded {l : List α // l.Chain' (flip r)} (fun l m ↦ List.Lex r l.val m.val) := by
  refine ⟨fun ⟨l, hl⟩ ↦ ?_⟩
  cases' l with a l
  · apply Acc.intro; rintro ⟨_⟩ ⟨_⟩
  induction hwf.apply a generalizing l with
  | intro a _ ih =>
    have hl' := (List.chain'_cons'.1 hl).2
    let l' : {l // l.Chain' (flip r)} := ⟨l, hl'⟩
    have : Acc (fun l m ↦ List.Lex r l.val m.val) l'
    · cases' l with b l
      · apply Acc.intro; rintro ⟨_⟩ ⟨_⟩
      · apply ih b (List.chain'_cons.1 hl).1
    revert hl
    rw [(by rfl : l = l'.1)]
    clear_value l'
    induction this with
    | intro l _ ihl =>
      intro hl
      apply Acc.intro
      rintro ⟨_ | ⟨b, l'⟩, hl'⟩ (_|hr|hr)
      · apply Acc.intro; rintro ⟨_⟩ ⟨_⟩
      · apply ihl ⟨l', (List.chain'_cons'.1 hl').2⟩ hr
      · apply ih b hr

instance [hwf : IsWellFounded α r] :
    IsWellFounded {l : List α // l.Chain' (flip r)} (fun l m ↦ List.Lex r l.val m.val) :=
  ⟨hwf.wf.list_chain'⟩

end ListWellFounded

section Piecewise
-- This section is PR #6373 and #6396

namespace LocallyConstant

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] {Z : Type _}

def piecewise {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂) (h : C₁ ∪ C₂ = Set.univ)
    (f : LocallyConstant C₁ Z) (g : LocallyConstant C₂ Z)
    (hfg : ∀ (x : X) (hx : x ∈ C₁ ∩ C₂), f.toFun ⟨x, hx.1⟩ = g.toFun ⟨x, hx.2⟩)
    [∀ j, Decidable (j ∈ C₁)] : LocallyConstant X Z where
  toFun i := if hi : i ∈ C₁ then f ⟨i, hi⟩ else g ⟨i, (Set.compl_subset_iff_union.mpr h) hi⟩
  isLocallyConstant := by
    let dZ : TopologicalSpace Z := ⊥
    haveI : DiscreteTopology Z := discreteTopology_bot Z
    obtain ⟨f, hf⟩ := f
    obtain ⟨g, hg⟩ := g
    rw [IsLocallyConstant.iff_continuous] at hf hg ⊢
    dsimp
    rw [Set.union_eq_iUnion] at h
    refine' (locallyFinite_of_finite _).continuous h (fun i ↦ _) (fun i ↦ _)
    · cases i; exact h₂; exact h₁
    · cases i
      <;> rw [continuousOn_iff_continuous_restrict]
      · convert hg
        ext x
        simp only [cond_false, Set.restrict_apply, Subtype.coe_eta, dite_eq_right_iff]
        exact fun hx ↦ hfg x ⟨hx, x.prop⟩
      · simp only [cond_true, Set.restrict_dite, Subtype.coe_eta]
        exact hf

theorem comap_comp_apply {α : Type _} [TopologicalSpace Z] (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g) (x : LocallyConstant Z α) :
    comap f (comap g x) = comap (g ∘ f) x := by
  rw [← comap_comp f g hf hg]; rfl

noncomputable
def equiv (e : X ≃ₜ Y) : LocallyConstant X Z ≃ LocallyConstant Y Z where
  toFun := comap e.invFun
  invFun := comap e.toFun
  left_inv := by
    intro x
    rw [comap_comp_apply _ _ e.continuous_toFun e.continuous_invFun x]
    simp
  right_inv := by
    intro x
    rw [comap_comp_apply _ _ e.continuous_invFun e.continuous_toFun]
    simp

@[simp]
theorem coe_comap_apply (f : X → Y) (g : LocallyConstant Y Z) (hf : Continuous f) :
    ∀ x, comap f g x = g (f x) := by
  intro x
  rw [← @Function.comp_apply _ _ _ g f x]
  rw [← coe_comap _ _ hf]

lemma comap_injective (f : X → Y) (hf: Continuous f)
    (hfs : Function.Surjective f) : Function.Injective
    ((LocallyConstant.comap f) : (LocallyConstant Y Z) → (LocallyConstant X Z)) := by
  intro a b h
  rw [LocallyConstant.ext_iff] at h
  ext y
  obtain ⟨x, hx⟩ := hfs y
  specialize h x
  rw [coe_comap_apply _ _ hf] at h
  rw [coe_comap_apply _ _ hf] at h
  rw [← hx]
  assumption

noncomputable
def comapMul [MulOneClass Z] (f : X → Y) (hf : Continuous f) :
    LocallyConstant Y Z →* LocallyConstant X Z where
  toFun := comap f
  map_one' := by
    ext x
    rw [coe_comap_apply _ _ hf]
    rfl
  map_mul' := by
    intro r s
    ext x
    simp
    rw [coe_comap_apply _ _ hf, coe_comap_apply _ _ hf, coe_comap_apply _ _ hf]
    simp

variable {R : Type _} [Ring R] [AddCommMonoid Z] [Module R Z]

variable (R) in
noncomputable
def comapLinear (f : X → Y) (hf : Continuous f) :
    LocallyConstant Y Z →ₗ[R] LocallyConstant X Z where
  toFun := comap f
  map_add' := by
    intro r s
    ext x
    simp
    rw [coe_comap_apply _ _ hf, coe_comap_apply _ _ hf, coe_comap_apply _ _ hf]
    rfl
  map_smul' := by
    intro r s
    ext x
    simp
    rw [coe_comap_apply _ _ hf, coe_comap_apply _ _ hf]
    rfl

lemma comapLinear_injective (f : X → Y) (hf : Continuous f) (hfs : Function.Surjective f) :
    LinearMap.ker (comapLinear R f hf : LocallyConstant Y Z →ₗ[R] LocallyConstant X Z) = ⊥ := by
  apply LinearMap.ker_eq_bot_of_injective
  dsimp [comapLinear]
  exact comap_injective _ hf hfs

noncomputable
def equivLinear (e : X ≃ₜ Y) : LocallyConstant X Z ≃ₗ[R] LocallyConstant Y Z :=
{ toFun := (equiv e).toFun
  map_smul' := (comapLinear R _ e.continuous_invFun).map_smul'
  map_add' := by -- note: (comapLinear _ e.continuous_invFun).map_add' doesn't work.
    intro r s
    ext x
    dsimp [equiv]
    have hf : Continuous ↑(e.symm) := e.continuous_invFun
    rw [coe_comap_apply _ _ hf, coe_comap_apply _ _ hf, coe_comap_apply _ _ hf]
    rfl
  invFun := (equiv e).invFun
  left_inv := (equiv e).left_inv
  right_inv := (equiv e).right_inv }

end LocallyConstant
end Piecewise

section Projections -- TODO: PR

variable {ι : Type u} {X : ι → Type} [∀ i, TopologicalSpace (X i)] [∀ i, Inhabited (X i)]
  (C : Set ((i : ι) → X i))

section General

variable (J K L : ι → Prop) [∀ i, Decidable (J i)] [∀ i, Decidable (K i)] [∀ i, Decidable (L i)]

def Proj : ((i : ι) → X i) → ((i : ι) → X i) :=
  fun c i ↦ if J i then c i else default

lemma continuous_proj :
    Continuous (Proj J : ((i : ι) → X i) → ((i : ι) → X i)) := by
  refine continuous_pi ?_
  intro i
  dsimp [Proj]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

lemma isClosedMap_proj [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)] :
    IsClosedMap (Proj J : ((i : ι) → X i) → ((i : ι) → X i)) :=
  fun _ hF ↦ (IsCompact.isClosed (hF.isCompact.image (continuous_proj J)))

def Set.proj : Set ((i : ι) → X i) := (Proj J) '' C

def ProjRestrict : C → C.proj J :=
  Set.codRestrict (Proj J ∘ Subtype.val) (C.proj J) (fun x ↦ Set.mem_image_of_mem _ x.prop)

lemma continuous_projRestrict :
    Continuous (ProjRestrict C J) :=
  Continuous.codRestrict (Continuous.comp (continuous_proj _) continuous_subtype_val) _

lemma surjective_projRestrict :
    Function.Surjective (ProjRestrict C J) := by
  intro x
  obtain ⟨y, hy⟩ := x.prop
  refine ⟨⟨y, hy.1⟩, ?_⟩
  exact Subtype.ext hy.2

lemma proj_eq_self {x : (i : ι) → X i} (h : ∀ i, x i ≠ default → J i) : Proj J x = x := by
  ext i
  dsimp [Proj]
  simp only [ite_eq_left_iff]
  rw [← not_imp_not, not_not, eq_comm, ← ne_eq]
  exact h i

lemma projRestrict_eq_self {x : C} {i : ι} (h : J i) : (ProjRestrict C J x).val i = x.val i := by
  simp only [ProjRestrict, Proj, Set.val_codRestrict_apply, Function.comp_apply, ite_eq_left_iff]
  exact fun hJ ↦ (by exfalso; exact hJ h)

lemma proj_prop_eq_self (hh : ∀ i x, x ∈ C → x i ≠ default → J i) : C.proj J = C := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨y, hy⟩ := h
    suffices x = y by rw [this]; exact hy.1
    rw [← hy.2, proj_eq_self]
    exact fun i ↦ hh i y hy.1
  · refine ⟨x, ⟨h, ?_⟩⟩
    rw [proj_eq_self]
    exact fun i ↦ hh i x h

lemma proj_comp_of_subset (h : ∀ i, J i → K i) : (Proj J ∘ Proj K) =
    (Proj J : ((i : ι) → X i) → ((i : ι) → X i)) := by
  ext x i
  dsimp [Proj]
  split_ifs with hh hh'
  · rfl
  · exfalso
    exact hh' (h i hh)
  · rfl

lemma proj_eq_of_subset (h : ∀ i, J i → K i) : (C.proj K).proj J = C.proj J := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨y, hy⟩ := h
    obtain ⟨z, hz⟩ := hy.1
    rw [← hy.2, ← hz.2]
    suffices Proj J z = (Proj J ∘ Proj K) z by dsimp at this; rw [← this]; refine ⟨z, ⟨hz.1, rfl⟩⟩
    rw [proj_comp_of_subset J K h]
  · obtain ⟨y, hy⟩ := h
    dsimp [Set.proj]
    rw [← Set.image_comp]
    refine ⟨y, ⟨hy.1, ?_⟩⟩
    rw [proj_comp_of_subset _ _ h]
    exact hy.2

variable {J K L}

def ProjRestricts (h : ∀ i, J i → K i) : C.proj K → C.proj J :=
  Homeomorph.setCongr (proj_eq_of_subset C J K h) ∘ ProjRestrict (C.proj K) J

lemma projRestricts_eq_self (x : C.proj K) (i : ι) (hJK : ∀ i, J i → K i) (h : J i) :
    (ProjRestricts C hJK x).val i = x.val i := by
  dsimp [ProjRestricts, Homeomorph.setCongr, ProjRestrict, Proj]
  simp only [Set.val_codRestrict_apply, Function.comp_apply, ite_eq_left_iff]
  exact fun hJ ↦ (by exfalso; exact hJ h)

@[simp]
lemma projRestricts_ne_default_iff (x : C.proj K) (i : ι) (hJK : ∀ i, J i → K i) :
    (ProjRestricts C hJK x).val i ≠ default ↔ J i ∧ x.val i ≠ default := by
  dsimp [ProjRestricts, Homeomorph.setCongr, ProjRestrict, Proj]
  simp only [ite_eq_right_iff, not_forall, exists_prop]

@[simp]
lemma projRestricts_eq_default_iff (x : C.proj K) (i : ι) (hJK : ∀ i, J i → K i) :
    (ProjRestricts C hJK x).val i = default ↔ ¬ J i ∨ x.val i = default := by
  rw [← not_iff_not]
  simp only [projRestricts_ne_default_iff, ne_eq]
  rw [not_or, not_not]


lemma continuous_projRestricts (h : ∀ i, J i → K i) : Continuous (ProjRestricts C h) :=
  Continuous.comp (Homeomorph.continuous _) (continuous_projRestrict _ _)

lemma surjective_projRestricts (h : ∀ i, J i → K i) : Function.Surjective (ProjRestricts C h) :=
  Function.Surjective.comp (Homeomorph.surjective _) (surjective_projRestrict _ _)

variable (J) in
lemma projRestricts_eq_id  :
    ProjRestricts C (fun i (h : J i) ↦ h) = id := by
  ext x i
  dsimp [ProjRestricts, ProjRestrict, Proj, Homeomorph.setCongr]
  simp only [id_eq, Proj, ite_eq_left_iff]
  obtain ⟨y, hy⟩ := x.prop
  rw [← hy.2]
  intro hijn
  apply Eq.symm
  simp only [Proj, Bool.default_bool, ite_eq_right_iff]
  intro hij
  exfalso
  exact hijn hij

lemma projRestricts_eq_comp (hJK : ∀ i, J i → K i) (hKL : ∀ i, K i → L i) :
    ProjRestricts C hJK ∘ ProjRestricts C hKL = ProjRestricts C (fun i ↦ hKL i ∘ hJK i) := by
  ext x i
  dsimp [ProjRestricts, ProjRestrict, Proj, Homeomorph.setCongr]
  simp only [Function.comp_apply, Proj]
  split_ifs with h hh
  · rfl
  · exfalso
    exact hh (hJK i h)
  · rfl

lemma projRestricts_comp_projRestrict (h : ∀ i, J i → K i) :
    ProjRestricts C h ∘ ProjRestrict C K = ProjRestrict C J := by
  ext x i
  dsimp [ProjRestricts, ProjRestrict, Proj, Homeomorph.setCongr, Function.comp_apply, Proj]
  split_ifs with hh hh'
  · rfl
  · exfalso
    exact hh' (h i hh)
  · rfl

end General

section Profinite

variable [∀ i, T2Space (X i)] [∀ i, TotallyDisconnectedSpace (X i)]
  {J K L : Finset ι} [∀ (J : Finset ι) i, Decidable (i ∈ J)]
  [∀ (J : Finset ι), Fintype (C.proj (· ∈ J))]
  {C} (hC : IsCompact C)

open CategoryTheory Limits Opposite

lemma mem_projRestrict (h : J ⊆ K) (x : C.proj (· ∈ K)) :
    Proj (· ∈ J) x.val ∈ C.proj (· ∈ J) := by
  obtain ⟨y, hy⟩ := x.prop
  refine ⟨y, ⟨hy.1, ?_⟩⟩
  dsimp [Proj]
  ext i
  split_ifs with hh
  · rw [← hy.2]
    apply Eq.symm
    simp only [Proj, ite_eq_left_iff]
    intro hK
    exfalso
    exact hK (h hh)
  · rfl

lemma CCompact : CompactSpace C := by
  rwa [← isCompact_iff_compactSpace]

variable (C) in
noncomputable
def FinsetsToProfinite :
    (Finset ι)ᵒᵖ ⥤ Profinite.{u} where
  obj J := Profinite.of (C.proj (· ∈ (unop J)))
  map := @fun J K h ↦ ⟨(ProjRestricts C (leOfHom h.unop)), continuous_projRestricts _ _⟩
  map_id J := by
    dsimp
    simp_rw [projRestricts_eq_id C (· ∈ (unop J))]
    rfl
  map_comp := by
    intros
    dsimp
    congr
    dsimp
    rw [projRestricts_eq_comp]

noncomputable
def FinsetsCone :
    Cone (FinsetsToProfinite C) :=
{ pt := @Profinite.of C _ (CCompact hC) _ _
  π :=
  { app := fun J ↦ ⟨ProjRestrict C (· ∈ (J.unop)), continuous_projRestrict _ _⟩
    naturality := by
      intro J K h
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
      congr
      dsimp [FinsetsToProfinite, ProjRestrict, ProjRestricts, Homeomorph.setCongr,
        Equiv.setCongr, Equiv.subtypeEquivProp]
      congr
      ext x i
      dsimp [Proj]
      split_ifs with hh hhh
      · rfl
      · exfalso
        exact hhh (leOfHom h.unop hh)
      · rfl } }

lemma C_eq_of_forall_proj_eq (a b : C) (h : ∀ (J : Finset ι), ProjRestrict C (· ∈ J) a =
    ProjRestrict C (· ∈ J) b) : a = b := by
  ext i
  specialize h ({i} : Finset ι)
  dsimp [ProjRestrict, Proj] at h
  rw [Subtype.ext_iff] at h
  have hh := congr_fun h i
  dsimp at hh
  split_ifs at hh with hhh
  · exact hh
  · exfalso
    apply hhh
    simp only [Finset.mem_singleton]

open Profinite in
instance isIso_finsetsCone_lift [DecidableEq ι] :
    IsIso ((limitConeIsLimit (FinsetsToProfinite C)).lift (FinsetsCone hC)) :=
  haveI : CompactSpace C := CCompact hC
  isIso_of_bijective _
    (by
      refine ⟨fun a b h ↦ ?_, fun a ↦ ?_⟩
      · refine C_eq_of_forall_proj_eq a b (fun J ↦ ?_)
        apply_fun fun f : (limitCone (FinsetsToProfinite C)).pt => f.val (op J) at h
        exact h
      · suffices : ∃ (x : C), ∀ (J : Finset ι), ProjRestrict C (· ∈ J) x = a.val (op J)
        · obtain ⟨b, hb⟩ := this
          use b
          apply Subtype.ext
          apply funext
          rintro J
          exact hb (unop J)
        have hc : ∀ (J : Finset ι) s, IsClosed ((ProjRestrict C (· ∈ J)) ⁻¹' s)
        · intro J s
          refine IsClosed.preimage (continuous_projRestrict C (· ∈ J)) ?_
          haveI : DiscreteTopology (C.proj (· ∈ J)) := discrete_of_t1_of_finite
          exact isClosed_discrete _
        have H₁ : ∀ (Q₁ Q₂ : Finset ι), Q₁ ≤ Q₂ →
            ProjRestrict C (· ∈ Q₁) ⁻¹' {a.val (op Q₁)} ⊇
            ProjRestrict C (· ∈ Q₂) ⁻¹' {a.val (op Q₂)}
        · intro J K h x hx
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
          rw [← projRestricts_comp_projRestrict C h, Function.comp_apply,
            hx, ← a.prop (homOfLE h).op]
          rfl
        obtain ⟨x, hx⟩ :
            Set.Nonempty (⋂ (J : Finset ι), ProjRestrict C (· ∈ J) ⁻¹' {a.val (op J)}) :=
          IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed
            (fun J : Finset ι => ProjRestrict C (· ∈ J) ⁻¹' {a.val (op J)}) (directed_of_sup H₁)
            (fun J => (Set.singleton_nonempty _).preimage (surjective_projRestrict _ _))
            (fun J => (hc J {a.val (op J)}).isCompact) fun J => hc J _
        exact ⟨x, Set.mem_iInter.1 hx⟩)

noncomputable
def isoFinsetsConeLift [DecidableEq ι] :
    @Profinite.of C _ (CCompact hC) _ _ ≅
    (Profinite.limitCone (FinsetsToProfinite C)).pt :=
  asIso <| (Profinite.limitConeIsLimit _).lift (FinsetsCone hC)

noncomputable
def asLimitFinsetsConeIso [DecidableEq ι] : FinsetsCone hC ≅ Profinite.limitCone _ :=
  Limits.Cones.ext (isoFinsetsConeLift hC) fun _ => rfl

noncomputable
def finsetsCone_isLimit [DecidableEq ι] : CategoryTheory.Limits.IsLimit (FinsetsCone hC) :=
  Limits.IsLimit.ofIsoLimit (Profinite.limitConeIsLimit _) (asLimitFinsetsConeIso hC).symm

end Profinite

end Projections

namespace LocallyConstant -- TODO: PR

variable {X Z : Type _} [TopologicalSpace X]

def eval (x : X) : (LocallyConstant X Z) → Z :=
  fun f ↦ f x

def evalLinear {R : Type _} [Semiring R] [AddCommMonoid Z]
  [Module R Z] (x : X) : LocallyConstant X Z →ₗ[R] Z where
  toFun f := f x
  map_add' _ _ := by simp only [LocallyConstant.coe_add, Pi.add_apply]
  map_smul' _ _ := by simp only [coe_smul, Pi.smul_apply, RingHom.id_apply]

def evalMul [MulOneClass Z] (x : X) : LocallyConstant X Z →* Z where
  toFun f := f x
  map_mul' _ _ := by simp only [LocallyConstant.coe_mul, Pi.mul_apply]
  map_one' := rfl

def mulLinear (R : Type _) [Semiring R] [AddCommMonoid Z] [Module R Z] [Mul Z] [LeftDistribClass Z]
    [SMulCommClass R Z Z] (f : LocallyConstant X Z) :
    LocallyConstant X Z →ₗ[R] LocallyConstant X Z where
  toFun := fun g ↦ f * g
  map_add' := by
    intro a b
    ext x
    simp only [coe_mul, coe_add, Pi.mul_apply, Pi.add_apply]
    exact mul_add _ _ _
  map_smul' := by
    intro r a
    ext x
    simp only [coe_mul, coe_smul, Pi.mul_apply, Pi.smul_apply, RingHom.id_apply]
    exact mul_smul_comm _ _ _

variable {Y : Type _} [TopologicalSpace Y]

noncomputable
def comapRingHom [Semiring Z]
  (f : X → Y) (hf : Continuous f) : LocallyConstant Y Z →+* LocallyConstant X Z where
    toMonoidHom := comapMul f hf
    map_zero' := by
      ext x
      rw [comapMul, coe_comap_apply _ _ hf]
      rfl
    map_add' r s := by
      ext x
      simp [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, coe_add, Pi.add_apply, comapMul]
      rw [coe_comap_apply _ _ hf, coe_comap_apply _ _ hf, coe_comap_apply _ _ hf]
      simp only [coe_add, Pi.add_apply]

noncomputable
def comapAlghom {R : Type _} [CommSemiring R] [Semiring Z] [Algebra R Z]
  (f : X → Y) (hf : Continuous f) : LocallyConstant Y Z →ₐ[R] LocallyConstant X Z where
    toRingHom := comapRingHom f hf
    commutes' r := by
      ext x
      simp only [comapRingHom, comapMul._eq_1, RingHom.toMonoidHom_eq_coe, RingHom.coe_monoidHom_mk,
        OneHom.toFun_eq_coe, OneHom.coe_mk, coe_algebraMap, Pi.algebraMap_apply]
      rw [coe_comap_apply _ _ hf]
      rfl

lemma comapList [Monoid Z] (f : X → Y) (hf : Continuous f) (l : List (LocallyConstant Y Z)) :
    l.prod ∘ f = (l.map (comap f)).prod := by
  have : comapMul f hf (l.prod) = comap f (l.prod) := rfl
  rw [← coe_comap _ _ hf, ← this, map_list_prod (comapMul f hf) l]
  rfl

end LocallyConstant

namespace NobelingProof

variable {I : Type u} [Inhabited I] [LinearOrder I] [IsWellOrder I (·<·)] (C : Set (I → Bool))

section Products

def Int.ofBool (a : Bool): ℤ := (if a then 1 else 0)

def e (μ : I) : LocallyConstant C ℤ :=
{ toFun := fun f ↦ Int.ofBool (f.1 μ)
  isLocallyConstant := by
    rw [IsLocallyConstant.iff_continuous]
    refine @Continuous.comp _ _ _ _ _ _ Int.ofBool _ continuous_of_discreteTopology ?_
    refine Continuous.comp (continuous_apply μ) ?_
    exact continuous_induced_dom }

def Products (I : Type _) [LinearOrder I] := {l : List I // l.Chain' (·>·)}

namespace Products

noncomputable
instance : LinearOrder (Products I) :=
  inferInstanceAs (LinearOrder {l : List I // l.Chain' (·>·)})

@[simp]
lemma lt_iff_lex_lt (l m : Products I) : l < m ↔ List.Lex (·<·) l.val m.val := by
  cases l
  cases m
  rw [Subtype.mk_lt_mk]
  simp
  exact Iff.rfl

def eval (l : Products I) := (l.1.map (e C)).prod

def isGood (l : Products I) : Prop :=
  l.eval C ∉ Submodule.span ℤ ((Products.eval C) '' {m | m < l})

end Products

def GoodProducts := {l : Products I | l.isGood C}

namespace GoodProducts

def eval (l : {l : Products I // l.isGood C}) :
  LocallyConstant C ℤ := Products.eval C l.1

lemma injective : Function.Injective (eval C) := by
  rintro ⟨a,ha⟩ ⟨b,hb⟩ h
  dsimp [eval] at h
  have hab : a < b ∨ a = b ∨ b < a := trichotomous_of (·<·) a b
  apply Or.elim3 hab
  · intro h'
    exfalso
    apply hb
    rw [← h]
    apply Submodule.subset_span
    use a
    exact ⟨h',rfl⟩
  · exact fun h ↦ Subtype.eq h
  · intro h'
    exfalso
    apply ha
    rw [h]
    apply Submodule.subset_span
    use b
    exact ⟨h',rfl⟩

def range := Set.range (GoodProducts.eval C)

noncomputable
def equiv_range : GoodProducts C ≃ range C :=
Equiv.ofInjective (eval C) (injective C)

lemma equiv_toFun_eq_eval : (equiv_range C).toFun =
  Set.rangeFactorization (eval C) := by rfl

lemma linearIndependent_iff_range : LinearIndependent ℤ (GoodProducts.eval C) ↔
    LinearIndependent ℤ (fun (p : range C) ↦ p.1) := by
  rw [← @Set.rangeFactorization_eq _ _ (GoodProducts.eval C), ← equiv_toFun_eq_eval C]
  exact linearIndependent_equiv (equiv_range C)

end GoodProducts

namespace Products

def Apply (l : Products I) (x : C) : List ℤ :=
List.map ((LocallyConstant.eval x) ∘ (e C)) l.val

lemma eval_apply (l : Products I) (x : C) :
    l.eval C x = List.prod (Apply C l x) := by
  dsimp [eval, Apply, LocallyConstant.eval]
  obtain ⟨l,hl⟩ := l
  induction l with
  | nil => rfl
  | cons a as ih =>
    · simp only [List.map, List.prod_cons, LocallyConstant.coe_mul, Pi.mul_apply,
        Function.comp_apply, mul_eq_mul_left_iff]
      specialize ih (List.Chain'.sublist hl (List.tail_sublist (a::as)))
      left
      exact ih

lemma eval_eq (l : Products I) (x : C) :
    l.eval C x = if ∀ i, i ∈ l.val → (x.val i = true) then 1 else 0 := by
  rw [eval_apply]
  split_ifs with h
  · dsimp [Apply]
    suffices : ∀ y, y ∈ List.map (LocallyConstant.eval x ∘ e C) l.val → y = 1
    · exact List.prod_eq_one this
    intro y hy
    simp only [List.mem_map, Function.comp_apply] at hy
    obtain ⟨i,hi⟩ := hy
    specialize h i hi.1
    dsimp [LocallyConstant.eval, e, Int.ofBool] at hi
    rw [← hi.2]
    simp only [ite_eq_left_iff]
    exact fun hx ↦ hx h
  · simp only [List.prod_eq_zero_iff]
    dsimp [Apply]
    simp only [List.mem_map, Function.comp_apply]
    push_neg at h
    obtain ⟨i,hi⟩ := h
    use i
    refine ⟨hi.1, ?_⟩
    dsimp [LocallyConstant.eval, e, Int.ofBool]
    simp only [ite_eq_right_iff]
    exact hi.2

lemma evalFacProps {l : Products I} (J K : I → Prop)
    (h : ∀ a, a ∈ l.val → J a) [∀ j, Decidable (J j)] [∀ j, Decidable (K j)]
    (hJK : ∀ i, J i → K i) :
    l.eval (C.proj J) ∘ ProjRestricts C hJK = l.eval (C.proj K) := by
  ext x
  dsimp [ProjRestrict, ProjRestricts, Homeomorph.setCongr]
  rw [Products.eval_eq, Products.eval_eq]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exfalso
    apply h₂
    intro i hi
    rw [← h₁ i hi]
    dsimp [Set.proj, Proj]
    split_ifs with h'
    · rfl
    · exfalso
      exact h' (h i hi)
  · exfalso
    apply h₁
    intro i hi
    rw [← h₂ i hi]
    dsimp [Set.proj, Proj]
    split_ifs with h'
    · rfl
    · exfalso
      exact h' (h i hi)
  · rfl
  -- rw [eval, eval, LocallyConstant.comapList _ (continuous_projRestricts _ _)]
  -- ext x
  -- have : ∀ (g : LocallyConstant _ ℤ), g x = LocallyConstant.evalMul x g := fun g ↦ rfl
  -- rw [this, this, map_list_prod, map_list_prod]
  -- simp only [List.map_map, FunLike.coe_fn_eq]
  -- congr
  -- ext i
  -- dsimp [LocallyConstant.evalMul]
  -- rw [LocallyConstant.coe_comap_apply _ _ (continuous_projRestricts _ _)]
  -- dsimp [e, Int.ofBool]
  -- split_ifs with h₁ h₂ h₂
  -- · rfl
  -- · exfalso
  --   rw [← h₁] at h₂
  --   rw [← Bool.not_eq_false, ← Bool.default_bool, ← ne_eq, projRestricts_ne_default_iff] at h₁
  --   exact h₂ (Eq.symm (projRestricts_eq_self C x i hJK h₁.1))
  -- · exfalso
  --   rw [Bool.not_eq_true, ← Bool.default_bool, projRestricts_eq_default_iff] at h₁
  --   obtain ⟨y, hy⟩ := x.prop
  --   rw [← hy.2, Proj] at h₂
  --   simp only [Bool.default_bool, Bool.ite_eq_true_distrib, if_false_right_eq_and] at h₂


lemma evalFacProp {l : Products I} (J : I → Prop)
    (h : ∀ a, a ∈ l.val → J a) [∀ j, Decidable (J j)] :
    l.eval (C.proj J) ∘ ProjRestrict C J = l.eval C := by
  ext x
  dsimp [ProjRestrict]
  rw [Products.eval_eq, Products.eval_eq]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exfalso
    apply h₂
    intro i hi
    rw [← h₁ i hi]
    dsimp [Set.proj, Proj]
    split_ifs with h'
    · rfl
    · exfalso
      exact h' (h i hi)
  · exfalso
    apply h₁
    intro i hi
    rw [← h₂ i hi]
    dsimp [Set.proj, Proj]
    split_ifs with h'
    · rfl
    · exfalso
      exact h' (h i hi)
  · rfl

lemma prop_of_isGood {l : Products I} (J : I → Prop) [∀ j, Decidable (J j)]
    (h : l.isGood (C.proj J)) : ∀ a, a ∈ l.val → J a := by
  intro i hi
  by_contra h'
  apply h
  suffices : eval (C.proj J) l = 0
  · rw [this]
    exact Submodule.zero_mem _
  ext x
  rw [eval_eq]
  split_ifs with h
  · exfalso
    apply h'
    specialize h i hi
    obtain ⟨y, hy⟩ := x.prop
    rw [← hy.2] at h
    simp only [Proj, Bool.ite_eq_true_distrib, if_false_right_eq_and] at h
    exact h.1
  · rfl

instance : IsWellFounded (Products I) (·<·) := by
  have : (fun (l m : Products I) ↦ l < m) = (fun l m ↦ List.Lex (·<·) l.val m.val)
  · ext l m
    exact Products.lt_iff_lex_lt l m
  rw [this]
  have hflip : (·>· : I → I → Prop) = flip (·<· : I → I → Prop) := rfl
  dsimp [Products]
  rw [hflip]
  exact inferInstance

lemma eval_mem_span_goodProducts (l : Products I) :
    l.eval C ∈ Submodule.span ℤ (Set.range (GoodProducts.eval C)) := by
  let L : Products I → Prop := fun m ↦ m.eval C ∈ Submodule.span ℤ (Set.range (GoodProducts.eval C))
  suffices L l by assumption
  apply IsWellFounded.induction (·<· : Products I → Products I → Prop)
  intro l h
  dsimp
  by_cases hl : l.isGood C
  · apply Submodule.subset_span
    exact ⟨⟨l, hl⟩, rfl⟩
  · simp only [Products.isGood, not_not] at hl
    suffices : Products.eval C '' {m | m < l} ⊆ Submodule.span ℤ (Set.range (GoodProducts.eval C))
    · rw [← Submodule.span_le] at this
      exact this hl
    intro a ha
    obtain ⟨m, hm⟩ := ha
    rw [← hm.2]
    exact h m hm.1

end Products

lemma GoodProducts.span_iff_products : ⊤ ≤ Submodule.span ℤ (Set.range (eval C)) ↔
    ⊤ ≤ Submodule.span ℤ (Set.range (Products.eval C)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine le_trans h ?_
    apply Submodule.span_mono
    intro a ha
    obtain ⟨b, hb⟩ := ha
    refine ⟨b.val, hb⟩
  · refine le_trans h ?_
    rw [Submodule.span_le]
    intro f hf
    obtain ⟨l,hl⟩ := hf
    rw [← hl]
    exact Products.eval_mem_span_goodProducts C l

end Products

section Span
section Fin

variable (J : Finset I)

noncomputable
def LinearResFin :
    LocallyConstant (C.proj (· ∈ J)) ℤ →ₗ[ℤ] LocallyConstant C ℤ :=
LocallyConstant.comapLinear ℤ _ (continuous_projRestrict C (· ∈ J))

lemma linearResFin_of_eval (l : Products I) (hl : l.isGood (C.proj (· ∈ J))) :
    l.eval C = LinearResFin C J (l.eval (C.proj (· ∈ J))) := by
  ext f
  dsimp [LinearResFin, LocallyConstant.comapLinear]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_projRestrict C (· ∈ J))]
  exact (congr_fun (Products.evalFacProp C (· ∈ J) (Products.prop_of_isGood C (· ∈ J) hl)) _).symm

def Products.ofElementSet (x : C.proj (· ∈ J)) : Set I := {i | x.val i = true}

lemma mem_J_of_x_true (x : C.proj (· ∈ J)) (i : I) : x.val i = true → i ∈ J := by
  intro hi
  obtain ⟨y, hx⟩ := x.prop
  rw [← hx.2] at hi
  simp only [Proj, Bool.ite_eq_true_distrib, if_false_right_eq_and] at hi
  exact hi.1

def Products.ofElementFun (x : C.proj (· ∈ J)) : ofElementSet C J x → J :=
fun ⟨i, hi⟩ ↦ ⟨i, mem_J_of_x_true C J x i hi⟩

lemma Products.ofElementFunInjective (x : C.proj (· ∈ J)) :
    Function.Injective (ofElementFun C J x) := by
  intro i j h
  rw [Subtype.ext_iff] at h
  exact Subtype.ext h

noncomputable
instance (x : C.proj (· ∈ J)) : Fintype (Products.ofElementSet C J x) :=
Fintype.ofInjective (Products.ofElementFun C J x) (Products.ofElementFunInjective C J x)

noncomputable
def Products.ofElementFinset (x : C.proj (· ∈ J)) := (ofElementSet C J x).toFinset

noncomputable
def Products.ofElementList (x : C.proj (· ∈ J)) :=
  List.insertionSort (·≥·) (ofElementFinset C J x).toList

lemma Products.ofElement_chain'_ge (x : C.proj (· ∈ J)) :
    (ofElementList C J x).Chain' (·≥· : I → I → Prop) := by
  rw [List.chain'_iff_pairwise]
  exact List.sorted_insertionSort _ _

lemma Products.ofElement_chain'_gt (x : C.proj (· ∈ J)) :
    (ofElementList C J x).Chain' (·>· : I → I → Prop) := by
  rw [List.chain'_iff_pairwise]
  have : ∀ (a b : I), a > b ↔ a ≥ b ∧ a ≠ b
  · intro a b
    rw [gt_iff_lt, lt_iff_le_and_ne]
    exact Iff.and Iff.rfl ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩
  have hr : (·>· : I → I → Prop) = (fun a b ↦ a ≥ b ∧ a ≠ b)
  · ext a b
    exact this a b
  rw [hr, List.pairwise_and_iff]
  refine ⟨List.chain'_iff_pairwise.mp (ofElement_chain'_ge C J x), ?_⟩
  have hn := (ofElementFinset C J x).nodup_toList
  have h := List.perm_insertionSort (·≥·) (ofElementFinset C J x).toList
  rw [List.Perm.nodup_iff h.symm] at hn
  exact hn

noncomputable
def Products.ofElement (x : C.proj (· ∈ J)) : Products I :=
⟨ofElementList C J x, ofElement_chain'_gt C J x⟩

noncomputable
instance : Fintype (C.proj (· ∈ J)) := by
  haveI : Fintype (J → Bool) := inferInstance
  let f : C.proj (· ∈ J) → (J → Bool) := fun x j ↦ x.val j.val
  refine Fintype.ofInjective f ?_
  intro x y h
  ext i
  by_cases hi : i ∈ J
  · exact congrFun h ⟨i, hi⟩
  · obtain ⟨x', hx⟩ := x.prop
    obtain ⟨y', hy⟩ := y.prop
    rw [← hx.2, ← hy.2]
    dsimp [Proj]
    split_ifs with hh
    · exfalso
      exact hi hh
    · rfl

noncomputable
def Finsupp.resFin_to_Z (f : LocallyConstant (C.proj (· ∈ J)) ℤ) : C.proj (· ∈ J) →₀ ℤ :=
  Finsupp.onFinset (Finset.univ) f.toFun (fun _ _ ↦ Finset.mem_univ _)

noncomputable
def Products.finsuppOfElement (f : LocallyConstant (C.proj (· ∈ J)) ℤ) :
    Products I →₀ ℤ :=
  (Finsupp.resFin_to_Z C J f).mapDomain (ofElement C J)

open Classical in
noncomputable
def SpanFinBasis (x : C.proj (· ∈ J)) : LocallyConstant (C.proj (· ∈ J)) ℤ where
  toFun := fun y ↦ if y = x then 1 else 0
  isLocallyConstant := by
    haveI : DiscreteTopology (C.proj (· ∈ J)) := discrete_of_t1_of_finite
    exact IsLocallyConstant.of_discrete _

open Classical in
lemma SpanFin.spanFin : ⊤ ≤ Submodule.span ℤ (Set.range (SpanFinBasis C J)) := by
  intro f _
  rw [Finsupp.mem_span_range_iff_exists_finsupp]
  use Finsupp.resFin_to_Z C J f
  ext x
  have hhh : ∀ α (map : α → LocallyConstant (C.proj (· ∈ J)) ℤ) (d : α →₀ ℤ),
      (d.sum (fun i (a : ℤ) ↦ a • map i)) x = d.sum (fun i a ↦ a • map i x) :=
    fun _ _ _ ↦ map_finsupp_sum (LocallyConstant.evalLinear x :
    LocallyConstant (C.proj (· ∈ J)) ℤ →ₗ[ℤ] ℤ) _ _
  rw [hhh]
  simp only [Finsupp.resFin_to_Z, LocallyConstant.toFun_eq_coe, SpanFinBasis,
    LocallyConstant.coe_mk, smul_eq_mul, mul_ite, mul_one, mul_zero, Finsupp.sum_ite_eq,
    Finsupp.mem_support_iff, Finsupp.onFinset_apply, ne_eq, ite_not,
    ite_eq_right_iff]
  exact fun h ↦ h.symm

def MapForList (x : C.proj (· ∈ J)) : I → LocallyConstant (C.proj (· ∈ J)) ℤ :=
  fun i ↦ if x.val i = true then e (C.proj (· ∈ J)) i else (1 - (e (C.proj (· ∈ J)) i))

def ListOfElementForProd (x : C.proj (· ∈ J)) :
    List (LocallyConstant (C.proj (· ∈ J)) ℤ) :=
  List.map (MapForList C J x) (J.sort (·≥·))

lemma listProd_apply (x : C) (l : List (LocallyConstant C ℤ)) :
    l.prod x = (l.map (LocallyConstant.evalMul x)).prod := by
  rw [← map_list_prod (LocallyConstant.evalMul x) l]
  rfl

lemma listProd_eq_basis (x : C.proj (· ∈ J)) :
    (ListOfElementForProd C J x).prod = SpanFinBasis C J x := by
  ext y
  dsimp [SpanFinBasis]
  split_ifs with h
  · rw [listProd_apply (C.proj (· ∈ J)) y _]
    apply List.prod_eq_one
    intro n hn
    simp only [List.mem_map] at hn
    obtain ⟨a, ha⟩ := hn
    rw [← ha.2]
    dsimp [LocallyConstant.evalMul]
    rw [h]
    dsimp [ListOfElementForProd] at ha
    simp only [List.mem_map] at ha
    obtain ⟨b, hb⟩ := ha.1
    rw [← hb.2]
    dsimp [MapForList]
    split_ifs with hh
    · simp only [e, Int.ofBool, LocallyConstant.coe_mk, ite_eq_left_iff]
      exact fun h' ↦ h' hh
    · rw [LocallyConstant.sub_apply]
      simp only [LocallyConstant.coe_one, Pi.one_apply, e, Int.ofBool, LocallyConstant.coe_mk,
        sub_eq_self, ite_eq_right_iff]
      exact hh
  · rw [listProd_apply (C.proj (· ∈ J)) y _]
    apply List.prod_eq_zero
    simp only [List.mem_map]
    have h' : y.val ≠ x.val
    · intro hh
      apply h
      exact Subtype.ext hh
    rw [Function.ne_iff] at h'
    obtain ⟨a, ha⟩ := h'
    by_cases hx : x.val a = true
    · refine ⟨e (C.proj (· ∈ J)) a, ⟨?_, ?_⟩⟩
      · simp only [ListOfElementForProd, List.mem_map]
        refine ⟨a, ⟨?_, ?_⟩⟩
        · simp only [Finset.mem_sort]
          obtain ⟨z, hz⟩ := x.prop
          rw [← hz.2, Proj] at hx
          simp only [Bool.ite_eq_true_distrib, if_false_right_eq_and] at hx
          exact hx.1
        · simp only [MapForList, ite_eq_left_iff]
          intro hxa
          exfalso
          exact hxa hx
      · simp only [LocallyConstant.evalMul, e, Int.ofBool, MonoidHom.coe_mk, OneHom.coe_mk,
          LocallyConstant.coe_mk, ite_eq_right_iff]
        rw [hx] at ha
        exact ha
    · refine ⟨1 - (e (C.proj (· ∈ J)) a), ⟨?_, ?_⟩⟩
      · simp only [ListOfElementForProd, List.mem_map]
        refine ⟨a, ⟨?_, ?_⟩⟩
        · simp only [Finset.mem_sort]
          obtain ⟨z, hz⟩ := y.prop
          simp only [Bool.not_eq_true] at hx
          rw [hx, ne_eq, Bool.not_eq_false] at ha
          rw [← hz.2, Proj] at ha
          simp only [Bool.ite_eq_true_distrib, if_false_right_eq_and] at ha
          exact ha.1
        · simp only [MapForList, ite_eq_right_iff]
          intro hxa
          exfalso
          exact hx hxa
      · simp only [LocallyConstant.evalMul, e, Int.ofBool, MonoidHom.coe_mk, OneHom.coe_mk,
          LocallyConstant.coe_mk, ite_eq_right_iff]
        rw [LocallyConstant.sub_apply]
        simp only [LocallyConstant.coe_one, Pi.one_apply, LocallyConstant.coe_mk]
        rw [sub_eq_zero]
        apply Eq.symm
        simp only [ite_eq_left_iff, Bool.not_eq_true]
        simp only [Bool.not_eq_true] at hx
        rw [hx] at ha
        exact ha

lemma GoodProducts.spanFin : ⊤ ≤ Submodule.span ℤ (Set.range (eval (C.proj (· ∈ J)))) := by
  rw [span_iff_products]
  refine le_trans (SpanFin.spanFin C J) ?_
  rw [Submodule.span_le]
  intro f hf
  obtain ⟨x, hx⟩ := hf
  rw [← hx, ← listProd_eq_basis]
  let l := J.sort (·≥·)
  have hlge : l.Chain' (·≥·)
  · rw [List.chain'_iff_pairwise]
    exact J.sort_sorted (·≥·)
  have hl : l.Chain' (·>·)
  · rw [List.chain'_iff_pairwise]
    dsimp
    have : ∀ (a b : I), a > b ↔ a ≥ b ∧ a ≠ b
    · intro a b
      rw [gt_iff_lt, lt_iff_le_and_ne]
      exact Iff.and Iff.rfl ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩
    have hr : (·>· : I → I → Prop) = (fun a b ↦ a ≥ b ∧ a ≠ b)
    · ext a b
      exact this a b
    rw [hr, List.pairwise_and_iff]
    refine ⟨List.chain'_iff_pairwise.mp hlge, ?_⟩
    have hn := J.nodup_toList
    have h := Finset.sort_perm_toList (·≥·) J
    rw [List.Perm.nodup_iff h.symm] at hn
    exact hn
  dsimp [ListOfElementForProd]
  suffices : l.Chain' (·>·) → (l.map (MapForList C J x)).prod ∈
      Submodule.span ℤ ((Products.eval (C.proj (· ∈ J))) '' {m | m.val ≤ l})
  · exact Submodule.span_mono (Set.image_subset_range _ _) (this hl)
  induction l with
  | nil =>
    · intro _
      apply Submodule.subset_span
      refine ⟨⟨[], List.chain'_nil⟩,⟨?_, rfl⟩⟩
      left
      rfl
  | cons a as ih =>
    · rw [List.map_cons, List.prod_cons]
      by_cases h : x.val a = true
      · have : MapForList C J x a = e (C.proj (· ∈ J)) a
        · simp only [MapForList, ite_eq_left_iff]
          intro hxa
          exfalso
          exact hxa h
        rw [this]
        intro ha
        rw [List.chain'_cons'] at ha
        specialize ih ha.2
        rw [← List.chain'_cons'] at ha
        rw [Finsupp.mem_span_image_iff_total] at ih
        obtain ⟨c, hc⟩ := ih
        rw [Finsupp.mem_supported, Finsupp.total_apply] at hc
        rw [← hc.2]
        have hmap :=
          fun g ↦ map_finsupp_sum (LocallyConstant.mulLinear ℤ (e (C.proj (· ∈ J)) a)) c g
        dsimp [LocallyConstant.mulLinear] at hmap
        rw [hmap]
        apply Submodule.finsupp_sum_mem
        intro m hm
        have hsm := (LocallyConstant.mulLinear ℤ (e (C.proj (· ∈ J)) a)).map_smul
        dsimp [LocallyConstant.mulLinear] at hsm
        rw [hsm]
        apply Submodule.smul_mem
        apply Submodule.subset_span
        have hmas : m.val ≤ as
        · apply hc.1
          simp only [Finset.mem_coe, Finsupp.mem_support_iff]
          exact hm
        refine ⟨⟨a :: m.val, ?_⟩, ⟨?_, ?_⟩⟩
        · by_cases hmnil : m.val = []
          · rw [hmnil]
            simp only [List.chain'_singleton]
          · rw [← List.cons_head!_tail hmnil, List.chain'_cons]
            refine ⟨?_, ?_⟩
            · have hasnil : as ≠ []
              · intro hna
                apply hmnil
                rw [hna, le_iff_lt_or_eq] at hmas
                cases' hmas with hmas hmas
                · exfalso
                  apply List.Lex.not_nil_right (·<·) m.val
                  exact hmas
                · exact hmas
              rw [← List.cons_head!_tail hasnil, List.chain'_cons] at ha
              refine gt_of_gt_of_ge ha.1 ?_
              rw [ge_iff_le, le_iff_lt_or_eq]
              rw [le_iff_lt_or_eq] at hmas
              cases' hmas with hmas hmas
              · rw [← le_iff_lt_or_eq]
                by_contra hh
                simp only [not_le] at hh
                rw [← List.cons_head!_tail hmnil, ← List.cons_head!_tail hasnil, ← not_le] at hmas
                apply hmas
                apply le_of_lt
                exact (Iff.mp (List.lt_iff_lex_lt _ _) (List.lt.head _ _ hh))
              · right
                rw [hmas]
            · rw [List.cons_head!_tail hmnil]
              exact m.prop
        · simp only [Set.mem_setOf_eq]
          rw [le_iff_lt_or_eq] at hmas ⊢
          cases' hmas with hmas hmas
          · left
            have haa : ¬(a < a) := gt_irrefl a
            exact Iff.mp (List.lt_iff_lex_lt _ _) (List.lt.tail haa haa
              (Iff.mpr (List.lt_iff_lex_lt _ _) hmas))
          · right
            rw [hmas]
        · simp only [Products.eval, List.map, List.prod_cons]
      · have : MapForList C J x a = 1 - (e (C.proj (· ∈ J)) a)
        · simp only [MapForList, ite_eq_right_iff]
          intro hxa
          exfalso
          exact h hxa
        rw [this]
        intro ha
        rw [List.chain'_cons'] at ha
        specialize ih ha.2
        rw [← List.chain'_cons'] at ha
        rw [Finsupp.mem_span_image_iff_total] at ih
        obtain ⟨c, hc⟩ := ih
        rw [Finsupp.mem_supported, Finsupp.total_apply] at hc
        rw [← hc.2]
        have hmap :=
          fun g ↦ map_finsupp_sum (LocallyConstant.mulLinear ℤ (e (C.proj (· ∈ J)) a)) c g
        dsimp [LocallyConstant.mulLinear] at hmap
        ring_nf
        rw [hmap]
        apply Submodule.add_mem
        · apply Submodule.neg_mem
          apply Submodule.finsupp_sum_mem
          intro m hm
          have hsm := (LocallyConstant.mulLinear ℤ (e (C.proj (· ∈ J)) a)).map_smul
          dsimp [LocallyConstant.mulLinear] at hsm
          rw [hsm]
          apply Submodule.smul_mem
          apply Submodule.subset_span
          have hmas : m.val ≤ as
          · apply hc.1
            simp only [Finset.mem_coe, Finsupp.mem_support_iff]
            exact hm
          refine ⟨⟨a :: m.val, ?_⟩, ⟨?_, ?_⟩⟩
          · by_cases hmnil : m.val = []
            · rw [hmnil]
              simp only [List.chain'_singleton]
            · rw [← List.cons_head!_tail hmnil, List.chain'_cons]
              refine ⟨?_, ?_⟩
              · have hasnil : as ≠ []
                · intro hna
                  apply hmnil
                  rw [hna, le_iff_lt_or_eq] at hmas
                  cases' hmas with hmas hmas
                  · exfalso
                    apply List.Lex.not_nil_right (·<·) m.val
                    exact hmas
                  · exact hmas
                rw [← List.cons_head!_tail hasnil, List.chain'_cons] at ha
                refine gt_of_gt_of_ge ha.1 ?_
                rw [ge_iff_le, le_iff_lt_or_eq]
                rw [le_iff_lt_or_eq] at hmas
                cases' hmas with hmas hmas
                · rw [← le_iff_lt_or_eq]
                  by_contra hh
                  simp only [not_le] at hh
                  rw [← List.cons_head!_tail hmnil, ← List.cons_head!_tail hasnil, ← not_le] at hmas
                  apply hmas
                  apply le_of_lt
                  exact (Iff.mp (List.lt_iff_lex_lt _ _) (List.lt.head _ _ hh))
                · right
                  rw [hmas]
              · rw [List.cons_head!_tail hmnil]
                exact m.prop
          · simp only [Set.mem_setOf_eq]
            rw [le_iff_lt_or_eq] at hmas ⊢
            cases' hmas with hmas hmas
            · left
              have haa : ¬(a < a) := gt_irrefl a
              exact Iff.mp (List.lt_iff_lex_lt _ _) (List.lt.tail haa haa
                (Iff.mpr (List.lt_iff_lex_lt _ _) hmas))
            · right
              rw [hmas]
          · simp only [Products.eval, List.map, List.prod_cons]
        · apply Submodule.finsupp_sum_mem
          intro m hm
          apply Submodule.smul_mem
          apply Submodule.subset_span
          have hmas : m.val ≤ as
          · apply hc.1
            simp only [Finset.mem_coe, Finsupp.mem_support_iff]
            exact hm
          refine ⟨m, ⟨?_, rfl⟩⟩
          simp only [Set.mem_setOf_eq]
          refine le_trans hmas ?_
          by_cases hasnil : as = []
          · rw [hasnil]
            apply le_of_lt
            exact List.nil_lt_cons a []
          · apply le_of_lt
            rw [← List.cons_head!_tail hasnil] at ha ⊢
            rw [List.chain'_cons] at ha
            have hlex := List.lt.head as.tail (as.head! :: as.tail) ha.1
            exact (Iff.mp (List.lt_iff_lex_lt _ _) hlex)

end Fin

lemma fin_comap_jointlySurjective
    (hC : IsClosed C)
    (f : LocallyConstant C ℤ) : ∃ (J : Finset I)
    (g : LocallyConstant (C.proj (· ∈ J)) ℤ), f = g.comap (ProjRestrict C (· ∈ J)) := by
  obtain ⟨J, g, h⟩ := @Profinite.exists_locallyConstant (Finset I)ᵒᵖ _ _ _
    (FinsetsCone hC.isCompact) _
    (finsetsCone_isLimit hC.isCompact) f
  exact ⟨(Opposite.unop J), g, h⟩

lemma GoodProducts.span (hC : IsClosed C) :
    ⊤ ≤ Submodule.span ℤ (Set.range (eval C)) := by
  rw [span_iff_products]
  intro f _
  have hf : ∃ K f', f = LinearResFin C K f' := fin_comap_jointlySurjective C hC f
  obtain ⟨K, f', hf⟩ := hf
  rw [hf]
  have hf' := spanFin C K (Submodule.mem_top : f' ∈ ⊤)
  have := Submodule.apply_mem_span_image_of_mem_span (LinearResFin C K) hf'
  refine Submodule.span_mono ?_ this
  intro l hl
  obtain ⟨y, ⟨m, hm⟩, hy⟩ := hl
  rw [← hm] at hy
  rw [← hy]
  exact ⟨m.val, linearResFin_of_eval C K m.val m.prop⟩

end Span

variable (I)

def ord (i : I) : Ordinal := Ordinal.typein ((·<·) : I → I → Prop) i

noncomputable
def term {o : Ordinal} (ho : o < Ordinal.type ((·<·) : I → I → Prop)) :
    I := Ordinal.enum ((·<·) : I → I → Prop) o ho

variable {I}

def contained (o : Ordinal) : Prop := ∀ f, f ∈ C → ∀ (i : I), f i = true → ord I i < o

section Zero

instance : Subsingleton (LocallyConstant (∅ : Set (I → Bool)) ℤ) :=
  subsingleton_iff.mpr (fun _ _ ↦ LocallyConstant.ext isEmptyElim)

instance GoodProducts.emptyEmpty :
    IsEmpty { l // Products.isGood (∅ : Set (I → Bool)) l } :=
    isEmpty_iff.mpr (fun ⟨l, hl⟩ ↦ hl (by
  rw [subsingleton_iff.mp inferInstance (Products.eval ∅ l) 0]
  exact Submodule.zero_mem _ ))

lemma GoodProducts.linearIndependentEmpty :
    LinearIndependent ℤ (eval (∅ : Set (I → Bool))) := linearIndependent_empty_type

def Products.nil : Products I := ⟨[], by simp only [List.chain'_nil]⟩

lemma Products.lt_nil_empty : { m : Products I | m < Products.nil } = ∅ := by
  ext ⟨m, hm⟩
  refine ⟨fun h ↦ ?_, by tauto⟩
  simp only [Set.mem_setOf_eq, lt_iff_lex_lt, nil, List.Lex.not_nil_right] at h

instance {α : Type _} [TopologicalSpace α] [Inhabited α] : Nontrivial (LocallyConstant α ℤ) := by
  use 0
  use 1
  intro h
  rw [LocallyConstant.ext_iff] at h
  apply @zero_ne_one ℤ
  exact h default

lemma Products.isGood_nil : Products.isGood ({fun _ ↦ false} : Set (I → Bool)) Products.nil:= by
  intro h
  rw [Products.lt_nil_empty] at h
  simp only [Products.eval, List.map, List.prod_nil, Set.image_empty, Submodule.span_empty,
    Submodule.mem_bot, one_ne_zero] at h

lemma Products.span_nil_eq_top :
    Submodule.span ℤ (eval ({fun _ ↦ false} : Set (I → Bool)) '' {nil}) = ⊤ := by
  rw [Set.image_singleton, eq_top_iff]
  intro f _
  rw [Submodule.mem_span_singleton]
  refine ⟨f default, ?_⟩
  simp only [eval, List.map, List.prod_nil, zsmul_eq_mul, mul_one]
  ext x
  have : x = default := by simp only [Set.default_coe_singleton, eq_iff_true_of_subsingleton]
  rw [this]
  rfl

noncomputable
instance GoodProducts.singletonUnique :
  Unique { l // Products.isGood ({fun _ ↦ false} : Set (I → Bool)) l } :=
{ default := ⟨Products.nil, Products.isGood_nil⟩
  uniq := by
    rintro ⟨⟨l, hl⟩, hll⟩
    ext
    cases' (List.Lex.nil_left_or_eq_nil l : List.Lex (·<·) [] l ∨ l = []) with h h
    · exfalso
      apply hll
      have he : {Products.nil} ⊆ {m | m < ⟨l,hl⟩ }
      · simpa only [Products.nil, Products.lt_iff_lex_lt, Set.singleton_subset_iff,
          Set.mem_setOf_eq]
      apply Submodule.span_mono (Set.image_subset _ he)
      rw [Products.span_nil_eq_top]
      exact Submodule.mem_top
    · exact Subtype.ext h }

instance (α : Type _) [TopologicalSpace α] : NoZeroSMulDivisors ℤ (LocallyConstant α ℤ) := by
  constructor
  intro c f h
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    ext x
    rw [LocallyConstant.ext_iff] at h
    apply_fun fun (y : ℤ) ↦ c * y
    · simp at h
      simp
      exact h x
    · exact mul_right_injective₀ hc

lemma GoodProducts.linearIndependentSingleton :
    LinearIndependent ℤ (eval ({fun _ ↦ false} : Set (I → Bool))) := by
  refine linearIndependent_unique (eval ({fun _ ↦ false} : Set (I → Bool))) ?_
  simp only [eval, Products.eval, List.map, List.prod_nil, ne_eq, one_ne_zero, not_false_eq_true]

end Zero

section Maps

lemma contained_eq_res (o : Ordinal) (h : contained C o) :
    C = C.proj (ord I · < o) := by
  have := proj_prop_eq_self C (ord I · < o)
  simp [Set.proj, Bool.not_eq_false] at this
  exact (this (fun i x hx ↦ h x hx i)).symm

lemma isClosed_res (o : Ordinal) (hC : IsClosed C) : IsClosed (C.proj (ord I · < o)) :=
  isClosedMap_proj _ C hC

lemma contained_res (o : Ordinal) : contained (C.proj (ord I · < o)) o := by
  intro x hx j hj
  obtain ⟨_, ⟨_, h⟩⟩ := hx
  dsimp [Proj] at h
  rw [← congr_fun h j] at hj
  simp only [Bool.ite_eq_true_distrib, if_false_right_eq_and] at hj
  exact hj.1

noncomputable
def ResOnSubset (o : Ordinal) : C → (C.proj (ord I · < o)) := ProjRestrict C _

lemma continuous_resOnSubset (o : Ordinal) : Continuous (ResOnSubset C o) :=
  continuous_projRestrict _ _

lemma surjective_resOnSubset (o : Ordinal) : Function.Surjective (ResOnSubset C o) :=
  surjective_projRestrict _ _

noncomputable
def ResOnSubsets {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) :
    (C.proj (ord I · < o₂)) → (C.proj (ord I · < o₁)) :=
  ProjRestricts _ (fun _ hh ↦ by simp only [Set.mem_setOf_eq]; exact lt_of_lt_of_le hh h)

lemma continuous_resOnSubsets {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) : Continuous (ResOnSubsets C h) :=
  continuous_projRestricts _ _

lemma surjective_resOnSubsets {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) :
    Function.Surjective (ResOnSubsets C h) :=
  surjective_projRestricts _ _

end Maps

section ProductsFactorisation

namespace Products

theorem lt_of_head!_lt {l : Products I} {o₁ : Ordinal}
    (hlhead : l.val ≠ [] → ord I (l.val.head!) < o₁) (a : I) (ha : a ∈ l.val) : ord I a < o₁ := by
  refine lt_of_le_of_lt ?_ (hlhead (List.ne_nil_of_mem ha))
  simp only [ord, Ordinal.typein_le_typein, not_lt]
  have hh := List.chain'_iff_pairwise.mp l.prop
  rw [← List.cons_head!_tail (List.ne_nil_of_mem ha)] at hh
  rw [← List.cons_head!_tail (List.ne_nil_of_mem ha)] at ha
  simp only [List.find?, List.mem_cons] at ha
  cases' ha with ha ha
  · exact le_of_eq ha
  · exact le_of_lt (List.rel_of_pairwise_cons hh ha)

lemma evalFac {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hlhead : l.val ≠ [] → ord I (l.val.head!) < o₁) :
    l.eval (C.proj (ord I · < o₁)) ∘ ResOnSubsets C h = l.eval (C.proj (ord I · < o₂)) := by
  refine evalFacProps C (fun (i : I) ↦ ord I i < o₁) (fun (i : I) ↦ ord I i < o₂) ?_ ?_
  exact fun a ha ↦ lt_of_head!_lt hlhead a ha

lemma evalFacC {l : Products I} {o : Ordinal}
    (hlhead : l.val ≠ [] → ord I (l.val.head!) < o) :
    l.eval (C.proj (ord I · < o)) ∘ ResOnSubset C o = l.eval C := by
  refine evalFacProp C (ord I · < o) ?_
  exact fun a ha ↦ lt_of_head!_lt hlhead a ha

lemma head_lt_ord_of_isGood {l : Products I} {o : Ordinal}
    (h : l.isGood (C.proj (ord I · < o))) : l.val ≠ [] → ord I (l.val.head!) < o :=
  fun hn ↦ prop_of_isGood C (ord I · < o) h l.val.head! (List.head!_mem_self hn)

lemma goodEvalFac {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (C.proj (ord I · < o₁))) :
    l.eval (C.proj (ord I · < o₁)) ∘ ResOnSubsets C h = l.eval (C.proj (ord I · < o₂)) :=
  evalFac C h (head_lt_ord_of_isGood C hl)

lemma goodEvalFacC {l : Products I} {o : Ordinal} (hl : l.isGood (C.proj (ord I · < o))) :
    l.eval (C.proj (ord I · < o)) ∘ ResOnSubset C o = l.eval C :=
  evalFacC C (head_lt_ord_of_isGood C hl)

lemma eval_comapFac {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (C.proj (ord I · < o₁))) :
    LocallyConstant.comap (ResOnSubsets C h) (l.eval (C.proj (ord I · < o₁))) =
    l.eval (C.proj (ord I · < o₂)) := by
  ext f
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_resOnSubsets _ _)]
  exact congr_fun (goodEvalFac C h hl) _

lemma eval_comapFacC {l : Products I} {o : Ordinal}
    (hl : l.isGood (C.proj (ord I · < o))) :
    LocallyConstant.comap (ResOnSubset C o) (l.eval (C.proj (ord I · < o))) = l.eval C := by
  ext f
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_resOnSubset C _)]
  exact congr_fun (goodEvalFacC C hl) _

lemma eval_comapFac' {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hlhead : l.val ≠ [] → ord I (l.val.head!) < o₁) :
    LocallyConstant.comap (ResOnSubsets C h) (l.eval (C.proj (ord I · < o₁))) =
    l.eval (C.proj (ord I · < o₂)) := by
  ext f
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_resOnSubsets _ _)]
  exact congr_fun (evalFac C h hlhead) _

lemma eval_comapFacLinear' {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hlhead : l.val ≠ [] → ord I (l.val.head!) < o₁) :
    LocallyConstant.comapLinear ℤ (ResOnSubsets C h) (continuous_resOnSubsets _ _)
    (l.eval (C.proj (ord I · < o₁))) =
    l.eval (C.proj (ord I · < o₂)) :=
  eval_comapFac' _ _ hlhead

lemma eval_comapFac'C {l : Products I} {o : Ordinal}
    (hlhead : l.val ≠ [] → ord I (l.val.head!) < o) :
    LocallyConstant.comap (ResOnSubset C o) (l.eval (C.proj (ord I · < o))) = l.eval C := by
  ext f
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_resOnSubset _ _)]
  exact congr_fun (evalFacC C hlhead) _

lemma eval_comapFacLinear'C {l : Products I} {o : Ordinal}
    (hlhead : l.val ≠ [] → ord I (l.val.head!) < o) :
    LocallyConstant.comapLinear ℤ (ResOnSubset C o) (continuous_resOnSubset _ _)
    (l.eval (C.proj (ord I · < o))) =
    l.eval C :=
  eval_comapFac'C _ hlhead

lemma lt_ord {l m : Products I} {o : Ordinal} (hmltl : m < l)
    (hlhead : l.val ≠ [] → ord I l.val.head! < o) : m.val ≠ [] → ord I m.val.head! < o := by
  intro hm
  rw [lt_iff_lex_lt] at hmltl
  by_cases hl : l.val = []
  · exfalso
    rw [hl] at hmltl
    exact List.Lex.not_nil_right _ _ hmltl
  · suffices hml : m.val.head! ≤ l.val.head!
    · refine lt_of_le_of_lt ?_ (hlhead hl)
      dsimp [ord]
      simp only [Ordinal.typein_le_typein, not_lt]
      exact hml
    rw [← List.cons_head!_tail hl] at hmltl
    rw [← List.cons_head!_tail hm] at hmltl
    by_contra hn
    simp only [not_le] at hn
    have hml : List.Lex (·<·) (l.val.head! :: l.val.tail) (m.val.head! :: m.val.tail) :=
      List.Lex.rel hn
    exact List.Lex.isAsymm.aux _ _ _ hml hmltl

lemma eval_comapFacImage' {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.val ≠ [] → ord I l.val.head! < o₁) : eval (C.proj (ord I · < o₂)) '' { m | m < l } =
    (LocallyConstant.comapLinear ℤ (ResOnSubsets C h) (continuous_resOnSubsets _ _)) ''
    (eval (C.proj (ord I · < o₁)) '' { m | m < l }) := by
  dsimp [LocallyConstant.comapLinear]
  ext f
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · obtain ⟨m,hm⟩ := hf
    rw [← eval_comapFac' C h (lt_ord hm.1 hl)] at hm
    rw [← hm.2]
    simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and]
    use m
    exact ⟨hm.1, by rfl⟩
  · rw [← Set.image_comp] at hf
    obtain ⟨m,hm⟩ := hf
    dsimp at hm
    rw [eval_comapFac' C h (lt_ord hm.1 hl)] at hm
    rw [← hm.2]
    simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and]
    use m
    exact ⟨hm.1, by rfl⟩

lemma eval_comapFacImage'C {l : Products I} {o : Ordinal}
    (hl : l.val ≠ [] → ord I l.val.head! < o) : eval C '' { m | m < l } =
    (LocallyConstant.comapLinear ℤ (ResOnSubset C o) (continuous_resOnSubset _ _)) ''
    (eval (C.proj (ord I · < o)) '' { m | m < l }) := by
  dsimp [LocallyConstant.comapLinear]
  ext f
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · obtain ⟨m,hm⟩ := hf
    rw [← eval_comapFac'C C (lt_ord hm.1 hl)] at hm
    rw [← hm.2]
    simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and]
    use m
    exact ⟨hm.1, by rfl⟩
  · rw [← Set.image_comp] at hf
    obtain ⟨m,hm⟩ := hf
    dsimp at hm
    rw [eval_comapFac'C C (lt_ord hm.1 hl)] at hm
    rw [← hm.2]
    simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and]
    use m
    exact ⟨hm.1, by rfl⟩

lemma eval_comapFacImage {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (C.proj (ord I · < o₁))) : eval (C.proj (ord I · < o₂)) '' { m | m < l } =
    (LocallyConstant.comapLinear ℤ (ResOnSubsets C h) (continuous_resOnSubsets _ _)) ''
    (eval (C.proj (ord I · < o₁)) '' { m | m < l }) :=
  eval_comapFacImage' C h (head_lt_ord_of_isGood C hl)

lemma isGood_mono {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (C.proj (ord I · < o₁))) : l.isGood (C.proj (ord I · < o₂)) := by
  intro hl'
  apply hl
  rw [eval_comapFacImage C h hl] at hl'
  simp only [Submodule.span_image, Submodule.mem_map] at hl'
  obtain ⟨y, ⟨hy₁, hy₂⟩ ⟩ := hl'
  dsimp [LocallyConstant.comapLinear] at hy₂
  rw [← eval_comapFac C h hl] at hy₂
  have hy := LocallyConstant.comap_injective _ (continuous_resOnSubsets C h)
    (surjective_resOnSubsets C h) hy₂
  subst hy
  assumption

end Products

lemma GoodProducts.evalFac {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (C.proj (ord I · < o₁))) : eval (C.proj (ord I · < o₂))
    ⟨l, (Products.isGood_mono C h hl)⟩ =
    eval (C.proj (ord I · < o₁)) ⟨l, hl⟩ ∘ ResOnSubsets C h :=
  (Products.goodEvalFac C h hl).symm

end ProductsFactorisation

section Nonempty

instance [Nonempty C] : Inhabited (C.proj (ord I · < 0)) := by
  use (fun _ ↦ false)
  have : C.Nonempty
  · rw [← Set.nonempty_coe_sort]
    assumption
  obtain ⟨x,hx⟩ := this
  use x
  refine ⟨hx, ?_⟩
  dsimp [Proj]
  ext i
  split_ifs with h
  · exfalso
    exact Ordinal.not_lt_zero _ h
  · rfl

instance [Nonempty C] : Nontrivial (LocallyConstant C ℤ) := by
  use 0
  use 1
  intro h
  rw [LocallyConstant.ext_iff] at h
  apply @zero_ne_one ℤ
  have : C.Nonempty
  · rw [← Set.nonempty_coe_sort]
    assumption
  obtain ⟨x,hx⟩ := this
  exact h ⟨x,hx⟩

lemma evalProducts.nilNeZeroAny [Nonempty C] : Products.nil.eval C ≠ 0 := by
  dsimp [Products.eval]
  exact one_ne_zero

lemma nilIsGoodAny [Nonempty C] : Products.isGood C Products.nil := by
  intro h
  rw [Products.lt_nil_empty] at h
  simp only [Set.image_empty, Submodule.span_empty, Submodule.mem_bot] at h
  apply evalProducts.nilNeZeroAny C h

instance [Nonempty C] (o : Ordinal) : Nonempty (C.proj (ord I · < o)) := by
  have : C.Nonempty
  · rw [← Set.nonempty_coe_sort]
    assumption
  rw [Set.nonempty_coe_sort]
  obtain ⟨x,hx⟩ := this
  use Proj (ord I · < o) x
  use x

end Nonempty

section Smaller

namespace GoodProducts

def smaller (o : Ordinal) : Set (LocallyConstant C ℤ) :=
  (LocallyConstant.comapLinear ℤ
    (ResOnSubset C o) (continuous_resOnSubset C o)) '' (range (C.proj (ord I · < o)))

noncomputable
def range_equiv_smaller_toFun (o : Ordinal) :
    range (C.proj (ord I · < o)) → smaller C o :=
  fun x ↦ ⟨(↑(LocallyConstant.comapLinear ℤ (ResOnSubset C o) (continuous_resOnSubset _ _)) :
    LocallyConstant (C.proj (ord I · < o)) ℤ → LocallyConstant C ℤ) ↑x,
    by { dsimp [smaller]; use x.val; exact ⟨x.property, rfl⟩  } ⟩

lemma range_equiv_smaller_toFun_bijective (o : Ordinal) :
    Function.Bijective (range_equiv_smaller_toFun C o) := by
  refine ⟨fun a b hab ↦ ?_, fun ⟨a,ha⟩ ↦ ?_⟩
  · dsimp [range_equiv_smaller_toFun, LocallyConstant.comapLinear] at hab
    ext1
    simp only [Subtype.mk.injEq] at hab
    exact LocallyConstant.comap_injective _ (continuous_resOnSubset _ _)
      (surjective_resOnSubset _ _) hab
  · obtain ⟨b,hb⟩ := ha
    use ⟨b,hb.1⟩
    dsimp [range_equiv_smaller_toFun]
    simp only [Subtype.mk.injEq]
    exact hb.2

noncomputable
def range_equiv_smaller (o : Ordinal) : range (C.proj (ord I · < o)) ≃ smaller C o :=
Equiv.ofBijective (range_equiv_smaller_toFun C o) (range_equiv_smaller_toFun_bijective C o)

lemma smaller_factorization (o : Ordinal) :
    (fun (p : smaller C o) ↦ p.1) ∘ (range_equiv_smaller C o).toFun =
    ↑(LocallyConstant.comapLinear ℤ (ResOnSubset C o) (continuous_resOnSubset _ _)) ∘
    (fun (p : range (C.proj (ord I · < o))) ↦ p.1) := by rfl

lemma linearIndependent_iff_smaller (o : Ordinal) :
    LinearIndependent ℤ (GoodProducts.eval (C.proj (ord I · < o))) ↔
    LinearIndependent ℤ (fun (p : smaller C o) ↦ p.1) := by
  rw [GoodProducts.linearIndependent_iff_range]
  rw [← LinearMap.linearIndependent_iff (LocallyConstant.comapLinear ℤ (ResOnSubset C o)
        (continuous_resOnSubset _ _)) (LocallyConstant.comapLinear_injective _
        (continuous_resOnSubset _ _) (surjective_resOnSubset _ _))]
  rw [← smaller_factorization C o]
  exact linearIndependent_equiv _

lemma smaller_mono {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) : smaller C o₁ ⊆ smaller C o₂ := by
  intro f hf
  dsimp [smaller, LocallyConstant.comapLinear] at *
  obtain ⟨g, hg⟩ := hf
  simp only [Set.mem_image]
  use LocallyConstant.comap (ResOnSubsets C h) g
  refine ⟨?_, ?_⟩
  · dsimp [range]
    dsimp [range] at hg
    obtain ⟨⟨l,gl⟩, hl⟩ := hg.1
    use ⟨l, Products.isGood_mono C h gl⟩
    ext x
    rw [LocallyConstant.coe_comap_apply _ _ (continuous_resOnSubsets _ _), ← hl]
    exact congr_fun (GoodProducts.evalFac _ _ _) x
  · rw [← hg.2]
    ext x
    rw [LocallyConstant.coe_comap_apply _ _ (continuous_resOnSubset _ _)]
    rw [LocallyConstant.coe_comap_apply _ _ (continuous_resOnSubset _ _)]
    rw [LocallyConstant.coe_comap_apply _ _ (continuous_resOnSubsets _ _)]
    congr
    exact congr_fun (projRestricts_comp_projRestrict C _) x

noncomputable
def equiv_smaller (o : Ordinal) : GoodProducts (C.proj (ord I · < o)) ≃ smaller C o :=
Equiv.trans (equiv_range (C.proj (ord I · < o))) (range_equiv_smaller C o)

lemma eval_eq_comp_equiv (o : Ordinal) :
    (fun (l : GoodProducts (C.proj (ord I · < o))) ↦ Products.eval C l.1) =
    (fun p ↦ ↑p) ∘ ↑(equiv_smaller C o) := by
  ext p f
  dsimp [equiv_smaller, range_equiv_smaller, range_equiv_smaller_toFun,
    equiv_range, eval, LocallyConstant.comapLinear]
  rw [congr_fun (Products.goodEvalFacC C p.2).symm f,
    LocallyConstant.coe_comap_apply _ _ (continuous_resOnSubset _ _)]
  rfl

end GoodProducts

end Smaller

section Limit

lemma Products.limitOrdinal {o : Ordinal} (ho : o.IsLimit) (l : Products I) :
    l.isGood (C.proj (ord I · < o)) ↔
    ∃ (o' : Ordinal), o' < o ∧ l.isGood (C.proj (ord I · < o')) := by
  refine ⟨fun h ↦ ?_, fun h ↦ by obtain ⟨o',⟨ho',hl⟩⟩ := h; exact isGood_mono C (le_of_lt ho') hl⟩
  refine Or.elim C.eq_empty_or_nonempty (fun hC ↦
    (by rw [hC] at h; simp only [Set.proj, Set.image_empty] at h ; exact isEmptyElim (⟨l, h⟩ :
    {m : Products I // m.isGood (∅ : Set (I → Bool))}))) (fun hC ↦ ?_)
  dsimp [Ordinal.IsLimit] at ho
  obtain ⟨l, hl⟩ := l
  induction l with
  | nil =>
    haveI : Nonempty C := Set.Nonempty.to_subtype hC
    have ho' : o ≠ 0 := ho.1
    rw [← Ordinal.pos_iff_ne_zero] at ho'
    use 0
    exact ⟨ho', nilIsGoodAny _⟩
  | cons a as _ =>
    have := Products.head_lt_ord_of_isGood C h (List.cons_ne_nil a as)
    simp only [List.head!_cons] at this
    refine ⟨Order.succ (ord I a), ⟨ho.2 _ this, fun he ↦ ?_⟩⟩
    apply h
    rw [eval_comapFacImage' C (le_of_lt (ho.2 (ord I a) this)) (fun _ ↦ by simp),
      ← eval_comapFacLinear' C (le_of_lt (ho.2 (ord I a) this)) (fun _ ↦ by simp),
      Submodule.apply_mem_span_image_iff_mem_span]
    · assumption
    · exact LocallyConstant.comap_injective _ (continuous_resOnSubsets _ _)
        (surjective_resOnSubsets _ _)

lemma GoodProducts.union {o : Ordinal} (ho : o.IsLimit) (hsC : contained C o) :
    range C = ⋃ (e : {o' // o' < o}), (smaller C e.val) := by
  ext p
  refine ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩
  · simp only [smaller, range, Set.mem_iUnion, Set.mem_image, Set.mem_range, Subtype.exists]
    dsimp [range] at hp
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_range, Subtype.exists]
    obtain ⟨⟨l,hl⟩,hp⟩ := hp
    rw [contained_eq_res C o hsC, Products.limitOrdinal C ho] at hl
    obtain ⟨o',ho'⟩ := hl
    use o'
    use ho'.1
    use GoodProducts.eval (C.proj (ord I · < o')) ⟨l,ho'.2⟩
    refine ⟨⟨l, ho'.2, rfl⟩, ?_⟩
    rw [← hp]
    exact Products.eval_comapFacC C ho'.2
  · dsimp [range]
    simp only [Set.mem_range, Subtype.exists]
    simp only [Set.mem_iUnion, Subtype.exists, exists_prop] at hp
    obtain ⟨o', ⟨h, ⟨f, ⟨⟨⟨l, hl⟩, hlf⟩, hf⟩⟩⟩⟩  := hp
    rw [← hlf] at hf
    rw [← hf]
    refine ⟨l, ?_, (Products.eval_comapFacC C hl).symm⟩
    rw [contained_eq_res C o hsC]
    exact Products.isGood_mono C (le_of_lt h) hl

def GoodProducts.range_equiv {o : Ordinal} (ho : o.IsLimit) (hsC : contained C o) :
    range C ≃ ⋃ (e : {o' // o' < o}), (smaller C e.val) :=
  Equiv.Set.ofEq (union C ho hsC)

lemma GoodProducts.range_equiv_factorization {o : Ordinal} (ho : o.IsLimit)
    (hsC : contained C o) :
    (fun (p : ⋃ (e : {o' // o' < o}), (smaller C e.val)) ↦ p.1) ∘ (range_equiv C ho hsC).toFun =
    (fun (p : range C) ↦ (p.1 : LocallyConstant C ℤ)) := by
  rfl

lemma GoodProducts.linearIndependent_iff_union_smaller {o : Ordinal} (ho : o.IsLimit)
    (hsC : contained C o) : LinearIndependent ℤ (GoodProducts.eval C) ↔
    LinearIndependent ℤ (fun (p : ⋃ (e : {o' // o' < o}), (smaller C e.val)) ↦ p.1) := by
  rw [GoodProducts.linearIndependent_iff_range, ← range_equiv_factorization C ho hsC]
  exact linearIndependent_equiv (range_equiv C ho hsC)

lemma DirectedS (o : Ordinal) : Directed (· ⊆ ·) (fun e ↦ GoodProducts.smaller C
    e.val : {o' // o' < o} → Set (LocallyConstant C ℤ)) := by
  rintro ⟨o₁,h₁⟩ ⟨o₂,h₂⟩
  dsimp
  have h : o₁ ≤ o₂ ∨ o₂ ≤ o₁ :=
    (inferInstance : IsTotal Ordinal ((·≤·) : Ordinal → Ordinal → Prop)).total o₁ o₂
  cases h
  · use ⟨o₂,h₂⟩
    exact ⟨GoodProducts.smaller_mono C (by assumption), GoodProducts.smaller_mono C (le_refl o₂)⟩
  · use ⟨o₁,h₁⟩
    exact ⟨GoodProducts.smaller_mono C (le_refl o₁), GoodProducts.smaller_mono C (by assumption)⟩

end Limit

section Successor

variable (o : Ordinal) (hC : IsClosed C) (hsC : contained C (Order.succ o))

def GoodProducts.StartingWithMax : Set (Products I) :=
{l | l.isGood C ∧ l.val ≠ [] ∧ ord I l.val.head! = o}

lemma GoodProducts.union_succ :
    GoodProducts C = GoodProducts (C.proj (ord I · < o)) ∪ StartingWithMax C o := by
  ext ⟨l,hl⟩
  dsimp [GoodProducts, StartingWithMax]
  simp only [Set.mem_union, Set.mem_setOf_eq]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_cases hln : l = []
    · left
      simp_rw [hln]
      refine Or.elim C.eq_empty_or_nonempty (fun hC ↦ ?_) (fun hC ↦ ?_)
      · rw [hC] at h
        exact isEmptyElim (⟨⟨l, hl⟩, h⟩ : {m : Products I // m.isGood (∅ : Set (I → Bool))})
      · haveI : Nonempty C := Iff.mpr Set.nonempty_coe_sort hC
        exact nilIsGoodAny (C.proj (ord I · < o))
    · by_cases hh : ord I l.head! = o
      · right
        exact ⟨h,hln,hh⟩
      · left
        intro he
        apply h
        rw [contained_eq_res C (Order.succ o) hsC] at h
        have hls := Products.head_lt_ord_of_isGood C h hln
        simp only [Order.lt_succ_iff] at hls
        have hlhead : ord I (⟨l,hl⟩ : Products I).val.head! < o := lt_of_le_of_ne hls hh
        rw [Products.eval_comapFacImage'C C (fun _ ↦ hlhead),
          ← Products.eval_comapFacLinear'C C (fun _ ↦ hlhead),
          Submodule.apply_mem_span_image_iff_mem_span]
        · assumption
        · exact LocallyConstant.comap_injective _ (continuous_resOnSubset _ _)
            (surjective_resOnSubset _ _)
  · refine Or.elim h (fun hh ↦ ?_) (fun hh ↦ ?_)
    · have := Products.isGood_mono C (le_of_lt (Order.lt_succ o)) hh
      rwa [contained_eq_res C (Order.succ o) hsC]
    · exact hh.1

def GoodProducts.sum_to :
    (GoodProducts (C.proj (ord I · < o))) ⊕ (StartingWithMax C o) → Products I :=
  Sum.elim Subtype.val Subtype.val

lemma GoodProducts.injective_sum_to : Function.Injective (sum_to C o) := by
  apply Function.Injective.sum_elim
  · exact Subtype.val_injective
  · exact Subtype.val_injective
  rintro ⟨a,ha⟩ ⟨b,hb⟩
  dsimp
  dsimp [GoodProducts] at ha
  dsimp [StartingWithMax] at hb
  by_cases hanil : a.val = []
  · rw [← hanil] at hb
    apply Ne.symm
    exact Subtype.ne_of_val_ne hb.2.1
  · have ha' := Products.head_lt_ord_of_isGood C ha hanil
    rw [← hb.2.2] at ha'
    dsimp [ord] at ha'
    simp only [Ordinal.typein_lt_typein] at ha'
    have := ne_of_lt ha'
    intro hab
    apply this
    rw [hab]

noncomputable
def GoodProducts.sum_to_equiv := Equiv.ofInjective (sum_to C o) (injective_sum_to C o)

lemma GoodProducts.sum_to_range :
    Set.range (sum_to C o) = GoodProducts (C.proj (ord I · < o)) ∪ StartingWithMax C o := by
  have h : Set.range (sum_to C o) = _ ∪ _ := Set.Sum.elim_range _ _
  rw [h]
  congr
  <;> ext l
  · refine ⟨fun hl ↦ ?_, fun hl ↦ ?_⟩
    · obtain ⟨m,hm⟩ := hl
      rw [← hm]
      exact m.prop
    · use ⟨l,hl⟩
  · refine ⟨fun hl ↦ ?_, fun hl ↦ ?_⟩
    · obtain ⟨m,hm⟩ := hl
      rw [← hm]
      exact m.prop
    · use ⟨l,hl⟩

noncomputable
def GoodProducts.sum_equiv :
    GoodProducts (C.proj (ord I · < o)) ⊕ (StartingWithMax C o) ≃ GoodProducts C :=
  Equiv.trans (Equiv.trans (sum_to_equiv C o) (Equiv.Set.ofEq (sum_to_range C o)))
    (Equiv.Set.ofEq (union_succ C o hsC).symm)

lemma GoodProducts.sum_equiv_comp_eval_eq_elim : eval C ∘ (sum_equiv C o hsC).toFun =
    (Sum.elim (fun (l : GoodProducts (C.proj (ord I · < o))) ↦ Products.eval C l.1)
    (fun (l : StartingWithMax C o) ↦ Products.eval C l.1)) := by
  ext ⟨_,_⟩
  · rfl
  · rfl

lemma GoodProducts.linearIndependent_iff_sum :
    LinearIndependent ℤ (eval C) ↔ LinearIndependent ℤ (Sum.elim
    (fun (l : GoodProducts (C.proj (ord I · < o))) ↦ Products.eval C l.1)
    (fun (l : StartingWithMax C o) ↦ Products.eval C l.1)) := by
  rw [← linearIndependent_equiv (sum_equiv C o hsC), ← sum_equiv_comp_eval_eq_elim C o hsC]
  exact Iff.rfl

lemma GoodProducts.span_sum :
    Set.range (eval C) = Set.range (Sum.elim
    (fun (l : GoodProducts (C.proj (ord I · < o))) ↦ Products.eval C l.1)
    (fun (l : StartingWithMax C o) ↦ Products.eval C l.1)) := by
  rw [← sum_equiv_comp_eval_eq_elim C o hsC]
  simp only [Equiv.toFun_as_coe, EquivLike.range_comp]

lemma GoodProducts.linearIndependent_succ_iff :
    LinearIndependent ℤ (eval (C.proj (ord I · < o))) ↔ LinearIndependent ℤ
    (fun (l : GoodProducts (C.proj (ord I · < o))) ↦ Products.eval C l.1) := by
  rw [linearIndependent_iff_smaller, ← linearIndependent_equiv (equiv_smaller C o),
    eval_eq_comp_equiv]

variable {o} (ho : o < Ordinal.type (·<· : I → I → Prop))

def C0 := C ∩ {f | f (term I ho) = false}

def C1 := C ∩ {f | f (term I ho) = true}

lemma isClosed_C0 : IsClosed (C0 C ho) := by
  refine IsClosed.inter hC ?_
  have h : Continuous ((fun f ↦ f (term I ho) : (I → Bool) → Bool)) :=
      continuous_apply (term I ho)
  exact (continuous_iff_isClosed.mp h) {false} (isClosed_discrete _)

lemma isClosed_C1 : IsClosed (C1 C ho) := by
  refine IsClosed.inter hC ?_
  have h : Continuous ((fun f ↦ f (term I ho) : (I → Bool) → Bool)) :=
      continuous_apply (term I ho)
  exact (continuous_iff_isClosed.mp h) {true} (isClosed_discrete _)

lemma contained_C1 : contained ((C1 C ho).proj (ord I · < o)) o :=
  contained_res _ _

lemma union_C0C1_eq : (C0 C ho) ∪ (C1 C ho) = C := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · dsimp [C0, C1] at hx
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq] at hx
    rw [← and_or_left] at hx
    exact hx.1
  · dsimp [C0, C1]
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [← and_or_left]
    refine ⟨hx, ?_⟩
    by_cases h : x (term I ho) = false
    · left
      assumption
    · right
      simpa only [← Bool.not_eq_false]

def C0' : Set C := {f | f.val ∈ C0 C ho}

def C1' : Set C := {f | f.val ∈ C1 C ho}

lemma isOpen_false : IsOpen {f : I → Bool | f (term I ho) = false} := by
  have h : Continuous ((fun f ↦ f (term I ho) : (I → Bool) → Bool)) :=
      continuous_apply (term I ho)
  exact IsOpen.preimage h (isOpen_discrete {false})

lemma isOpen_true : IsOpen {f : I → Bool | f (term I ho) = true} := by
  have h : Continuous ((fun f ↦ f (term I ho) : (I → Bool) → Bool)) :=
      continuous_apply (term I ho)
  exact IsOpen.preimage h (isOpen_discrete {true})

lemma isClopen_C0' : IsClopen (C0' C ho) := by
  constructor
  · have := IsOpen.preimage (continuous_subtype_val : Continuous (fun (i : C) ↦ i.val))
      (isOpen_false ho)
    suffices h : C0' C ho = Subtype.val ⁻¹' {f | f (term I ho) = false}
    · rw [h]
      exact this
    ext x
    exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨x.prop, hx⟩⟩
  · have := IsClosed.preimage (continuous_subtype_val : Continuous (fun (i : C) ↦ i.val))
      (isClosed_C0 C hC ho)
    suffices h : C0' C ho = Subtype.val ⁻¹' (C0 C ho)
    · rw [h]
      exact this
    rfl

lemma isClopen_C1' : IsClopen (C1' C ho) := by
  constructor
  · have := IsOpen.preimage (continuous_subtype_val : Continuous (fun (i : C) ↦ i.val))
      (isOpen_true ho)
    suffices h : C1' C ho = Subtype.val ⁻¹' {f | f (term I ho) = true}
    · rw [h]
      exact this
    ext x
    exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨x.prop, hx⟩⟩
  · have := IsClosed.preimage (continuous_subtype_val : Continuous (fun (i : C) ↦ i.val))
      (isClosed_C1 C hC ho)
    suffices h : C1' C ho = Subtype.val ⁻¹' (C1 C ho)
    · rw [h]
      exact this
    rfl

lemma union_C0'C1'_eq_univ : (C0' C ho) ∪ (C1' C ho) = Set.univ := by
  rw [(by rfl : C0' C ho = Subtype.val ⁻¹' (C0 C ho)),
    (by rfl : C1' C ho = Subtype.val ⁻¹' (C1 C ho)),
    (by simp only [← Subtype.coe_preimage_self] :
    (Set.univ : Set C) = Subtype.val ⁻¹' C)]
  simp only [← Set.preimage_union]
  rw [union_C0C1_eq]

def C' := C0 C ho ∩ (C1 C ho).proj (ord I · < o)

lemma isClosed_C' : IsClosed (C' C ho) :=
IsClosed.inter (isClosed_C0 _ hC _) (isClosed_res _ _ (isClosed_C1 _ hC _))

lemma contained_C' : contained (C' C ho) o := fun f hf i hi ↦ contained_C1 C ho f hf.2 i hi

def CC'₀ : C' C ho → C := fun g ↦ ⟨g.val,g.prop.1.1⟩

lemma continuous_CC'₀ : Continuous (CC'₀ C ho) :=
Continuous.subtype_mk continuous_subtype_val _

variable (o)

noncomputable
def SwapTrue : (I → Bool) → I → Bool :=
fun f i ↦ if ord I i = o then true else f i

lemma continuous_swapTrue  :
    Continuous (SwapTrue o : (I → Bool) → I → Bool) := by
  refine continuous_pi ?_
  intro i
  dsimp [SwapTrue]
  split_ifs
  · exact continuous_const
  · exact continuous_apply _

noncomputable
def SwapFalse : (I → Bool) → I → Bool :=
fun f i ↦ if ord I i = o then false else f i

lemma continuous_swapFalse :
    Continuous (SwapFalse o : (I → Bool) → I → Bool) := by
  refine continuous_pi ?_
  intro i
  dsimp [SwapFalse]
  split_ifs
  · exact continuous_const
  · exact continuous_apply _

variable {o}

lemma swapTrue_mem_C1 (f : (C1 C ho).proj (ord I · < o)) :
    SwapTrue o f.val ∈ C1 C ho := by
  obtain ⟨f,hf⟩ := f
  obtain ⟨g,hg⟩ := hf
  suffices : SwapTrue o f = g
  · rw [this]
    exact hg.1
  dsimp [SwapTrue]
  ext i
  split_ifs with h
  · dsimp [C1, term] at hg
    simp_rw [← h] at hg
    dsimp [ord] at hg
    simp only [Ordinal.enum_typein, Set.mem_inter_iff, Set.mem_setOf_eq] at hg
    exact hg.1.2.symm
  · dsimp [Proj] at hg
    have := congr_fun hg.2 i
    split_ifs at this with h'
    · exact this.symm
    · simp only [not_lt] at h'
      have hh := Order.succ_le_of_lt (lt_of_le_of_ne h' (Ne.symm h))
      specialize hsC g hg.1.1 i
      rw [← not_imp_not] at hsC
      simp only [not_lt, Bool.not_eq_true] at hsC
      rw [← this]
      exact (hsC hh).symm

lemma swapTrue_mem_C (f : C' C ho) : SwapTrue o f.val ∈ C := by
  suffices : SwapTrue o f.val ∈ C1 C ho
  · exact this.1
  exact (swapTrue_mem_C1 C hsC ho ⟨f.val,f.prop.2⟩)

noncomputable
def CC'₁ : C' C ho → C :=
fun g ↦ ⟨SwapTrue o g.val, swapTrue_mem_C C hsC ho g⟩

lemma continuous_CC'₁ : Continuous (CC'₁ C hsC ho) :=
Continuous.subtype_mk (Continuous.comp (continuous_swapTrue o) continuous_subtype_val) _

noncomputable
def Linear_CC'₀ : LocallyConstant C ℤ →ₗ[ℤ] LocallyConstant (C' C ho) ℤ :=
LocallyConstant.comapLinear ℤ (CC'₀ C ho) (continuous_CC'₀ C ho)

noncomputable
def Linear_CC'₁ : LocallyConstant C ℤ →ₗ[ℤ] LocallyConstant (C' C ho) ℤ :=
LocallyConstant.comapLinear ℤ (CC'₁ C hsC ho) (continuous_CC'₁ C hsC ho)

noncomputable
def Linear_CC' : LocallyConstant C ℤ →ₗ[ℤ] LocallyConstant (C' C ho) ℤ :=
Linear_CC'₁ C hsC ho - Linear_CC'₀ C ho

variable (o)

noncomputable
def Linear_ResC : LocallyConstant (C.proj (ord I · < o)) ℤ →ₗ[ℤ]
    LocallyConstant C ℤ :=
  LocallyConstant.comapLinear ℤ _ (continuous_resOnSubset C o)

def GoodProducts.v : GoodProducts (C.proj (ord I · < o)) →
    LocallyConstant (C.proj (ord I · < o)) ℤ :=
  eval (C.proj (ord I · < o))

def GoodProducts.v' : GoodProducts (C.proj (ord I · < o)) → LocallyConstant C ℤ :=
fun l ↦ l.1.eval C

def GoodProducts.w' : StartingWithMax C o → LocallyConstant C ℤ :=
fun l ↦ l.1.eval C

def GoodProducts.u : GoodProducts (C.proj (ord I · < o)) ⊕ StartingWithMax C o →
    LocallyConstant C ℤ :=
Sum.elim (v' C o) (w' C o)

lemma GoodProducts.injective_u : Function.Injective (u C o) := by
  have := injective C
  have hu := union_succ C o hsC
  have hr : GoodProducts (C.proj (ord I · < o)) ⊆ GoodProducts C
  · rw [hu]
    exact Set.subset_union_left _ _
  have hs : StartingWithMax C o ⊆ GoodProducts C
  · rw [hu]
    exact Set.subset_union_right _ _
  dsimp [eval] at this
  apply Function.Injective.sum_elim
  <;> dsimp [v', w']
  · intro a b h
    have hra : (⟨a.val, hr a.prop⟩ : GoodProducts C).val = a.val := by rfl
    have hrb : (⟨b.val, hr b.prop⟩ : GoodProducts C).val = b.val := by rfl
    dsimp at h
    rw [← hra, ← hrb] at h
    ext
    specialize this h
    apply_fun fun f ↦ f.val at this
    rwa [hra, hrb] at this
  · intro a b h
    have hsa : (⟨a.val, hs a.prop⟩ : GoodProducts C).val = a.val := by rfl
    have hsb : (⟨b.val, hs b.prop⟩ : GoodProducts C).val = b.val := by rfl
    dsimp at h
    rw [← hsa, ← hsb] at h
    ext
    specialize this h
    apply_fun fun f ↦ f.val at this
    rwa [hsa, hsb] at this
  · intro a b h
    have hra : (⟨a.val, hr a.prop⟩ : GoodProducts C).val = a.val := by rfl
    have hsb : (⟨b.val, hs b.prop⟩ : GoodProducts C).val = b.val := by rfl
    rw [← hra, ← hsb] at h
    specialize this h
    apply_fun fun f ↦ f.val at this
    rw [hra, hsb] at this
    by_cases hanil : a.val.val = []
    · apply b.prop.2.1
      rwa [← this]
    · have ha' := Products.head_lt_ord_of_isGood C a.prop hanil
      simp_rw [← b.prop.2.2] at ha'
      dsimp [ord] at ha'
      simp only [Ordinal.typein_lt_typein] at ha'
      apply ne_of_lt ha'
      rw [this]

lemma GoodProducts.huv : u C o ∘ Sum.inl = Linear_ResC C o ∘ v C o := by
  dsimp [u, v, v', Linear_ResC, LocallyConstant.comapLinear, eval]
  ext1 l
  rw [← Products.eval_comapFacC C l.prop]
  rfl

variable {o}

noncomputable
def GoodProducts.w : StartingWithMax C o → LocallyConstant (C' C ho) ℤ :=
Linear_CC' C hsC ho ∘ u C o ∘ Sum.inr

lemma swapTrue_swapFalse (x : I → Bool) (hx : x ∈ (C1 C ho).proj (ord I · < o)) :
    SwapFalse o (SwapTrue o x) = x := by
  ext i
  dsimp [SwapTrue, SwapFalse]
  split_ifs with h
  · obtain ⟨y, hy⟩ := hx
    rw [← hy.2]
    dsimp [Proj]
    split_ifs with h'
    · exfalso
      exact (ne_of_lt h') h
    · rfl
  · rfl

lemma CC_comp_zero : ∀ y, (Linear_CC' C hsC ho) ((Linear_ResC C o) y) = 0 := by
  intro y
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁]
  ext x
  rw [LocallyConstant.sub_apply]
  dsimp [Linear_ResC, LocallyConstant.comapLinear]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₀ _ _)]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_resOnSubset _ _)]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₁ _ _ _)]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_resOnSubset _ _)]
  suffices : ResOnSubset C o (CC'₁ C hsC ho x) = ResOnSubset C o (CC'₀ C ho x)
  · rw [this]
    simp only [sub_self]
  dsimp [CC'₀, CC'₁, ResOnSubset, ProjRestrict, Proj]
  ext i
  dsimp
  split_ifs with h
  · dsimp [SwapTrue]
    split_ifs with h'
    · exfalso
      exact (ne_of_lt h) h'
    · rfl
  · rfl

lemma C0_projOrd : ∀ x, x ∈ C0 C ho → Proj (ord I · < o) x = x := by
  intro x hx
  ext i
  simp only [Proj, Set.mem_setOf, ite_eq_left_iff, not_lt]
  intro hi
  rw [le_iff_lt_or_eq] at hi
  cases' hi with hi hi
  · specialize hsC x hx.1 i
    rw [← not_imp_not] at hsC
    simp only [not_lt, Bool.not_eq_true, Order.succ_le_iff] at hsC
    exact (hsC hi).symm
  · simp only [C0, Set.mem_inter_iff, Set.mem_setOf_eq, ← Bool.default_bool] at hx
    rw [← hx.2]
    congr 1
    dsimp [term]
    simp_rw [hi]
    simp only [ord, Ordinal.enum_typein]

lemma C1_projOrd : ∀ x, x ∈ C1 C ho → SwapTrue o (Proj (ord I · < o) x) = x := by
  intro x hx
  ext i
  dsimp [SwapTrue, Proj]
  split_ifs with hi h
  · rw [hx.2.symm]
    congr
    dsimp [term]
    simp_rw [← hi]
    simp only [ord, Ordinal.enum_typein]
  · rfl
  · simp only [not_lt] at h
    have h' : o < ord I i := lt_of_le_of_ne h (Ne.symm hi)
    specialize hsC x hx.1 i
    rw [← not_imp_not] at hsC
    simp only [not_lt, Bool.not_eq_true, Order.succ_le_iff] at hsC
    exact (hsC h').symm

lemma C0_eq_res : C0 C ho = (C0 C ho).proj (ord I · < o) := by
  ext y
  refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
  · exact ⟨y, ⟨hy, C0_projOrd C hsC ho y hy⟩⟩
  · obtain ⟨z, hz⟩ := hy
    rw [← hz.2]
    simp only [C0, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rw [C0_projOrd C hsC ho z hz.1]
      exact hz.1.1
    · simp only [Proj._eq_1, Bool.default_bool, ite_eq_right_iff]
      intro h
      simp only [ord, term, Ordinal.typein_enum, lt_self_iff_false] at h

lemma mem_res_of_mem_C0 : ∀ x, x ∈ C0 C ho → x ∈ C.proj (ord I · < o) := by
  intro x hx
  exact ⟨x, ⟨hx.1,C0_projOrd C hsC ho x hx⟩⟩

lemma mem_resC0_of_mem_C0 : ∀ x, x ∈ C0 C ho → x ∈ (C0 C ho).proj (ord I · < o) := by
  intro x hx
  rwa [← C0_eq_res C hsC ho]

lemma mem_C0_of_mem_resC0 : ∀ x, x ∈ (C0 C ho).proj (ord I · < o) → x ∈ C0 C ho := by
  intro x hx
  rwa [C0_eq_res C hsC ho]

noncomputable
def C0_homeo : C0 C ho ≃ₜ {i : C.proj (ord I · < o) | i.val ∈ (C0 C ho).proj (ord I · < o)} where
  toFun := fun x ↦ ⟨⟨x.val, mem_res_of_mem_C0 C hsC ho x.val x.prop⟩,
    mem_resC0_of_mem_C0 C hsC ho x.val x.prop⟩
  invFun := fun x ↦ ⟨x.val.val, mem_C0_of_mem_resC0 C hsC ho x.val.val x.prop⟩
  left_inv := by
    intro x
    dsimp
  right_inv := by
    intro x
    dsimp
    apply Subtype.ext
    apply Subtype.ext
    rfl
  continuous_toFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_induced_dom _) _
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.comp continuous_subtype_val continuous_subtype_val) _

lemma projOrd_eq_swapFalse : ∀ x, x ∈ C → Proj (ord I · < o) x = SwapFalse o x := by
  intro x hx
  ext i
  dsimp [Proj, SwapFalse]
  split_ifs with hi hi' hi'
  · exfalso
    exact (ne_of_lt hi) hi'
  · specialize hsC x hx i
    rw [← not_imp_not] at hsC
  · rfl
  · specialize hsC x hx i
    rw [← not_imp_not] at hsC
    simp only [not_lt, Bool.not_eq_true, Order.succ_le_iff] at hsC
    apply Eq.symm ∘ hsC
    simp only [not_lt] at hi
    exact lt_of_le_of_ne hi (Ne.symm hi')

lemma mem_res_of_mem_C1 : ∀ x, x ∈ C1 C ho → SwapFalse o x ∈ C.proj (ord I · < o) :=
  fun x hx ↦ ⟨x, ⟨hx.1, projOrd_eq_swapFalse C hsC x hx.1⟩⟩

lemma mem_resC1_of_mem_C1 : ∀ x, x ∈ C1 C ho → SwapFalse o x ∈ (C1 C ho).proj (ord I · < o) :=
  fun x hx ↦ ⟨x, ⟨hx, projOrd_eq_swapFalse C hsC x hx.1⟩⟩

lemma swapFalse_swapTrue (x : I → Bool) (hx : x ∈ C1 C ho) :
    SwapTrue o (SwapFalse o x) = x := by
  ext i
  dsimp [SwapTrue, SwapFalse]
  split_ifs with h
  · rw [← hx.2]
    congr
    dsimp [term]
    simp_rw [← h]
    simp only [ord, Ordinal.enum_typein]
  · rfl

lemma mem_C1_of_mem_resC1 : ∀ x, x ∈ (C1 C ho).proj (ord I · < o) → SwapTrue o x ∈ C1 C ho := by
  intro x hx
  obtain ⟨y, hy⟩ := hx
  rw [← hy.2, projOrd_eq_swapFalse C hsC y hy.1.1, swapFalse_swapTrue C ho y hy.1]
  exact hy.1

noncomputable
def C1_homeo : C1 C ho ≃ₜ {i : C.proj (ord I · < o) | i.val ∈ (C1 C ho).proj (ord I · < o)} where
  toFun := fun x ↦ ⟨⟨SwapFalse o x.val, mem_res_of_mem_C1 C hsC ho x.val x.prop⟩,
    mem_resC1_of_mem_C1 C hsC ho x.val x.prop⟩
  invFun := fun x ↦ ⟨SwapTrue o x.val.val, mem_C1_of_mem_resC1 C hsC ho x.val.val x.prop⟩
  left_inv := by
    intro x
    simp_rw [swapFalse_swapTrue C ho x.val x.prop]
  right_inv := by
    intro x
    dsimp
    simp_rw [swapTrue_swapFalse C ho x.val x.prop]
    apply Subtype.ext
    apply Subtype.ext
    rfl
  continuous_toFun :=
    Continuous.subtype_mk (Continuous.subtype_mk (Continuous.comp (continuous_swapFalse o)
    continuous_subtype_val) _) _
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.comp (continuous_swapTrue o)
    (Continuous.comp continuous_subtype_val continuous_subtype_val)) _

open Classical in
lemma CC_exact {f : LocallyConstant C ℤ} (hf : Linear_CC' C hsC ho f = 0) :
    ∃ y, Linear_ResC C o y = f := by
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁] at hf
  rw [sub_eq_zero] at hf
  dsimp [LocallyConstant.comapLinear] at hf
  rw [← LocallyConstant.coe_inj] at hf
  rw [LocallyConstant.coe_comap _ _ (continuous_CC'₁ _ _ _)] at hf
  rw [LocallyConstant.coe_comap _ _ (continuous_CC'₀ _ _)] at hf
  have hC₀' : IsClosed ((C0 C ho).proj (ord I · < o)) := isClosed_res _ _ (isClosed_C0 C hC ho)
  have hC₁' : IsClosed ((C1 C ho).proj (ord I · < o)) := isClosed_res _ _ (isClosed_C1 C hC ho)
  have hC₀ : IsClosed {i : C.proj (ord I · < o) | i.val ∈ (C0 C ho).proj (ord I · < o)}
  · rw [isClosed_induced_iff]
    exact ⟨(C0 C ho).proj (ord I · < o), ⟨hC₀', rfl⟩⟩
  have hC₁ : IsClosed {i : C.proj (ord I · < o) | i.val ∈ (C1 C ho).proj (ord I · < o)}
  · rw [isClosed_induced_iff]
    exact ⟨(C1 C ho).proj (ord I · < o), ⟨hC₁', rfl⟩⟩
  let e₀ : C0 C ho ≃ₜ {i : C.proj (ord I · < o) | i.val ∈ (C0 C ho).proj (ord I · < o)} :=
    C0_homeo C hsC ho
  let E₀ : LocallyConstant (C0 C ho) ℤ ≃ LocallyConstant _ ℤ := LocallyConstant.equiv e₀
  let e₁ : C1 C ho ≃ₜ {i : C.proj (ord I · < o) | i.val ∈ (C1 C ho).proj (ord I · < o)} :=
    C1_homeo C hsC ho
  let E₁ : LocallyConstant (C1 C ho) ℤ ≃ LocallyConstant _ ℤ := LocallyConstant.equiv e₁
  let C₀C : C0 C ho → C := fun x ↦ ⟨x.val, x.prop.1⟩
  have h₀ : Continuous C₀C := Continuous.subtype_mk continuous_induced_dom _
  let C₁C : C1 C ho → C := fun x ↦ ⟨x.val, x.prop.1⟩
  have h₁ : Continuous C₁C := Continuous.subtype_mk continuous_induced_dom _
  refine ⟨LocallyConstant.piecewise hC₀ hC₁ ?_ (E₀ (f.comap C₀C)) (E₁ (f.comap C₁C)) ?_, ?_⟩
  · ext ⟨x, hx⟩
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    obtain ⟨y, ⟨hyC, hy⟩⟩ := hx
    by_cases hyt : y (term I ho) = true
    · right
      rw [← hy]
      refine ⟨y, ⟨⟨hyC, hyt⟩, rfl⟩⟩
    · left
      simp only [Bool.not_eq_true] at hyt
      rw [← hy]
      refine ⟨y, ⟨⟨hyC, hyt⟩, rfl⟩⟩
  · rintro ⟨x, hrx⟩ hx
    have hx' : x ∈ C' C ho
    · refine ⟨?_, hx.2⟩
      rw [C0_eq_res C hsC ho]
      exact hx.1
    dsimp [LocallyConstant.equiv]
    rw [LocallyConstant.coe_comap_apply _ _ (Homeomorph.continuous _)]
    rw [LocallyConstant.coe_comap_apply _ _ h₀]
    rw [LocallyConstant.coe_comap_apply _ _ (Homeomorph.continuous _)]
    rw [LocallyConstant.coe_comap_apply _ _ h₁]
    exact (congrFun hf ⟨x, hx'⟩).symm
  · dsimp [Linear_ResC, LocallyConstant.comapLinear]
    ext ⟨x,hx⟩
    rw [← union_C0C1_eq C ho] at hx
    cases' hx with hx₀ hx₁
    · rw [LocallyConstant.coe_comap_apply _ _ (continuous_resOnSubset _ _)]
      dsimp [LocallyConstant.piecewise]
      split_ifs with h
      · dsimp [LocallyConstant.equiv]
        rw [LocallyConstant.coe_comap_apply _ _ (Homeomorph.continuous _)]
        rw [LocallyConstant.coe_comap_apply _ _ h₀]
        congr 1
        ext i
        dsimp [ResOnSubset, ProjRestrict] at h ⊢
        dsimp [C0_homeo]
        rw [C0_projOrd C hsC ho x hx₀]
      · dsimp [LocallyConstant.equiv]
        exfalso
        apply h
        exact ⟨x, ⟨hx₀, rfl⟩⟩
    · rw [LocallyConstant.coe_comap_apply _ _ (continuous_resOnSubset _ _)]
      dsimp [LocallyConstant.piecewise]
      split_ifs with h
      · dsimp [LocallyConstant.equiv]
        rw [LocallyConstant.coe_comap_apply _ _ (Homeomorph.continuous _)]
        rw [LocallyConstant.coe_comap_apply _ _ h₀]
        dsimp [C0_homeo]
        have hx' : Proj (ord I · < o) x ∈ C' C ho
        · refine ⟨?_, ⟨x, ⟨hx₁, rfl⟩⟩⟩
          rwa [C0_eq_res C hsC ho]
        have := congrFun hf ⟨Proj (ord I · < o) x, hx'⟩
        dsimp [ResOnSubset]
        dsimp [CC'₁] at this
        simp_rw [C1_projOrd C hsC ho x hx₁] at this
        exact this.symm
      · dsimp [LocallyConstant.equiv]
        rw [LocallyConstant.coe_comap_apply _ _ (Homeomorph.continuous _)]
        rw [LocallyConstant.coe_comap_apply _ _ h₁]
        congr 1
        ext i
        dsimp [ResOnSubset, ProjRestrict] at h ⊢
        dsimp [C1_homeo]
        rw [C1_projOrd C hsC ho x hx₁]

noncomputable
def C1_homeo' : C1' C ho ≃ₜ {i : C.proj (ord I · < o) | i.val ∈ (C1 C ho).proj (ord I · < o)} where
  toFun := fun x ↦ ⟨⟨SwapFalse o x.val, mem_res_of_mem_C1 C hsC ho x.val x.prop⟩,
    mem_resC1_of_mem_C1 C hsC ho x.val x.prop⟩
  invFun := fun x ↦ ⟨⟨SwapTrue o x.val.val,
    (swapTrue_mem_C1 C hsC ho ⟨x.val, x.prop⟩).1⟩, mem_C1_of_mem_resC1 C hsC ho x.val.val x.prop⟩
  left_inv := by
    intro x
    simp_rw [swapFalse_swapTrue C ho x.val x.prop]
  right_inv := by
    intro x
    dsimp
    simp_rw [swapTrue_swapFalse C ho x.val x.prop]
    apply Subtype.ext
    apply Subtype.ext
    rfl
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    refine Continuous.comp (continuous_swapFalse o) ?_
    exact Continuous.comp continuous_subtype_val continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact Continuous.comp (continuous_swapTrue o) (Continuous.comp continuous_subtype_val
      continuous_subtype_val)

variable (o) in
lemma succ_mono : CategoryTheory.Mono (ModuleCat.ofHom (Linear_ResC C o)) := by
  rw [ModuleCat.mono_iff_injective]
  exact LocallyConstant.comap_injective (ResOnSubset C o)
    (continuous_resOnSubset C o) (surjective_resOnSubset C o)

lemma succ_exact : CategoryTheory.Exact
    (ModuleCat.ofHom (Linear_ResC C o))
    (ModuleCat.ofHom (Linear_CC' C hsC ho)) := by
  rw [ModuleCat.exact_iff]
  ext f
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · obtain ⟨y,hy⟩ := hf
    rw [← hy]
    dsimp [ModuleCat.ofHom]
    exact CC_comp_zero _ _ _ y
  · exact CC_exact _ hC _ ho hf

lemma swapTrue_eq_true : ∀ x, SwapTrue o x (term I ho) = true := by
  intro x
  dsimp [SwapTrue]
  split_ifs with h
  · rfl
  · dsimp [ord, term] at h
    simp only [Ordinal.typein_enum, not_true] at h

lemma mem_C'_eq_false : ∀ x, x ∈ C' C ho → x (term I ho) = false := by
  rintro x ⟨_,⟨y,⟨_,hy⟩⟩⟩
  rw [← hy]
  dsimp [Proj]
  split_ifs with h
  · dsimp [ord, term] at h
    simp only [Ordinal.typein_enum, lt_self_iff_false] at h
  · rfl

def Products.Tail (l : Products I) : Products I :=
⟨l.val.tail, List.Chain'.tail l.prop⟩

def GoodProducts.MaxTail (l : StartingWithMax C o) : Products I :=
l.val.Tail

lemma Products.max_eq_o_cons_tail (l : Products I) (hl : l.val ≠ [])
    (hlh : l.val.head! = term I ho) : l.val = term I ho :: l.Tail.val := by
  rw [← List.cons_head!_tail hl, hlh]
  rfl

lemma GoodProducts.max_eq_o_cons_tail (l : StartingWithMax C o) :
    l.val.val = (term I ho) :: (MaxTail C l).val := by
  rw [← List.cons_head!_tail l.prop.2.1]
  dsimp [MaxTail]
  congr
  dsimp [term]
  simp_rw [← l.prop.2.2]
  dsimp [ord]
  simp only [Ordinal.enum_typein]

lemma Products.evalCons {l : List I} {a : I}
    (hla : (a::l).Chain' (·>·)) : Products.eval C ⟨a::l,hla⟩ =
    (e C a) * Products.eval C ⟨l,List.Chain'.sublist hla (List.tail_sublist (a::l))⟩ := by
  dsimp [eval]
  simp only [List.prod_cons]

lemma Products.max_eq_eval (l : Products I) (hl : l.val ≠ [])
    (hlh : l.val.head! = term I ho) :
    Linear_CC' C hsC ho (l.eval C) = l.Tail.eval (C' C ho) := by
  have hl' : l.val = (term I ho) :: l.Tail.val := max_eq_o_cons_tail ho l hl hlh
  have hlc : ((term I ho) :: l.Tail.val).Chain' (·>·)
  · rw [← hl']
    exact l.prop
  have hl : l = ⟨(term I ho) :: l.Tail.val, hlc⟩
  · simp_rw [← hl']
    rfl
  rw [hl, Products.evalCons]
  ext x
  dsimp [Linear_CC', Linear_CC'₁, Linear_CC'₀, LocallyConstant.comapLinear]
  rw [LocallyConstant.sub_apply]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₀ _ _)]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₁ _ _ _)]
  dsimp [CC'₀, CC'₁]
  rw [Products.eval_eq]
  rw [Products.eval_eq]
  rw [Products.eval_eq]
  simp only [mul_ite, mul_one, mul_zero]
  have hi' : ∀ i, i ∈ l.Tail.val → (x.val i = SwapTrue o x.val i)
  · intro i hi
    dsimp [SwapTrue]
    split_ifs with h₁
    · exfalso
      suffices : i < term I ho
      · dsimp [term] at this
        simp_rw [← h₁] at this
        dsimp [ord] at this
        simp only [Ordinal.enum_typein, lt_self_iff_false] at this
      rw [← gt_iff_lt]
      apply List.Chain.rel _ hi
      exact hlc
    · rfl
  split_ifs with h₁ h₂ h₂ h₃ h₄ h₅ h₆
  <;> dsimp [e, Int.ofBool]
  · split_ifs with hh₁ hh₂
    · exfalso
      rwa [mem_C'_eq_false C ho x x.prop, Bool.coe_false] at hh₂
    · rfl
    · exfalso
      exact hh₁ (swapTrue_eq_true _ _)
    · exfalso
      exact hh₁ (swapTrue_eq_true _ _)
  · push_neg at h₂
    obtain ⟨i, hi⟩ := h₂
    specialize h₁ i hi.1
    specialize hi' i hi.1
    exfalso
    apply hi.2
    rwa [hi']
  · push_neg at h₂
    obtain ⟨i, hi⟩ := h₂
    specialize h₁ i hi.1
    specialize hi' i hi.1
    exfalso
    apply hi.2
    rwa [hi']
  · push_neg at h₂
    obtain ⟨i, hi⟩ := h₂
    specialize h₁ i hi.1
    specialize hi' i hi.1
    exfalso
    apply hi.2
    rwa [hi']
  · push_neg at h₁
    obtain ⟨i, hi⟩ := h₁
    specialize h₄ i hi.1
    specialize hi' i hi.1
    exfalso
    apply hi.2
    rwa [← hi']
  · push_neg at h₁
    obtain ⟨i, hi⟩ := h₁
    specialize h₄ i hi.1
    specialize hi' i hi.1
    exfalso
    apply hi.2
    rwa [← hi']
  · push_neg at h₁
    obtain ⟨i, hi⟩ := h₁
    specialize h₆ i hi.1
    specialize hi' i hi.1
    exfalso
    apply hi.2
    rwa [← hi']
  · rfl

lemma GoodProducts.max_eq_eval (l : StartingWithMax C o) :
    Linear_CC' C hsC ho (l.val.eval C) = (MaxTail C l).eval (C' C ho) := by
  have hl' : l.val.val = (term I ho) :: (MaxTail C l).val := max_eq_o_cons_tail C ho l
  have hlc : ((term I ho) :: (MaxTail C l).val).Chain' (·>·)
  · rw [← hl']
    exact l.val.prop
  have hl : l.val = ⟨(term I ho) :: (MaxTail C l).val, hlc⟩
  · simp_rw [← hl']
    rfl
  rw [hl, Products.evalCons]
  ext x
  dsimp [Linear_CC', Linear_CC'₁, Linear_CC'₀, LocallyConstant.comapLinear]
  rw [LocallyConstant.sub_apply]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₀ _ _)]
  rw [LocallyConstant.coe_comap_apply _ _ (continuous_CC'₁ _ _ _)]
  dsimp [CC'₀, CC'₁]
  rw [Products.eval_eq]
  rw [Products.eval_eq]
  rw [Products.eval_eq]
  simp only [mul_ite, mul_one, mul_zero]
  have hi' : ∀ i, i ∈ (MaxTail C l).val → (x.val i = SwapTrue o x.val i)
  · intro i hi
    dsimp [SwapTrue]
    split_ifs with h₁
    · exfalso
      suffices : i < term I ho
      · dsimp [term] at this
        simp_rw [← h₁] at this
        dsimp [ord] at this
        simp only [Ordinal.enum_typein, lt_self_iff_false] at this
      rw [← gt_iff_lt]
      apply List.Chain.rel _ hi
      exact hlc
    · rfl
  split_ifs with h₁ h₂ h₂
  <;> dsimp [e, Int.ofBool]
  · split_ifs with hh₁ hh₂
    · exfalso
      rwa [mem_C'_eq_false C ho x x.prop, Bool.coe_false] at hh₂
    · rfl
    · exfalso
      exact hh₁ (swapTrue_eq_true _ _)
    · exfalso
      exact hh₁ (swapTrue_eq_true _ _)
  · push_neg at h₂
    obtain ⟨i, hi⟩ := h₂
    specialize h₁ i hi.1
    specialize hi' i hi.1
    exfalso
    apply hi.2
    rwa [hi']
  · push_neg at h₁
    obtain ⟨i, hi⟩ := h₁
    specialize h₂ i hi.1
    specialize hi' i hi.1
    exfalso
    apply hi.2
    rwa [← hi']
  · rfl

lemma GoodProducts.max_eq_eval_unapply :
    (Linear_CC' C hsC ho) ∘ (fun (l : StartingWithMax C o) ↦ Products.eval C l.val) =
    (fun l ↦ (MaxTail C l).eval (C' C ho)) := by
  ext1 l
  exact max_eq_eval _ _ _ _

lemma Products.head_lt_ord_of_isGood' {l : Products I}
    (h : l.isGood (C' C ho)) : l.val ≠ [] → ord I (l.val.head!) < o := by
  intro hn
  by_contra h'
  apply h
  obtain ⟨l,hl⟩ := l
  dsimp at hn
  have hl' : List.Chain' (·>·) (l.head! :: l.tail)
  · rw [List.cons_head!_tail hn]
    exact hl
  have : (⟨l,hl⟩ : Products I) = ⟨l.head! :: l.tail, hl'⟩
  · simp_rw [List.cons_head!_tail hn]
  rw [this, evalCons (C' C ho) hl']
  have eZero : e (C' C ho) (List.head! l) = 0
  · dsimp [e]
    ext ⟨f,hf⟩
    dsimp [Int.ofBool]
    dsimp [C', Proj, Set.proj] at hf
    obtain ⟨g, hg⟩ := hf.2
    rw [← hg.2]
    split_ifs
    · exfalso
      assumption
    · rfl
    · exfalso
      assumption
    · rfl
  rw [eZero]
  simp only [zero_mul, Submodule.zero_mem]

lemma GoodProducts.cons_o_chain' (l : GoodProducts (C' C ho)) :
    (term I ho :: l.val.val).Chain' (·>·) := by
  by_cases hl : l.val.val = []
  · rw [hl]
    simp only [List.chain'_singleton]
  · rw [List.chain'_cons']
    refine ⟨?_, l.val.prop⟩
    intro y hy
    have hy' := List.eq_cons_of_mem_head? hy
    have h := Products.head_lt_ord_of_isGood' C ho l.prop hl
    rw [hy'] at h
    dsimp [term]
    rw [← List.head!_cons y (List.tail l.val.val)]
    simp only [gt_iff_lt]
    rw [← Ordinal.typein_lt_typein (·<·)]
    dsimp [ord] at h
    simpa only [List.head!_cons, Ordinal.typein_enum]

lemma GoodProducts.maxTail_isGood (l : StartingWithMax C o)
    (h₁: ⊤ ≤ Submodule.span ℤ (Set.range (eval (C.proj (ord I · < o))))) :
    (MaxTail C l).isGood (C' C ho) := by
  intro h
  rw [Finsupp.mem_span_image_iff_total, ← max_eq_eval C hsC ho] at h
  obtain ⟨m, ⟨hmmem, hmsum⟩⟩ := h
  rw [Finsupp.total_apply] at hmsum
  have : (Linear_CC' C hsC ho) (l.val.eval C) = (Linear_CC' C hsC ho)
    (Finsupp.sum m fun i a ↦ a • ((term I ho :: i.1).map (e C)).prod)
  · rw [← hmsum]
    simp only [LinearMap.map_finsupp_sum]
    apply Finsupp.sum_congr
    intro q hq
    rw [LinearMap.map_smul]
    rw [Finsupp.mem_supported] at hmmem
    have hx'' : q < MaxTail C l := hmmem hq
    have : ∃ (p : Products I), p.val ≠ [] ∧ p.val.head! = term I ho ∧ q = p.Tail
    · refine ⟨⟨term I ho :: q.val, ?_⟩, ⟨?_, ?_, ?_⟩⟩
      · rw [List.chain'_cons']
        refine ⟨?_, q.prop⟩
        cases' q with x' x'prop
        induction x' with
        | nil =>
          · intro y hy
            simp only [List.head?_nil, Option.mem_def] at hy
        | cons a as _ =>
          · intro y hy
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
            rw [← hy]
            by_cases hM : (MaxTail C l).val = []
            · have : a :: as < []
              · rw [← hM]
                exact hx''
              exfalso
              exact List.Lex.not_nil_right _ _ this
            · obtain ⟨b, L, hbL⟩ := List.exists_cons_of_ne_nil hM
              have : a :: as < b :: L
              · rw [← hbL]
                exact hx''
              have hab : a ≤ b
              · by_contra hab
                simp only [not_le] at hab
                have habs : b :: L < a :: as := List.Lex.rel hab
                simp only [← not_le] at habs
                exact habs (le_of_lt this)
              refine lt_of_le_of_lt hab ?_
              have hll : l.val.val = term I ho :: b :: L
              · rw [max_eq_o_cons_tail C ho l, hbL]
              have hlp := l.val.prop
              rw [hll, List.chain'_cons] at hlp
              exact hlp.1
      · exact List.cons_ne_nil _ _
      · simp only [List.head!_cons]
      · simp only [Products.Tail, List.tail_cons, Subtype.coe_eta]
    obtain ⟨p, hp⟩ := this
    rw [hp.2.2, ← Products.max_eq_eval C hsC ho p hp.1 hp.2.1]
    dsimp [Products.eval]
    rw [Products.max_eq_o_cons_tail ho p hp.1 hp.2.1]
    rfl
  have hse := succ_exact C hC hsC ho
  rw [ModuleCat.exact_iff] at hse
  dsimp [ModuleCat.ofHom] at hse
  rw [← LinearMap.sub_mem_ker_iff, ← hse] at this
  obtain ⟨(n : LocallyConstant (C.proj (ord I · < o)) ℤ), hn⟩ := this
  rw [eq_sub_iff_add_eq] at hn
  have hn' := h₁ (Submodule.mem_top : n ∈ ⊤)
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hn'
  obtain ⟨w,hc⟩ := hn'
  rw [← hc, map_finsupp_sum] at hn
  apply l.prop.1
  rw [← hn]
  apply Submodule.add_mem
  · rw [Finsupp.mem_span_image_iff_total]
    let f : GoodProducts (C.proj (ord I · < o)) → Products I := fun l ↦ l.val
    have hfi : f.Injective := fun _ _ h ↦ Subtype.ext h
    let v : Products I →₀ ℤ := w.mapDomain f
    refine ⟨v, ⟨?_, ?_⟩⟩
    · rw [Finsupp.mem_supported, Finsupp.mapDomain_support_of_injective hfi]
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finsupp.mem_support_iff,
        ne_eq, Subtype.exists, exists_and_right, exists_eq_right] at hx
      simp only [Set.mem_setOf_eq]
      obtain ⟨hx, hx'⟩ := hx
      by_cases hxnil : x.val = []
      · cases' x with x _
        suffices : [] < l.val.val
        · rw [← hxnil] at this
          exact this
        rw [max_eq_o_cons_tail C ho l]
        exact List.Lex.nil
      · have := Products.head_lt_ord_of_isGood C hx hxnil
        suffices : x.val < l.val.val
        · exact this
        rw [max_eq_o_cons_tail C ho l, ← List.cons_head!_tail hxnil]
        apply List.Lex.rel
        have hto : ord I (term I ho) = o
        · simp only [ord, term, Ordinal.typein_enum]
        rw [← hto] at this
        simp only [ord, Ordinal.typein_lt_typein] at this
        exact this
    · rw [Finsupp.total_apply, Finsupp.sum_mapDomain_index_inj hfi]
      congr
      ext q r x
      rw [LinearMap.map_smul]
      dsimp [Linear_ResC, LocallyConstant.comapLinear]
      rw [← Products.eval_comapFacC C q.prop]
      rfl
  · rw [Finsupp.mem_span_image_iff_total]
    let f : Products I → List I := fun q ↦ term I ho :: q.val
    have hfi : Function.Injective f
    · intro a b hab
      exact Subtype.ext (List.tail_eq_of_cons_eq hab)
    let m' : List I →₀ ℤ := m.mapDomain f
    let g : Products I → List I := fun q ↦ q.val
    have hg : Function.Injective g
    · intro a b hab
      exact Subtype.ext hab
    let c : Products I →₀ ℤ := m'.comapDomain g (hg.injOn _)
    refine ⟨c,⟨?_, ?_⟩⟩
    · rw [Finsupp.mem_supported] at hmmem ⊢
      simp only [Finsupp.comapDomain_support, Finset.coe_preimage]
      have hm' : m'.support ⊆ Finset.image _ m.support := Finsupp.mapDomain_support
      refine subset_trans (Set.preimage_mono hm') ?_
      simp only [Finset.image_val, Multiset.mem_dedup, Multiset.mem_map, Finset.mem_val]
      intro q hq
      simp only [Set.mem_preimage] at hq
      obtain ⟨a, ha⟩ := hq
      have ha' : a < MaxTail C l := hmmem ha.1
      simp only [Set.mem_setOf_eq, gt_iff_lt]
      suffices hql : q.val < l.val.val
      · exact hql
      rw [← ha.2, max_eq_o_cons_tail C ho]
      exact List.Lex.cons ha'
    · rw [Finsupp.total_apply]
      dsimp
      have hf : Set.BijOn g (g ⁻¹' m'.support) m'.support
      · refine ⟨?_, ?_, ?_⟩
        · intro x hx
          exact hx
        · exact Function.Injective.injOn hg _
        · intro x hx
          rw [Finsupp.mapDomain_support_of_injOn m (Function.Injective.injOn hfi _)] at hx ⊢
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
          obtain ⟨x', hx'⟩ := hx
          rw [Finsupp.mem_supported] at hmmem
          have hx'' : x' < MaxTail C l := hmmem hx'.1
          refine ⟨⟨x, ?_⟩,⟨?_, ?_⟩⟩
          · rw [← hx'.2, List.chain'_cons']
            refine ⟨?_, x'.prop⟩
            cases' x' with x' x'prop
            induction x' with
            | nil =>
              · intro y hy
                simp only [List.head?_nil, Option.mem_def] at hy
            | cons a as _ =>
              · intro y hy
                simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
                rw [← hy]
                by_cases hM : (MaxTail C l).val = []
                · have : a :: as < []
                  · rw [← hM]
                    exact hx''
                  exfalso
                  exact List.Lex.not_nil_right _ _ this
                · obtain ⟨b, L, hbL⟩ := List.exists_cons_of_ne_nil hM
                  have : a :: as < b :: L
                  · rw [← hbL]
                    exact hx''
                  have hab : a ≤ b
                  · by_contra hab
                    simp only [not_le] at hab
                    have habs : b :: L < a :: as := List.Lex.rel hab
                    simp only [← not_le] at habs
                    exact habs (le_of_lt this)
                  refine lt_of_le_of_lt hab ?_
                  have hll : l.val.val = term I ho :: b :: L
                  · rw [max_eq_o_cons_tail C ho l, hbL]
                  have hlp := l.val.prop
                  rw [hll, List.chain'_cons] at hlp
                  exact hlp.1
          · simp only [Finset.coe_image, Set.mem_preimage, Set.mem_image, Finset.mem_coe]
            refine ⟨x', hx'⟩
          · rfl
      let g' := fun (i : List I) (a : ℤ) ↦ a • (i.map (e C)).prod
      have hf' : (fun (i : Products I) (a : ℤ) ↦ a • i.eval C) = g' ∘ g := by rfl
      rw [hf']
      rw [Finsupp.sum_comapDomain g m' _ hf]
      dsimp
      rw [Finsupp.sum_mapDomain_index_inj hfi]
      rfl

noncomputable
def GoodProducts.StartingWithMaxFunToGood
    (h₁: ⊤ ≤ Submodule.span ℤ (Set.range (eval (C.proj (ord I · < o))))) :
    StartingWithMax C o → GoodProducts (C' C ho) :=
  fun l ↦ ⟨MaxTail C l, maxTail_isGood C hC hsC ho l h₁⟩

lemma GoodProducts.StartingWithMaxFunToGoodInj
    (h₁: ⊤ ≤ Submodule.span ℤ (Set.range (eval (C.proj (ord I · < o))))) :
    (StartingWithMaxFunToGood C hC hsC ho h₁).Injective := by
  intro m n h
  apply Subtype.ext ∘ Subtype.ext
  rw [Subtype.ext_iff] at h
  dsimp [StartingWithMaxFunToGood] at h
  rw [max_eq_o_cons_tail C ho m, max_eq_o_cons_tail C ho n, h]

lemma GoodProducts.hhw (h₁: ⊤ ≤ Submodule.span ℤ (Set.range (eval (C.proj (ord I · < o))))) :
    LinearIndependent ℤ (eval (C' C ho)) → LinearIndependent ℤ (w C hsC ho) := by
  dsimp [w, u, w']
  rw [max_eq_eval_unapply C hsC ho]
  intro h
  let f := StartingWithMaxFunToGood C hC hsC ho h₁
  have hf : f.Injective := StartingWithMaxFunToGoodInj C hC hsC ho h₁
  have hh : (fun l ↦ Products.eval (C' C ho) (MaxTail C l)) = eval (C' C ho) ∘ f := rfl
  rw [hh]
  exact h.comp f hf

end Successor

section Induction

variable (I) in
def P (o : Ordinal) : Prop :=
  o ≤ Ordinal.type (·<· : I → I → Prop) →
  (∀ (C : Set (I → Bool)), IsClosed C → contained C o →
    LinearIndependent ℤ (GoodProducts.eval C))

lemma GoodProducts.P0 : P I 0 := by
  dsimp [P]
  intro _ C _ hsC
  have : C ⊆ {(fun _ ↦ false)}
  · intro c hc
    simp
    ext x
    simp at hsC
    specialize hsC c hc x
    rw [Bool.eq_false_iff]
    intro ht
    apply Ordinal.not_lt_zero (ord I x)
    exact hsC ht
  rw [Set.subset_singleton_iff_eq] at this
  rcases this
  · subst C
    exact linearIndependentEmpty
  · subst C
    exact linearIndependentSingleton

lemma GoodProducts.Plimit :
    ∀ (o : Ordinal), Ordinal.IsLimit o → (∀ (o' : Ordinal), o' < o → P I o') → P I o := by
  intro o ho h
  dsimp [P] at *
  intro hho
  intro C hC hsC
  rw [linearIndependent_iff_union_smaller C ho hsC]
  refine linearIndependent_iUnion_of_directed (DirectedS C o) ?_
  rintro ⟨o', ho'⟩
  have hho' : o' < Ordinal.type (·<· : I → I → Prop) :=
    lt_of_lt_of_le ho' hho
  specialize h o' ho' (le_of_lt hho')
  have h' := h (C.proj (ord I · < o')) (isClosed_res _ _ hC) (contained_res _ _)
  rw [linearIndependent_iff_smaller] at h'
  exact h'

lemma GoodProducts.linearIndependentAux (μ : Ordinal) : P I μ := by
  refine Ordinal.limitRecOn μ P0 ?_
      (fun o ho h ↦ (GoodProducts.Plimit o ho (fun o' ho' ↦ (h o' ho'))))
  intro o h
  dsimp [P] at *
  intro ho C hC hsC
  have ho' : o < Ordinal.type (·<· : I → I → Prop) :=
    lt_of_lt_of_le (Order.lt_succ _) ho
  rw [linearIndependent_iff_sum C o hsC]
  refine ModuleCat.linearIndependent_leftExact ?_ ?_ (injective_u C o hsC)
      (succ_mono C o) (succ_exact C hC hsC ho')
      (huv C o)
  · exact h (le_of_lt ho') (C.proj (ord I · < o)) (isClosed_res C o hC) (contained_res C o)
  · exact hhw C hC hsC ho' (span (C.proj (ord I · < o)) (isClosed_res C o hC))
      (h (le_of_lt ho') (C' C ho') (isClosed_C' C hC ho') (contained_C' C ho'))

lemma GoodProducts.linearIndependent (hC : IsClosed C) :
    LinearIndependent ℤ (GoodProducts.eval C) :=
  GoodProducts.linearIndependentAux (Ordinal.type (·<· : I → I → Prop)) (le_refl _)
    C hC (fun _ _ _ _ ↦ Ordinal.typein_lt_type _ _)

noncomputable
def GoodProducts.Basis (hC : IsClosed C) :
    Basis (GoodProducts C) ℤ (LocallyConstant C ℤ) :=
Basis.mk (GoodProducts.linearIndependent C hC) (GoodProducts.span C hC)

end Induction

variable {S : Profinite} {ι : S → I → Bool} (hι : ClosedEmbedding ι)

lemma Nobeling : Module.Free ℤ (LocallyConstant S ℤ) := Module.Free.of_equiv'
  (Module.Free.of_basis <| GoodProducts.Basis _ hι.closed_range) (LocallyConstant.equivLinear
  (Homeomorph.ofEmbedding ι hι.toEmbedding)).symm

end NobelingProof

variable (S : Profinite.{u})

open Classical in
noncomputable
def Nobeling.ι : S → ({C : Set S // IsClopen C} → Bool) := fun s C => decide (s ∈ C.1)

instance totally_separated_of_totally_disconnected_compact_hausdorff (α : Type _)
    [TopologicalSpace α] [CompactSpace α] [TotallyDisconnectedSpace α] [T2Space α] :
    TotallySeparatedSpace α := by
  rwa [← compact_t2_tot_disc_iff_tot_sep]

open Classical in
lemma Nobeling.embedding : ClosedEmbedding (Nobeling.ι S) := by
  apply Continuous.closedEmbedding
  · dsimp [ι]
    refine continuous_pi ?_
    intro C
    rw [← IsLocallyConstant.iff_continuous]
    refine ((IsLocallyConstant.tfae _).out 0 3).mpr ?_
    rintro ⟨⟩
    · have : (fun a ↦ decide (a ∈ C.1)) ⁻¹' {false} = C.1ᶜ
      · ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff,
          decide_eq_false_iff_not, Set.mem_compl_iff]
      · rw [this]
        refine IsClopen.isOpen ?_
        simp only [isClopen_compl_iff]
        exact C.2
    · have : (fun a ↦ decide (a ∈ C.1)) ⁻¹' {true} = C.1
      · ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq]
      · rw [this]
        refine IsClopen.isOpen ?_
        exact C.2
  · intro a b hab
    by_contra hnab
    have h' := exists_clopen_of_totally_separated hnab
    obtain ⟨C, hC, h₁⟩ := h'
    apply h₁.2
    have ha : ι S a ⟨C, hC⟩ = decide (a ∈ C) := rfl
    have hb : ι S b ⟨C, hC⟩ = decide (b ∈ C) := rfl
    apply of_decide_eq_true
    rw [← hb, ← hab, ha]
    apply decide_eq_true
    exact h₁.1

instance : Inhabited {C : Set S // IsClopen C} where
  default := ⟨∅, isClopen_empty⟩

theorem Nobeling : Module.Free ℤ (LocallyConstant S ℤ) :=
@NobelingProof.Nobeling {C : Set S // IsClopen C} _ (IsWellOrder.linearOrder WellOrderingRel)
  WellOrderingRel.isWellOrder S (Nobeling.ι S) (Nobeling.embedding S)
