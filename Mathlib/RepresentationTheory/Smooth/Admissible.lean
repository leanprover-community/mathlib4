/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.RepresentationTheory.HeckeModule
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Smooth.Res

/-!
# Induction

This file introduces admissible representations over a field and prove basic properties.
We also prove **Schur's Lemma** for irreducible admissible smooth representations over an
algeraically closed field.

## Main definitions


## Implementation notes

-/

@[expose] public section

variable {G : Type*} [Group G]
variable {k : Type*} [Field k]
variable {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
variable {W : Type*} [AddCommGroup W] [Module k W] (σ : Representation k G W)

namespace Representation

lemma finiteDimensional_invariants_of_le_subgroup {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂)
    [FiniteDimensional k (invariants (ρ.comp H₁.subtype))] :
    FiniteDimensional k (invariants (ρ.comp H₂.subtype)) := by
  let f : invariants (ρ.comp H₂.subtype) →ₗ[k] invariants (ρ.comp H₁.subtype) :=
    { toFun v := ⟨v.val, fun ⟨g, hg⟩ => by simp only [MonoidHom.coe_comp,
      Subgroup.coe_subtype, Function.comp_apply]; exact v.prop ⟨g, (h hg)⟩⟩
      map_add' _ _ := by simp [Subtype.ext_iff]
      map_smul' _ _ := by simp [Subtype.ext_iff]}
  exact FiniteDimensional.of_injective f (fun _ _ => by simp only [f, Subtype.ext_iff]; simp)

instance {H : Subgroup G} [FiniteDimensional k (invariants (ρ.comp H.subtype))] :
    FiniteDimensional k (HeckeModule₁ H ρ) :=
  LinearEquiv.finiteDimensional (HeckeModule₁.invariantsEquiv H ρ)

namespace Smooth

variable [TopologicalSpace G]

section admissible

/-- A representation `(ρ, V)` of `G` is called admissible if for any open subgroup `K` of `G`, its
`K`-invariants is finite dimensional. -/
@[mk_iff] class IsAdmissible : Prop where
  finiteDimensional_HeckeModule₁' :
  ∀ (H : OpenSubgroup G), FiniteDimensional k (invariants (ρ.comp H.subtype))

lemma isAdmissible_iff' : IsAdmissible ρ ↔
    ∀ (H : OpenSubgroup G), FiniteDimensional k (HeckeModule₁ H ρ) := by
  rw [isAdmissible_iff]
  exact ⟨fun h H => inferInstance,
    fun h H => LinearEquiv.finiteDimensional (HeckeModule₁.invariantsEquiv H ρ).symm⟩

variable [IsAdmissible ρ]

instance IsAdmissible.finiteDimensional_invariants (H : OpenSubgroup G) :
    FiniteDimensional k (invariants (ρ.comp H.1.subtype)) := (isAdmissible_iff ρ).mp inferInstance H

lemma isAdmissible_injective {f : IntertwiningMap σ ρ}
    (h_inj : Function.Injective f) : IsAdmissible σ := by
  rw [isAdmissible_iff']
  intro H
  have : FiniteDimensional k (HeckeModule₁ H ρ) := inferInstance
  have : Function.Injective (IntertwiningMap.llcomp (ofMulAction k G (G ⧸ H.1)) σ ρ f) := by
    intro _ _ h_eq
    apply IntertwiningMap.ext
    apply Function.Injective.injective_linearMapComp_left h_inj
    exact LinearMap.ext fun v => congrArg (fun f ↦ f v) h_eq
  exact FiniteDimensional.of_injective _ this

instance isAdmissible_subrepresentation (φ : Subrepresentation ρ) :
    IsAdmissible φ.toRepresentation := by
  have : Function.Injective (⟨φ.1.subtype, fun _ ↦ rfl⟩ : IntertwiningMap φ.toRepresentation ρ) :=
    Submodule.subtype_injective φ.1
  exact isAdmissible_injective _ _ this

variable {H : Type*} [Group H] [TopologicalSpace H] (φ : H →* G) in
lemma isAdmissible_res (h : IsOpenMap φ) : IsAdmissible (ρ.comp φ) := by
  rw [isAdmissible_iff]
  intro K
  let F : invariants ((ρ.comp φ).comp K.subtype) →ₗ[k] invariants (ρ.comp (K.map φ).subtype) :=
    {toFun := fun ⟨v, hv⟩ => ⟨v, by simpa using hv⟩, map_add' := by simp, map_smul' := by simp}
  have : FiniteDimensional k (invariants (ρ.comp (K.map φ).subtype)) := by
    exact IsAdmissible.finiteDimensional_invariants ρ ⟨K.1.map φ, h _ K.2⟩
  exact FiniteDimensional.of_injective F fun _ _ heq => by simpa [F] using heq

variable (P : Subgroup G) [IsTopologicalGroup G] in
instance instIsAdmissible_coind [h_cmpct : CompactSpace (G ⧸ P)] (ρ : Representation k P V)
    [IsAdmissible ρ] :
    IsAdmissible (coind P.subtype ρ):= by classical
  rw [isAdmissible_iff]
  intro H
  let U : G → Set (G ⧸ P) := fun g => QuotientGroup.mk '' ((fun x : G => x * g⁻¹) '' (H : Set G))
  have hU_open (g : G) : IsOpen (U g) := by
    apply QuotientGroup.isOpenMap_coe
    exact isOpenMap_mul_right g⁻¹ (H : Set G) H.2
  have hU_cover : (⊤ : Set (G ⧸ P)) ⊆ ⋃ g, U g := by
    intro x
    simp only [Set.top_eq_univ, Set.mem_univ, Set.mem_iUnion, forall_const]
    exact ⟨x.out⁻¹, x.out, by simp⟩
  obtain ⟨τ, hτ⟩ := h_cmpct.isCompact_univ.elim_finite_subcover U hU_open hU_cover
  have h_decomp (g : G) : ∃ (p : P) (i : τ) (h : H), g = p * i * h := by
    obtain ⟨i, hig⟩ := Set.mem_iUnion.mp (hτ (show ⟦g⁻¹⟧ ∈ (⊤ : Set (G ⧸ P)) by simp))
    simp only [Set.image_mul_right, inv_inv, Set.mem_iUnion, Set.mem_image, Set.mem_preimage,
      SetLike.mem_coe, exists_prop, U] at hig
    obtain ⟨h, hh, hp⟩ := hig.2
    rw [QuotientGroup.eq] at hp
    exact ⟨⟨(h⁻¹ * g⁻¹), hp⟩⁻¹, ⟨i, hig.1⟩ , ⟨(h * i), hh⟩⁻¹, by simp⟩
  let M (i : τ ) : Subgroup G := H.map (MulAut.conj (i : G))
  let F : invariants ((coind P.subtype ρ).comp H.subtype) →ₗ[k]
      Π i : τ, invariants (ρ.comp ((M i).subgroupOf P).subtype) :=
    { toFun := fun f i  => ⟨f.val.val i, by
        intro ⟨⟨_, _⟩, ⟨h, hh, hconj⟩⟩
        simp only [MonoidHom.coe_coe, MulAut.conj_apply, Subgroup.subtype_apply] at hconj
        simp only [← hconj, MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply]
        rw [← f.val.prop, Subgroup.subtype_apply, inv_mul_cancel_right]
        nth_rw 2 [← f.prop ⟨h, hh⟩]
        rfl⟩
      map_add' _ _ := by rfl
      map_smul' _ _ := by rfl}
  have h_inj : Function.Injective F := by
    intro x y hF
    ext g
    obtain ⟨p, i, h, hg⟩ := h_decomp g
    simp only [hg, mul_assoc, ← Subgroup.subtype_apply p, coindV_apply_map_mul]
    rw [← inv_apply_eq_iff, inv_self_apply, ← x.prop h⁻¹, ← y.prop h⁻¹]
    simp only [MonoidHom.coe_comp,Function.comp_apply, coind.apply_val_apply]
    simpa [F, Subtype.ext_iff] using congrFun hF i
  have h_open (i : τ) : IsOpen (((M i).subgroupOf P) : Set P) := by
    have h_conj : IsOpen (M i : Set G) := by
      convert isOpenMap_mul_right (i : G)⁻¹ _ (isOpenMap_mul_left (i : G) (H.1 : Set G) H.2)
      ext x
      exact ⟨fun ⟨_, _,  hhx⟩ => by simpa [← hhx], fun h => ⟨(↑i)⁻¹ * (x * i), by simpa using h⟩⟩
    exact Continuous.isOpen_preimage (f := P.subtype) continuous_subtype_val (M i) h_conj
  have (i : τ) : FiniteDimensional k
      (invariants (ρ.comp ((H.map (MulAut.conj (i : G))).subgroupOf P).subtype)) := by
    exact IsAdmissible.finiteDimensional_invariants ρ ⟨(M i).subgroupOf P, h_open i⟩
  exact FiniteDimensional.of_injective F h_inj

variable {P : Subgroup G} [IsTopologicalGroup G] in
lemma isAdmissible_smoothCoind [CompactSpace (G ⧸ P)] (ρ : Representation k P V) [IsAdmissible ρ] :
    IsAdmissible (smoothCoind P.subtype ρ) := inferInstance

end admissible

section Schur

namespace IsAdmissible

variable [IsIrreducible ρ] [IsSmooth ρ] [IsAdmissible ρ]

open MonoidAlgebra

lemma IsIrreducible.finiteDimensional_intertwiningMap_self :
    FiniteDimensional k (IntertwiningMap ρ ρ) := by
  have : Nontrivial V := IsSimpleModule.nontrivial k[G] ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let H := ρ.stabilizer v
  have : FiniteDimensional k (HeckeModule₁ H ρ) :=
    (isAdmissible_iff' ρ).mp inferInstance ⟨H, IsSmooth.smooth v⟩
  let f := HeckeModule₁.invariantsEquiv H (ρ := ρ) ⟨v, (fun h ↦ by simp [mem_stabilizer.mp h.2])⟩
  have hf : f ≠ 0 := by
    have hfeq : f (cosetVector k (1 : G)) = v := by
      simp [f]
    by_contra
    have : v = 0 := by
      rw [← hfeq, this, IntertwiningMap.coe_zero, Pi.zero_apply]
    contradiction
  have h_inj : Function.Injective ((IntertwiningMap.llcomp _ ρ ρ).flip f) := by
    intro _ _ h
    ext x
    obtain ⟨w, hw⟩ := (IsIrreducible.surjective_or_eq_zero f).resolve_right hf x
    simp only [← hw, IntertwiningMap.coe_toLinearMap, IntertwiningMap.coe_toLinearMap]
    exact congrArg (fun f ↦ f w) h
  exact FiniteDimensional.of_injective ((IntertwiningMap.llcomp _ ρ ρ).flip f) h_inj

theorem IsIrreducible.finrank_intertwiningMap_self_eq_one [IsAlgClosed k] :
    Module.finrank k (IntertwiningMap ρ ρ) = 1 := by
  have : FiniteDimensional k (IntertwiningMap ρ ρ) :=
    IsIrreducible.finiteDimensional_intertwiningMap_self ρ
  exact IsIrreducible.finrank_intertwiningMap_self ρ

theorem IsIrreducible.algebraMap_intertwiningMap_self_bijective [IsAlgClosed k] :
    Function.Bijective (algebraMap k (IntertwiningMap ρ ρ)) := by
  have : FiniteDimensional k (IntertwiningMap ρ ρ) :=
    IsIrreducible.finiteDimensional_intertwiningMap_self ρ
  exact IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed

end IsAdmissible

end Schur

end Representation.Smooth
