/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Isotypic modules and isotypic components
-/


universe u

variable (R : Type*) (M : Type u) (N S : Type*) [Ring R] [AddCommGroup M] [AddCommGroup N]
  [AddCommGroup S] [Module R M] [Module R N] [Module R S]

/-- An `R`-module `M` is isotypic of type `S` if all simple submodules of `M` are isomorphic
to `S`. If `M` is semisimple, it is equivalent to requiring that all simple quotients of `M` are
isomorphic to `S`. -/
def IsIsotypicOfType : Prop := ∀ (m : Submodule R M) [IsSimpleModule R m], Nonempty (m ≃ₗ[R] S)

/-- An `R`-module `M` is isotypic if all its simple submodules are isomorphic. -/
def IsIsotypic : Prop := ∀ (m : Submodule R M) [IsSimpleModule R m], IsIsotypicOfType R M m

variable {R M S} in
theorem IsIsotypicOfType.isIsotypic (h : IsIsotypicOfType R M S) : IsIsotypic R M :=
  fun m _ m' _ ↦ ⟨(h m').some.trans (h m).some.symm⟩

@[nontriviality]
theorem IsIsotypicOfType.of_subsingleton [Subsingleton M] : IsIsotypicOfType R M S :=
  fun S ↦ have := IsSimpleModule.nontrivial R S
    (not_subsingleton _ S.subtype_injective.subsingleton).elim

@[nontriviality] theorem IsIsotypic.of_subsingleton [Subsingleton M] : IsIsotypic R M :=
  fun S ↦ (IsIsotypicOfType.of_subsingleton R M S).isIsotypic S

theorem IsIsotypicOfType.of_isSimpleModule [IsSimpleModule R M] : IsIsotypicOfType R M M :=
  fun S hS  ↦ by
    rw [isSimpleModule_iff_isAtom, isAtom_iff_eq_top] at hS
    exact ⟨.trans (.ofEq _ _ hS) Submodule.topEquiv⟩

variable {R M N S}

theorem IsIsotypicOfType.of_linearEquiv_type (h : IsIsotypicOfType R M S) (e : S ≃ₗ[R] N) :
    IsIsotypicOfType R M N := fun m _ ↦ ⟨(h m).some.trans e⟩

theorem IsIsotypicOfType.of_injective (h : IsIsotypicOfType R N S) (f : M →ₗ[R] N)
    (inj : Function.Injective f) : IsIsotypicOfType R M S := fun m ↦
  have em := m.equivMapOfInjective f inj
  have := IsSimpleModule.congr em.symm
  ⟨em.trans (h (m.map f)).some⟩

theorem IsIsotypic.of_injective (h : IsIsotypic R N) (f : M →ₗ[R] N) (inj : Function.Injective f) :
    IsIsotypic R M := fun m _ ↦
  have em := (m.equivMapOfInjective f inj).symm
  have := IsSimpleModule.congr em
  ((h (m.map f)).of_injective f inj).of_linearEquiv_type em

theorem LinearEquiv.isIsotypicOfType_iff (e : M ≃ₗ[R] N) :
    IsIsotypicOfType R M S ↔ IsIsotypicOfType R N S :=
  ⟨(·.of_injective _ e.symm.injective), (·.of_injective _ e.injective)⟩

theorem LinearEquiv.isIsotypicOfType_iff_type (e : N ≃ₗ[R] S) :
    IsIsotypicOfType R M N ↔ IsIsotypicOfType R M S :=
  ⟨(·.of_linearEquiv_type e), (·.of_linearEquiv_type e.symm)⟩

theorem LinearEquiv.isIsotypic_iff (e : M ≃ₗ[R] N) : IsIsotypic R M ↔ IsIsotypic R N :=
  ⟨(·.of_injective _ e.symm.injective), (·.of_injective _ e.injective)⟩

theorem isIsotypicOfType_submodule_iff {N : Submodule R M} :
    IsIsotypicOfType R N S ↔ ∀ m ≤ N, [IsSimpleModule R m] → Nonempty (m ≃ₗ[R] S) := by
  rw [Subtype.forall', ← (Submodule.MapSubtype.orderIso N).forall_congr_right]
  have e := Submodule.equivMapOfInjective _ N.subtype_injective
  simp_rw [Submodule.MapSubtype.orderIso, Equiv.coe_fn_mk, ← (e _).isSimpleModule_iff]
  exact forall₂_congr fun m _ ↦ ⟨fun ⟨e'⟩ ↦ ⟨(e m).symm.trans e'⟩, fun ⟨e'⟩ ↦ ⟨(e m).trans e'⟩⟩

theorem isIsotypic_submodule_iff {N : Submodule R M} :
    IsIsotypic R N ↔ ∀ m ≤ N, [IsSimpleModule R m] → IsIsotypicOfType R N m := by
  rw [Subtype.forall', ← (Submodule.MapSubtype.orderIso N).forall_congr_right]
  have e := Submodule.equivMapOfInjective _ N.subtype_injective
  simp_rw [Submodule.MapSubtype.orderIso, Equiv.coe_fn_mk, ← (e _).isSimpleModule_iff,
    ← (e _).isIsotypicOfType_iff_type, IsIsotypic]

section Finsupp

variable [IsSemisimpleModule R M]

theorem IsIsotypicOfType.linearEquiv_finsupp (h : IsIsotypicOfType R M S) :
    ∃ ι : Type u, Nonempty (M ≃ₗ[R] ι →₀ S) := by
  have ⟨s, e, _, hs⟩ := IsSemisimpleModule.exists_linearEquiv_dfinsupp R M
  classical exact ⟨s, ⟨e.trans (DFinsupp.mapRange.linearEquiv fun m : s ↦ (h m.1).some)
    |>.trans (finsuppLequivDFinsupp R).symm⟩⟩

theorem IsIsotypic.linearEquiv_finsupp [Nontrivial M] (h : IsIsotypic R M) :
    ∃ (ι : Type u) (_ : Nonempty ι) (S : Submodule R M),
      IsSimpleModule R S ∧ Nonempty (M ≃ₗ[R] ι →₀ S) := by
  have ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R M)
  rw [← isSimpleModule_iff_isAtom] at hS
  have ⟨ι, e⟩ := (h S).linearEquiv_finsupp
  exact ⟨ι, (isEmpty_or_nonempty ι).resolve_left fun _ ↦ not_subsingleton _ (e.some.subsingleton),
    S, hS, e⟩

theorem IsIsotypicOfType.linearEquiv_fun [Module.Finite R M] (h : IsIsotypicOfType R M S) :
    ∃ n : ℕ, Nonempty (M ≃ₗ[R] Fin n → S) := by
  have ⟨n, S, e, hs⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp R M
  classical exact ⟨n, ⟨e.trans (DFinsupp.mapRange.linearEquiv fun i ↦ (h (S i)).some)
    |>.trans (finsuppLequivDFinsupp R).symm |>.trans (Finsupp.linearEquivFunOnFinite ..)⟩⟩

theorem IsIsotypic.linearEquiv_fun [Module.Finite R M] [Nontrivial M] (h : IsIsotypic R M) :
    ∃ (n : ℕ) (_ : NeZero n) (S : Submodule R M),
      IsSimpleModule R S ∧ Nonempty (M ≃ₗ[R] Fin n → S) := by
  have ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R M)
  rw [← isSimpleModule_iff_isAtom] at hS
  have ⟨n, e⟩ := (h S).linearEquiv_fun
  exact ⟨n, neZero_iff.2 <| by rintro rfl; exact not_subsingleton _ (e.some.subsingleton), S, hS, e⟩

end Finsupp

/-- A submodule `N` an `R`-module `M` is fully invariant if `N` is mapped into itself by all
`R`-linear endomorphisms of `M`.

TODO: If `M` is semisimple, this is equivalent to `N` being a sum of isotypic components of `M`. -/
def Submodule.IsFullyInvariant (N : Submodule R M) : Prop :=
  ∀ f : Module.End R M, N ≤ N.comap f

theorem isFullyInvariant_iff_isTwoSided {I : Ideal R} : I.IsFullyInvariant ↔ I.IsTwoSided := by
  simpa only [Submodule.IsFullyInvariant, ← MulOpposite.opEquiv.trans (RingEquiv.moduleEndSelf R
    |>.toEquiv) |>.forall_congr_right, SetLike.le_def, I.isTwoSided_iff] using forall_comm

variable (R M S)

/-- If `S` is a simple `R`-module, the `S`-isotypic component in an `R`-module `M` is the sum of
all submodules of `M` isomorphic to `S`. -/
def isotypicComponent : Submodule R M := sSup {m | Nonempty (m ≃ₗ[R] S)}

theorem Submodule.le_isotypicComponent (m : Submodule R M) : m ≤ isotypicComponent R M m :=
  le_sSup ⟨.refl ..⟩

theorem bot_lt_isotypicComponent (S : Submodule R M) [IsSimpleModule R S] :
    ⊥ < isotypicComponent R M S :=
  lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr <| (S.nontrivial_iff_ne_bot).mp <|
    IsSimpleModule.nontrivial R S) S.le_isotypicComponent

instance [IsSemisimpleModule R S] : IsSemisimpleModule R (isotypicComponent R M S) := by
  rw [isotypicComponent, sSup_eq_iSup]
  refine isSemisimpleModule_biSup_of_isSemisimpleModule_submodule fun m ⟨e⟩ ↦ ?_
  have := IsSemisimpleModule.congr e
  infer_instance

section SimpleSubmodule

variable {R M} (N : Submodule R M) [IsSimpleModule R N] (s : Set (Submodule R M))

open LinearMap in
theorem Submodule.le_linearEquiv_of_sSup_eq_top [IsSemisimpleModule R M]
    (hs : sSup s = ⊤) : ∃ m ∈ s, ∃ S ≤ m, Nonempty (N ≃ₗ[R] S) := by
  have := IsSimpleModule.nontrivial R N
  have ⟨_, compl⟩ := exists_isCompl N
  have ⟨m, hm, ne⟩ := exists_ne_zero_of_sSup_eq_top (ne_zero_of_surjective
    (N.linearProjOfIsCompl_surjective compl)) _ hs
  have ⟨S, ⟨e⟩⟩ := linearEquiv_of_ne_zero ne
  exact ⟨m, hm, _, m.map_subtype_le S, ⟨e.trans (S.equivMapOfInjective _ m.subtype_injective)⟩⟩

theorem Submodule.linearEquiv_of_sSup_eq_top [h : ∀ m : s, IsSimpleModule R m]
    (hs : sSup s = ⊤) : ∃ S ∈ s, Nonempty (N ≃ₗ[R] S) :=
  have := isSemisimpleModule_of_isSemisimpleModule_submodule' (fun _ ↦ inferInstance)
    (sSup_eq_iSup' s ▸ hs)
  have ⟨m, hm, _S, le, ⟨e⟩⟩ := N.le_linearEquiv_of_sSup_eq_top _ hs
  have := isSimpleModule_iff_isAtom.mp (IsSimpleModule.congr e.symm)
  have := ((isSimpleModule_iff_isAtom.mp <| h ⟨m, hm⟩).le_iff_eq this.1).mp le
  ⟨m, hm, ⟨e.trans (.ofEq _ _ this)⟩⟩

/-- If a simple module is contained in a sum of semisimple modules, it must be isomorphic
to a submodule of one of the summands. -/
theorem Submodule.le_linearEquiv_of_le_sSup [hs : ∀ m : s, IsSemisimpleModule R m]
    (hN : N ≤ sSup s) : ∃ m ∈ s, ∃ S ≤ m, Nonempty (N ≃ₗ[R] S) := by
  rw [sSup_eq_iSup] at hN
  have e := LinearEquiv.ofInjective _ (inclusion_injective hN)
  have := IsSimpleModule.congr e.symm
  have := isSemisimpleModule_biSup_of_isSemisimpleModule_submodule fun m hm ↦ hs ⟨m, hm⟩
  obtain ⟨_, ⟨m, hm, rfl⟩, S, le, ⟨e'⟩⟩ := LinearMap.range (inclusion hN)
      |>.le_linearEquiv_of_sSup_eq_top (comap (⨆ i ∈ s, i).subtype '' s) <| by
    rw [sSup_image, biSup_comap_subtype_eq_top]
  exact ⟨m, hm, _, map_le_iff_le_comap.mpr le,
    ⟨(e.trans e').trans (equivMapOfInjective _ (subtype_injective _) _)⟩⟩

theorem Submodule.linearEquiv_of_le_sSup [simple : ∀ m : s, IsSimpleModule R m]
    (hs : N ≤ sSup s) : ∃ S ∈ s, Nonempty (N ≃ₗ[R] S) :=
  have ⟨m, hm, _S, le, ⟨e⟩⟩ := N.le_linearEquiv_of_le_sSup _ hs
  have := isSimpleModule_iff_isAtom.mp (.congr e.symm)
  have := ((isSimpleModule_iff_isAtom.mp <| simple ⟨m, hm⟩).le_iff_eq this.1).mp le
  ⟨m, hm, ⟨e.trans (.ofEq _ _ this)⟩⟩

end SimpleSubmodule

section IsSimpleModule

variable [IsSimpleModule R S]

local instance (m : {m : Submodule R M | Nonempty (m ≃ₗ[R] S)}) :
    IsSimpleModule R m := .congr m.2.some

protected theorem IsIsotypicOfType.isotypicComponent :
    IsIsotypicOfType R (isotypicComponent R M S) S :=
  isIsotypicOfType_submodule_iff.mpr fun m h _ ↦
    have ⟨_, ⟨e⟩, ⟨e'⟩⟩ := m.linearEquiv_of_le_sSup _ h
    ⟨e'.trans e⟩

protected theorem IsIsotypic.isotypicComponent : IsIsotypic R (isotypicComponent R M S) :=
  (IsIsotypicOfType.isotypicComponent R M S).isIsotypic

variable {R M S}

theorem IsIsotypicOfType.of_isotypicComponent_eq_top (h : isotypicComponent R M S = ⊤) :
    IsIsotypicOfType R M S :=
  fun m _ ↦ have ⟨_, ⟨e⟩, ⟨e'⟩⟩ := m.linearEquiv_of_sSup_eq_top _ h; ⟨e'.trans e⟩

theorem isotypicComponent_eq_top_iff [IsSemisimpleModule R M] :
    isotypicComponent R M S = ⊤ ↔ IsIsotypicOfType R M S :=
  ⟨fun h ↦ .of_isotypicComponent_eq_top h, fun h ↦ top_unique <|
    (IsSemisimpleModule.sSup_simples_eq_top R M).ge.trans (sSup_le_sSup @h)⟩

variable (R M S) in
theorem isFullyInvariant_isotypicComponent : (isotypicComponent R M S).IsFullyInvariant :=
  fun f ↦ sSup_le fun m ⟨e⟩ ↦ Submodule.map_le_iff_le_comap.mp <| by
    have := IsSimpleModule.congr e
    rw [← m.range_subtype, ← LinearMap.range_comp]
    obtain inj | eq := (f ∘ₗ m.subtype).injective_or_eq_zero
    · exact le_sSup ⟨.trans (.symm <| LinearEquiv.ofInjective _ inj) e⟩
    · simp_rw [eq, LinearMap.range_zero, bot_le]

end IsSimpleModule

open IsSemisimpleModule in
theorem isIsotypic_iff_isFullyInvariant_imp_bot_or_top [IsSemisimpleModule R M] :
    IsIsotypic R M ↔ ∀ N : Submodule R M, N.IsFullyInvariant → N = ⊥ ∨ N = ⊤ := by
  refine ⟨fun h N hN ↦ (eq_bot_or_exists_simple_le N).imp_right fun ⟨S, le, _⟩ ↦ top_unique <|
    sSup_simples_eq_top R M ▸ sSup_le fun S' (_ : IsSimpleModule R S') ↦ ?_, fun h ↦ ?_⟩
  · nontriviality M
    have ⟨S, _⟩ := exists_simple_submodule R M
    have eq := (h _ (isFullyInvariant_isotypicComponent R M S)).resolve_left
      (bot_lt_isotypicComponent R M S).ne'
    exact .of_injective (.isotypicComponent R M S) _
      ((LinearEquiv.ofEq _ _ eq).trans Submodule.topEquiv).symm.injective
  · have ⟨e⟩ := h S S'
    have ⟨p, eq⟩ := extension_property _ S.subtype_injective (S'.subtype ∘ₗ e.symm)
    refine (le_trans ?_ (Submodule.map_mono le)).trans (Submodule.map_le_iff_le_comap.mpr (hN p))
    rw [← S.range_subtype, ← LinearMap.range_comp, eq, e.symm.range_comp, S'.range_subtype]
