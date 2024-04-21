/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.JordanHolder
import Mathlib.Order.CompactlyGenerated.Intervals
import Mathlib.LinearAlgebra.FiniteDimensional

#align_import ring_theory.simple_module from "leanprover-community/mathlib"@"cce7f68a7eaadadf74c82bbac20721cdc03a1cc1"

/-!
# Simple Modules

## Main Definitions
  * `IsSimpleModule` indicates that a module has no proper submodules
  (the only submodules are `⊥` and `⊤`).
  * `IsSemisimpleModule` indicates that every submodule has a complement, or equivalently,
    the module is a direct sum of simple modules.
  * A `DivisionRing` structure on the endomorphism ring of a simple module.

## Main Results
  * Schur's Lemma: `bijective_or_eq_zero` shows that a linear map between simple modules
    is either bijective or 0, leading to a `DivisionRing` structure on the endomorphism ring.
  * `isSimpleModule_iff_quot_maximal`:
    a module is simple iff it's isomorphic to the quotient of the ring by a maximal left ideal.
  * `sSup_simples_eq_top_iff_isSemisimpleModule`:
    a module is semisimple iff it is generated by its simple submodules.
  * `IsSemisimpleModule.annihilator_isRadical`:
    the annihilator of a semisimple module over a commutative ring is a radical ideal.
  * `IsSemisimpleModule.submodule`, `IsSemisimpleModule.quotient`:
    any submodule or quotient module of a semisimple module is semisimple.
  * `isSemisimpleModule_of_isSemisimpleModule_submodule`:
    a module generated by semisimple submodules is itself semisimple.
  * `IsSemisimpleRing.isSemisimpleModule`: every module over a semisimple ring is semisimple.
  * `instIsSemisimpleRingForAllRing`: a finite product of semisimple rings is semisimple.
  * `RingHom.isSemisimpleRing_of_surjective`: any quotient of a semisimple ring is semisimple.

## TODO
  * Artin-Wedderburn Theory
  * Unify with the work on Schur's Lemma in a category theory context

-/


variable {ι : Type*} (R S : Type*) [Ring R] [Ring S] (M : Type*) [AddCommGroup M] [Module R M]

/-- A module is simple when it has only two submodules, `⊥` and `⊤`. -/
abbrev IsSimpleModule :=
  IsSimpleOrder (Submodule R M)
#align is_simple_module IsSimpleModule

/-- A module is semisimple when every submodule has a complement, or equivalently, the module
  is a direct sum of simple modules. -/
abbrev IsSemisimpleModule :=
  ComplementedLattice (Submodule R M)
#align is_semisimple_module IsSemisimpleModule

/-- A ring is semisimple if it is semisimple as a module over itself. -/
abbrev IsSemisimpleRing := IsSemisimpleModule R R

theorem RingEquiv.isSemisimpleRing (e : R ≃+* S) [IsSemisimpleRing R] : IsSemisimpleRing S :=
  (Submodule.orderIsoMapComap e.toSemilinearEquiv).complementedLattice

-- Making this an instance causes the linter to complain of "dangerous instances"
theorem IsSimpleModule.nontrivial [IsSimpleModule R M] : Nontrivial M :=
  ⟨⟨0, by
      have h : (⊥ : Submodule R M) ≠ ⊤ := bot_ne_top
      contrapose! h
      ext x
      simp [Submodule.mem_bot, Submodule.mem_top, h x]⟩⟩
#align is_simple_module.nontrivial IsSimpleModule.nontrivial

variable {m : Submodule R M} {N : Type*} [AddCommGroup N] [Module R N] {R S M}

theorem LinearMap.isSimpleModule_iff_of_bijective [Module S N] {σ : R →+* S} [RingHomSurjective σ]
    (l : M →ₛₗ[σ] N) (hl : Function.Bijective l) : IsSimpleModule R M ↔ IsSimpleModule S N :=
  (Submodule.orderIsoMapComapOfBijective l hl).isSimpleOrder_iff

theorem IsSimpleModule.congr (l : M ≃ₗ[R] N) [IsSimpleModule R N] : IsSimpleModule R M :=
  (Submodule.orderIsoMapComap l).isSimpleOrder
#align is_simple_module.congr IsSimpleModule.congr

theorem isSimpleModule_iff_isAtom : IsSimpleModule R m ↔ IsAtom m := by
  rw [← Set.isSimpleOrder_Iic_iff_isAtom]
  apply OrderIso.isSimpleOrder_iff
  exact Submodule.MapSubtype.relIso m
#align is_simple_module_iff_is_atom isSimpleModule_iff_isAtom

theorem isSimpleModule_iff_isCoatom : IsSimpleModule R (M ⧸ m) ↔ IsCoatom m := by
  rw [← Set.isSimpleOrder_Ici_iff_isCoatom]
  apply OrderIso.isSimpleOrder_iff
  exact Submodule.comapMkQRelIso m
#align is_simple_module_iff_is_coatom isSimpleModule_iff_isCoatom

theorem covBy_iff_quot_is_simple {A B : Submodule R M} (hAB : A ≤ B) :
    A ⋖ B ↔ IsSimpleModule R (B ⧸ Submodule.comap B.subtype A) := by
  set f : Submodule R B ≃o Set.Iic B := Submodule.MapSubtype.relIso B with hf
  rw [covBy_iff_coatom_Iic hAB, isSimpleModule_iff_isCoatom, ← OrderIso.isCoatom_iff f, hf]
  -- This used to be in the next `simp`, but we need `erw` after leanprover/lean4#2644
  erw [RelIso.coe_fn_mk]
  simp [-OrderIso.isCoatom_iff, Submodule.MapSubtype.relIso, Submodule.map_comap_subtype,
    inf_eq_right.2 hAB]
#align covby_iff_quot_is_simple covBy_iff_quot_is_simple

namespace IsSimpleModule

variable [hm : IsSimpleModule R m]

@[simp]
theorem isAtom : IsAtom m :=
  isSimpleModule_iff_isAtom.1 hm
#align is_simple_module.is_atom IsSimpleModule.isAtom

variable [IsSimpleModule R M] (R)
open LinearMap

theorem span_singleton_eq_top {m : M} (hm : m ≠ 0) : Submodule.span R {m} = ⊤ :=
  (eq_bot_or_eq_top _).resolve_left fun h ↦ hm (h.le <| Submodule.mem_span_singleton_self m)

instance (S : Submodule R M) : S.IsPrincipal where
  principal' := by
    obtain rfl | rfl := eq_bot_or_eq_top S
    · exact ⟨0, Submodule.span_zero.symm⟩
    have := IsSimpleModule.nontrivial R M
    have ⟨m, hm⟩ := exists_ne (0 : M)
    exact ⟨m, (span_singleton_eq_top R hm).symm⟩

theorem toSpanSingleton_surjective {m : M} (hm : m ≠ 0) :
    Function.Surjective (toSpanSingleton R M m) := by
  rw [← range_eq_top, ← span_singleton_eq_range, span_singleton_eq_top R hm]

theorem ker_toSpanSingleton_isMaximal {m : M} (hm : m ≠ 0) :
    Ideal.IsMaximal (ker (toSpanSingleton R M m)) := by
  rw [Ideal.isMaximal_def, ← isSimpleModule_iff_isCoatom]
  exact congr (quotKerEquivOfSurjective _ <| toSpanSingleton_surjective R hm)

end IsSimpleModule

open IsSimpleModule in
/-- A module is simple iff it's isomorphic to the quotient of the ring by a maximal left ideal
(not necessarily unique if the ring is not commutative). -/
theorem isSimpleModule_iff_quot_maximal :
    IsSimpleModule R M ↔ ∃ I : Ideal R, I.IsMaximal ∧ Nonempty (M ≃ₗ[R] R ⧸ I) := by
  refine ⟨fun h ↦ ?_, fun ⟨I, ⟨coatom⟩, ⟨equiv⟩⟩ ↦ ?_⟩
  · have := IsSimpleModule.nontrivial R M
    have ⟨m, hm⟩ := exists_ne (0 : M)
    exact ⟨_, ker_toSpanSingleton_isMaximal R hm,
      ⟨(LinearMap.quotKerEquivOfSurjective _ <| toSpanSingleton_surjective R hm).symm⟩⟩
  · convert congr equiv; rwa [isSimpleModule_iff_isCoatom]

/-- In general, the annihilator of a simple module is called a primitive ideal, and it is
always a two-sided prime ideal, but mathlib's `Ideal.IsPrime` is not the correct definition
for noncommutative rings. -/
theorem IsSimpleModule.annihilator_isMaximal {R} [CommRing R] [Module R M]
    [simple : IsSimpleModule R M] : (Module.annihilator R M).IsMaximal := by
  have ⟨I, max, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp simple
  rwa [e.annihilator_eq, I.annihilator_quotient]

theorem isSimpleModule_iff_toSpanSingleton_surjective : IsSimpleModule R M ↔
    Nontrivial M ∧ ∀ x : M, x ≠ 0 → Function.Surjective (LinearMap.toSpanSingleton R M x) :=
  ⟨fun h ↦ ⟨h.nontrivial, fun _ ↦ h.toSpanSingleton_surjective⟩, fun ⟨_, h⟩ ↦
    ⟨fun m ↦ or_iff_not_imp_left.mpr fun ne_bot ↦
      have ⟨x, hxm, hx0⟩ := m.ne_bot_iff.mp ne_bot
      top_unique <| fun z _ ↦ by obtain ⟨y, rfl⟩ := h x hx0 z; exact m.smul_mem _ hxm⟩⟩

/-- A ring is a simple module over itself iff it is a division ring. -/
theorem isSimpleModule_self_iff_isUnit :
    IsSimpleModule R R ↔ Nontrivial R ∧ ∀ x : R, x ≠ 0 → IsUnit x :=
  isSimpleModule_iff_toSpanSingleton_surjective.trans <| and_congr_right fun _ ↦ by
    refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ (h x hx).unit.mulRight_bijective.surjective⟩
    obtain ⟨y, hyx : y * x = 1⟩ := h x hx 1
    have hy : y ≠ 0 := left_ne_zero_of_mul (hyx.symm ▸ one_ne_zero)
    obtain ⟨z, hzy : z * y = 1⟩ := h y hy 1
    exact ⟨⟨x, y, left_inv_eq_right_inv hzy hyx ▸ hzy, hyx⟩, rfl⟩

theorem isSimpleModule_iff_finrank_eq_one {R} [DivisionRing R] [Module R M] :
    IsSimpleModule R M ↔ FiniteDimensional.finrank R M = 1 :=
  ⟨fun h ↦ have := h.nontrivial; have ⟨v, hv⟩ := exists_ne (0 : M)
    (finrank_eq_one_iff_of_nonzero' v hv).mpr (IsSimpleModule.toSpanSingleton_surjective R hv),
  is_simple_module_of_finrank_eq_one⟩

theorem IsSemisimpleModule.of_sSup_simples_eq_top
    (h : sSup { m : Submodule R M | IsSimpleModule R m } = ⊤) : IsSemisimpleModule R M :=
  complementedLattice_of_sSup_atoms_eq_top (by simp_rw [← h, isSimpleModule_iff_isAtom])
#align is_semisimple_of_Sup_simples_eq_top IsSemisimpleModule.of_sSup_simples_eq_top
@[deprecated]
alias is_semisimple_of_sSup_simples_eq_top := IsSemisimpleModule.of_sSup_simples_eq_top

namespace IsSemisimpleModule

variable [IsSemisimpleModule R M]

theorem sSup_simples_eq_top : sSup { m : Submodule R M | IsSimpleModule R m } = ⊤ := by
  simp_rw [isSimpleModule_iff_isAtom]
  exact sSup_atoms_eq_top
#align is_semisimple_module.Sup_simples_eq_top IsSemisimpleModule.sSup_simples_eq_top

/-- The annihilator of a semisimple module over a commutative ring is a radical ideal. -/
theorem annihilator_isRadical {R} [CommRing R] [Module R M] [IsSemisimpleModule R M] :
    (Module.annihilator R M).IsRadical := by
  rw [← Submodule.annihilator_top, ← sSup_simples_eq_top, sSup_eq_iSup', Submodule.annihilator_iSup]
  exact Ideal.isRadical_iInf _ fun i ↦ (i.2.annihilator_isMaximal).isPrime.isRadical

instance submodule {m : Submodule R M} : IsSemisimpleModule R m :=
  haveI f : Submodule R m ≃o Set.Iic m := Submodule.MapSubtype.relIso m
  f.complementedLattice_iff.2 IsModularLattice.complementedLattice_Iic
#align is_semisimple_module.is_semisimple_submodule IsSemisimpleModule.submodule

open LinearMap

theorem congr [IsSemisimpleModule R N] (e : M ≃ₗ[R] N) : IsSemisimpleModule R M :=
  (Submodule.orderIsoMapComap e.symm).complementedLattice

instance quotient : IsSemisimpleModule R (M ⧸ m) :=
  have ⟨P, compl⟩ := exists_isCompl m
  .congr (m.quotientEquivOfIsCompl P compl)

-- does not work as an instance, not sure why
protected theorem range (f : M →ₗ[R] N) : IsSemisimpleModule R (range f) :=
  .congr (quotKerEquivRange _).symm

section

variable [Module S N] {σ : R →+* S} [RingHomSurjective σ] (l : M →ₛₗ[σ] N)

theorem _root_.LinearMap.isSemisimpleModule_iff_of_bijective (hl : Function.Bijective l) :
    IsSemisimpleModule R M ↔ IsSemisimpleModule S N :=
  (Submodule.orderIsoMapComapOfBijective l hl).complementedLattice_iff

-- TODO: generalize Submodule.equivMapOfInjective from InvPair to RingHomSurjective
proof_wanted _root_.LinearMap.isSemisimpleModule_of_injective (_ : Function.Injective l)
    [IsSemisimpleModule S N] : IsSemisimpleModule R M

--TODO: generalize LinearMap.quotKerEquivOfSurjective to SemilinearMaps + RingHomSurjective
proof_wanted _root_.LinearMap.isSemisimpleModule_of_surjective (_ : Function.Surjective l)
    [IsSemisimpleModule R M] : IsSemisimpleModule S N

end

end IsSemisimpleModule

/-- A module is semisimple iff it is generated by its simple submodules. -/
theorem sSup_simples_eq_top_iff_isSemisimpleModule :
    sSup { m : Submodule R M | IsSimpleModule R m } = ⊤ ↔ IsSemisimpleModule R M :=
  ⟨.of_sSup_simples_eq_top, fun _ ↦ IsSemisimpleModule.sSup_simples_eq_top⟩
#align is_semisimple_iff_top_eq_Sup_simples sSup_simples_eq_top_iff_isSemisimpleModule
@[deprecated]
alias is_semisimple_iff_top_eq_sSup_simples := sSup_simples_eq_top_iff_isSemisimpleModule

/-- A module generated by semisimple submodules is itself semisimple. -/
lemma isSemisimpleModule_of_isSemisimpleModule_submodule {s : Set ι} {p : ι → Submodule R M}
    (hp : ∀ i ∈ s, IsSemisimpleModule R (p i)) (hp' : ⨆ i ∈ s, p i = ⊤) :
    IsSemisimpleModule R M := by
  refine complementedLattice_of_complementedLattice_Iic (fun i hi ↦ ?_) hp'
  let e : Submodule R (p i) ≃o Set.Iic (p i) := Submodule.MapSubtype.relIso (p i)
  simpa only [← e.complementedLattice_iff] using hp i hi

lemma isSemisimpleModule_biSup_of_isSemisimpleModule_submodule {s : Set ι} {p : ι → Submodule R M}
    (hp : ∀ i ∈ s, IsSemisimpleModule R (p i)) :
    IsSemisimpleModule R ↥(⨆ i ∈ s, p i) := by
  let q := ⨆ i ∈ s, p i
  let p' : ι → Submodule R q := fun i ↦ (p i).comap q.subtype
  have hp₀ : ∀ i ∈ s, p i ≤ LinearMap.range q.subtype := fun i hi ↦ by
    simpa only [Submodule.range_subtype] using le_biSup _ hi
  have hp₁ : ∀ i ∈ s, IsSemisimpleModule R (p' i) := fun i hi ↦ by
    let e : p' i ≃ₗ[R] p i := (p i).comap_equiv_self_of_inj_of_le q.injective_subtype (hp₀ i hi)
    exact (Submodule.orderIsoMapComap e).complementedLattice_iff.mpr <| hp i hi
  have hp₂ : ⨆ i ∈ s, p' i = ⊤ := by
    apply Submodule.map_injective_of_injective q.injective_subtype
    simp_rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_iSup]
    exact biSup_congr fun i hi ↦ Submodule.map_comap_eq_of_le (hp₀ i hi)
  exact isSemisimpleModule_of_isSemisimpleModule_submodule hp₁ hp₂

lemma isSemisimpleModule_of_isSemisimpleModule_submodule' {p : ι → Submodule R M}
    (hp : ∀ i, IsSemisimpleModule R (p i)) (hp' : ⨆ i, p i = ⊤) :
    IsSemisimpleModule R M :=
  isSemisimpleModule_of_isSemisimpleModule_submodule (s := Set.univ) (fun i _ ↦ hp i) (by simpa)

theorem IsSemisimpleModule.sup {p q : Submodule R M}
    (_ : IsSemisimpleModule R p) (_ : IsSemisimpleModule R q) :
    IsSemisimpleModule R ↥(p ⊔ q) := by
  let f : Bool → Submodule R M := Bool.rec q p
  rw [show p ⊔ q = ⨆ i ∈ Set.univ, f i by rw [iSup_univ, iSup_bool_eq]]
  exact isSemisimpleModule_biSup_of_isSemisimpleModule_submodule (by rintro (_|_) _ <;> assumption)

instance IsSemisimpleRing.isSemisimpleModule [IsSemisimpleRing R] : IsSemisimpleModule R M :=
  have : IsSemisimpleModule R (M →₀ R) := isSemisimpleModule_of_isSemisimpleModule_submodule'
    (fun _ ↦ .congr (LinearMap.quotKerEquivRange _).symm) Finsupp.iSup_lsingle_range
  .congr (LinearMap.quotKerEquivOfSurjective _ <| Finsupp.total_id_surjective R M).symm

open LinearMap in
/-- A finite product of semisimple rings is semisimple. -/
instance {ι} [Finite ι] (R : ι → Type*) [∀ i, Ring (R i)] [∀ i, IsSemisimpleRing (R i)] :
    IsSemisimpleRing (∀ i, R i) := by
  letI (i) : Module (∀ i, R i) (R i) := Module.compHom _ (Pi.evalRingHom R i)
  let e (i) : R i →ₛₗ[Pi.evalRingHom R i] R i :=
    { AddMonoidHom.id (R i) with map_smul' := fun _ _ ↦ rfl }
  have (i) : IsSemisimpleModule (∀ i, R i) (R i) :=
    ((e i).isSemisimpleModule_iff_of_bijective Function.bijective_id).mpr inferInstance
  classical
  exact isSemisimpleModule_of_isSemisimpleModule_submodule' (p := (range <| single ·))
    (fun i ↦ .range _) (by simp_rw [range_eq_map, Submodule.iSup_map_single, Submodule.pi_top])

/-- A binary product of semisimple rings is semisimple. -/
instance [hR : IsSemisimpleRing R] [hS : IsSemisimpleRing S] : IsSemisimpleRing (R × S) := by
  letI : Module (R × S) R := Module.compHom _ (.fst R S)
  letI : Module (R × S) S := Module.compHom _ (.snd R S)
  -- e₁, e₂ got falsely flagged by the unused argument linter
  let _e₁ : R →ₛₗ[.fst R S] R := { AddMonoidHom.id R with map_smul' := fun _ _ ↦ rfl }
  let _e₂ : S →ₛₗ[.snd R S] S := { AddMonoidHom.id S with map_smul' := fun _ _ ↦ rfl }
  rw [IsSemisimpleRing, ← _e₁.isSemisimpleModule_iff_of_bijective Function.bijective_id] at hR
  rw [IsSemisimpleRing, ← _e₂.isSemisimpleModule_iff_of_bijective Function.bijective_id] at hS
  rw [IsSemisimpleRing, ← Submodule.topEquiv.isSemisimpleModule_iff_of_bijective
    (LinearEquiv.bijective _), ← LinearMap.sup_range_inl_inr]
  exact .sup (.range _) (.range _)

theorem RingHom.isSemisimpleRing_of_surjective (f : R →+* S) (hf : Function.Surjective f)
    [IsSemisimpleRing R] : IsSemisimpleRing S := by
  letI : Module R S := Module.compHom _ f
  haveI : RingHomSurjective f := ⟨hf⟩
  let e : S →ₛₗ[f] S := { AddMonoidHom.id S with map_smul' := fun _ _ ↦ rfl }
  rw [IsSemisimpleRing, ← e.isSemisimpleModule_iff_of_bijective Function.bijective_id]
  infer_instance

theorem IsSemisimpleRing.ideal_eq_span_idempotent [IsSemisimpleRing R] (I : Ideal R) :
    ∃ e : R, IsIdempotentElem e ∧ I = .span {e} := by
  obtain ⟨J, h⟩ := exists_isCompl I
  obtain ⟨f, idem, rfl⟩ := I.isIdempotentElemEquiv.symm (I.isComplEquivProj ⟨J, h⟩)
  exact ⟨f 1, LinearMap.isIdempotentElem_apply_one_iff.mpr idem, by
    erw [LinearMap.range_eq_map, ← Ideal.span_one, LinearMap.map_span, Set.image_singleton]; rfl⟩

instance [IsSemisimpleRing R] : IsPrincipalIdealRing R where
  principal I := have ⟨e, _, he⟩ := IsSemisimpleRing.ideal_eq_span_idempotent I; ⟨e, he⟩

variable (ι R)

proof_wanted IsSemisimpleRing.mulOpposite [IsSemisimpleRing R] : IsSemisimpleRing Rᵐᵒᵖ

proof_wanted IsSemisimpleRing.module_end [IsSemisimpleRing R] [Module.Finite R M] :
    IsSemisimpleRing (Module.End R M)

proof_wanted IsSemisimpleRing.matrix [Fintype ι] [DecidableEq ι] [IsSemisimpleRing R] :
    IsSemisimpleRing (Matrix ι ι R)

universe u in
/-- The existence part of the Artin–Wedderburn theorem. -/
proof_wanted isSemisimpleRing_iff_pi_matrix_divisionRing {R : Type u} [Ring R] :
    IsSemisimpleRing R ↔
    ∃ (n : ℕ) (S : Fin n → Type u) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (S i)),
      Nonempty (R ≃+* ∀ i, Matrix (Fin (d i)) (Fin (d i)) (S i))

variable {ι R}

namespace LinearMap

theorem injective_or_eq_zero [IsSimpleModule R M] (f : M →ₗ[R] N) :
    Function.Injective f ∨ f = 0 := by
  rw [← ker_eq_bot, ← ker_eq_top]
  apply eq_bot_or_eq_top
#align linear_map.injective_or_eq_zero LinearMap.injective_or_eq_zero

theorem injective_of_ne_zero [IsSimpleModule R M] {f : M →ₗ[R] N} (h : f ≠ 0) :
    Function.Injective f :=
  f.injective_or_eq_zero.resolve_right h
#align linear_map.injective_of_ne_zero LinearMap.injective_of_ne_zero

theorem surjective_or_eq_zero [IsSimpleModule R N] (f : M →ₗ[R] N) :
    Function.Surjective f ∨ f = 0 := by
  rw [← range_eq_top, ← range_eq_bot, or_comm]
  apply eq_bot_or_eq_top
#align linear_map.surjective_or_eq_zero LinearMap.surjective_or_eq_zero

theorem surjective_of_ne_zero [IsSimpleModule R N] {f : M →ₗ[R] N} (h : f ≠ 0) :
    Function.Surjective f :=
  f.surjective_or_eq_zero.resolve_right h
#align linear_map.surjective_of_ne_zero LinearMap.surjective_of_ne_zero

/-- **Schur's Lemma** for linear maps between (possibly distinct) simple modules -/
theorem bijective_or_eq_zero [IsSimpleModule R M] [IsSimpleModule R N] (f : M →ₗ[R] N) :
    Function.Bijective f ∨ f = 0 :=
  or_iff_not_imp_right.mpr fun h ↦ ⟨injective_of_ne_zero h, surjective_of_ne_zero h⟩
#align linear_map.bijective_or_eq_zero LinearMap.bijective_or_eq_zero

theorem bijective_of_ne_zero [IsSimpleModule R M] [IsSimpleModule R N] {f : M →ₗ[R] N} (h : f ≠ 0) :
    Function.Bijective f :=
  f.bijective_or_eq_zero.resolve_right h
#align linear_map.bijective_of_ne_zero LinearMap.bijective_of_ne_zero

theorem isCoatom_ker_of_surjective [IsSimpleModule R N] {f : M →ₗ[R] N}
    (hf : Function.Surjective f) : IsCoatom (LinearMap.ker f) := by
  rw [← isSimpleModule_iff_isCoatom]
  exact IsSimpleModule.congr (f.quotKerEquivOfSurjective hf)
#align linear_map.is_coatom_ker_of_surjective LinearMap.isCoatom_ker_of_surjective

/-- Schur's Lemma makes the endomorphism ring of a simple module a division ring. -/
noncomputable instance _root_.Module.End.divisionRing
    [DecidableEq (Module.End R M)] [IsSimpleModule R M] : DivisionRing (Module.End R M) where
  __ := Module.End.ring
  inv f := if h : f = 0 then 0 else (LinearEquiv.ofBijective _ <| bijective_of_ne_zero h).symm
  exists_pair_ne := ⟨0, 1, have := IsSimpleModule.nontrivial R M; zero_ne_one⟩
  mul_inv_cancel a a0 := by
    simp_rw [dif_neg a0]; ext
    exact (LinearEquiv.ofBijective _ <| bijective_of_ne_zero a0).right_inv _
  inv_zero := dif_pos rfl
  qsmul := qsmulRec _
#align module.End.division_ring Module.End.divisionRing

end LinearMap

-- Porting note: adding a namespace with all the new statements; existing result is not used in ML3
namespace JordanHolderModule

-- Porting note: jordanHolderModule was timing out so outlining the fields

/-- An isomorphism `X₂ / X₁ ∩ X₂ ≅ Y₂ / Y₁ ∩ Y₂` of modules for pairs
`(X₁,X₂) (Y₁,Y₂) : Submodule R M` -/
def Iso (X Y : Submodule R M × Submodule R M) : Prop :=
  Nonempty <| (X.2 ⧸ X.1.comap X.2.subtype) ≃ₗ[R] Y.2 ⧸ Y.1.comap Y.2.subtype

theorem iso_symm {X Y : Submodule R M × Submodule R M} : Iso X Y → Iso Y X :=
  fun ⟨f⟩ => ⟨f.symm⟩

theorem iso_trans {X Y Z : Submodule R M × Submodule R M} : Iso X Y → Iso Y Z → Iso X Z :=
  fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩

@[nolint unusedArguments]
theorem second_iso {X Y : Submodule R M} (_ : X ⋖ X ⊔ Y) :
    Iso (X,X ⊔ Y) (X ⊓ Y,Y) := by
  constructor
  rw [sup_comm, inf_comm]
  dsimp
  exact (LinearMap.quotientInfEquivSupQuotient Y X).symm

instance instJordanHolderLattice : JordanHolderLattice (Submodule R M) where
  IsMaximal := (· ⋖ ·)
  lt_of_isMaximal := CovBy.lt
  sup_eq_of_isMaximal hxz hyz := WCovBy.sup_eq hxz.wcovBy hyz.wcovBy
  isMaximal_inf_left_of_isMaximal_sup := inf_covBy_of_covBy_sup_of_covBy_sup_left
  Iso := Iso
  iso_symm := iso_symm
  iso_trans := iso_trans
  second_iso := second_iso
#align jordan_holder_module JordanHolderModule.instJordanHolderLattice

end JordanHolderModule
