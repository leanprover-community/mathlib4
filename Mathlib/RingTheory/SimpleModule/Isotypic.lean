/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Order.CompleteSublattice
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Isotypic modules and isotypic components

## Main definitions

* `IsIsotypicOfType R M S` means that all simple submodules of the `R`-module `M`
  are isomorphic to `S`. Such a module `M` is isomorphic to a finsupp over `S`,
  see `IsIsotypicOfType.linearEquiv_finsupp`.

* `IsIsotypic R M` means that all simple submodules of the `R`-module `M`
  are isomorphic to each other.

* `isotypicComponent R M S` is the sum of all submodules of `M` isomorphic to `S`.

* `isotypicComponents R M` is the set of all nontrivial isotypic components of `M`
  (where `S` is taken to be simple submodules).

* `Submodule.IsFullyInvariant N` means that the submodule `N` of an `R`-module `M` is mapped into
  itself by all endomorphisms of `M`. The `fullyInvariantSubmodule`s of `M` form a complete
  lattice, which is atomic if `M` is semisimple, in which case the atoms are the isotypic
  components of `M`. A fully invariant submodule of a semiring as a module over itself
  is simply a two-sided ideal, see `isFullyInvariant_iff_isTwoSided`.

* `iSupIndep.ringEquiv`, `iSupIndep.algEquiv`: if `M` is the direct sum of fully invariant
  submodules `Nᵢ`, then `End R M` is isomorphic to `Πᵢ End R Nᵢ`. This can be applied to
  the isotypic components of a semisimple module `M`, yielding `IsSemisimpleModule.endAlgEquiv`.

## Keywords

isotypic component, fully invariant submodule

-/

universe u

variable (R₀ R : Type*) (M : Type u) (N S : Type*) [CommSemiring R₀]
  [Ring R] [Algebra R₀ R] [AddCommGroup M] [AddCommGroup N]
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

theorem IsIsotypic.submodule_linearEquiv_fun {m : Submodule R M} [Module.Finite R m] [Nontrivial m]
    (h : IsIsotypic R m) : ∃ (n : ℕ) (_ : NeZero n) (S : Submodule R M),
      S ≤ m ∧ IsSimpleModule R S ∧ Nonempty (m ≃ₗ[R] Fin n → S) :=
  have ⟨n, hn, S, _, ⟨e⟩⟩ := h.linearEquiv_fun
  let e' := S.equivMapOfInjective _ m.subtype_injective
  ⟨n, hn, _, m.map_subtype_le S, .congr e'.symm, ⟨e.trans <| .piCongrRight fun _ ↦ e'⟩⟩

end Finsupp

variable (R M S)

/-- If `S` is a simple `R`-module, the `S`-isotypic component in an `R`-module `M` is the sum of
all submodules of `M` isomorphic to `S`. -/
def isotypicComponent : Submodule R M := sSup {m | Nonempty (m ≃ₗ[R] S)}

/-- The set of all (nontrivial) isotypic components of a module. -/
def isotypicComponents : Set (Submodule R M) :=
  { m | ∃ S : Submodule R M, IsSimpleModule R S ∧ m = isotypicComponent R M S }

variable {R M}

theorem Submodule.le_isotypicComponent (m : Submodule R M) : m ≤ isotypicComponent R M m :=
  le_sSup ⟨.refl ..⟩

theorem bot_lt_isotypicComponent (S : Submodule R M) [IsSimpleModule R S] :
    ⊥ < isotypicComponent R M S :=
  (bot_lt_iff_ne_bot.mpr <| (S.nontrivial_iff_ne_bot).mp <| IsSimpleModule.nontrivial R S).trans_le
    S.le_isotypicComponent

theorem bot_lt_isotypicComponents {m : Submodule R M} (h : m ∈ isotypicComponents R M) : ⊥ < m := by
  obtain ⟨_, _, rfl⟩ := h; exact bot_lt_isotypicComponent ..

instance (c : isotypicComponents R M) : Nontrivial c :=
  Submodule.nontrivial_iff_ne_bot.mpr (bot_lt_isotypicComponents c.2).ne'

instance [IsSemisimpleModule R S] : IsSemisimpleModule R (isotypicComponent R M S) := by
  rw [isotypicComponent, sSup_eq_iSup]
  refine isSemisimpleModule_biSup_of_isSemisimpleModule_submodule fun m ⟨e⟩ ↦ ?_
  have := IsSemisimpleModule.congr e
  infer_instance

instance (c : isotypicComponents R M) : IsSemisimpleModule R c := by
  obtain ⟨c, S, _, rfl⟩ := c; infer_instance

variable {S} in
theorem LinearEquiv.isotypicComponent_eq (e : N ≃ₗ[R] S) :
    isotypicComponent R M N = isotypicComponent R M S :=
  congr_arg sSup <| Set.ext fun _ ↦ Nonempty.congr (·.trans e) (·.trans e.symm)

section SimpleSubmodule

variable (N : Submodule R M) [IsSimpleModule R N] (s : Set (Submodule R M))

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

variable (R M) [IsSimpleModule R S]

local instance (m : {m : Submodule R M | Nonempty (m ≃ₗ[R] S)}) : IsSimpleModule R m :=
  .congr m.2.some

protected theorem IsIsotypicOfType.isotypicComponent :
    IsIsotypicOfType R (isotypicComponent R M S) S :=
  isIsotypicOfType_submodule_iff.mpr fun m h _ ↦
    have ⟨_, ⟨e⟩, ⟨e'⟩⟩ := m.linearEquiv_of_le_sSup _ h
    ⟨e'.trans e⟩

protected theorem IsIsotypic.isotypicComponent : IsIsotypic R (isotypicComponent R M S) :=
  (IsIsotypicOfType.isotypicComponent R M S).isIsotypic

variable {R M} in
protected theorem IsIsotypic.isotypicComponents {m : Submodule R M}
    (h : m ∈ isotypicComponents R M) : IsIsotypic R m := by
  obtain ⟨_, _, rfl⟩ := h; exact .isotypicComponent R M _

variable {R M} in
theorem eq_isotypicComponent_of_le {S c : Submodule R M} (hc : c ∈ isotypicComponents R M)
    [IsSimpleModule R S] (le : S ≤ c) : c = isotypicComponent R M S := by
  obtain ⟨S', _, rfl⟩ := hc
  have ⟨e⟩ := isIsotypicOfType_submodule_iff.mp (.isotypicComponent R M S') _ le
  exact e.symm.isotypicComponent_eq

theorem sSupIndep_isotypicComponents : sSupIndep (isotypicComponents R M) :=
  fun c hc ↦ disjoint_iff.mpr <| of_not_not fun ne ↦ by
    set s := isotypicComponents R M \ {c}
    have : IsSemisimpleModule R c := by obtain ⟨S, _, rfl⟩ := hc; infer_instance
    have := IsSemisimpleModule.of_injective _
      (Submodule.inclusion_injective (inf_le_left : c ⊓ sSup s ≤ c))
    have (c : s) : IsSemisimpleModule R c := by obtain ⟨_, ⟨_, _, rfl⟩, _⟩ := c; infer_instance
    have ⟨S, le, _⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le _).resolve_left ne
    have ⟨c', hc', S', le', ⟨e⟩⟩ := S.le_linearEquiv_of_le_sSup _ (le.trans inf_le_right)
    have := IsSimpleModule.congr e.symm
    refine hc'.2 ?_
    rw [eq_isotypicComponent_of_le hc (le.trans inf_le_left), eq_isotypicComponent_of_le hc'.1 le']
    exact e.symm.isotypicComponent_eq

instance [IsNoetherian R M] : Finite (isotypicComponents R M) :=
  Set.finite_coe_iff.mpr <| WellFoundedGT.finite_of_sSupIndep (sSupIndep_isotypicComponents R M)

variable {R M S}

theorem IsIsotypicOfType.of_isotypicComponent_eq_top (h : isotypicComponent R M S = ⊤) :
    IsIsotypicOfType R M S :=
  fun m _ ↦ have ⟨_, ⟨e⟩, ⟨e'⟩⟩ := m.linearEquiv_of_sSup_eq_top _ h; ⟨e'.trans e⟩

theorem Submodule.map_le_isotypicComponent (S : Submodule R M) [IsSimpleModule R S]
    (f : M →ₗ[R] N) : S.map f ≤ isotypicComponent R N S := by
  conv_lhs => rw [← S.range_subtype, ← LinearMap.range_comp]
  obtain inj | eq := (f ∘ₗ S.subtype).injective_or_eq_zero
  · exact le_sSup ⟨.symm <| .ofInjective _ inj⟩
  · simp_rw [eq, LinearMap.range_zero, bot_le]

variable (S) in
theorem LinearMap.le_comap_isotypicComponent (f : M →ₗ[R] N) :
    isotypicComponent R M S ≤ (isotypicComponent R N S).comap f :=
  sSup_le fun m ⟨e⟩ ↦ Submodule.map_le_iff_le_comap.mp <|
    have := IsSimpleModule.congr e
    (m.map_le_isotypicComponent f).trans_eq e.isotypicComponent_eq

section IsFullyInvariant

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A submodule `N` an `R`-module `M` is fully invariant if `N` is mapped into itself by all
`R`-linear endomorphisms of `M`.

If `M` is semisimple, this is equivalent to `N` being a sum of isotypic components of `M`:
see `isFullyInvariant_iff_sSup_isotypicComponents`. -/
def Submodule.IsFullyInvariant (N : Submodule R M) : Prop :=
  ∀ f : Module.End R M, N ≤ N.comap f

theorem isFullyInvariant_iff_isTwoSided {I : Ideal R} : I.IsFullyInvariant ↔ I.IsTwoSided := by
  simpa only [Submodule.IsFullyInvariant, ← MulOpposite.opEquiv.trans (RingEquiv.moduleEndSelf R
    |>.toEquiv) |>.forall_congr_right, SetLike.le_def, I.isTwoSided_iff] using forall_comm

variable (R M) in
/-- The fully invariant submodules of a module form a complete sublattice in the lattice of
submodules. -/
def fullyInvariantSubmodule : CompleteSublattice (Submodule R M) :=
  .mk' { N : Submodule R M | N.IsFullyInvariant }
    (fun _s hs f ↦ sSup_le fun _N hN ↦ (hs hN f).trans <| Submodule.comap_mono <| le_sSup hN)
    fun _s hs f ↦ Submodule.map_le_iff_le_comap.mp <| le_sInf fun _N hN ↦
      Submodule.map_le_iff_le_comap.mpr <| (sInf_le hN).trans (hs hN f)

theorem mem_fullyInvariantSubmodule_iff {m : Submodule R M} :
    m ∈ fullyInvariantSubmodule R M ↔ m.IsFullyInvariant := Iff.rfl

end IsFullyInvariant

section Equiv

variable {ι : Type*} [DecidableEq ι] {N : ι → Submodule R M}
  (ind : iSupIndep N) (iSup_top : ⨆ i, N i = ⊤) (invar : ∀ i, (N i).IsFullyInvariant)

/-- If an `R`-module `M` is the direct sum of fully invariant submodules `Nᵢ`,
then `End R M` is isomorphic to `Πᵢ End R Nᵢ` as a ring. -/
noncomputable def iSupIndep.ringEquiv : Module.End R M ≃+* Π i, Module.End R (N i) where
  toFun f i := f.restrict (invar i f)
  invFun f := letI e := ind.linearEquiv iSup_top; e ∘ₗ DFinsupp.mapRange.linearMap f ∘ₗ e.symm
  left_inv f := LinearMap.ext fun x ↦ by
    exact Submodule.iSup_induction _ (motive := (_ = f ·)) (iSup_top ▸ Submodule.mem_top (x := x))
      (fun i x h ↦ by simp [ind.linearEquiv_symm_apply _ h]) (by simp)
      fun _ _ h₁ h₂ ↦ by simpa only [map_add] using congr($h₁ + $h₂)
  right_inv f := by ext i x; simp [ind.linearEquiv_symm_apply _ x.2]
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- If an `R`-module `M` is the direct sum of fully invariant submodules `Nᵢ`,
then `End R M` is isomorphic to `Πᵢ End R Nᵢ` as an algebra. -/
noncomputable def iSupIndep.algEquiv [Module R₀ M] [IsScalarTower R₀ R M] :
    Module.End R M ≃ₐ[R₀] Π i, Module.End R (N i) where
  __ := ind.ringEquiv iSup_top invar
  commutes' _ := rfl

end Equiv

variable (R M S) in
protected theorem Submodule.IsFullyInvariant.isotypicComponent :
    (isotypicComponent R M S).IsFullyInvariant :=
  LinearMap.le_comap_isotypicComponent S

theorem Submodule.IsFullyInvariant.of_mem_isotypicComponents {m : Submodule R M}
    (h : m ∈ isotypicComponents R M) : m.IsFullyInvariant := by
  obtain ⟨_, _, rfl⟩ := h; exact .isotypicComponent R M _

variable (R M) in
/-- The Galois coinsertion from sets of isotypic components to fully invariant submodules. -/
def GaloisCoinsertion.setIsotypicComponents :
    GaloisCoinsertion (α := Set (isotypicComponents R M)) (β := fullyInvariantSubmodule R M)
      (fun s ↦ ⨆ c ∈ s, ⟨c, .of_mem_isotypicComponents c.2⟩) fun m ↦ {c | c.1 ≤ m} :=
  GaloisConnection.toGaloisCoinsertion (fun _ _ ↦ iSup₂_le_iff) fun s c hc ↦ of_not_not fun hcs ↦
    (bot_lt_isotypicComponents c.2).ne' <| (sSupIndep_isotypicComponents R M c.2).eq_bot_of_le <|
    hc.trans <| by
      simp_rw [CompleteSublattice.coe_iSup, iSup₂_le_iff]
      exact fun c hc ↦ le_sSup ⟨c.2, Subtype.coe_ne_coe.mpr (ne_of_mem_of_not_mem hc hcs)⟩

theorem le_isotypicComponent_iff [IsSemisimpleModule R M] {m : Submodule R M} :
    m ≤ isotypicComponent R M S ↔ IsIsotypicOfType R m S where
  mp h := .of_injective (.isotypicComponent R M S) _ (Submodule.inclusion_injective h)
  mpr h := (IsSemisimpleModule.sSup_simples_le m).ge.trans
    (sSup_le_sSup fun S ⟨_, le⟩ ↦ isIsotypicOfType_submodule_iff.mp h S le)

theorem isotypicComponent_eq_top_iff [IsSemisimpleModule R M] :
    isotypicComponent R M S = ⊤ ↔ IsIsotypicOfType R M S := by
  rw [← top_le_iff, le_isotypicComponent_iff, Submodule.topEquiv.isIsotypicOfType_iff]

open IsSemisimpleModule in
theorem isFullyInvariant_iff_le_imp_isotypicComponent_le [IsSemisimpleModule R M]
    {m : Submodule R M} :
    m.IsFullyInvariant ↔ ∀ S ≤ m, [IsSimpleModule R S] → isotypicComponent R M S ≤ m where
  mp h S le _ := sSup_le fun S' ⟨e⟩ ↦ by
    have ⟨p, eq⟩ := extension_property _ S.subtype_injective (S'.subtype ∘ₗ e.symm)
    refine le_trans ?_ (Submodule.map_le_iff_le_comap.mpr (le.trans (h p)))
    rw [← S.range_subtype, ← LinearMap.range_comp, eq, e.symm.range_comp, S'.range_subtype]
  mpr h f := (sSup_simples_le m).ge.trans <| sSup_le fun S ⟨_, le⟩ ↦
    Submodule.map_le_iff_le_comap.mp ((S.map_le_isotypicComponent f).trans (h S le))

theorem eq_isotypicComponent_iff [IsSemisimpleModule R M] {m : Submodule R M} (ne : m ≠ ⊥) :
    m = isotypicComponent R M S ↔ IsIsotypicOfType R m S ∧ m.IsFullyInvariant where
  mp := by rintro rfl; exact ⟨.isotypicComponent R M S, .isotypicComponent R M S⟩
  mpr := fun ⟨iso, invar⟩ ↦ (le_isotypicComponent_iff.mpr iso).antisymm <|
    have ⟨S', le, _⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le m).resolve_left ne
    (isIsotypicOfType_submodule_iff.mp iso S' le).some.symm.isotypicComponent_eq.trans_le
      (isFullyInvariant_iff_le_imp_isotypicComponent_le.mp invar _ le)

end IsSimpleModule

variable [IsSemisimpleModule R M]

open IsSemisimpleModule

theorem isIsotypic_iff_isFullyInvariant_imp_bot_or_top :
    IsIsotypic R M ↔ ∀ N : Submodule R M, N.IsFullyInvariant → N = ⊥ ∨ N = ⊤ where
  mp h N hN := (eq_bot_or_exists_simple_le N).imp_right fun ⟨S, le, _⟩ ↦ top_unique <|
    (isotypicComponent_eq_top_iff.mpr (h S)).ge.trans
    ((isFullyInvariant_iff_le_imp_isotypicComponent_le.mp hN) _ le)
  mpr h S _ := isotypicComponent_eq_top_iff.mp <|
    (h _ (.isotypicComponent R M S)).resolve_left (bot_lt_isotypicComponent S).ne'

theorem mem_isotypicComponents_iff {m : Submodule R M} :
    m ∈ isotypicComponents R M ↔ IsIsotypic R m ∧ m.IsFullyInvariant ∧ m ≠ ⊥ where
  mp := by rintro ⟨S, _, rfl⟩; exact ⟨.isotypicComponent R M S,
    .isotypicComponent R M S, (bot_lt_isotypicComponent S).ne'⟩
  mpr := fun ⟨iso, invar, ne⟩ ↦
    have ⟨S, le, simple⟩ := (eq_bot_or_exists_simple_le m).resolve_left ne
    ⟨S, simple, (eq_isotypicComponent_iff ne).mpr ⟨isIsotypic_submodule_iff.mp iso S le, invar⟩⟩

/-- Sets of isotypic components in a semisimple module are in order-preserving 1-1
correspondence with fully invariant submodules. Consequently, the fully invariant submodules
form a complete atomic Boolean algebra. -/
@[simps] def OrderIso.setIsotypicComponents :
    Set (isotypicComponents R M) ≃o fullyInvariantSubmodule R M where
  toFun s := ⨆ c ∈ s, ⟨c, .of_mem_isotypicComponents c.2⟩
  invFun m := { c | c.1 ≤ m }
  left_inv := (GaloisCoinsertion.setIsotypicComponents R M).u_l_eq
  right_inv m := (iSup₂_le fun _ ↦ by exact id).antisymm <| (sSup_simples_le m.1).ge.trans <|
      sSup_le fun S ⟨simple, le⟩ ↦ S.le_isotypicComponent.trans <| by
    let c : isotypicComponents R M := ⟨_, S, simple, rfl⟩
    simp_rw [← show c.1 = isotypicComponent R M S from rfl, CompleteSublattice.coe_iSup]
    exact le_biSup _ (isFullyInvariant_iff_le_imp_isotypicComponent_le.mp m.2 _ le)
  map_rel_iff' := (GaloisCoinsertion.setIsotypicComponents R M).l_le_l_iff

theorem isFullyInvariant_iff_sSup_isotypicComponents {m : Submodule R M} :
    m.IsFullyInvariant ↔ ∃ s ⊆ isotypicComponents R M, m = sSup s := by
  refine ⟨fun h ↦ ⟨OrderIso.setIsotypicComponents.symm ⟨m, h⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · rintro _ ⟨c, _, rfl⟩; exact c.2
  · convert Subtype.ext_iff.mp (OrderIso.setIsotypicComponents.right_inv ⟨m, h⟩).symm
    simp [sSup_image, OrderIso.setIsotypicComponents, OrderIso.symm]
  · rintro ⟨_, hs, rfl⟩
    exact (fullyInvariantSubmodule R M).sSupClosed fun _ h ↦ .of_mem_isotypicComponents (hs h)

variable (R M) in
theorem sSup_isotypicComponents : sSup (isotypicComponents R M) = ⊤ :=
  have ⟨_, h, eq⟩ := isFullyInvariant_iff_sSup_isotypicComponents.mp
    (fullyInvariantSubmodule R M).top_mem
  top_unique <| eq.le.trans (sSup_le_sSup h)

namespace IsSemisimpleModule

variable (R M) [Module R₀ M] [IsScalarTower R₀ R M] [DecidableEq (isotypicComponents R M)]

/-- The endomorphism algebra of a semisimple module is the direct product of the endomorphism
algebras of its isotypic components. -/
noncomputable def endAlgEquiv :
    Module.End R M ≃ₐ[R₀] Π c : isotypicComponents R M, Module.End R c.1 :=
  ((sSupIndep_iff _).mp <| sSupIndep_isotypicComponents R M).algEquiv R₀
    ((sSup_eq_iSup' _).symm.trans <| sSup_isotypicComponents R M) (.of_mem_isotypicComponents ·.2)

/-- The endomorphism ring of a semisimple module is the direct product of the endomorphism rings
of its isotypic components. -/
noncomputable def endRingEquiv :
    Module.End R M ≃+* Π c : isotypicComponents R M, Module.End R c.1 :=
  (endAlgEquiv ℕ R M).toRingEquiv

end IsSemisimpleModule
