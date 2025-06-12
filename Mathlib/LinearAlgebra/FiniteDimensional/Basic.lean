/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite dimensional vector spaces

Basic properties of finite dimensional vector spaces, of their dimensions, and
of linear maps on such spaces.

## Main definitions

Preservation of finite-dimensionality and formulas for the dimension are given for
- submodules (`FiniteDimensional.finiteDimensional_submodule`)
- quotients (for the dimension of a quotient, see `Submodule.finrank_quotient_add_finrank` in
  `Mathlib/LinearAlgebra/FiniteDimensional.lean`)
- linear equivs, in `LinearEquiv.finiteDimensional`

Basic properties of linear maps of a finite-dimensional vector space are given. Notably, the
equivalence of injectivity and surjectivity is proved in `LinearMap.injective_iff_surjective`,
and the equivalence between left-inverse and right-inverse in `LinearMap.mul_eq_one_comm`
and `LinearMap.comp_eq_id_comm`.

## Implementation notes

You should not assume that there has been any effort to state lemmas as generally as possible.

Plenty of the results hold for general fg modules or notherian modules, and they can be found in
`Mathlib/LinearAlgebra/FreeModule/Finite/Rank.lean` and `Mathlib/RingTheory/Noetherian.lean`.
-/

universe u v v' w

open Cardinal Function IsNoetherian Module Submodule

variable {K : Type u} {V : Type v}

namespace FiniteDimensional
section DivisionRing
variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

theorem _root_.LinearIndependent.lt_aleph0_of_finiteDimensional {ι : Type w} [FiniteDimensional K V]
    {v : ι → V} (h : LinearIndependent K v) : #ι < ℵ₀ :=
  h.lt_aleph0_of_finite

/-- If a submodule has maximal dimension in a finite dimensional space, then it is equal to the
whole space. -/
theorem _root_.Submodule.eq_top_of_finrank_eq [FiniteDimensional K V] {S : Submodule K V}
    (h : finrank K S = finrank K V) : S = ⊤ := by
  set bS := Basis.ofVectorSpace K S with bS_eq
  have : LinearIndepOn K id (Subtype.val '' Basis.ofVectorSpaceIndex K S) := by
    simpa [bS] using bS.linearIndependent.linearIndepOn_id.image
      (f := Submodule.subtype S) (by simp)
  set b := Basis.extend this with b_eq
  letI i1 : Fintype (this.extend _) :=
    (LinearIndependent.set_finite_of_isNoetherian (by simpa [b] using b.linearIndependent)).fintype
  letI i2 : Fintype (((↑) : S → V) '' Basis.ofVectorSpaceIndex K S) :=
    (LinearIndependent.set_finite_of_isNoetherian this).fintype
  letI i3 : Fintype (Basis.ofVectorSpaceIndex K S) :=
    (LinearIndependent.set_finite_of_isNoetherian
      (by simpa [bS] using bS.linearIndependent)).fintype
  have : (↑) '' Basis.ofVectorSpaceIndex K S = this.extend (Set.subset_univ _) :=
    Set.eq_of_subset_of_card_le (this.subset_extend _)
      (by
        rw [Set.card_image_of_injective _ Subtype.coe_injective, ← finrank_eq_card_basis bS, ←
            finrank_eq_card_basis b, h])
  rw [← b.span_eq, b_eq, Basis.coe_extend, Subtype.range_coe, ← this, ← Submodule.coe_subtype,
    span_image]
  have := bS.span_eq
  rw [bS_eq, Basis.coe_ofVectorSpace, Subtype.range_coe] at this
  rw [this, Submodule.map_top (Submodule.subtype S), range_subtype]

section

open Finset

variable {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
variable {W : Type v} [AddCommGroup W] [Module L W]

/-- A slight strengthening of `exists_nontrivial_relation_sum_zero_of_rank_succ_lt_card`
available when working over an ordered field:
we can ensure a positive coefficient, not just a nonzero coefficient.
-/
theorem exists_relation_sum_zero_pos_coefficient_of_finrank_succ_lt_card [FiniteDimensional L W]
    {t : Finset W} (h : finrank L W + 1 < t.card) :
    ∃ f : W → L, ∑ e ∈ t, f e • e = 0 ∧ ∑ e ∈ t, f e = 0 ∧ ∃ x ∈ t, 0 < f x := by
  obtain ⟨f, sum, total, nonzero⟩ :=
    Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card h
  exact ⟨f, sum, total, exists_pos_of_sum_zero_of_exists_nonzero f total nonzero⟩


end

/-- In a vector space with dimension 1, each set {v} is a basis for `v ≠ 0`. -/
@[simps repr_apply]
noncomputable def basisSingleton (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V)
    (hv : v ≠ 0) : Basis ι K V :=
  let b := Module.basisUnique ι h
  let h : b.repr v default ≠ 0 := mt Module.basisUnique_repr_eq_zero_iff.mp hv
  Basis.ofRepr
    { toFun := fun w => Finsupp.single default (b.repr w default / b.repr v default)
      invFun := fun f => f default • v
      map_add' := by simp [add_div]
      map_smul' := by simp [mul_div]
      left_inv := fun w => by
        apply_fun b.repr using b.repr.toEquiv.injective
        apply_fun Equiv.finsuppUnique
        simp only [LinearEquiv.map_smulₛₗ, Finsupp.coe_smul, Finsupp.single_eq_same,
          smul_eq_mul, Pi.smul_apply, Equiv.finsuppUnique_apply]
        exact div_mul_cancel₀ _ h
      right_inv := fun f => by
        ext
        simp only [LinearEquiv.map_smulₛₗ, Finsupp.coe_smul, Finsupp.single_eq_same,
          RingHom.id_apply, smul_eq_mul, Pi.smul_apply]
        exact mul_div_cancel_right₀ _ h }

@[simp]
theorem basisSingleton_apply (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v ≠ 0)
    (i : ι) : basisSingleton ι h v hv i = v := by
  cases Unique.uniq ‹Unique ι› i
  simp [basisSingleton]

@[simp]
theorem range_basisSingleton (ι : Type*) [Unique ι] (h : finrank K V = 1) (v : V) (hv : v ≠ 0) :
    Set.range (basisSingleton ι h v hv) = {v} := by rw [Set.range_unique, basisSingleton_apply]

end DivisionRing

end FiniteDimensional

section ZeroRank

variable [DivisionRing K] [AddCommGroup V] [Module K V]

theorem FiniteDimensional.of_rank_eq_nat {n : ℕ} (h : Module.rank K V = n) :
    FiniteDimensional K V :=
  Module.finite_of_rank_eq_nat h

theorem FiniteDimensional.of_rank_eq_zero (h : Module.rank K V = 0) : FiniteDimensional K V :=
  Module.finite_of_rank_eq_zero h

theorem FiniteDimensional.of_rank_eq_one (h : Module.rank K V = 1) : FiniteDimensional K V :=
  Module.finite_of_rank_eq_one h

variable (K V)

instance finiteDimensional_bot : FiniteDimensional K (⊥ : Submodule K V) :=
  .of_rank_eq_zero <| by simp

variable {K V}

end ZeroRank

namespace Submodule

open IsNoetherian Module

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A submodule contained in a finite-dimensional submodule is
finite-dimensional. -/
theorem finiteDimensional_of_le {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (h : S₁ ≤ S₂) :
    FiniteDimensional K S₁ :=
  (isNoetherian_of_le h).finite

/-- The inf of two submodules, the first finite-dimensional, is
finite-dimensional. -/
instance finiteDimensional_inf_left (S₁ S₂ : Submodule K V) [FiniteDimensional K S₁] :
    FiniteDimensional K (S₁ ⊓ S₂ : Submodule K V) :=
  finiteDimensional_of_le inf_le_left

/-- The inf of two submodules, the second finite-dimensional, is
finite-dimensional. -/
instance finiteDimensional_inf_right (S₁ S₂ : Submodule K V) [FiniteDimensional K S₂] :
    FiniteDimensional K (S₁ ⊓ S₂ : Submodule K V) :=
  finiteDimensional_of_le inf_le_right

/-- The sup of two finite-dimensional submodules is
finite-dimensional. -/
instance finiteDimensional_sup (S₁ S₂ : Submodule K V) [h₁ : FiniteDimensional K S₁]
    [h₂ : FiniteDimensional K S₂] : FiniteDimensional K (S₁ ⊔ S₂ : Submodule K V) := by
  unfold FiniteDimensional at *
  rw [finite_def] at *
  exact (fg_top _).2 (((fg_top S₁).1 h₁).sup ((fg_top S₂).1 h₂))

/-- The submodule generated by a finite supremum of finite dimensional submodules is
finite-dimensional.

Note that strictly this only needs `∀ i ∈ s, FiniteDimensional K (S i)`, but that doesn't
work well with typeclass search. -/
instance finiteDimensional_finset_sup {ι : Type*} (s : Finset ι) (S : ι → Submodule K V)
    [∀ i, FiniteDimensional K (S i)] : FiniteDimensional K (s.sup S : Submodule K V) := by
  refine
    @Finset.sup_induction _ _ _ _ s S (fun i => FiniteDimensional K ↑i) (finiteDimensional_bot K V)
      ?_ fun i _ => by infer_instance
  intro S₁ hS₁ S₂ hS₂
  exact Submodule.finiteDimensional_sup S₁ S₂

/-- The submodule generated by a supremum of finite dimensional submodules, indexed by a finite
sort is finite-dimensional. -/
instance finiteDimensional_iSup {ι : Sort*} [Finite ι] (S : ι → Submodule K V)
    [∀ i, FiniteDimensional K (S i)] : FiniteDimensional K ↑(⨆ i, S i) := by
  cases nonempty_fintype (PLift ι)
  rw [← iSup_plift_down, ← Finset.sup_univ_eq_iSup]
  exact Submodule.finiteDimensional_finset_sup _ _

end DivisionRing

end Submodule

section

variable [DivisionRing K] [AddCommGroup V] [Module K V]

instance finiteDimensional_finsupp {ι : Type*} [Finite ι] [FiniteDimensional K V] :
    FiniteDimensional K (ι →₀ V) :=
  Module.Finite.finsupp

end

namespace Submodule
variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- If a submodule is contained in a finite-dimensional
submodule with the same or smaller dimension, they are equal. -/
theorem eq_of_le_of_finrank_le {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (hle : S₁ ≤ S₂)
    (hd : finrank K S₂ ≤ finrank K S₁) : S₁ = S₂ := by
  rw [← LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)] at hd
  exact le_antisymm hle (Submodule.comap_subtype_eq_top.1
    (eq_top_of_finrank_eq (le_antisymm (comap (Submodule.subtype S₂) S₁).finrank_le hd)))

/-- If a submodule is contained in a finite-dimensional
submodule with the same dimension, they are equal. -/
theorem eq_of_le_of_finrank_eq {S₁ S₂ : Submodule K V} [FiniteDimensional K S₂] (hle : S₁ ≤ S₂)
    (hd : finrank K S₁ = finrank K S₂) : S₁ = S₂ :=
  eq_of_le_of_finrank_le hle hd.ge

end Submodule

namespace Subalgebra

variable {K L : Type*} [Field K] [Ring L] [Algebra K L] {F E : Subalgebra K L}
  [hfin : FiniteDimensional K E]

/-- If a subalgebra is contained in a finite-dimensional
subalgebra with the same or smaller dimension, they are equal. -/
theorem eq_of_le_of_finrank_le (h_le : F ≤ E) (h_finrank : finrank K E ≤ finrank K F) : F = E :=
  haveI : Module.Finite K (Subalgebra.toSubmodule E) := hfin
  toSubmodule_injective <| Submodule.eq_of_le_of_finrank_le h_le h_finrank

/-- If a subalgebra is contained in a finite-dimensional
subalgebra with the same dimension, they are equal. -/
theorem eq_of_le_of_finrank_eq (h_le : F ≤ E) (h_finrank : finrank K F = finrank K E) : F = E :=
  eq_of_le_of_finrank_le h_le h_finrank.ge

end Subalgebra

namespace LinearMap

open Module

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/-- On a finite-dimensional space, an injective linear map is surjective. -/
theorem surjective_of_injective [FiniteDimensional K V] {f : V →ₗ[K] V} (hinj : Injective f) :
    Surjective f := by
  have h := rank_range_of_injective _ hinj
  rw [← finrank_eq_rank, ← finrank_eq_rank, Nat.cast_inj] at h
  exact range_eq_top.1 (eq_top_of_finrank_eq h)

/-- The image under an onto linear map of a finite-dimensional space is also finite-dimensional. -/
theorem finiteDimensional_of_surjective [FiniteDimensional K V] (f : V →ₗ[K] V₂)
    (hf : LinearMap.range f = ⊤) : FiniteDimensional K V₂ :=
  Module.Finite.of_surjective f <| range_eq_top.1 hf

/-- The range of a linear map defined on a finite-dimensional space is also finite-dimensional. -/
instance finiteDimensional_range [FiniteDimensional K V] (f : V →ₗ[K] V₂) :
    FiniteDimensional K (LinearMap.range f) :=
  Module.Finite.range f

/-- On a finite-dimensional space, a linear map is injective if and only if it is surjective. -/
theorem injective_iff_surjective [FiniteDimensional K V] {f : V →ₗ[K] V} :
    Injective f ↔ Surjective f :=
  ⟨surjective_of_injective, fun hsurj =>
    let ⟨g, hg⟩ := f.exists_rightInverse_of_surjective (range_eq_top.2 hsurj)
    have : Function.RightInverse g f := LinearMap.ext_iff.1 hg
    (leftInverse_of_surjective_of_rightInverse (surjective_of_injective this.injective)
        this).injective⟩

lemma injOn_iff_surjOn {p : Submodule K V} [FiniteDimensional K p]
    {f : V →ₗ[K] V} (h : ∀ x ∈ p, f x ∈ p) :
    Set.InjOn f p ↔ Set.SurjOn f p p := by
  rw [Set.injOn_iff_injective, ← Set.MapsTo.restrict_surjective_iff h]
  change Injective (f.domRestrict p) ↔ Surjective (f.restrict h)
  simp [disjoint_iff, ← injective_iff_surjective]

theorem ker_eq_bot_iff_range_eq_top [FiniteDimensional K V] {f : V →ₗ[K] V} :
    LinearMap.ker f = ⊥ ↔ LinearMap.range f = ⊤ := by
  rw [range_eq_top, ker_eq_bot, injective_iff_surjective]

/-- In a finite-dimensional space, if linear maps are inverse to each other on one side then they
are also inverse to each other on the other side. -/
theorem mul_eq_one_of_mul_eq_one [FiniteDimensional K V] {f g : V →ₗ[K] V} (hfg : f * g = 1) :
    g * f = 1 := by
  have ginj : Injective g :=
    HasLeftInverse.injective ⟨f, fun x => show (f * g) x = (1 : V →ₗ[K] V) x by rw [hfg]⟩
  let ⟨i, hi⟩ := g.exists_rightInverse_of_surjective
    (range_eq_top.2 (injective_iff_surjective.1 ginj))
  have : f * (g * i) = f * 1 := congr_arg _ hi
  rw [← mul_assoc, hfg, one_mul, mul_one] at this; rwa [← this]

/-- In a finite-dimensional space, linear maps are inverse to each other on one side if and only if
they are inverse to each other on the other side. -/
theorem mul_eq_one_comm [FiniteDimensional K V] {f g : V →ₗ[K] V} : f * g = 1 ↔ g * f = 1 :=
  ⟨mul_eq_one_of_mul_eq_one, mul_eq_one_of_mul_eq_one⟩

/-- In a finite-dimensional space, linear maps are inverse to each other on one side if and only if
they are inverse to each other on the other side. -/
theorem comp_eq_id_comm [FiniteDimensional K V] {f g : V →ₗ[K] V} : f.comp g = id ↔ g.comp f = id :=
  mul_eq_one_comm

theorem comap_eq_sup_ker_of_disjoint {p : Submodule K V} [FiniteDimensional K p] {f : V →ₗ[K] V}
    (h : ∀ x ∈ p, f x ∈ p) (h' : Disjoint p (ker f)) :
    p.comap f = p ⊔ ker f := by
  refine le_antisymm (fun x hx ↦ ?_) (sup_le_iff.mpr ⟨h, ker_le_comap _⟩)
  obtain ⟨⟨y, hy⟩, hxy⟩ :=
    surjective_of_injective ((injective_restrict_iff_disjoint h).mpr h') ⟨f x, hx⟩
  replace hxy : f y = f x := by simpa [Subtype.ext_iff] using hxy
  exact Submodule.mem_sup.mpr ⟨y, hy, x - y, by simp [hxy], add_sub_cancel y x⟩

theorem ker_comp_eq_of_commute_of_disjoint_ker [FiniteDimensional K V] {f g : V →ₗ[K] V}
    (h : Commute f g) (h' : Disjoint (ker f) (ker g)) :
    ker (f ∘ₗ g) = ker f ⊔ ker g := by
  suffices ∀ x, f x = 0 → f (g x) = 0 by rw [ker_comp, comap_eq_sup_ker_of_disjoint _ h']; simpa
  intro x hx
  rw [← comp_apply, ← Module.End.mul_eq_comp, h.eq, Module.End.mul_apply, hx, map_zero]

theorem ker_noncommProd_eq_of_supIndep_ker [FiniteDimensional K V] {ι : Type*} {f : ι → V →ₗ[K] V}
    (s : Finset ι) (comm) (h : s.SupIndep fun i ↦ ker (f i)) :
    ker (s.noncommProd f comm) = ⨆ i ∈ s, ker (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Module.End.one_eq_id]
  | insert i s hi ih =>
    replace ih : ker (Finset.noncommProd s f <| Set.Pairwise.mono (s.subset_insert i) comm) =
        ⨆ x ∈ s, ker (f x) := ih _ (h.subset (s.subset_insert i))
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi, Module.End.mul_eq_comp,
      ker_comp_eq_of_commute_of_disjoint_ker]
    · simp_rw [Finset.mem_insert_coe, iSup_insert, Finset.mem_coe, ih]
    · exact s.noncommProd_commute _ _ _ fun j hj ↦
        comm (s.mem_insert_self i) (Finset.mem_insert_of_mem hj) (by aesop)
    · replace h := Finset.supIndep_iff_disjoint_erase.mp h i (s.mem_insert_self i)
      simpa [ih, hi, Finset.sup_eq_iSup] using h

end DivisionRing

end LinearMap

namespace LinearEquiv

open Module

variable [DivisionRing K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/-- The linear equivalence corresponding to an injective endomorphism. -/
noncomputable def ofInjectiveEndo (f : V →ₗ[K] V) (h_inj : Injective f) : V ≃ₗ[K] V :=
  LinearEquiv.ofBijective f ⟨h_inj, LinearMap.injective_iff_surjective.mp h_inj⟩

@[simp]
theorem coe_ofInjectiveEndo (f : V →ₗ[K] V) (h_inj : Injective f) :
    ⇑(ofInjectiveEndo f h_inj) = f :=
  rfl

@[simp]
theorem ofInjectiveEndo_right_inv (f : V →ₗ[K] V) (h_inj : Injective f) :
    f * (ofInjectiveEndo f h_inj).symm = 1 :=
  LinearMap.ext <| (ofInjectiveEndo f h_inj).apply_symm_apply

@[simp]
theorem ofInjectiveEndo_left_inv (f : V →ₗ[K] V) (h_inj : Injective f) :
    ((ofInjectiveEndo f h_inj).symm : V →ₗ[K] V) * f = 1 :=
  LinearMap.ext <| (ofInjectiveEndo f h_inj).symm_apply_apply

variable {V' : Type*} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
omit [FiniteDimensional K V]

/-- An injective linear map between finite-dimensional modules of equal rank
is a linear equivalence.

Unlike `LinearEquiv.ofFinrankEq` (which creates an *abstract* linear equivalence from `V` to `V'`),
this lemma improves a *given* injective linear map to a linear equivalence.
-/
noncomputable def ofInjectiveOfFinrankEq (f : V →ₗ[K] V') (hinj : Function.Injective f)
    (hrank : Module.finrank K V = Module.finrank K V') : V ≃ₗ[K] V' :=
  haveI : LinearMap.range f = ⊤ :=
    Submodule.eq_top_of_finrank_eq ((LinearMap.finrank_range_of_inj hinj).trans hrank)
  (ofInjective f hinj).trans (ofTop (LinearMap.range f) this)

@[simp]
lemma coe_ofInjectiveOfFinrankEq (f : V →ₗ[K] V') (hinj : Function.Injective f)
    (hrank : Module.finrank K V = Module.finrank K V') :
    (ofInjectiveOfFinrankEq f hinj hrank).toLinearMap = f :=
  rfl
end LinearEquiv

namespace LinearMap

variable [DivisionRing K] [AddCommGroup V] [Module K V]

theorem isUnit_iff_ker_eq_bot [FiniteDimensional K V] (f : V →ₗ[K] V) :
    IsUnit f ↔ (LinearMap.ker f) = ⊥ := by
  constructor
  · rintro ⟨u, rfl⟩
    exact LinearMap.ker_eq_bot_of_inverse u.inv_mul
  · intro h_inj
    rw [ker_eq_bot] at h_inj
    exact ⟨⟨f, (LinearEquiv.ofInjectiveEndo f h_inj).symm.toLinearMap,
      LinearEquiv.ofInjectiveEndo_right_inv f h_inj, LinearEquiv.ofInjectiveEndo_left_inv f h_inj⟩,
      rfl⟩

theorem isUnit_iff_range_eq_top [FiniteDimensional K V] (f : V →ₗ[K] V) :
    IsUnit f ↔ (LinearMap.range f) = ⊤ := by
  rw [isUnit_iff_ker_eq_bot, ker_eq_bot_iff_range_eq_top]

end LinearMap

open FiniteDimensional Module

section

variable [DivisionRing K] [AddCommGroup V] [Module K V]

theorem finrank_zero_iff_forall_zero [FiniteDimensional K V] : finrank K V = 0 ↔ ∀ x : V, x = 0 :=
  Module.finrank_zero_iff.trans (subsingleton_iff_forall_eq 0)

/-- If `ι` is an empty type and `V` is zero-dimensional, there is a unique `ι`-indexed basis. -/
noncomputable def basisOfFinrankZero [FiniteDimensional K V] {ι : Type*} [IsEmpty ι]
    (hV : finrank K V = 0) : Basis ι K V :=
  haveI : Subsingleton V := finrank_zero_iff.1 hV
  Basis.empty _

end

section

lemma FiniteDimensional.exists_mul_eq_one (F : Type*) {K : Type*} [Field F] [Ring K] [IsDomain K]
    [Algebra F K] [FiniteDimensional F K] {x : K} (H : x ≠ 0) : ∃ y, x * y = 1 := by
  have : Function.Surjective (LinearMap.mulLeft F x) :=
    LinearMap.injective_iff_surjective.1 fun y z => ((mul_right_inj' H).1 : x * y = x * z → y = z)
  exact this 1

/-- A domain that is module-finite as an algebra over a field is a division ring. -/
noncomputable def divisionRingOfFiniteDimensional (F K : Type*) [Field F] [Ring K] [IsDomain K]
    [Algebra F K] [FiniteDimensional F K] : DivisionRing K where
  __ := ‹IsDomain K›
  inv x :=
    letI := Classical.decEq K
    if H : x = 0 then 0 else Classical.choose <| FiniteDimensional.exists_mul_eq_one F H
  mul_inv_cancel x hx := show x * dite _ (h := _) _ _ = _ by
    rw [dif_neg hx]
    exact (Classical.choose_spec (FiniteDimensional.exists_mul_eq_one F hx) :)
  inv_zero := dif_pos rfl
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

lemma FiniteDimensional.isUnit (F : Type*) {K : Type*} [Field F] [Ring K] [IsDomain K]
    [Algebra F K] [FiniteDimensional F K] {x : K} (H : x ≠ 0) : IsUnit x :=
  let _ := divisionRingOfFiniteDimensional F K; H.isUnit

/-- An integral domain that is module-finite as an algebra over a field is a field. -/
noncomputable def fieldOfFiniteDimensional (F K : Type*) [Field F] [h : CommRing K] [IsDomain K]
    [Algebra F K] [FiniteDimensional F K] : Field K :=
  { divisionRingOfFiniteDimensional F K with
    toCommRing := h }

end
section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

section Span

open Submodule

theorem finrank_span_singleton {v : V} (hv : v ≠ 0) : finrank K (K ∙ v) = 1 := by
  apply le_antisymm
  · exact finrank_span_le_card ({v} : Set V)
  · rw [Nat.succ_le_iff, finrank_pos_iff]
    use ⟨v, mem_span_singleton_self v⟩, 0
    apply Subtype.coe_ne_coe.mp
    simp [hv]

/-- In a one-dimensional space, any vector is a multiple of any nonzero vector -/
lemma exists_smul_eq_of_finrank_eq_one
    (h : finrank K V = 1) {x : V} (hx : x ≠ 0) (y : V) :
    ∃ (c : K), c • x = y := by
  have : Submodule.span K {x} = ⊤ := by
    have : FiniteDimensional K V := .of_finrank_eq_succ h
    apply eq_top_of_finrank_eq
    rw [h]
    exact finrank_span_singleton hx
  have : y ∈ Submodule.span K {x} := by rw [this]; exact mem_top
  exact mem_span_singleton.1 this

theorem Set.finrank_mono [FiniteDimensional K V] {s t : Set V} (h : s ⊆ t) :
    s.finrank K ≤ t.finrank K :=
  Submodule.finrank_mono (span_mono h)

end Span

/-!
We now give characterisations of `finrank K V = 1` and `finrank K V ≤ 1`.
-/


section finrank_eq_one

/-- A vector space with a nonzero vector `v` has dimension 1 iff `v` spans.
-/
theorem finrank_eq_one_iff_of_nonzero (v : V) (nz : v ≠ 0) :
    finrank K V = 1 ↔ span K ({v} : Set V) = ⊤ :=
  ⟨fun h => by simpa using (basisSingleton Unit h v nz).span_eq, fun s =>
    finrank_eq_card_basis
      (Basis.mk (LinearIndepOn.id_singleton _ nz)
        (by simp [← s]))⟩

/-- A module with a nonzero vector `v` has dimension 1 iff every vector is a multiple of `v`.
-/
theorem finrank_eq_one_iff_of_nonzero' (v : V) (nz : v ≠ 0) :
    finrank K V = 1 ↔ ∀ w : V, ∃ c : K, c • v = w := by
  rw [finrank_eq_one_iff_of_nonzero v nz]
  apply span_singleton_eq_top_iff

-- We use the `LinearMap.CompatibleSMul` typeclass here, to encompass two situations:
-- * `A = K`
-- * `[Field K] [Algebra K A] [IsScalarTower K A V] [IsScalarTower K A W]`
theorem surjective_of_nonzero_of_finrank_eq_one {W A : Type*} [Semiring A] [Module A V]
    [AddCommGroup W] [Module K W] [Module A W] [LinearMap.CompatibleSMul V W K A]
    (h : finrank K W = 1) {f : V →ₗ[A] W} (w : f ≠ 0) : Surjective f := by
  change Surjective (f.restrictScalars K)
  obtain ⟨v, n⟩ := DFunLike.ne_iff.mp w
  intro z
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (f v) n).mp h z
  exact ⟨c • v, by simp⟩

end finrank_eq_one

end DivisionRing

section SubalgebraRank

open Module

variable {F E : Type*} [Field F] [Ring E] [Algebra F E]

/-- A `Subalgebra` is `FiniteDimensional` iff it is `FiniteDimensional` as a submodule. -/
theorem Subalgebra.finiteDimensional_toSubmodule {S : Subalgebra F E} :
    FiniteDimensional F (Subalgebra.toSubmodule S) ↔ FiniteDimensional F S :=
  Iff.rfl

alias ⟨FiniteDimensional.of_subalgebra_toSubmodule, FiniteDimensional.subalgebra_toSubmodule⟩ :=
  Subalgebra.finiteDimensional_toSubmodule

instance FiniteDimensional.finiteDimensional_subalgebra [FiniteDimensional F E]
    (S : Subalgebra F E) : FiniteDimensional F S :=
  FiniteDimensional.of_subalgebra_toSubmodule inferInstance

end SubalgebraRank

namespace Module

namespace End

variable [DivisionRing K] [AddCommGroup V] [Module K V]

theorem ker_pow_constant {f : End K V} {k : ℕ}
    (h : LinearMap.ker (f ^ k) = LinearMap.ker (f ^ k.succ)) :
    ∀ m, LinearMap.ker (f ^ k) = LinearMap.ker (f ^ (k + m))
  | 0 => by simp
  | m + 1 => by
    apply le_antisymm
    · rw [add_comm, pow_add]
      apply LinearMap.ker_le_ker_comp
    · rw [ker_pow_constant h m, add_comm m 1, ← add_assoc, pow_add, pow_add f k m,
        Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.ker_comp, LinearMap.ker_comp, h,
        Nat.add_one]

end End

end Module
