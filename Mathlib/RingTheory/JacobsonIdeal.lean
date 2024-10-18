/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Devon Tuma, Wojciech Nawrocki
-/
import Mathlib.RingTheory.Ideal.IsPrimary
import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Jacobson radical

The Jacobson radical of a module `M` over a ring `R` is defined to be the intersection of all
maximal submodules of `M`. The Jacobson radical of a ring `R` is the Jacobson radical of `R` as
an `R`-module, which is equal to the intersection of all maximal left ideals of `R`.
This is similar to how the nilradical of a commutative ring `R` is equal to the intersection
of all prime ideals of `R`.

We can extend the idea of the nilradical of `R` to ideals of `R`,
by letting the nilradical of an ideal `I` be the intersection of prime ideals containing `I`.
Under this extension, the original nilradical is the radical of the zero ideal `⊥`.
Here we define the Jacobson radical of an ideal `I` in a similar way,
as the intersection of maximal ideals containing `I`.

## Main definitions

Let `R` be a ring, `I` a left ideal of `R`, and `M` an `R`-module.

* `Module.jacobson R M` is the Jacobson radical of `M`,
i.e. the infimum of all maximal submodules in `M`.

* `Ideal.jacobson I` is the Jacobson radical, i.e. the infimum of all maximal ideals containing `I`.

* `Ideal.IsLocal I` is the proposition that the jacobson radical of `I` is itself a maximal ideal

Furthermore when `I` is a two-sided ideal of `R`

* `TwoSidedIdeal.jacobson I` is the Jacobson radical as a two-sided ideal

## Main statements

* `mem_jacobson_iff` gives a characterization of members of the jacobson of I

* `Ideal.isLocal_of_isMaximal_radical`: if the radical of I is maximal then so is the jacobson
  radical

## Tags

Jacobson, Jacobson radical, Local Ideal

-/


universe u v

namespace Module

open Submodule

variable (R R₂ M M₂ : Type*) [Ring R] [Ring R₂]
variable [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]
variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂] (f : F)

/-- The Jacobson radical of an `R`-module `M` is the infimum of all maximal submodules in `M`. -/
def jacobson : Submodule R M :=
  sInf { m : Submodule R M | IsCoatom m }

variable {R R₂ M M₂}

theorem le_comap_jacobson : jacobson R M ≤ comap f (jacobson R₂ M₂) := by
  conv_rhs => rw [jacobson, sInf_eq_iInf', comap_iInf]
  refine le_iInf_iff.mpr fun S m hm ↦ ?_
  obtain h | h := isCoatom_comap_or_eq_top f S.2
  · exact mem_sInf.mp hm _ h
  · simpa only [h] using mem_top

theorem map_jacobson_le : map f (jacobson R M) ≤ jacobson R₂ M₂ :=
  map_le_iff_le_comap.mpr (le_comap_jacobson f)

include τ₁₂ in
theorem jacobson_eq_bot_of_injective (inj : Function.Injective f) (h : jacobson R₂ M₂ = ⊥) :
    jacobson R M = ⊥ :=
  le_bot_iff.mp <| (le_comap_jacobson f).trans <| by
    simp_rw [h, comap_bot, ((LinearMapClass.ker_eq_bot _).mpr inj).le]

variable {f}

theorem map_jacobson_of_ker_le (surj : Function.Surjective f)
    (le : LinearMap.ker f ≤ jacobson R M) :
    map f (jacobson R M) = jacobson R₂ M₂ :=
  le_antisymm (map_jacobson_le f) <| by
    rw [jacobson, sInf_eq_iInf'] at le
    conv_rhs => rw [jacobson, sInf_eq_iInf', map_iInf_of_ker_le surj le]
    exact le_iInf fun m ↦ sInf_le (isCoatom_map_of_ker_le surj (le_iInf_iff.mp le m) m.2)

theorem comap_jacobson_of_ker_le (surj : Function.Surjective f)
    (le : LinearMap.ker f ≤ jacobson R M) :
    comap f (jacobson R₂ M₂) = jacobson R M := by
  rw [← map_jacobson_of_ker_le surj le, comap_map_eq_self le]

theorem map_jacobson_of_bijective (hf : Function.Bijective f) :
    map f (jacobson R M) = jacobson R₂ M₂ :=
  map_jacobson_of_ker_le hf.2 <| by simp_rw [(LinearMapClass.ker_eq_bot _).mpr hf.1, bot_le]

theorem comap_jacobson_of_bijective (hf : Function.Bijective f) :
    comap f (jacobson R₂ M₂) = jacobson R M :=
  comap_jacobson_of_ker_le hf.2 <| by simp_rw [(LinearMapClass.ker_eq_bot _).mpr hf.1, bot_le]

theorem jacobson_quotient_of_le {N : Submodule R M} (le : N ≤ jacobson R M) :
    jacobson R (M ⧸ N) = map N.mkQ (jacobson R M) :=
  (map_jacobson_of_ker_le N.mkQ_surjective <| by rwa [ker_mkQ]).symm

theorem jacobson_le_of_eq_bot {N : Submodule R M} (h : jacobson R (M ⧸ N) = ⊥) :
    jacobson R M ≤ N := by
  simp_rw [← N.ker_mkQ, ← comap_bot, ← h, le_comap_jacobson]

variable (R M)

theorem jacobson_quotient_jacobson : jacobson R (M ⧸ jacobson R M) = ⊥ := by
  rw [jacobson_quotient_of_le le_rfl, mkQ_map_self]

theorem jacobson_lt_top [Nontrivial M] [IsCoatomic (Submodule R M)] : jacobson R M < ⊤ := by
  obtain ⟨m, hm, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule R M)).resolve_left bot_ne_top
  exact (sInf_le <| Set.mem_setOf.mpr hm).trans_lt hm.1.lt_top

example [Nontrivial M] [Module.Finite R M] : jacobson R M < ⊤ := jacobson_lt_top R M

variable {ι} (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

theorem jacobson_pi_le : jacobson R (Π i, M i) ≤ Submodule.pi Set.univ (jacobson R <| M ·) := by
  simp_rw [← iInf_comap_proj, jacobson, sInf_eq_iInf', comap_iInf, le_iInf_iff]
  intro i m
  exact iInf_le_of_le ⟨_, (isCoatom_comap_iff <| LinearMap.proj_surjective i).mpr m.2⟩ le_rfl

/-- A product of modules with trivial Jacobson radical (e.g. simple modules) also has trivial
Jacobson radical. -/
theorem jacobson_pi_eq_bot (h : ∀ i, jacobson R (M i) = ⊥) : jacobson R (∀ i, M i) = ⊥ :=
  le_bot_iff.mp <| (jacobson_pi_le R M).trans <| by simp_rw [h, pi_univ_bot, le_rfl]

end Module

section

variable (R R₂ : Type*) [Ring R] [Ring R₂] (f : R →+* R₂) [RingHomSurjective f]
variable (M : Type*) [AddCommGroup M] [Module R M]

namespace Ring

abbrev jacobson : Ideal R := Module.jacobson R R

instance : (jacobson R).IsTwoSided :=
  ⟨fun b ha ↦ Module.le_comap_jacobson (f := LinearMap.toSpanSingleton R R b) ha⟩

variable {R R₂}

theorem le_comap_jacobson : jacobson R ≤ Ideal.comap f (jacobson R₂) :=
  Module.le_comap_jacobson f.toSemilinearMap

theorem map_jacobson_le : Submodule.map f.toSemilinearMap (jacobson R) ≤ jacobson R₂ :=
  Module.map_jacobson_le f.toSemilinearMap

variable {f} in
theorem map_jacobson_of_ker_le (le : RingHom.ker f ≤ jacobson R) :
    Submodule.map f.toSemilinearMap (jacobson R) = jacobson R₂ :=
  Module.map_jacobson_of_ker_le f.surjective le

theorem coe_jacobson_quotient (I : Ideal R) [I.IsTwoSided] :
    (jacobson (R ⧸ I) : Set (R ⧸ I)) = Module.jacobson R (R ⧸ I) := by
  let f : R ⧸ I →ₛₗ[Ideal.Quotient.mk I] R ⧸ I := ⟨AddHom.id _, fun _ _ ↦ rfl⟩
  rw [jacobson, ← Module.map_jacobson_of_ker_le (f := f) Function.surjective_id]
  · apply Set.image_id
  · rintro _ rfl; exact zero_mem _

theorem jacobson_quotient_of_le {I : Ideal R} [I.IsTwoSided] (le : I ≤ jacobson R) :
    jacobson (R ⧸ I) = Submodule.map (Ideal.Quotient.mk I).toSemilinearMap (jacobson R) :=
  .symm <| Module.map_jacobson_of_ker_le (by exact Ideal.Quotient.mk_surjective) <| by
    rwa [← I.ker_mkQ] at le

theorem jacobson_le_of_eq_bot {I : Ideal R} [I.IsTwoSided] (h : jacobson (R ⧸ I) = ⊥) :
    jacobson R ≤ I :=
  Module.jacobson_le_of_eq_bot <| by
    rw [← le_bot_iff, ← SetLike.coe_subset_coe] at h ⊢
    rwa [← coe_jacobson_quotient]

variable (R)

theorem jacobson_quotient_jacobson : jacobson (R ⧸ jacobson R) = ⊥ :=
  (jacobson_quotient_of_le le_rfl).trans <| SetLike.ext' <| by
    apply SetLike.ext'_iff.mp (jacobson R).mkQ_map_self

theorem jacobson_lt_top [Nontrivial R] : jacobson R < ⊤ := Module.jacobson_lt_top R R

theorem jacobson_smul_top_le : jacobson R • (⊤ : Submodule R M) ≤ Module.jacobson R M :=
  Submodule.smul_le.mpr fun _ hr m _ ↦ Module.le_comap_jacobson (LinearMap.toSpanSingleton R M m) hr

end Ring

namespace Submodule

variable {R M}

theorem jacobson_smul_lt_top [Nontrivial M] [IsCoatomic (Submodule R M)] (N : Submodule R M) :
    Ring.jacobson R • N < ⊤ :=
  ((smul_mono_right _ le_top).trans <| Ring.jacobson_smul_top_le R M).trans_lt
    (Module.jacobson_lt_top R M)

theorem FG.jacobson_smul_lt {N : Submodule R M} (ne_bot : N ≠ ⊥) (fg : N.FG) :
    Ring.jacobson R • N < N := by
  rw [← Module.Finite.iff_fg] at fg
  rw [← nontrivial_iff_ne_bot] at ne_bot
  convert map_strictMono_of_injective N.injective_subtype (jacobson_smul_lt_top ⊤)
  on_goal 1 => rw [map_smul'']
  all_goals rw [Submodule.map_top, range_subtype]

/-- A form of Nakayama's lemma for modules over noncommutative rings. -/
theorem FG.eq_bot_of_le_jacobson_smul {N : Submodule R M} (fg : N.FG)
    (le : N ≤ Ring.jacobson R • N) : N = ⊥ := by
  contrapose! le; exact (jacobson_smul_lt le fg).not_le

end Submodule

end

namespace Ideal

variable {R : Type u} {S : Type v}

open Polynomial

section Jacobson

section Ring

variable [Ring R] [Ring S] {I : Ideal R}

/-- The Jacobson radical of `I` is the infimum of all maximal (left) ideals containing `I`. -/
def jacobson (I : Ideal R) : Ideal R :=
  sInf { J : Ideal R | I ≤ J ∧ IsMaximal J }

theorem le_jacobson : I ≤ jacobson I := fun _ hx => mem_sInf.mpr fun _ hJ => hJ.left hx

@[simp]
theorem jacobson_idem : jacobson (jacobson I) = jacobson I :=
  le_antisymm (sInf_le_sInf fun _ hJ => ⟨sInf_le hJ, hJ.2⟩) le_jacobson

@[simp]
theorem jacobson_top : jacobson (⊤ : Ideal R) = ⊤ :=
  eq_top_iff.2 le_jacobson

theorem jacobson_bot : jacobson (⊥ : Ideal R) = Ring.jacobson R := by
  simp_rw [jacobson, Ring.jacobson, Module.jacobson, bot_le, true_and, isMaximal_def]

@[simp]
theorem jacobson_eq_top_iff : jacobson I = ⊤ ↔ I = ⊤ :=
  ⟨fun H =>
    by_contradiction fun hi => let ⟨M, hm, him⟩ := exists_le_maximal I hi
      lt_top_iff_ne_top.1
        (lt_of_le_of_lt (show jacobson I ≤ M from sInf_le ⟨him, hm⟩) <|
          lt_top_iff_ne_top.2 hm.ne_top) H,
    fun H => eq_top_iff.2 <| le_sInf fun _ ⟨hij, _⟩ => H ▸ hij⟩

theorem jacobson_eq_bot : jacobson I = ⊥ → I = ⊥ := fun h => eq_bot_iff.mpr (h ▸ le_jacobson)

theorem jacobson_eq_self_of_isMaximal [H : IsMaximal I] : I.jacobson = I :=
  le_antisymm (sInf_le ⟨le_of_eq rfl, H⟩) le_jacobson

instance (priority := 100) jacobson.isMaximal [H : IsMaximal I] : IsMaximal (jacobson I) :=
  ⟨⟨fun htop => H.1.1 (jacobson_eq_top_iff.1 htop), fun _ hJ =>
    H.1.2 _ (lt_of_le_of_lt le_jacobson hJ)⟩⟩

theorem mem_jacobson_iff {x : R} : x ∈ jacobson I ↔ ∀ y, ∃ z, z * y * x + z - 1 ∈ I :=
  ⟨fun hx y =>
    by_cases
      (fun hxy : I ⊔ span {y * x + 1} = ⊤ =>
        let ⟨p, hpi, q, hq, hpq⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 hxy)
        let ⟨r, hr⟩ := mem_span_singleton'.1 hq
        ⟨r, by
          -- Porting note: supply `mul_add_one` with explicit variables
          rw [mul_assoc, ← mul_add_one r (y * x), hr, ← hpq, ← neg_sub, add_sub_cancel_right]
          exact I.neg_mem hpi⟩)
      fun hxy : I ⊔ span {y * x + 1} ≠ ⊤ => let ⟨M, hm1, hm2⟩ := exists_le_maximal _ hxy
      suffices x ∉ M from (this <| mem_sInf.1 hx ⟨le_trans le_sup_left hm2, hm1⟩).elim
      fun hxm => hm1.1.1 <| (eq_top_iff_one _).2 <| add_sub_cancel_left (y * x) 1 ▸
        M.sub_mem (le_sup_right.trans hm2 <| subset_span rfl) (M.mul_mem_left _ hxm),
    fun hx => mem_sInf.2 fun M ⟨him, hm⟩ => by_contradiction fun hxm =>
      let ⟨y, i, hi, df⟩ := hm.exists_inv hxm
      let ⟨z, hz⟩ := hx (-y)
      hm.1.1 <| (eq_top_iff_one _).2 <| sub_sub_cancel (z * -y * x + z) 1 ▸
        M.sub_mem (by
          -- Porting note: supply `mul_add_one` with explicit variables
          rw [mul_assoc, ← mul_add_one z, neg_mul, ← sub_eq_iff_eq_add.mpr df.symm, neg_sub,
            sub_add_cancel]
          exact M.mul_mem_left _ hi) <| him hz⟩

theorem exists_mul_add_sub_mem_of_mem_jacobson {I : Ideal R} (r : R) (h : r ∈ jacobson I) :
    ∃ s, s * (r + 1) - 1 ∈ I := by
  cases' mem_jacobson_iff.1 h 1 with s hs
  use s
  rw [mul_add, mul_one]
  simpa using hs

theorem exists_mul_sub_mem_of_sub_one_mem_jacobson {I : Ideal R} (r : R) (h : r - 1 ∈ jacobson I) :
    ∃ s, s * r - 1 ∈ I := by
  convert exists_mul_add_sub_mem_of_mem_jacobson _ h
  simp

/-- An ideal equals its Jacobson radical iff it is the intersection of a set of maximal ideals.
Allowing the set to include ⊤ is equivalent, and is included only to simplify some proofs. -/
theorem eq_jacobson_iff_sInf_maximal :
    I.jacobson = I ↔ ∃ M : Set (Ideal R), (∀ J ∈ M, IsMaximal J ∨ J = ⊤) ∧ I = sInf M := by
  use fun hI => ⟨{ J : Ideal R | I ≤ J ∧ J.IsMaximal }, ⟨fun _ hJ => Or.inl hJ.right, hI.symm⟩⟩
  rintro ⟨M, hM, hInf⟩
  refine le_antisymm (fun x hx => ?_) le_jacobson
  rw [hInf, mem_sInf]
  intro I hI
  cases' hM I hI with is_max is_top
  · exact (mem_sInf.1 hx) ⟨le_sInf_iff.1 (le_of_eq hInf) I hI, is_max⟩
  · exact is_top.symm ▸ Submodule.mem_top

theorem eq_jacobson_iff_sInf_maximal' :
    I.jacobson = I ↔ ∃ M : Set (Ideal R), (∀ J ∈ M, ∀ (K : Ideal R), J < K → K = ⊤) ∧ I = sInf M :=
  eq_jacobson_iff_sInf_maximal.trans
    ⟨fun h =>
      let ⟨M, hM⟩ := h
      ⟨M,
        ⟨fun J hJ K hK =>
          Or.recOn (hM.1 J hJ) (fun h => h.1.2 K hK) fun h => eq_top_iff.2 (le_of_lt (h ▸ hK)),
          hM.2⟩⟩,
      fun h =>
      let ⟨M, hM⟩ := h
      ⟨M,
        ⟨fun J hJ =>
          Or.recOn (Classical.em (J = ⊤)) (fun h => Or.inr h) fun h => Or.inl ⟨⟨h, hM.1 J hJ⟩⟩,
          hM.2⟩⟩⟩

/-- An ideal `I` equals its Jacobson radical if and only if every element outside `I`
also lies outside of a maximal ideal containing `I`. -/
theorem eq_jacobson_iff_not_mem :
    I.jacobson = I ↔ ∀ (x) (_ : x ∉ I), ∃ M : Ideal R, (I ≤ M ∧ M.IsMaximal) ∧ x ∉ M := by
  constructor
  · intro h x hx
    erw [← h, mem_sInf] at hx
    push_neg at hx
    exact hx
  · refine fun h => le_antisymm (fun x hx => ?_) le_jacobson
    contrapose hx
    erw [mem_sInf]
    push_neg
    exact h x hx

theorem map_jacobson_of_surjective {f : R →+* S} (hf : Function.Surjective f) :
    RingHom.ker f ≤ I → map f I.jacobson = (map f I).jacobson := by
  intro h
  unfold Ideal.jacobson
  -- Porting note: dot notation for `RingHom.ker` does not work
  have : ∀ J ∈ { J : Ideal R | I ≤ J ∧ J.IsMaximal }, RingHom.ker f ≤ J :=
    fun J hJ => le_trans h hJ.left
  refine Trans.trans (map_sInf hf this) (le_antisymm ?_ ?_)
  · refine
      sInf_le_sInf fun J hJ =>
        ⟨comap f J, ⟨⟨le_comap_of_map_le hJ.1, ?_⟩, map_comap_of_surjective f hf J⟩⟩
    haveI : J.IsMaximal := hJ.right
    exact comap_isMaximal_of_surjective f hf
  · refine sInf_le_sInf_of_subset_insert_top fun j hj => hj.recOn fun J hJ => ?_
    rw [← hJ.2]
    cases' map_eq_top_or_isMaximal_of_surjective f hf hJ.left.right with htop hmax
    · exact htop.symm ▸ Set.mem_insert ⊤ _
    · exact Set.mem_insert_of_mem ⊤ ⟨map_mono hJ.1.1, hmax⟩

theorem map_jacobson_of_bijective {f : R →+* S} (hf : Function.Bijective f) :
    map f I.jacobson = (map f I).jacobson :=
  map_jacobson_of_surjective hf.right
    (le_trans (le_of_eq (f.injective_iff_ker_eq_bot.1 hf.left)) bot_le)

theorem comap_jacobson {f : R →+* S} {K : Ideal S} :
    comap f K.jacobson = sInf (comap f '' { J : Ideal S | K ≤ J ∧ J.IsMaximal }) :=
  Trans.trans (comap_sInf' f _) sInf_eq_iInf.symm

theorem comap_jacobson_of_surjective {f : R →+* S} (hf : Function.Surjective f) {K : Ideal S} :
    comap f K.jacobson = (comap f K).jacobson := by
  unfold Ideal.jacobson
  refine le_antisymm ?_ ?_
  · rw [← top_inf_eq (sInf _), ← sInf_insert, comap_sInf', sInf_eq_iInf]
    refine iInf_le_iInf_of_subset fun J hJ => ?_
    have : comap f (map f J) = J :=
      Trans.trans (comap_map_of_surjective f hf J)
        (le_antisymm (sup_le_iff.2 ⟨le_of_eq rfl, le_trans (comap_mono bot_le) hJ.left⟩)
          le_sup_left)
    cases' map_eq_top_or_isMaximal_of_surjective _ hf hJ.right with htop hmax
    · exact ⟨⊤, Set.mem_insert ⊤ _, htop ▸ this⟩
    · exact ⟨map f J, Set.mem_insert_of_mem _ ⟨le_map_of_comap_le_of_surjective f hf hJ.1, hmax⟩,
        this⟩
  · simp_rw [comap_sInf, le_iInf_iff]
    intros J hJ
    haveI : J.IsMaximal := hJ.right
    exact sInf_le ⟨comap_mono hJ.left, comap_isMaximal_of_surjective _ hf⟩

@[mono]
theorem jacobson_mono {I J : Ideal R} : I ≤ J → I.jacobson ≤ J.jacobson := by
  intro h x hx
  erw [mem_sInf] at hx ⊢
  exact fun K ⟨hK, hK_max⟩ => hx ⟨Trans.trans h hK, hK_max⟩

/-- The Jacobson radical of a two-sided ideal is two-sided.

It is preferable to use `TwoSidedIdeal.jacobson` instead of this lemma. -/
theorem jacobson_mul_mem_right {I : Ideal R}
    (mul_mem_right : ∀ {x y}, x ∈ I → x * y ∈ I) :
    ∀ {x y}, x ∈ I.jacobson → x * y ∈ I.jacobson := by
  -- Proof generalized from
  -- https://ysharifi.wordpress.com/2022/08/16/the-jacobson-radical-definition-and-basic-results/
  intro x r xJ
  apply mem_sInf.mpr
  intro 𝔪 𝔪_mem
  by_cases r𝔪 : r ∈ 𝔪
  · apply 𝔪.smul_mem _ r𝔪
  -- 𝔪₀ := { a : R | a*r ∈ 𝔪 }
  let 𝔪₀ : Ideal R := Submodule.comap (DistribMulAction.toLinearMap R (S := Rᵐᵒᵖ) R (.op r)) 𝔪
  suffices x ∈ 𝔪₀ by simpa [𝔪₀] using this
  have I𝔪₀ : I ≤ 𝔪₀ := fun i iI =>
    𝔪_mem.left (mul_mem_right iI)
  have 𝔪₀_maximal : IsMaximal 𝔪₀ := by
    refine isMaximal_iff.mpr ⟨
      fun h => r𝔪 (by simpa [𝔪₀] using h),
      fun J b 𝔪₀J b𝔪₀ bJ => ?_⟩
    let K : Ideal R := Ideal.span {b*r} ⊔ 𝔪
    have ⟨s, y, y𝔪, sbyr⟩ :=
      mem_span_singleton_sup.mp <|
        mul_mem_left _ r <|
          (isMaximal_iff.mp 𝔪_mem.right).right K (b*r)
          le_sup_right b𝔪₀
          (mem_sup_left <| mem_span_singleton_self _)
    have : 1 - s*b ∈ 𝔪₀ := by
      rw [mul_one, add_comm, ← eq_sub_iff_add_eq] at sbyr
      rw [sbyr, ← mul_assoc] at y𝔪
      simp [𝔪₀, sub_mul, y𝔪]
    have : 1 - s*b + s*b ∈ J := by
      apply add_mem (𝔪₀J this) (J.mul_mem_left _ bJ)
    simpa using this
  exact mem_sInf.mp xJ ⟨I𝔪₀, 𝔪₀_maximal⟩

end Ring

section CommRing

variable [CommRing R] [CommRing S] {I : Ideal R}

theorem radical_le_jacobson : radical I ≤ jacobson I :=
  le_sInf fun _ hJ => (radical_eq_sInf I).symm ▸ sInf_le ⟨hJ.left, IsMaximal.isPrime hJ.right⟩

theorem isRadical_of_eq_jacobson (h : jacobson I = I) : I.IsRadical :=
  radical_le_jacobson.trans h.le

theorem isUnit_of_sub_one_mem_jacobson_bot (r : R) (h : r - 1 ∈ jacobson (⊥ : Ideal R)) :
    IsUnit r := by
  cases' exists_mul_sub_mem_of_sub_one_mem_jacobson r h with s hs
  rw [mem_bot, sub_eq_zero, mul_comm] at hs
  exact isUnit_of_mul_eq_one _ _ hs

theorem mem_jacobson_bot {x : R} : x ∈ jacobson (⊥ : Ideal R) ↔ ∀ y, IsUnit (x * y + 1) :=
  ⟨fun hx y =>
    let ⟨z, hz⟩ := (mem_jacobson_iff.1 hx) y
    isUnit_iff_exists_inv.2
      ⟨z, by rwa [add_mul, one_mul, ← sub_eq_zero, mul_right_comm, mul_comm _ z, mul_right_comm]⟩,
    fun h =>
    mem_jacobson_iff.mpr fun y =>
      let ⟨b, hb⟩ := isUnit_iff_exists_inv.1 (h y)
      ⟨b, (Submodule.mem_bot R).2 (hb ▸ by ring)⟩⟩

/-- An ideal `I` of `R` is equal to its Jacobson radical if and only if
the Jacobson radical of the quotient ring `R/I` is the zero ideal -/
-- Porting note: changed `Quotient.mk'` to ``
theorem jacobson_eq_iff_jacobson_quotient_eq_bot :
    I.jacobson = I ↔ jacobson (⊥ : Ideal (R ⧸ I)) = ⊥ := by
  have hf : Function.Surjective (Ideal.Quotient.mk I) := Submodule.Quotient.mk_surjective I
  constructor
  · intro h
    replace h := congr_arg (Ideal.map (Ideal.Quotient.mk I)) h
    rw [map_jacobson_of_surjective hf (le_of_eq mk_ker)] at h
    simpa using h
  · intro h
    replace h := congr_arg (comap (Ideal.Quotient.mk I)) h
    rw [comap_jacobson_of_surjective hf, ← RingHom.ker_eq_comap_bot (Ideal.Quotient.mk I)] at h
    simpa using h

/-- The standard radical and Jacobson radical of an ideal `I` of `R` are equal if and only if
the nilradical and Jacobson radical of the quotient ring `R/I` coincide -/
-- Porting note: changed `Quotient.mk'` to ``
theorem radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot :
    I.radical = I.jacobson ↔ radical (⊥ : Ideal (R ⧸ I)) = jacobson ⊥ := by
  have hf : Function.Surjective (Ideal.Quotient.mk I) := Submodule.Quotient.mk_surjective I
  constructor
  · intro h
    have := congr_arg (map (Ideal.Quotient.mk I)) h
    rw [map_radical_of_surjective hf (le_of_eq mk_ker),
      map_jacobson_of_surjective hf (le_of_eq mk_ker)] at this
    simpa using this
  · intro h
    have := congr_arg (comap (Ideal.Quotient.mk I)) h
    rw [comap_radical, comap_jacobson_of_surjective hf,
      ← RingHom.ker_eq_comap_bot (Ideal.Quotient.mk I)] at this
    simpa using this

theorem jacobson_radical_eq_jacobson : I.radical.jacobson = I.jacobson :=
  le_antisymm
    (le_trans (le_of_eq (congr_arg jacobson (radical_eq_sInf I)))
      (sInf_le_sInf fun _ hJ => ⟨sInf_le ⟨hJ.1, hJ.2.isPrime⟩, hJ.2⟩))
    (jacobson_mono le_radical)

end CommRing

end Jacobson

section Polynomial

open Polynomial

variable [CommRing R]

theorem jacobson_bot_polynomial_le_sInf_map_maximal :
    jacobson (⊥ : Ideal R[X]) ≤ sInf (map (C : R →+* R[X]) '' { J : Ideal R | J.IsMaximal }) := by
  refine le_sInf fun J => exists_imp.2 fun j hj => ?_
  haveI : j.IsMaximal := hj.1
  refine Trans.trans (jacobson_mono bot_le) (le_of_eq ?_ : J.jacobson ≤ J)
  suffices t : (⊥ : Ideal (Polynomial (R ⧸ j))).jacobson = ⊥ by
    rw [← hj.2, jacobson_eq_iff_jacobson_quotient_eq_bot]
    replace t := congr_arg (map (polynomialQuotientEquivQuotientPolynomial j).toRingHom) t
    rwa [map_jacobson_of_bijective _, map_bot] at t
    exact RingEquiv.bijective (polynomialQuotientEquivQuotientPolynomial j)
  refine eq_bot_iff.2 fun f hf => ?_
  have r1 : (X : (R ⧸ j)[X]) ≠ 0 := fun hX => by
    replace hX := congr_arg (fun f => coeff f 1) hX
    simp only [coeff_X_one, coeff_zero] at hX
    exact zero_ne_one hX.symm
  have r2 := eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit ((mem_jacobson_bot.1 hf) X))
  simp only [coeff_add, mul_coeff_zero, coeff_X_zero, mul_zero, coeff_one_zero, zero_add] at r2
  erw [add_left_eq_self] at r2
  simpa using (mul_eq_zero.mp r2).resolve_right r1
  -- Porting note: this is golfed to much
  -- simpa [(fun hX => by simpa using congr_arg (fun f => coeff f 1) hX : (X : (R ⧸ j)[X]) ≠ 0)]
  --   using eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit ((mem_jacobson_bot.1 hf) X))

theorem jacobson_bot_polynomial_of_jacobson_bot (h : jacobson (⊥ : Ideal R) = ⊥) :
    jacobson (⊥ : Ideal R[X]) = ⊥ := by
  refine eq_bot_iff.2 (le_trans jacobson_bot_polynomial_le_sInf_map_maximal ?_)
  refine fun f hf => (Submodule.mem_bot R[X]).2 <| Polynomial.ext fun n =>
    Trans.trans (?_ : coeff f n = 0) (coeff_zero n).symm
  suffices f.coeff n ∈ Ideal.jacobson ⊥ by rwa [h, Submodule.mem_bot] at this
  exact mem_sInf.2 fun j hj => (mem_map_C_iff.1 ((mem_sInf.1 hf) ⟨j, ⟨hj.2, rfl⟩⟩)) n

end Polynomial

section IsLocal

variable [CommRing R]

/-- An ideal `I` is local iff its Jacobson radical is maximal. -/
class IsLocal (I : Ideal R) : Prop where
  /-- A ring `R` is local if and only if its jacobson radical is maximal -/
  out : IsMaximal (jacobson I)

theorem isLocal_iff {I : Ideal R} : IsLocal I ↔ IsMaximal (jacobson I) :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem isLocal_of_isMaximal_radical {I : Ideal R} (hi : IsMaximal (radical I)) : IsLocal I :=
  ⟨have : radical I = jacobson I :=
      le_antisymm (le_sInf fun _ ⟨him, hm⟩ => hm.isPrime.radical_le_iff.2 him)
        (sInf_le ⟨le_radical, hi⟩)
    show IsMaximal (jacobson I) from this ▸ hi⟩

theorem IsLocal.le_jacobson {I J : Ideal R} (hi : IsLocal I) (hij : I ≤ J) (hj : J ≠ ⊤) :
    J ≤ jacobson I :=
  let ⟨_, hm, hjm⟩ := exists_le_maximal J hj
  le_trans hjm <| le_of_eq <| Eq.symm <| hi.1.eq_of_le hm.1.1 <| sInf_le ⟨le_trans hij hjm, hm⟩

theorem IsLocal.mem_jacobson_or_exists_inv {I : Ideal R} (hi : IsLocal I) (x : R) :
    x ∈ jacobson I ∨ ∃ y, y * x - 1 ∈ I :=
  by_cases
    (fun h : I ⊔ span {x} = ⊤ =>
      let ⟨p, hpi, q, hq, hpq⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 h)
      let ⟨r, hr⟩ := mem_span_singleton.1 hq
      Or.inr ⟨r, by
        rw [← hpq, mul_comm, ← hr, ← neg_sub, add_sub_cancel_right]; exact I.neg_mem hpi⟩)
    fun h : I ⊔ span {x} ≠ ⊤ =>
    Or.inl <|
      le_trans le_sup_right (hi.le_jacobson le_sup_left h) <| mem_span_singleton.2 <| dvd_refl x

end IsLocal

theorem isPrimary_of_isMaximal_radical [CommRing R] {I : Ideal R} (hi : IsMaximal (radical I)) :
    IsPrimary I :=
  have : radical I = jacobson I :=
    le_antisymm (le_sInf fun _ ⟨him, hm⟩ => hm.isPrime.radical_le_iff.2 him)
      (sInf_le ⟨le_radical, hi⟩)
  ⟨ne_top_of_lt <| lt_of_le_of_lt le_radical (lt_top_iff_ne_top.2 hi.1.1), fun {x y} hxy =>
    ((isLocal_of_isMaximal_radical hi).mem_jacobson_or_exists_inv y).symm.imp
      (fun ⟨z, hz⟩ => by
        rw [← mul_one x, ← sub_sub_cancel (z * y) 1, mul_sub, mul_left_comm]
        exact I.sub_mem (I.mul_mem_left _ hxy) (I.mul_mem_left _ hz))
      (this ▸ id)⟩

end Ideal

namespace TwoSidedIdeal

variable {R : Type u} [Ring R]

/-- The Jacobson radical of `I` is the infimum of all maximal (left) ideals containing `I`. -/
def jacobson (I : TwoSidedIdeal R) : TwoSidedIdeal R :=
  (asIdeal I).jacobson.toTwoSided (Ideal.jacobson_mul_mem_right <| I.mul_mem_right _ _)

lemma asIdeal_jacobson (I : TwoSidedIdeal R) : asIdeal I.jacobson = (asIdeal I).jacobson := by
  ext; simp [jacobson]

end TwoSidedIdeal
