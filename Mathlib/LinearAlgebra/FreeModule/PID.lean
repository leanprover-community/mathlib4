/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.LinearAlgebra.Dimension
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Finiteness

#align_import linear_algebra.free_module.pid from "leanprover-community/mathlib"@"d87199d51218d36a0a42c66c82d147b5a7ff87b3"

/-! # Free modules over PID

A free `R`-module `M` is a module with a basis over `R`,
equivalently it is an `R`-module linearly equivalent to `ι →₀ R` for some `ι`.

This file proves a submodule of a free `R`-module of finite rank is also
a free `R`-module of finite rank, if `R` is a principal ideal domain (PID),
i.e. we have instances `[IsDomain R] [IsPrincipalIdealRing R]`.
We express "free `R`-module of finite rank" as a module `M` which has a basis
`b : ι → R`, where `ι` is a `Fintype`.
We call the cardinality of `ι` the rank of `M` in this file;
it would be equal to `finrank R M` if `R` is a field and `M` is a vector space.

## Main results

In this section, `M` is a free and finitely generated `R`-module, and
`N` is a submodule of `M`.

 - `Submodule.inductionOnRank`: if `P` holds for `⊥ : Submodule R M` and if
  `P N` follows from `P N'` for all `N'` that are of lower rank, then `P` holds
   on all submodules

 - `submodule.exists_basis_of_pid`: if `R` is a PID, then `N : Submodule R M` is
   free and finitely generated. This is the first part of the structure theorem
   for modules.

- `Submodule.smithNormalForm`: if `R` is a PID, then `M` has a basis
  `bM` and `N` has a basis `bN` such that `bN i = a i • bM i`.
  Equivalently, a linear map `f : M →ₗ M` with `range f = N` can be written as
  a matrix in Smith normal form, a diagonal matrix with the coefficients `a i`
  along the diagonal.

## Tags

free module, finitely generated module, rank, structure theorem

-/


open BigOperators

universe u v

section Ring

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

variable {ι : Type*} (b : Basis ι R M)

open Submodule.IsPrincipal Submodule

theorem eq_bot_of_generator_maximal_map_eq_zero (b : Basis ι R M) {N : Submodule R M}
    {ϕ : M →ₗ[R] R} (hϕ : ∀ ψ : M →ₗ[R] R, ¬N.map ϕ < N.map ψ) [(N.map ϕ).IsPrincipal]
    (hgen : generator (N.map ϕ) = (0 : R)) : N = ⊥ := by
  rw [Submodule.eq_bot_iff]
  -- ⊢ ∀ (x : M), x ∈ N → x = 0
  intro x hx
  -- ⊢ x = 0
  refine' b.ext_elem fun i ↦ _
  -- ⊢ ↑(↑b.repr x) i = ↑(↑b.repr 0) i
  rw [(eq_bot_iff_generator_eq_zero _).mpr hgen] at hϕ
  -- ⊢ ↑(↑b.repr x) i = ↑(↑b.repr 0) i
  rw [LinearEquiv.map_zero, Finsupp.zero_apply]
  -- ⊢ ↑(↑b.repr x) i = 0
  exact
    (Submodule.eq_bot_iff _).mp (not_bot_lt_iff.1 <| hϕ (Finsupp.lapply i ∘ₗ ↑b.repr)) _
      ⟨x, hx, rfl⟩
#align eq_bot_of_generator_maximal_map_eq_zero eq_bot_of_generator_maximal_map_eq_zero

theorem eq_bot_of_generator_maximal_submoduleImage_eq_zero {N O : Submodule R M} (b : Basis ι R O)
    (hNO : N ≤ O) {ϕ : O →ₗ[R] R} (hϕ : ∀ ψ : O →ₗ[R] R, ¬ϕ.submoduleImage N < ψ.submoduleImage N)
    [(ϕ.submoduleImage N).IsPrincipal] (hgen : generator (ϕ.submoduleImage N) = 0) : N = ⊥ := by
  rw [Submodule.eq_bot_iff]
  -- ⊢ ∀ (x : M), x ∈ N → x = 0
  intro x hx
  -- ⊢ x = 0
  refine (mk_eq_zero _ _).mp (show (⟨x, hNO hx⟩ : O) = 0 from b.ext_elem fun i ↦ ?_)
  -- ⊢ ↑(↑b.repr { val := x, property := (_ : x ∈ O) }) i = ↑(↑b.repr 0) i
  rw [(eq_bot_iff_generator_eq_zero _).mpr hgen] at hϕ
  -- ⊢ ↑(↑b.repr { val := x, property := (_ : x ∈ O) }) i = ↑(↑b.repr 0) i
  rw [LinearEquiv.map_zero, Finsupp.zero_apply]
  -- ⊢ ↑(↑b.repr { val := x, property := (_ : x ∈ O) }) i = 0
  refine (Submodule.eq_bot_iff _).mp (not_bot_lt_iff.1 <| hϕ (Finsupp.lapply i ∘ₗ ↑b.repr)) _ ?_
  -- ⊢ ↑(↑b.repr { val := x, property := (_ : x ∈ O) }) i ∈ LinearMap.submoduleImag …
  exact (LinearMap.mem_submoduleImage_of_le hNO).mpr ⟨x, hx, rfl⟩
  -- 🎉 no goals
#align eq_bot_of_generator_maximal_submodule_image_eq_zero eq_bot_of_generator_maximal_submoduleImage_eq_zero

end Ring

section IsDomain

variable {ι : Type*} {R : Type*} [CommRing R] [IsDomain R]

variable {M : Type*} [AddCommGroup M] [Module R M] {b : ι → M}

open Submodule.IsPrincipal Set Submodule

theorem dvd_generator_iff {I : Ideal R} [I.IsPrincipal] {x : R} (hx : x ∈ I) :
    x ∣ generator I ↔ I = Ideal.span {x} := by
  conv_rhs => rw [← span_singleton_generator I]
  -- ⊢ x ∣ generator I ↔ span R {generator I} = Ideal.span {x}
  rw [Ideal.submodule_span_eq, Ideal.span_singleton_eq_span_singleton, ← dvd_dvd_iff_associated,
    ← mem_iff_generator_dvd]
  exact ⟨fun h ↦ ⟨hx, h⟩, fun h ↦ h.2⟩
  -- 🎉 no goals
#align dvd_generator_iff dvd_generator_iff

end IsDomain

section PrincipalIdealDomain

open Submodule.IsPrincipal Set Submodule

variable {ι : Type*} {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

variable {M : Type*} [AddCommGroup M] [Module R M] {b : ι → M}

open Submodule.IsPrincipal

theorem generator_maximal_submoduleImage_dvd {N O : Submodule R M} (hNO : N ≤ O) {ϕ : O →ₗ[R] R}
    (hϕ : ∀ ψ : O →ₗ[R] R, ¬ϕ.submoduleImage N < ψ.submoduleImage N)
    [(ϕ.submoduleImage N).IsPrincipal] (y : M) (yN : y ∈ N)
    (ϕy_eq : ϕ ⟨y, hNO yN⟩ = generator (ϕ.submoduleImage N)) (ψ : O →ₗ[R] R) :
    generator (ϕ.submoduleImage N) ∣ ψ ⟨y, hNO yN⟩ := by
  let a : R := generator (ϕ.submoduleImage N)
  -- ⊢ generator (LinearMap.submoduleImage ϕ N) ∣ ↑ψ { val := y, property := (_ : y …
  let d : R := IsPrincipal.generator (Submodule.span R {a, ψ ⟨y, hNO yN⟩})
  -- ⊢ generator (LinearMap.submoduleImage ϕ N) ∣ ↑ψ { val := y, property := (_ : y …
  have d_dvd_left : d ∣ a := (mem_iff_generator_dvd _).mp (subset_span (mem_insert _ _))
  -- ⊢ generator (LinearMap.submoduleImage ϕ N) ∣ ↑ψ { val := y, property := (_ : y …
  have d_dvd_right : d ∣ ψ ⟨y, hNO yN⟩ :=
    (mem_iff_generator_dvd _).mp (subset_span (mem_insert_of_mem _ (mem_singleton _)))
  refine' dvd_trans _ d_dvd_right
  -- ⊢ generator (LinearMap.submoduleImage ϕ N) ∣ d
  rw [dvd_generator_iff, Ideal.span, ←
    span_singleton_generator (Submodule.span R {a, ψ ⟨y, hNO yN⟩})]
  obtain ⟨r₁, r₂, d_eq⟩ : ∃ r₁ r₂ : R, d = r₁ * a + r₂ * ψ ⟨y, hNO yN⟩ := by
    obtain ⟨r₁, r₂', hr₂', hr₁⟩ :=
      mem_span_insert.mp (IsPrincipal.generator_mem (Submodule.span R {a, ψ ⟨y, hNO yN⟩}))
    obtain ⟨r₂, rfl⟩ := mem_span_singleton.mp hr₂'
    exact ⟨r₁, r₂, hr₁⟩
  let ψ' : O →ₗ[R] R := r₁ • ϕ + r₂ • ψ
  -- ⊢ span R {generator (span R {a, ↑ψ { val := y, property := (_ : y ∈ O) }})} =  …
  have : span R {d} ≤ ψ'.submoduleImage N := by
    rw [span_le, singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_submoduleImage_of_le hNO]
    refine' ⟨y, yN, _⟩
    change r₁ * ϕ ⟨y, hNO yN⟩ + r₂ * ψ ⟨y, hNO yN⟩ = d
    rw [d_eq, ϕy_eq]
  refine'
    le_antisymm (this.trans (le_of_eq _)) (Ideal.span_singleton_le_span_singleton.mpr d_dvd_left)
  rw [span_singleton_generator]
  -- ⊢ LinearMap.submoduleImage ψ' N = LinearMap.submoduleImage ϕ N
  apply (le_trans _ this).eq_of_not_gt (hϕ ψ')
  -- ⊢ LinearMap.submoduleImage ϕ N ≤ span R {d}
  rw [← span_singleton_generator (ϕ.submoduleImage N)]
  -- ⊢ span R {generator (LinearMap.submoduleImage ϕ N)} ≤ span R {d}
  exact Ideal.span_singleton_le_span_singleton.mpr d_dvd_left
  -- ⊢ generator (LinearMap.submoduleImage ϕ N) ∈ span R {a, ↑ψ { val := y, propert …
  · exact subset_span (mem_insert _ _)
    -- 🎉 no goals
#align generator_maximal_submodule_image_dvd generator_maximal_submoduleImage_dvd

/-- The induction hypothesis of `Submodule.basisOfPid` and `Submodule.smithNormalForm`.

Basically, it says: let `N ≤ M` be a pair of submodules, then we can find a pair of
submodules `N' ≤ M'` of strictly smaller rank, whose basis we can extend to get a basis
of `N` and `M`. Moreover, if the basis for `M'` is up to scalars a basis for `N'`,
then the basis we find for `M` is up to scalars a basis for `N`.

For `basis_of_pid` we only need the first half and can fix `M = ⊤`,
for `smith_normal_form` we need the full statement,
but must also feed in a basis for `M` using `basis_of_pid` to keep the induction going.
-/
theorem Submodule.basis_of_pid_aux [Finite ι] {O : Type*} [AddCommGroup O] [Module R O]
    (M N : Submodule R O) (b'M : Basis ι R M) (N_bot : N ≠ ⊥) (N_le_M : N ≤ M) :
    ∃ y ∈ M,
      ∃ (a : R) (_ : a • y ∈ N),
        ∃ M' ≤ M,
          ∃ N' ≤ N,
            ∃ (_N'_le_M' : N' ≤ M') (_y_ortho_M' :
              ∀ (c : R) (z : O), z ∈ M' → c • y + z = 0 → c = 0) (_ay_ortho_N' :
              ∀ (c : R) (z : O), z ∈ N' → c • a • y + z = 0 → c = 0),
              ∀ (n') (bN' : Basis (Fin n') R N'),
                ∃ bN : Basis (Fin (n' + 1)) R N,
                  ∀ (m') (hn'm' : n' ≤ m') (bM' : Basis (Fin m') R M'),
                    ∃ (hnm : n' + 1 ≤ m' + 1) (bM : Basis (Fin (m' + 1)) R M),
                      ∀ (as : Fin n' → R)
                        (_h : ∀ i : Fin n', (bN' i : O) = as i • (bM' (Fin.castLE hn'm' i) : O)),
                        ∃ as' : Fin (n' + 1) → R,
                          ∀ i : Fin (n' + 1), (bN i : O) = as' i • (bM (Fin.castLE hnm i) : O) := by
  -- Let `ϕ` be a maximal projection of `M` onto `R`, in the sense that there is
  -- no `ψ` whose image of `N` is larger than `ϕ`'s image of `N`.
  have : ∃ ϕ : M →ₗ[R] R, ∀ ψ : M →ₗ[R] R, ¬ϕ.submoduleImage N < ψ.submoduleImage N := by
    obtain ⟨P, P_eq, P_max⟩ :=
      set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R) _
        (show (Set.range fun ψ : M →ₗ[R] R ↦ ψ.submoduleImage N).Nonempty from
          ⟨_, Set.mem_range.mpr ⟨0, rfl⟩⟩)
    obtain ⟨ϕ, rfl⟩ := Set.mem_range.mp P_eq
    exact ⟨ϕ, fun ψ hψ ↦ P_max _ ⟨_, rfl⟩ hψ⟩
  let ϕ := this.choose
  -- ⊢ ∃ y, y ∈ M ∧ ∃ a x M', M' ≤ M ∧ ∃ N', N' ≤ N ∧ ∃ _N'_le_M' _y_ortho_M' _ay_o …
  have ϕ_max := this.choose_spec
  -- ⊢ ∃ y, y ∈ M ∧ ∃ a x M', M' ≤ M ∧ ∃ N', N' ≤ N ∧ ∃ _N'_le_M' _y_ortho_M' _ay_o …
  -- Since `ϕ(N)` is an `R`-submodule of the PID `R`,
  -- it is principal and generated by some `a`.
  let a := generator (ϕ.submoduleImage N)
  -- ⊢ ∃ y, y ∈ M ∧ ∃ a x M', M' ≤ M ∧ ∃ N', N' ≤ N ∧ ∃ _N'_le_M' _y_ortho_M' _ay_o …
  have a_mem : a ∈ ϕ.submoduleImage N := generator_mem _
  -- ⊢ ∃ y, y ∈ M ∧ ∃ a x M', M' ≤ M ∧ ∃ N', N' ≤ N ∧ ∃ _N'_le_M' _y_ortho_M' _ay_o …
  -- If `a` is zero, then the submodule is trivial. So let's assume `a ≠ 0`, `N ≠ ⊥`.
  by_cases a_zero : a = 0
  -- ⊢ ∃ y, y ∈ M ∧ ∃ a x M', M' ≤ M ∧ ∃ N', N' ≤ N ∧ ∃ _N'_le_M' _y_ortho_M' _ay_o …
  · have := eq_bot_of_generator_maximal_submoduleImage_eq_zero b'M N_le_M ϕ_max a_zero
    -- ⊢ ∃ y, y ∈ M ∧ ∃ a x M', M' ≤ M ∧ ∃ N', N' ≤ N ∧ ∃ _N'_le_M' _y_ortho_M' _ay_o …
    contradiction
    -- 🎉 no goals
  -- We claim that `ϕ⁻¹ a = y` can be taken as basis element of `N`.
  obtain ⟨y, yN, ϕy_eq⟩ := (LinearMap.mem_submoduleImage_of_le N_le_M).mp a_mem
  -- ⊢ ∃ y, y ∈ M ∧ ∃ a x M', M' ≤ M ∧ ∃ N', N' ≤ N ∧ ∃ _N'_le_M' _y_ortho_M' _ay_o …
  have _ϕy_ne_zero : ϕ ⟨y, N_le_M yN⟩ ≠ 0 := fun h ↦ a_zero (ϕy_eq.symm.trans h)
  -- ⊢ ∃ y, y ∈ M ∧ ∃ a x M', M' ≤ M ∧ ∃ N', N' ≤ N ∧ ∃ _N'_le_M' _y_ortho_M' _ay_o …
  -- Write `y` as `a • y'` for some `y'`.
  have hdvd : ∀ i, a ∣ b'M.coord i ⟨y, N_le_M yN⟩ := fun i ↦
    generator_maximal_submoduleImage_dvd N_le_M ϕ_max y yN ϕy_eq (b'M.coord i)
  choose c hc using hdvd
  -- ⊢ ∃ y, y ∈ M ∧ ∃ a x M', M' ≤ M ∧ ∃ N', N' ≤ N ∧ ∃ _N'_le_M' _y_ortho_M' _ay_o …
  cases nonempty_fintype ι
  -- ⊢ ∃ y, y ∈ M ∧ ∃ a x M', M' ≤ M ∧ ∃ N', N' ≤ N ∧ ∃ _N'_le_M' _y_ortho_M' _ay_o …
  let y' : O := ∑ i, c i • b'M i
  -- ⊢ ∃ y, y ∈ M ∧ ∃ a x M', M' ≤ M ∧ ∃ N', N' ≤ N ∧ ∃ _N'_le_M' _y_ortho_M' _ay_o …
  have y'M : y' ∈ M := M.sum_mem fun i _ ↦ M.smul_mem (c i) (b'M i).2
  -- ⊢ ∃ y, y ∈ M ∧ ∃ a x M', M' ≤ M ∧ ∃ N', N' ≤ N ∧ ∃ _N'_le_M' _y_ortho_M' _ay_o …
  have mk_y' : (⟨y', y'M⟩ : M) = ∑ i, c i • b'M i :=
    Subtype.ext
      (show y' = M.subtype _ by
        simp only [LinearMap.map_sum, LinearMap.map_smul]
        rfl)
  have a_smul_y' : a • y' = y := by
    refine Subtype.mk_eq_mk.mp (show (a • ⟨y', y'M⟩ : M) = ⟨y, N_le_M yN⟩ from ?_)
    rw [← b'M.sum_repr ⟨y, N_le_M yN⟩, mk_y', Finset.smul_sum]
    refine' Finset.sum_congr rfl fun i _ ↦ _
    rw [← mul_smul, ← hc]
    rfl
  -- We found a `y` and an `a`!
  refine' ⟨y', y'M, a, a_smul_y'.symm ▸ yN, _⟩
  -- ⊢ ∃ M', M' ≤ M ∧ ∃ N', N' ≤ N ∧ ∃ _N'_le_M' _y_ortho_M' _ay_ortho_N', ∀ (n' :  …
  have ϕy'_eq : ϕ ⟨y', y'M⟩ = 1 :=
    mul_left_cancel₀ a_zero
      (calc
        a • ϕ ⟨y', y'M⟩ = ϕ ⟨a • y', _⟩ := (ϕ.map_smul a ⟨y', y'M⟩).symm
        _ = ϕ ⟨y, N_le_M yN⟩ := by simp only [a_smul_y']
        _ = a := ϕy_eq
        _ = a * 1 := (mul_one a).symm
        )
  have ϕy'_ne_zero : ϕ ⟨y', y'M⟩ ≠ 0 := by simpa only [ϕy'_eq] using one_ne_zero
  -- ⊢ ∃ M', M' ≤ M ∧ ∃ N', N' ≤ N ∧ ∃ _N'_le_M' _y_ortho_M' _ay_ortho_N', ∀ (n' :  …
  -- `M' := ker (ϕ : M → R)` is smaller than `M` and `N' := ker (ϕ : N → R)` is smaller than `N`.
  let M' : Submodule R O := ϕ.ker.map M.subtype
  -- ⊢ ∃ M', M' ≤ M ∧ ∃ N', N' ≤ N ∧ ∃ _N'_le_M' _y_ortho_M' _ay_ortho_N', ∀ (n' :  …
  let N' : Submodule R O := (ϕ.comp (ofLe N_le_M)).ker.map N.subtype
  -- ⊢ ∃ M', M' ≤ M ∧ ∃ N', N' ≤ N ∧ ∃ _N'_le_M' _y_ortho_M' _ay_ortho_N', ∀ (n' :  …
  have M'_le_M : M' ≤ M := M.map_subtype_le (LinearMap.ker ϕ)
  -- ⊢ ∃ M', M' ≤ M ∧ ∃ N', N' ≤ N ∧ ∃ _N'_le_M' _y_ortho_M' _ay_ortho_N', ∀ (n' :  …
  have N'_le_M' : N' ≤ M' := by
    intro x hx
    simp only [mem_map, LinearMap.mem_ker] at hx ⊢
    obtain ⟨⟨x, xN⟩, hx, rfl⟩ := hx
    exact ⟨⟨x, N_le_M xN⟩, hx, rfl⟩
  have N'_le_N : N' ≤ N := N.map_subtype_le (LinearMap.ker (ϕ.comp (ofLe N_le_M)))
  -- ⊢ ∃ M', M' ≤ M ∧ ∃ N', N' ≤ N ∧ ∃ _N'_le_M' _y_ortho_M' _ay_ortho_N', ∀ (n' :  …
  -- So fill in those results as well.
  refine' ⟨M', M'_le_M, N', N'_le_N, N'_le_M', _⟩
  -- ⊢ ∃ _y_ortho_M' _ay_ortho_N', ∀ (n' : ℕ) (bN' : Basis (Fin n') R { x // x ∈ N' …
  -- Note that `y'` is orthogonal to `M'`.
  have y'_ortho_M' : ∀ (c : R), ∀ z ∈ M', c • y' + z = 0 → c = 0 := by
    intro c x xM' hc
    obtain ⟨⟨x, xM⟩, hx', rfl⟩ := Submodule.mem_map.mp xM'
    rw [LinearMap.mem_ker] at hx'
    have hc' : (c • ⟨y', y'M⟩ + ⟨x, xM⟩ : M) = 0 := by exact @Subtype.coe_injective O (· ∈ M) _ _ hc
    simpa only [LinearMap.map_add, LinearMap.map_zero, LinearMap.map_smul, smul_eq_mul, add_zero,
      mul_eq_zero, ϕy'_ne_zero, hx', or_false_iff] using congr_arg ϕ hc'
  -- And `a • y'` is orthogonal to `N'`.
  have ay'_ortho_N' : ∀ (c : R), ∀ z ∈ N', c • a • y' + z = 0 → c = 0 := by
    intro c z zN' hc
    refine' (mul_eq_zero.mp (y'_ortho_M' (a * c) z (N'_le_M' zN') _)).resolve_left a_zero
    rw [mul_comm, mul_smul, hc]
  -- So we can extend a basis for `N'` with `y`
  refine' ⟨y'_ortho_M', ay'_ortho_N', fun n' bN' ↦ ⟨_, _⟩⟩
  -- ⊢ Basis (Fin (n' + 1)) R { x // x ∈ N }
  · refine' Basis.mkFinConsOfLE y yN bN' N'_le_N _ _
    -- ⊢ ∀ (c : R) (x : O), x ∈ N' → c • y + x = 0 → c = 0
    · intro c z zN' hc
      -- ⊢ c = 0
      refine' ay'_ortho_N' c z zN' _
      -- ⊢ c • a • y' + z = 0
      rwa [← a_smul_y'] at hc
      -- 🎉 no goals
    · intro z zN
      -- ⊢ ∃ c, z + c • y ∈ N'
      obtain ⟨b, hb⟩ : _ ∣ ϕ ⟨z, N_le_M zN⟩ := generator_submoduleImage_dvd_of_mem N_le_M ϕ zN
      -- ⊢ ∃ c, z + c • y ∈ N'
      refine' ⟨-b, Submodule.mem_map.mpr ⟨⟨_, N.sub_mem zN (N.smul_mem b yN)⟩, _, _⟩⟩
      -- ⊢ { val := z - b • y, property := (_ : z - b • y ∈ N) } ∈ LinearMap.ker (Linea …
      · refine' LinearMap.mem_ker.mpr (show ϕ (⟨z, N_le_M zN⟩ - b • ⟨y, N_le_M yN⟩) = 0 from _)
        -- ⊢ ↑ϕ ({ val := z, property := (_ : z ∈ M) } - b • { val := y, property := (_ : …
        rw [LinearMap.map_sub, LinearMap.map_smul, hb, ϕy_eq, smul_eq_mul, mul_comm, sub_self]
        -- 🎉 no goals
      · simp only [sub_eq_add_neg, neg_smul, coeSubtype]
        -- 🎉 no goals
  -- And extend a basis for `M'` with `y'`
  intro m' hn'm' bM'
  -- ⊢ ∃ hnm bM, ∀ (as : Fin n' → R), (∀ (i : Fin n'), ↑(↑bN' i) = as i • ↑(↑bM' (F …
  refine' ⟨Nat.succ_le_succ hn'm', _, _⟩
  -- ⊢ Basis (Fin (m' + 1)) R { x // x ∈ M }
  · refine' Basis.mkFinConsOfLE y' y'M bM' M'_le_M y'_ortho_M' _
    -- ⊢ ∀ (z : O), z ∈ M → ∃ c, z + c • y' ∈ M'
    intro z zM
    -- ⊢ ∃ c, z + c • y' ∈ M'
    refine' ⟨-ϕ ⟨z, zM⟩, ⟨⟨z, zM⟩ - ϕ ⟨z, zM⟩ • ⟨y', y'M⟩, LinearMap.mem_ker.mpr _, _⟩⟩
    -- ⊢ ↑ϕ ({ val := z, property := zM } - ↑ϕ { val := z, property := zM } • { val : …
    · rw [LinearMap.map_sub, LinearMap.map_smul, ϕy'_eq, smul_eq_mul, mul_one, sub_self]
      -- 🎉 no goals
    · rw [LinearMap.map_sub, LinearMap.map_smul, sub_eq_add_neg, neg_smul]
      -- ⊢ ↑(Submodule.subtype M) { val := z, property := zM } + -(↑ϕ { val := z, prope …
      rfl
      -- 🎉 no goals
  -- It remains to show the extended bases are compatible with each other.
  intro as h
  -- ⊢ ∃ as', ∀ (i : Fin (n' + 1)), ↑(↑(Basis.mkFinConsOfLE y yN bN' N'_le_N (_ : ∀ …
  refine' ⟨Fin.cons a as, _⟩
  -- ⊢ ∀ (i : Fin (n' + 1)), ↑(↑(Basis.mkFinConsOfLE y yN bN' N'_le_N (_ : ∀ (c : R …
  intro i
  -- ⊢ ↑(↑(Basis.mkFinConsOfLE y yN bN' N'_le_N (_ : ∀ (c : R) (z : O), z ∈ N' → c  …
  rw [Basis.coe_mkFinConsOfLE, Basis.coe_mkFinConsOfLE]
  -- ⊢ ↑(Fin.cons { val := y, property := yN } (↑(ofLe N'_le_N) ∘ ↑bN') i) = Fin.co …
  refine' Fin.cases _ (fun i ↦ _) i
  -- ⊢ ↑(Fin.cons { val := y, property := yN } (↑(ofLe N'_le_N) ∘ ↑bN') 0) = Fin.co …
  · simp only [Fin.cons_zero, Fin.castLE_zero]
    -- ⊢ y = generator (LinearMap.submoduleImage (Exists.choose this) N) • ∑ x : ι, ↑ …
    exact a_smul_y'.symm
    -- 🎉 no goals
  · rw [Fin.castLE_succ]
    -- ⊢ ↑(Fin.cons { val := y, property := yN } (↑(ofLe N'_le_N) ∘ ↑bN') (Fin.succ i …
    simp only [Fin.cons_succ, Function.comp_apply, coe_ofLe, map_coe, coeSubtype, h i]
    -- 🎉 no goals
#align submodule.basis_of_pid_aux Submodule.basis_of_pid_aux

/-- A submodule of a free `R`-module of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain.

This is a `lemma` to make the induction a bit easier. To actually access the basis,
see `Submodule.basisOfPid`.

See also the stronger version `Submodule.smithNormalForm`.
-/
theorem Submodule.nonempty_basis_of_pid {ι : Type*} [Finite ι] (b : Basis ι R M)
    (N : Submodule R M) : ∃ n : ℕ, Nonempty (Basis (Fin n) R N) := by
  haveI := Classical.decEq M
  -- ⊢ ∃ n, Nonempty (Basis (Fin n) R { x // x ∈ N })
  cases nonempty_fintype ι
  -- ⊢ ∃ n, Nonempty (Basis (Fin n) R { x // x ∈ N })
  induction' N using inductionOnRank with N ih
  · exact b
    -- 🎉 no goals
  let b' := (b.reindex (Fintype.equivFin ι)).map (LinearEquiv.ofTop _ rfl).symm
  -- ⊢ ∃ n, Nonempty (Basis (Fin n) R { x // x ∈ N })
  by_cases N_bot : N = ⊥
  · subst N_bot
    -- ⊢ ∃ n, Nonempty (Basis (Fin n) R { x // x ∈ ⊥ })
    exact ⟨0, ⟨Basis.empty _⟩⟩
    -- 🎉 no goals
  obtain ⟨y, -, a, hay, M', -, N', N'_le_N, -, -, ay_ortho, h'⟩ :=
    Submodule.basis_of_pid_aux ⊤ N b' N_bot le_top
  obtain ⟨n', ⟨bN'⟩⟩ := ih N' N'_le_N _ hay ay_ortho
  -- ⊢ ∃ n, Nonempty (Basis (Fin n) R { x // x ∈ N })
  obtain ⟨bN, _hbN⟩ := h' n' bN'
  -- ⊢ ∃ n, Nonempty (Basis (Fin n) R { x // x ∈ N })
  exact ⟨n' + 1, ⟨bN⟩⟩
  -- ⊢ Fintype ι
  infer_instance
  -- 🎉 no goals
#align submodule.nonempty_basis_of_pid Submodule.nonempty_basis_of_pid

/-- A submodule of a free `R`-module of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain.

See also the stronger version `Submodule.smithNormalForm`.
-/
noncomputable def Submodule.basisOfPid {ι : Type*} [Finite ι] (b : Basis ι R M)
    (N : Submodule R M) : Σn : ℕ, Basis (Fin n) R N :=
  ⟨_, (N.nonempty_basis_of_pid b).choose_spec.some⟩
#align submodule.basis_of_pid Submodule.basisOfPid

theorem Submodule.basisOfPid_bot {ι : Type*} [Finite ι] (b : Basis ι R M) :
    Submodule.basisOfPid b ⊥ = ⟨0, Basis.empty _⟩ := by
  obtain ⟨n, b'⟩ := Submodule.basisOfPid b ⊥
  -- ⊢ { fst := n, snd := b' } = { fst := 0, snd := Basis.empty { x // x ∈ ⊥ } }
  let e : Fin n ≃ Fin 0 := b'.indexEquiv (Basis.empty _ : Basis (Fin 0) R (⊥ : Submodule R M))
  -- ⊢ { fst := n, snd := b' } = { fst := 0, snd := Basis.empty { x // x ∈ ⊥ } }
  obtain rfl : n = 0 := by simpa using Fintype.card_eq.mpr ⟨e⟩
  -- ⊢ { fst := 0, snd := b' } = { fst := 0, snd := Basis.empty { x // x ∈ ⊥ } }
  exact Sigma.eq rfl (Basis.eq_of_apply_eq <| finZeroElim)
  -- 🎉 no goals
#align submodule.basis_of_pid_bot Submodule.basisOfPid_bot

/-- A submodule inside a free `R`-submodule of finite rank is also a free `R`-module of finite rank,
if `R` is a principal ideal domain.

See also the stronger version `Submodule.smithNormalFormOfLE`.
-/
noncomputable def Submodule.basisOfPidOfLE {ι : Type*} [Finite ι] {N O : Submodule R M}
    (hNO : N ≤ O) (b : Basis ι R O) : Σn : ℕ, Basis (Fin n) R N :=
  let ⟨n, bN'⟩ := Submodule.basisOfPid b (N.comap O.subtype)
  ⟨n, bN'.map (Submodule.comapSubtypeEquivOfLe hNO)⟩
#align submodule.basis_of_pid_of_le Submodule.basisOfPidOfLE

/-- A submodule inside the span of a linear independent family is a free `R`-module of finite rank,
if `R` is a principal ideal domain. -/
noncomputable def Submodule.basisOfPidOfLESpan {ι : Type*} [Finite ι] {b : ι → M}
    (hb : LinearIndependent R b) {N : Submodule R M} (le : N ≤ Submodule.span R (Set.range b)) :
    Σn : ℕ, Basis (Fin n) R N :=
  Submodule.basisOfPidOfLE le (Basis.span hb)
#align submodule.basis_of_pid_of_le_span Submodule.basisOfPidOfLESpan

/-- A finite type torsion free module over a PID admits a basis. -/
noncomputable def Module.basisOfFiniteTypeTorsionFree [Fintype ι] {s : ι → M}
    (hs : span R (range s) = ⊤) [NoZeroSMulDivisors R M] : Σn : ℕ, Basis (Fin n) R M := by
  classical
    -- We define `N` as the submodule spanned by a maximal linear independent subfamily of `s`
    have := exists_maximal_independent R s
    let I : Set ι := this.choose
    obtain
      ⟨indepI : LinearIndependent R (s ∘ (fun x => x) : I → M), hI :
        ∀ (i) (_ : i ∉ I), ∃ a : R, a ≠ 0 ∧ a • s i ∈ span R (s '' I)⟩ :=
      this.choose_spec
    let N := span R (range <| (s ∘ (fun x => x) : I → M))
    -- same as `span R (s '' I)` but more convenient
    let _sI : I → N := fun i ↦ ⟨s i.1, subset_span (mem_range_self i)⟩
    -- `s` restricted to `I` is a basis of `N`
    let sI_basis : Basis I R N := Basis.span indepI
    -- Our first goal is to build `A ≠ 0` such that `A • M ⊆ N`
    have exists_a : ∀ i : ι, ∃ a : R, a ≠ 0 ∧ a • s i ∈ N := by
      intro i
      by_cases hi : i ∈ I
      · use 1, zero_ne_one.symm
        rw [one_smul]
        exact subset_span (mem_range_self (⟨i, hi⟩ : I))
      · simpa [image_eq_range s I] using hI i hi
    choose a ha ha' using exists_a
    let A := ∏ i, a i
    have hA : A ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      simpa using ha
    -- `M ≃ A • M` because `M` is torsion free and `A ≠ 0`
    let φ : M →ₗ[R] M := LinearMap.lsmul R M A
    have : LinearMap.ker φ = ⊥ := @LinearMap.ker_lsmul R M _ _ _ _ _ hA
    let ψ := LinearEquiv.ofInjective φ (LinearMap.ker_eq_bot.mp this)
    have : LinearMap.range φ ≤ N := by
      -- as announced, `A • M ⊆ N`
      suffices ∀ i, φ (s i) ∈ N by
        rw [LinearMap.range_eq_map, ← hs, map_span_le]
        rintro _ ⟨i, rfl⟩
        apply this
      intro i
      calc
        (∏ j, a j) • s i = (∏ j in {i}ᶜ, a j) • a i • s i := by
          rw [Fintype.prod_eq_prod_compl_mul i, mul_smul]
        _ ∈ N := N.smul_mem _ (ha' i)

    -- Since a submodule of a free `R`-module is free, we get that `A • M` is free
    obtain ⟨n, b : Basis (Fin n) R (LinearMap.range φ)⟩ := Submodule.basisOfPidOfLE this sI_basis
    -- hence `M` is free.
    exact ⟨n, b.map ψ.symm⟩
#align module.basis_of_finite_type_torsion_free Module.basisOfFiniteTypeTorsionFree

theorem Module.free_of_finite_type_torsion_free [_root_.Finite ι] {s : ι → M}
    (hs : span R (range s) = ⊤) [NoZeroSMulDivisors R M] : Module.Free R M := by
  cases nonempty_fintype ι
  -- ⊢ Free R M
  obtain ⟨n, b⟩ : Σn, Basis (Fin n) R M := Module.basisOfFiniteTypeTorsionFree hs
  -- ⊢ Free R M
  exact Module.Free.of_basis b
  -- 🎉 no goals
#align module.free_of_finite_type_torsion_free Module.free_of_finite_type_torsion_free

/-- A finite type torsion free module over a PID admits a basis. -/
noncomputable def Module.basisOfFiniteTypeTorsionFree' [Module.Finite R M]
    [NoZeroSMulDivisors R M] : Σn : ℕ, Basis (Fin n) R M :=
  Module.basisOfFiniteTypeTorsionFree Module.Finite.exists_fin.choose_spec.choose_spec
#align module.basis_of_finite_type_torsion_free' Module.basisOfFiniteTypeTorsionFree'

-- It would be nice to make this an instance but it is empirically problematic, possibly because
-- of the loop that it causes with `Module.Free.noZeroSMulDivisors`
theorem Module.free_of_finite_type_torsion_free' [Module.Finite R M] [NoZeroSMulDivisors R M] :
    Module.Free R M := by
  obtain ⟨n, b⟩ : Σn, Basis (Fin n) R M := Module.basisOfFiniteTypeTorsionFree'
  -- ⊢ Free R M
  exact Module.Free.of_basis b
  -- 🎉 no goals
#align module.free_of_finite_type_torsion_free' Module.free_of_finite_type_torsion_free'

section SmithNormal

/-- A Smith normal form basis for a submodule `N` of a module `M` consists of
bases for `M` and `N` such that the inclusion map `N → M` can be written as a
(rectangular) matrix with `a` along the diagonal: in Smith normal form. -/
-- Porting note: @[nolint has_nonempty_instance]
structure Basis.SmithNormalForm (N : Submodule R M) (ι : Type*) (n : ℕ) where
  /-- The basis of M. -/
  bM : Basis ι R M
  /-- The basis of N. -/
  bN : Basis (Fin n) R N
  /-- The mapping between the vectors of the bases. -/
  f : Fin n ↪ ι
  /-- The (diagonal) entries of the matrix. -/
  a : Fin n → R
  /-- The SNF relation between the vectors of the bases. -/
  snf : ∀ i, (bN i : M) = a i • bM (f i)
#align basis.smith_normal_form Basis.SmithNormalForm

namespace Basis.SmithNormalForm

variable {n : ℕ} {N : Submodule R M} (snf : Basis.SmithNormalForm N ι n) (m : N)

lemma repr_eq_zero_of_nmem_range {i : ι} (hi : i ∉ Set.range snf.f) :
    snf.bM.repr m i = 0 := by
  obtain ⟨m, hm⟩ := m
  -- ⊢ ↑(↑snf.bM.repr ↑{ val := m, property := hm }) i = 0
  obtain ⟨c, rfl⟩ := snf.bN.mem_submodule_iff.mp hm
  -- ⊢ ↑(↑snf.bM.repr ↑{ val := Finsupp.sum c fun i x => x • ↑(↑snf.bN i), property …
  replace hi : ∀ j, snf.f j ≠ i := by simpa using hi
  -- ⊢ ↑(↑snf.bM.repr ↑{ val := Finsupp.sum c fun i x => x • ↑(↑snf.bN i), property …
  simp [Finsupp.single_apply, hi, snf.snf]
  -- 🎉 no goals

lemma le_ker_coord_of_nmem_range {i : ι} (hi : i ∉ Set.range snf.f) :
    N ≤ LinearMap.ker (snf.bM.coord i) :=
  fun m hm ↦ snf.repr_eq_zero_of_nmem_range ⟨m, hm⟩ hi

@[simp] lemma repr_apply_embedding_eq_repr_smul {i : Fin n} :
    snf.bM.repr m (snf.f i) = snf.bN.repr (snf.a i • m) i := by
  obtain ⟨m, hm⟩ := m
  -- ⊢ ↑(↑snf.bM.repr ↑{ val := m, property := hm }) (↑snf.f i) = ↑(↑snf.bN.repr (a …
  obtain ⟨c, rfl⟩ := snf.bN.mem_submodule_iff.mp hm
  -- ⊢ ↑(↑snf.bM.repr ↑{ val := Finsupp.sum c fun i x => x • ↑(↑snf.bN i), property …
  replace hm : (⟨Finsupp.sum c fun i t ↦ t • (↑(snf.bN i) : M), hm⟩ : N) =
      Finsupp.sum c fun i t ↦ t • ⟨snf.bN i, (snf.bN i).2⟩ := by ext; change _ = N.subtype _; simp
  classical
  simp_rw [hm, map_smul, LinearEquiv.map_finsupp_sum, map_smul, Subtype.coe_eta, repr_self,
    Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum_single, Finsupp.smul_apply, snf.snf,
    map_smul, repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum_apply,
    Finsupp.single_apply, EmbeddingLike.apply_eq_iff_eq, Finsupp.sum_ite_eq',
    Finsupp.mem_support_iff, ite_not, mul_comm, ite_eq_right_iff]
  exact fun a ↦ (mul_eq_zero_of_right _ a).symm

@[simp] lemma repr_comp_embedding_eq_smul :
    snf.bM.repr m ∘ snf.f = snf.a • (snf.bN.repr m : Fin n → R) := by
  ext i
  -- ⊢ (↑(↑snf.bM.repr ↑m) ∘ ↑snf.f) i = (snf.a • ↑(↑snf.bN.repr m)) i
  simp [Pi.smul_apply (snf.a i)]
  -- 🎉 no goals

@[simp] lemma coord_apply_embedding_eq_smul_coord {i : Fin n} :
    snf.bM.coord (snf.f i) ∘ₗ N.subtype = snf.a i • snf.bN.coord i := by
  ext m
  -- ⊢ ↑(LinearMap.comp (coord snf.bM (↑snf.f i)) (Submodule.subtype N)) m = ↑(a sn …
  simp [Pi.smul_apply (snf.a i)]
  -- 🎉 no goals

/-- Given a Smith-normal-form pair of bases for `N ⊆ M`, and a linear endomorphism `f` of `M`
that preserves `N`, the diagonal of the matrix of the restriction `f` to `N` does not depend on
which of the two bases for `N` is used. -/
@[simp]
lemma toMatrix_restrict_eq_toMatrix [Fintype ι] [DecidableEq ι]
    (f : M →ₗ[R] M) (hf : ∀ x, f x ∈ N) (hf' : ∀ x ∈ N, f x ∈ N := fun x _ ↦ hf x) {i : Fin n} :
    LinearMap.toMatrix snf.bN snf.bN (LinearMap.restrict f hf') i i =
    LinearMap.toMatrix snf.bM snf.bM f (snf.f i) (snf.f i) := by
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    snf.repr_apply_embedding_eq_repr_smul ⟨_, (hf _)⟩]
  congr
  -- ⊢ ↑(LinearMap.restrict f hf') (↑snf.bN i) = a snf i • { val := ↑f (↑snf.bM (↑s …
  ext
  -- ⊢ ↑(↑(LinearMap.restrict f hf') (↑snf.bN i)) = ↑(a snf i • { val := ↑f (↑snf.b …
  simp [snf.snf]
  -- 🎉 no goals

end Basis.SmithNormalForm

/-- If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagonal matrix
in Smith normal form.

See `Submodule.smithNormalFormOfLE` for a version of this theorem that returns
a `Basis.SmithNormalForm`.

This is a strengthening of `Submodule.basisOfPidOfLE`.
-/
theorem Submodule.exists_smith_normal_form_of_le [Finite ι] (b : Basis ι R M) (N O : Submodule R M)
    (N_le_O : N ≤ O) :
    ∃ (n o : ℕ) (hno : n ≤ o) (bO : Basis (Fin o) R O) (bN : Basis (Fin n) R N) (a : Fin n → R),
      ∀ i, (bN i : M) = a i • bO (Fin.castLE hno i) := by
  cases nonempty_fintype ι
  -- ⊢ ∃ n o hno bO bN a, ∀ (i : Fin n), ↑(↑bN i) = ↑(a i • ↑bO (Fin.castLE hno i))
  revert N
  -- ⊢ ∀ (N : Submodule R M), N ≤ O → ∃ n o hno bO bN a, ∀ (i : Fin n), ↑(↑bN i) =  …
  induction' O using inductionOnRank with M0 ih
  · exact b
    -- 🎉 no goals
  intro N N_le_M0
  -- ⊢ ∃ n o hno bO bN a, ∀ (i : Fin n), ↑(↑bN i) = ↑(a i • ↑bO (Fin.castLE hno i))
  obtain ⟨m, b'M⟩ := M0.basisOfPid b
  -- ⊢ ∃ n o hno bO bN a, ∀ (i : Fin n), ↑(↑bN i) = ↑(a i • ↑bO (Fin.castLE hno i))
  by_cases N_bot : N = ⊥
  · subst N_bot
    -- ⊢ ∃ n o hno bO bN a, ∀ (i : Fin n), ↑(↑bN i) = ↑(a i • ↑bO (Fin.castLE hno i))
    exact ⟨0, m, Nat.zero_le _, b'M, Basis.empty _, finZeroElim, finZeroElim⟩
    -- 🎉 no goals
  obtain ⟨y, hy, a, _, M', M'_le_M, N', _, N'_le_M', y_ortho, _, h⟩ :=
    Submodule.basis_of_pid_aux M0 N b'M N_bot N_le_M0

  obtain ⟨n', m', hn'm', bM', bN', as', has'⟩ := ih M' M'_le_M y hy y_ortho N' N'_le_M'
  -- ⊢ ∃ n o hno bO bN a, ∀ (i : Fin n), ↑(↑bN i) = ↑(a i • ↑bO (Fin.castLE hno i))
  obtain ⟨bN, h'⟩ := h n' bN'
  -- ⊢ ∃ n o hno bO bN a, ∀ (i : Fin n), ↑(↑bN i) = ↑(a i • ↑bO (Fin.castLE hno i))
  obtain ⟨hmn, bM, h''⟩ := h' m' hn'm' bM'
  -- ⊢ ∃ n o hno bO bN a, ∀ (i : Fin n), ↑(↑bN i) = ↑(a i • ↑bO (Fin.castLE hno i))
  obtain ⟨as, has⟩ := h'' as' has'
  -- ⊢ ∃ n o hno bO bN a, ∀ (i : Fin n), ↑(↑bN i) = ↑(a i • ↑bO (Fin.castLE hno i))
  exact ⟨_, _, hmn, bM, bN, as, has⟩
  -- ⊢ Fintype ι
-- Porting note: Lean generates a goal Fintype ι for some reason
  infer_instance
  -- 🎉 no goals
#align submodule.exists_smith_normal_form_of_le Submodule.exists_smith_normal_form_of_le

/-- If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagonal matrix
in Smith normal form.

See `Submodule.exists_smith_normal_form_of_le` for a version of this theorem that doesn't
need to map `N` into a submodule of `O`.

This is a strengthening of `Submodule.basisOfPidOfLe`.
-/
noncomputable def Submodule.smithNormalFormOfLE [Finite ι] (b : Basis ι R M) (N O : Submodule R M)
    (N_le_O : N ≤ O) : Σo n : ℕ, Basis.SmithNormalForm (N.comap O.subtype) (Fin o) n := by
  choose n o hno bO bN a snf using N.exists_smith_normal_form_of_le b O N_le_O
  -- ⊢ (o : ℕ) × (n : ℕ) × Basis.SmithNormalForm (comap (Submodule.subtype O) N) (F …
  refine'
    ⟨o, n, bO, bN.map (comapSubtypeEquivOfLe N_le_O).symm, (Fin.castLEEmb hno).toEmbedding, a,
      fun i ↦ _⟩
  ext
  -- ⊢ ↑↑(↑(Basis.map bN (LinearEquiv.symm (comapSubtypeEquivOfLe N_le_O))) i) = ↑( …
  simp only [snf, Basis.map_apply, Submodule.comapSubtypeEquivOfLe_symm_apply,
    Submodule.coe_smul_of_tower, RelEmbedding.coe_toEmbedding, Fin.castLEEmb_apply]
#align submodule.smith_normal_form_of_le Submodule.smithNormalFormOfLE

/-- If `M` is finite free over a PID `R`, then any submodule `N` is free
and we can find a basis for `M` and `N` such that the inclusion map is a diagonal matrix
in Smith normal form.

This is a strengthening of `Submodule.basisOfPid`.

See also `Ideal.smithNormalForm`, which moreover proves that the dimension of
an ideal is the same as the dimension of the whole ring.
-/
noncomputable def Submodule.smithNormalForm [Finite ι] (b : Basis ι R M) (N : Submodule R M) :
    Σn : ℕ, Basis.SmithNormalForm N ι n :=
  let ⟨m, n, bM, bN, f, a, snf⟩ := N.smithNormalFormOfLE b ⊤ le_top
  let bM' := bM.map (LinearEquiv.ofTop _ rfl)
  let e := bM'.indexEquiv b
  ⟨n, bM'.reindex e, bN.map (comapSubtypeEquivOfLe le_top), f.trans e.toEmbedding, a, fun i ↦ by
    simp only [snf, Basis.map_apply, LinearEquiv.ofTop_apply, Submodule.coe_smul_of_tower,
      Submodule.comapSubtypeEquivOfLe_apply_coe, Basis.reindex_apply,
      Equiv.toEmbedding_apply, Function.Embedding.trans_apply, Equiv.symm_apply_apply]⟩
#align submodule.smith_normal_form Submodule.smithNormalForm

section Ideal

variable {S : Type*} [CommRing S] [IsDomain S] [Algebra R S]

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix.

See `Ideal.exists_smith_normal_form` for a version of this theorem that doesn't
need to map `I` into a submodule of `R`.

This is a strengthening of `Submodule.basisOfPid`.
-/
noncomputable def Ideal.smithNormalForm [Fintype ι] (b : Basis ι R S) (I : Ideal S) (hI : I ≠ ⊥) :
    Basis.SmithNormalForm (I.restrictScalars R) ι (Fintype.card ι) :=
  let ⟨n, bS, bI, f, a, snf⟩ := (I.restrictScalars R).smithNormalForm b
  have eq := Ideal.rank_eq bS hI (bI.map ((restrictScalarsEquiv R S S I).restrictScalars R))
  let e : Fin n ≃ Fin (Fintype.card ι) := Fintype.equivOfCardEq (by rw [eq, Fintype.card_fin])
                                                                    -- 🎉 no goals
  ⟨bS, bI.reindex e, e.symm.toEmbedding.trans f, a ∘ e.symm, fun i ↦ by
    simp only [snf, Basis.coe_reindex, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      (· ∘ ·)]⟩
#align ideal.smith_normal_form Ideal.smithNormalForm

variable [Finite ι]

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix.

See also `Ideal.smithNormalForm` for a version of this theorem that returns
a `Basis.SmithNormalForm`.

The definitions `Ideal.ringBasis`, `Ideal.selfBasis`, `Ideal.smithCoeffs` are (noncomputable)
choices of values for this existential quantifier.
-/
theorem Ideal.exists_smith_normal_form (b : Basis ι R S) (I : Ideal S) (hI : I ≠ ⊥) :
    ∃ (b' : Basis ι R S) (a : ι → R) (ab' : Basis ι R I), ∀ i, (ab' i : S) = a i • b' i := by
  cases nonempty_fintype ι
  -- ⊢ ∃ b' a ab', ∀ (i : ι), ↑(↑ab' i) = a i • ↑b' i
  let ⟨bS, bI, f, a, snf⟩ := I.smithNormalForm b hI
  -- ⊢ ∃ b' a ab', ∀ (i : ι), ↑(↑ab' i) = a i • ↑b' i
  let e : Fin (Fintype.card ι) ≃ ι :=
    Equiv.ofBijective f
      ((Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, Fintype.card_fin _⟩)
  have fe : ∀ i, f (e.symm i) = i := e.apply_symm_apply
  -- ⊢ ∃ b' a ab', ∀ (i : ι), ↑(↑ab' i) = a i • ↑b' i
  exact
    ⟨bS, a ∘ e.symm, (bI.reindex e).map ((restrictScalarsEquiv R S _ _).restrictScalars R),
      fun i ↦ by
        simp only [snf, fe, Basis.map_apply, LinearEquiv.restrictScalars_apply R,
          Submodule.restrictScalarsEquiv_apply, Basis.coe_reindex, (· ∘ ·)]⟩
#align ideal.exists_smith_normal_form Ideal.exists_smith_normal_form

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix; this is the basis for `S`.
See `Ideal.selfBasis` for the basis on `I`,
see `Ideal.smithCoeffs` for the entries of the diagonal matrix
and `Ideal.selfBasis_def` for the proof that the inclusion map forms a square diagonal matrix.
-/
noncomputable def Ideal.ringBasis (b : Basis ι R S) (I : Ideal S) (hI : I ≠ ⊥) : Basis ι R S :=
  (Ideal.exists_smith_normal_form b I hI).choose
#align ideal.ring_basis Ideal.ringBasis

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix; this is the basis for `I`.
See `Ideal.ringBasis` for the basis on `S`,
see `Ideal.smithCoeffs` for the entries of the diagonal matrix
and `Ideal.selfBasis_def` for the proof that the inclusion map forms a square diagonal matrix.
-/
noncomputable def Ideal.selfBasis (b : Basis ι R S) (I : Ideal S) (hI : I ≠ ⊥) : Basis ι R I :=
  (Ideal.exists_smith_normal_form b I hI).choose_spec.choose_spec.choose
#align ideal.self_basis Ideal.selfBasis

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix; these are the entries of the diagonal matrix.
See `Ideal.ringBasis` for the basis on `S`,
see `Ideal.selfBasis` for the basis on `I`,
and `Ideal.selfBasis_def` for the proof that the inclusion map forms a square diagonal matrix.
-/
noncomputable def Ideal.smithCoeffs (b : Basis ι R S) (I : Ideal S) (hI : I ≠ ⊥) : ι → R :=
  (Ideal.exists_smith_normal_form b I hI).choose_spec.choose
#align ideal.smith_coeffs Ideal.smithCoeffs

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix.
-/
@[simp]
theorem Ideal.selfBasis_def (b : Basis ι R S) (I : Ideal S) (hI : I ≠ ⊥) :
    ∀ i, (Ideal.selfBasis b I hI i : S) = Ideal.smithCoeffs b I hI i • Ideal.ringBasis b I hI i :=
  (Ideal.exists_smith_normal_form b I hI).choose_spec.choose_spec.choose_spec
#align ideal.self_basis_def Ideal.selfBasis_def

@[simp]
theorem Ideal.smithCoeffs_ne_zero (b : Basis ι R S) (I : Ideal S) (hI : I ≠ ⊥) (i) :
    Ideal.smithCoeffs b I hI i ≠ 0 := by
  intro hi
  -- ⊢ False
  apply Basis.ne_zero (Ideal.selfBasis b I hI) i
  -- ⊢ ↑(selfBasis b I hI) i = 0
  refine' Subtype.coe_injective _
  -- ⊢ (fun a => ↑a) (↑(selfBasis b I hI) i) = (fun a => ↑a) 0
  simp [hi]
  -- 🎉 no goals
#align ideal.smith_coeffs_ne_zero Ideal.smithCoeffs_ne_zero

-- porting note: can be inferred in Lean 4 so no longer necessary
#noalign has_quotient.quotient.module

end Ideal

end SmithNormal

end PrincipalIdealDomain

/-- A set of linearly independent vectors in a module `M` over a semiring `S` is also linearly
independent over a subring `R` of `K`. -/
theorem LinearIndependent.restrict_scalars_algebras {R S M ι : Type*} [CommSemiring R] [Semiring S]
    [AddCommMonoid M] [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]
    (hinj : Function.Injective (algebraMap R S)) {v : ι → M} (li : LinearIndependent S v) :
    LinearIndependent R v :=
  LinearIndependent.restrict_scalars (by rwa [Algebra.algebraMap_eq_smul_one'] at hinj) li
                                         -- 🎉 no goals
#align linear_independent.restrict_scalars_algebras LinearIndependent.restrict_scalars_algebras
