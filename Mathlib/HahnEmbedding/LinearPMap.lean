import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Order.CompletePartialOrder

abbrev combine {ι : Type*} {R : Type*} {N : Type*}
    [Semiring R] [AddCommMonoid N] [Module R N] [DecidableEq ι] (p : ι → Submodule R N) :
    (Π₀ (i : ι), ↥(p i)) →ₗ[R] ((⨆ i : ι, p i) : Submodule R N) where

  toFun (f) := ⟨((DFinsupp.lsum ℕ) fun (i : ι) => (p i).subtype) f, by
    simp only [DFinsupp.lsum_apply_apply]
    apply Submodule.dfinsuppSumAddHom_mem
    intro i h0
    apply Submodule.mem_iSup_of_mem i
    simp
  ⟩
  map_add' := by
    intro a b
    simp
  map_smul' := by
    intro s a
    simp

theorem combine_surjective
    {ι : Type*} {R : Type*} {N : Type*}
    [Semiring R] [AddCommMonoid N] [Module R N] [DecidableEq ι] (p : ι → Submodule R N) :
    Function.Surjective (combine p) := by

  intro x
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp p x.val).mp x.prop
  use f
  rw [Subtype.eq_iff]
  exact hf

theorem combine_injective
    {ι : Type*} {R : Type*} {N : Type*}
    [Ring R] [AddCommGroup N] [Module R N] [DecidableEq ι] {p : ι → Submodule R N}
    (h : iSupIndep p) :
    Function.Injective (combine p) := by

  intro a b hab
  rw [Subtype.eq_iff] at hab
  exact iSupIndep.dfinsupp_lsum_injective h hab

noncomputable
abbrev combine_equiv {ι : Type*} {R : Type*} {N : Type*}
    [Ring R] [AddCommGroup N] [Module R N] [DecidableEq ι] {p : ι → Submodule R N}
    (h : iSupIndep p) :
    (Π₀ (i : ι), ↥(p i)) ≃ₗ[R] ((⨆ i : ι, p i) : Submodule R N) :=

  LinearEquiv.ofBijective (combine p) ⟨combine_injective h, combine_surjective p⟩

theorem decomp_i {ι : Type*} {R : Type*} {N : Type*}
    [Ring R] [AddCommGroup N] [Module R N] [DecidableEq ι] {p : ι → Submodule R N}
    (h : iSupIndep p) {x :  ((⨆ i : ι, p i) : Submodule R N)}
    {i : ι} (hx : x.val ∈ p i) :
    (combine_equiv h).symm x = DFinsupp.lsingle (R := ℕ) i ⟨x.val, hx⟩ := by

  rw [LinearEquiv.symm_apply_eq]
  simp

noncomputable def LinearPMap.iSup {R : Type*} [Ring R]
    {E : Type*} [AddCommGroup E] [Module R E]
    {F : Type*} [AddCommGroup F] [Module R F]
    {ι : Type*} [DecidableEq ι] {p : ι → (E →ₗ.[R] F)}
    (h : iSupIndep (fun i ↦ (p i).domain)) :
    E →ₗ.[R] F where
  domain := ⨆ i : ι, (p i).domain
  toFun := LinearMap.comp (DFinsupp.lsum ℕ (fun i ↦ (p i).toFun)) (combine_equiv h).symm.toLinearMap

theorem LinearPMap.domain_iSup {R : Type*} [Ring R]
    {E : Type*} [AddCommGroup E] [Module R E]
    {F : Type*} [AddCommGroup F] [Module R F]
    {ι : Type*} [DecidableEq ι] {p : ι → (E →ₗ.[R] F)}
    (h : iSupIndep (fun i ↦ (p i).domain)) :
    (LinearPMap.iSup h).domain = ⨆ i : ι, (p i).domain := by rfl

nonrec
theorem LinearPMap.le_iSup {R : Type*} [Ring R]
    {E : Type*} [AddCommGroup E] [Module R E]
    {F : Type*} [AddCommGroup F] [Module R F]
    {ι : Type*} [DecidableEq ι] {p : ι → (E →ₗ.[R] F)}
    (h : iSupIndep (fun i ↦ (p i).domain)) (i : ι):
    (p i).domain ≤ (LinearPMap.iSup h).domain := by
  rw [LinearPMap.domain_iSup]
  apply le_iSup _ i

theorem LinearPMap.iSup_apply_i {R : Type*} [Ring R]
    {E : Type*} [AddCommGroup E] [Module R E]
    {F : Type*} [AddCommGroup F] [Module R F]
    {ι : Type*} [DecidableEq ι] {p : ι → (E →ₗ.[R] F)}
    (h : iSupIndep (fun i ↦ (p i).domain))
    {x : (LinearPMap.iSup h).domain}
    {i : ι} (hx : x.val ∈ (p i).domain):
    (LinearPMap.iSup h) x = (p i) ⟨x.val, hx⟩ := by

  unfold LinearPMap.iSup
  simp only [mk_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    DFinsupp.lsum_apply_apply]
  rw [decomp_i h hx]
  simp

theorem LinearPMap.iSup_apply {R : Type*} [Ring R]
    {E : Type*} [AddCommGroup E] [Module R E]
    {F : Type*} [AddCommGroup F] [Module R F]
    {ι : Type*} [DecidableEq ι] {p : ι → (E →ₗ.[R] F)}
    (h : iSupIndep (fun i ↦ (p i).domain))
    {x : (LinearPMap.iSup h).domain}
    {f : Π₀ (i : ι), (p i).domain}
    (hx : x.val = ((DFinsupp.lsum ℕ) fun (i : ι) ↦ (p i).domain.subtype) f) :
    (LinearPMap.iSup h) x = ((DFinsupp.lsum ℕ) fun (i : ι) ↦ (p i).toFun) f := by

  unfold LinearPMap.iSup
  simp only [mk_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    DFinsupp.lsum_apply_apply]
  congr
  rw [LinearEquiv.symm_apply_eq]
  rw [Subtype.eq_iff]
  exact hx
