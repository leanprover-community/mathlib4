import Mathlib.Order.KrullDimension
import Mathlib.Order.TrimmedLength
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Data.ENat.Lattice
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# The length of a module
-/

variable {R : Type*} [Ring R] {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']

open Order

variable (R M) in
/--
The length of a module M is defined to be the supremum of lengths of chains of submodules of M. We
define this using the existing krull dimension api, and as a result this takes values in
WithBot ℕ∞ in spite of the fact that there is no module with length equal to ⊥.
-/
noncomputable def Module.length : WithBot ℕ∞ := krullDim (α := Submodule R M)

lemma Module.length_nonneg : 0 ≤ Module.length R M :=
  haveI : Nonempty (Submodule R M) := ⟨⊤⟩
  krullDim_nonneg

lemma Module.length_ne_bot : Module.length R M ≠ ⊥ := by
  intro h
  rw [Module.length, krullDim_eq_bot_iff] at h
  exact IsEmpty.false (⊤ : Submodule R M)

@[simp] lemma Module.length_eq_zero_iff : Module.length R M = 0 ↔ Subsingleton M := by
  rw [Module.length, orderTop_krullDim_eq_zero_iff, Submodule.subsingleton_iff]

lemma isSimpleModule_length_eq_one (M : Type*) [AddCommGroup M] [Module R M] [IsSimpleModule R M] :
    Module.length R M = 1 := by rw [Module.length]; exact Order.krullDim_isSimpleOrder

lemma isSimpleModule_iff_length_eq_one (M : Type*) [AddCommGroup M] [Module R M] :
    IsSimpleModule R M ↔ Module.length R M = 1 := by
  constructor
  · intro h; exact isSimpleModule_length_eq_one (R := R) M
  · rw [Module.length, orderBot_orderTop_krullDim_eq_one_iff]
    intro h; exact h

lemma exists_maximal_submodule_of_length_ne_zero_top (M : Type*) [AddCommGroup M] [Module R M]
    (h : Module.length R M ≠ 0) (h' : Module.length R M ≠ ⊤) : ∃ N : Submodule R M, IsCoatom N := by
  have : FiniteDimensionalOrder (Submodule R M) := by
    apply Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mpr
    refine ⟨Module.length_ne_bot, by exact h'⟩
  have : Nontrivial (Submodule R M) := by
    by_contra h'; rw [not_nontrivial_iff_subsingleton] at h'
    have : Module.length R M ≤ 0 := by
      rw [Module.length]
      exact Order.krullDim_nonpos_of_subsingleton
    exact h (le_antisymm this Module.length_nonneg)
  exact exists_coatom_of_finiteDimensional

open Classical in
/--
The length of a module is greater than or equal to the trimmedLength of any
rs : RelSeries (α := Submodule R M) (· ≤ ·).
-/
theorem RelSeries.moduleLength_ge_trimmedLength (rs : RelSeries (α := Submodule R M) (· ≤ ·)) :
    RelSeries.trimmedLength rs ≤ Module.length R M := by
  rw [← rs.trim_length, Module.length, krullDim]
  exact le_iSup_iff.mpr fun b a ↦ a rs.trim


open Classical in
/-- The module length is additive in short exact sequences. -/
theorem Module.length_additive {S : CategoryTheory.ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    Module.length R S.X₂ = Module.length R S.X₁ + Module.length R S.X₃ := by
  simp only [length, krullDim, le_antisymm_iff, iSup_le_iff]
  constructor
  · intro rs
    trans ((RelSeries.submoduleComap rs S.f.hom).trimmedLength +
            (RelSeries.submoduleMap rs S.g.hom).trimmedLength)
    · apply Nat.mono_cast
      have trimmedProof := RelSeries.trimmedLength_additive hS rs
      rwa [Nat.add_comm] at trimmedProof
    · have trimleft :=
        RelSeries.moduleLength_ge_trimmedLength (RelSeries.submoduleComap rs S.f.hom)
      have trimright :=
        RelSeries.moduleLength_ge_trimmedLength (RelSeries.submoduleMap rs S.g.hom)
      exact add_le_add trimleft trimright
  · rw [WithBot.iSup_le_add]
    intro rstemp rstemp'
    obtain ⟨rs, hrs⟩ := RelSeries.exists_ltSeries_ge_head_bot_last_top rstemp
    obtain ⟨rs', hrs'⟩ := RelSeries.exists_ltSeries_ge_head_bot_last_top rstemp'
    let gInv : RelSeries (fun (a : Submodule R S.X₂) (b : Submodule R S.X₂) => a < b) :=
      LTSeries.map rs' (Submodule.comap S.g.hom)
      (Submodule.comap_strictMono_of_surjective hS.moduleCat_surjective_g)
    let fIm : RelSeries (fun (a : Submodule R S.X₂) (b : Submodule R S.X₂) => a < b) :=
      LTSeries.map rs (Submodule.map S.f.hom)
      (Submodule.map_strictMono_of_injective hS.moduleCat_injective_f)
    have connect : fIm.last = gInv.head := by
      convert CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker hS.exact
      · simp only [RelSeries.last, LTSeries.map_length, LTSeries.map_toFun, fIm]
        have obv : (rs.toFun (Fin.last rs.length)) = ⊤ := hrs.2.2
        rw [obv]; exact Submodule.map_top S.f.hom
      · simp only [RelSeries.head, LTSeries.map_toFun, gInv]
        have obv : rs'.toFun 0 = ⊥ := hrs'.2.1
        rw [obv]; exact rfl
    let smashfg := RelSeries.smash fIm gInv connect
    trans ↑smashfg.length
    · have this' : smashfg.length = rs.length + rs'.length := rfl
      rw [this']
      simp only [Nat.cast_add, ge_iff_le]
      apply add_le_add
      all_goals simp only [Nat.cast_le, hrs.1, hrs'.1]
    · exact le_iSup_iff.mpr fun b a ↦ a smashfg


theorem Module.length_additive_of_quotient {N : Submodule R M} :
  Module.length R M = Module.length R N + Module.length R (M ⧸ N) := by
  let quotientSeq : CategoryTheory.ShortComplex (ModuleCat R) := {
    X₁ := ModuleCat.of R N
    X₂ := ModuleCat.of R M
    X₃ := ModuleCat.of R (M ⧸ N)
    f := ModuleCat.ofHom <| Submodule.subtype N
    g := ModuleCat.ofHom <| Submodule.mkQ N
    zero := by
      ext a
      simp
    }
  let ex : quotientSeq.ShortExact := {
    exact := by
      simp[CategoryTheory.ShortComplex.moduleCat_exact_iff]
      intro a b
      have X2 : ↑quotientSeq.X₂ = M := rfl
      have X1 : ↑quotientSeq.X₁ = @Subtype M fun x ↦ x ∈ N := rfl
      let a'' : N := {
        val := a
        property := (Submodule.Quotient.mk_eq_zero N).mp b
      }
      use a''
      aesop
    mono_f := by
      simp[quotientSeq]
      have : Function.Injective (N.subtype) := by exact Submodule.injective_subtype N
      exact (ModuleCat.mono_iff_injective (ModuleCat.ofHom N.subtype)).mpr this
    epi_g := by
      simp[quotientSeq]
      have : Function.Surjective (N.mkQ) := by exact Submodule.mkQ_surjective N
      exact (ModuleCat.epi_iff_surjective (ModuleCat.ofHom N.mkQ)).mpr this
  }
  have := Module.length_additive ex
  aesop

section field

proof_wanted Module.length_eq_rank_of_field (R M : Type*) [Field R] [AddCommGroup M] [Module R M] :
    Module.length R M = (Module.rank R M).toENat := sorry

end field
