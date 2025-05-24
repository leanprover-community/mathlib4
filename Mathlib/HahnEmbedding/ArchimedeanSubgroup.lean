import Mathlib.HahnEmbedding.Divisible
import Mathlib.HahnEmbedding.RealEmbed

import Mathlib.Algebra.Module.Submodule.Order
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Star
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Binomial


variable {M: Type*}
variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M]

@[to_additive archimedeanSubgroup.of_nonempty]
def mulArchimedeanSubgroup.of_nonempty {s : UpperSet (mulArchimedeanClass M)} (hs : s.carrier.Nonempty) :
    Subgroup M where
  carrier := mulArchimedeanClass.mk ⁻¹' s.carrier
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_preimage] at ha hb ⊢
    obtain h|h := min_le_iff.mp (mulArchimedeanClass.min_le_mk_mul a b)
    · apply s.upper' h ha
    · apply s.upper' h hb
  one_mem' := by
    simp only [Set.mem_preimage]
    obtain ⟨u, hu⟩ := hs
    simpa using s.upper' (mulArchimedeanClass.le_one u) hu
  inv_mem' := by
    intro a h
    simpa using h


open Classical in
@[to_additive archimedeanSubgroup]
noncomputable
def mulArchimedeanSubgroup (s : UpperSet (mulArchimedeanClass M)) : Subgroup M :=
  if hs : s.carrier.Nonempty then
    mulArchimedeanSubgroup.of_nonempty hs
  else
    ⊥


namespace mulArchimedeanSubgroup

@[to_additive]
theorem eq_of_nonempty {s : UpperSet (mulArchimedeanClass M)} (hs : s.carrier.Nonempty) :
    mulArchimedeanSubgroup s = mulArchimedeanSubgroup.of_nonempty hs := by
  unfold mulArchimedeanSubgroup
  simp only [hs]
  simp

@[to_additive]
theorem mem_iff {s : UpperSet (mulArchimedeanClass M)} (hs : s.carrier.Nonempty) (a : M):
    a ∈ mulArchimedeanSubgroup s ↔ mulArchimedeanClass.mk a ∈ s := by
  rw [eq_of_nonempty hs]
  exact Set.mem_preimage

@[to_additive]
theorem lt_of_lt {s t : UpperSet (mulArchimedeanClass M)} (hs : s.carrier.Nonempty) (ht : t.carrier.Nonempty)
    (hst : s < t) : mulArchimedeanSubgroup t < mulArchimedeanSubgroup s := by
  rw [eq_of_nonempty hs, eq_of_nonempty ht]
  apply lt_of_le_of_ne
  · rw [Subgroup.mk_le_mk]
    refine (Set.preimage_subset_preimage_iff (by simp)).mpr ?_
    simpa using hst.le
  · contrapose! hst with heq
    apply le_of_eq
    unfold mulArchimedeanSubgroup.of_nonempty at heq
    simpa [mulArchimedeanClass.mk_surjective] using heq

@[to_additive]
theorem le_of_le {s t : UpperSet (mulArchimedeanClass M)} (hs : s.carrier.Nonempty) (ht : t.carrier.Nonempty)
    (hst : s ≤ t) : mulArchimedeanSubgroup t ≤ mulArchimedeanSubgroup s := by
  obtain hlt|heq := lt_or_eq_of_le hst
  · exact (lt_of_lt hs ht hlt).le
  · apply le_of_eq
    obtain heq' := heq.symm
    congr

end mulArchimedeanSubgroup


section Divisible

variable {M: Type*}
variable [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] [DivisibleBy M ℕ]

namespace archimedeanSubgroup

noncomputable
def toSubmodule (s : UpperSet (archimedeanClass M)) : Submodule ℚ M := {
  archimedeanSubgroup s with
  smul_mem' := by
    by_cases hs : s.carrier.Nonempty
    · intro q a ha
      rw [AddSubgroup.mem_carrier, mem_iff hs] at ha ⊢
      by_cases hq : q.num = 0
      · have : q = 0 := Rat.zero_of_num_zero hq
        rw [this]
        obtain ⟨b, hb⟩ := hs
        simpa using s.upper (archimedeanClass.nonpos b) hb
      · refine Set.mem_of_eq_of_mem ?_ ha
        rw [DivisibleBy.rat_smul_eq]
        rw [archimedeanClass.eq]
        refine ⟨⟨Int.natAbs q.num, by simpa using hq, ?_⟩, ⟨Int.natAbs q.den, by simp, ?_⟩⟩
        · rw [DivisibleBy.abs_div]
          apply le_trans (DivisibleBy.div_le_self (by simp) (by simp))
          rw [abs_zsmul, ← natCast_zsmul]
          exact smul_le_smul_of_nonneg_right (by simp) (by simp)
        · rw [DivisibleBy.abs_div, Int.natAbs_natCast, DivisibleBy.div_cancel _ (by simp), abs_zsmul]
          nth_rw 1 [← one_smul ℤ |a|]
          refine smul_le_smul_of_nonneg_right ?_ (by simp)
          exact Int.one_le_abs hq
    · intro q a ha
      rw [AddSubgroup.mem_carrier] at ha ⊢
      unfold archimedeanSubgroup at ha ⊢
      simp only [hs] at ha ⊢
      simp only [↓reduceDIte, AddSubgroup.mem_bot, smul_eq_zero] at ha ⊢
      exact Or.inr ha
}

theorem mem_submodule_iff_mem (s : UpperSet (archimedeanClass M)) (a : M) :
    a ∈ toSubmodule s ↔ a ∈ archimedeanSubgroup s := by rfl

theorem exists_compl_of_le {s t : UpperSet (archimedeanClass M)} (hs : s.carrier.Nonempty) (ht : t.carrier.Nonempty)
    (hst : s ≤ t) :
    ∃ A : Submodule ℚ M, (toSubmodule t) ⊓ A = ⊥
      ∧ toSubmodule t ⊔ A = toSubmodule s := by

  obtain ⟨a, ha⟩ := Submodule.exists_isCompl (Submodule.comap (toSubmodule s).subtype (toSubmodule t))

  have hmap : toSubmodule t = Submodule.map (toSubmodule s).subtype (Submodule.comap (toSubmodule s).subtype (toSubmodule t)) := by
    refine Eq.symm (Submodule.map_comap_eq_self ?_)
    simpa using le_of_le hs ht hst

  use Submodule.map (toSubmodule s).subtype a
  constructor
  · obtain hdisj := ha.inf_eq_bot
    rw [hmap]
    rw [← Submodule.map_inf _ (toSubmodule s).injective_subtype]
    rw [hdisj]
    simp
  · obtain hcodisj := ha.sup_eq_top
    rw [hmap]
    rw [← Submodule.map_sup]
    rw [hcodisj]
    simp

end archimedeanSubgroup

noncomputable
def archimedeanGrade.of_nonzero {A : archimedeanClass M} (hA : A ≠ 0) :=
    (archimedeanSubgroup.exists_compl_of_le (s := UpperSet.Ici A) (t := UpperSet.Ioi A)
    (by simp) (archimedeanClass.Ioi_nonempty hA) (by apply UpperSet.Ici_le_Ioi)).choose

noncomputable
def archimedeanGrade (A : archimedeanClass M) :=
  if hA : A ≠ 0 then
    archimedeanGrade.of_nonzero hA
  else
    ⊥

namespace archimedeanGrade

theorem eq_of_nonzero {A : archimedeanClass M} (hA : A ≠ 0) :
    archimedeanGrade A = archimedeanGrade.of_nonzero hA := by
  unfold archimedeanGrade
  simp [hA]

theorem eq_of_zero {A : archimedeanClass M} (hA : A = 0) :
    archimedeanGrade A = ⊥ := by
  unfold archimedeanGrade
  simp [hA]

theorem disj_Ioi {A : archimedeanClass M} (hA : A ≠ 0) :
    (archimedeanSubgroup.toSubmodule (UpperSet.Ioi A)) ⊓ archimedeanGrade A = ⊥ := by
  rw [eq_of_nonzero hA]
  exact (Exists.choose_spec (archimedeanSubgroup.exists_compl_of_le (s := UpperSet.Ici A) (t := UpperSet.Ioi A)
    (by simp) (archimedeanClass.Ioi_nonempty hA) (by apply UpperSet.Ici_le_Ioi))).1

theorem codisj_Ioi {A : archimedeanClass M} (hA : A ≠ 0) :
    (archimedeanSubgroup.toSubmodule (UpperSet.Ioi A)) ⊔ archimedeanGrade A =
    (archimedeanSubgroup.toSubmodule (UpperSet.Ici A)) := by
  rw [eq_of_nonzero hA]
  exact (Exists.choose_spec (archimedeanSubgroup.exists_compl_of_le (s := UpperSet.Ici A) (t := UpperSet.Ioi A)
    (by simp) (archimedeanClass.Ioi_nonempty hA) (by apply UpperSet.Ici_le_Ioi))).2

theorem nontrivial_of_nonzero {A : archimedeanClass M} (hA : A ≠ 0) :
    Nontrivial (archimedeanGrade A) := by
  by_contra! htrivial
  have hbot : archimedeanGrade A = ⊥ := by
    simpa using Submodule.nontrivial_iff_ne_bot.not.mp htrivial
  obtain hcodisj := codisj_Ioi hA
  rw [hbot] at hcodisj
  simp only [bot_le, sup_of_le_left] at hcodisj
  contrapose! hcodisj
  suffices archimedeanSubgroup (UpperSet.Ioi A) ≠ archimedeanSubgroup (UpperSet.Ici A) by
    contrapose! this
    unfold archimedeanSubgroup.toSubmodule at this
    simpa using this
  apply ne_of_lt
  apply archimedeanSubgroup.lt_of_lt (by simp) (archimedeanClass.Ioi_nonempty hA)
  apply lt_of_le_of_ne
  · exact UpperSet.Ici_le_Ioi A
  · apply UpperSet.ext_iff.ne.mpr
    simp only [UpperSet.coe_Ici, UpperSet.coe_Ioi]
    by_contra! h
    have h' : A ∈ Set.Ici A := Set.left_mem_Ici
    rw [h] at h'
    simp at h'

theorem le_Ici {A : archimedeanClass M} (hA : A ≠ 0) :
    archimedeanGrade A ≤ (archimedeanSubgroup.toSubmodule (UpperSet.Ici A)) := by
  rw [← codisj_Ioi hA]
  simp

theorem exists_add {A : archimedeanClass M} (hA : A ≠ 0) {a : M}
    (ha : a ∈ archimedeanSubgroup.toSubmodule (UpperSet.Ici A)) :
    ∃! (x : M × M),
      x.1 ∈ archimedeanSubgroup.toSubmodule (UpperSet.Ioi A) ∧
      x.2 ∈ archimedeanGrade A ∧
      x.1 + x.2 = a := by

  rw [← codisj_Ioi hA] at ha

  obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp ha
  use (b, c)
  constructor
  · exact ⟨hb, hc, hbc⟩
  · intro ⟨b', c'⟩
    simp only [Prod.mk.injEq, and_imp]
    intro hb' hc' hbc'
    let p := b - b'
    have hpb : p ∈ archimedeanSubgroup.toSubmodule (UpperSet.Ioi A) :=
      (Submodule.sub_mem_iff_left (archimedeanSubgroup.toSubmodule (UpperSet.Ioi A)) hb').mpr hb
    have hpeq : p = c' - c := by
      unfold p
      apply sub_eq_sub_iff_add_eq_add.mpr
      rw [hbc, add_comm, hbc']
    have hpc : p ∈ archimedeanGrade A :=
      hpeq ▸ (Submodule.sub_mem_iff_left (archimedeanGrade A) hc).mpr hc'
    obtain hp0 := (Submodule.disjoint_def.mp (disjoint_iff.mpr (disj_Ioi hA))) p hpb hpc
    constructor
    · unfold p at hp0
      exact (sub_eq_zero.mp hp0).symm
    · rw [hpeq] at hp0
      exact sub_eq_zero.mp hp0

theorem mem_class_of_nonzero {A : archimedeanClass M} (hA : A ≠ 0) {a : M}
    (ha : a ∈ archimedeanGrade A) (h0 : a ≠ 0) :
    archimedeanClass.mk a = A := by
  apply eq_of_ge_of_not_gt
  · apply (archimedeanSubgroup.mem_iff (show (UpperSet.Ici A).carrier.Nonempty by simp) a).mp
    exact Set.mem_of_subset_of_mem (le_Ici hA) ha
  · contrapose! h0 with hlt
    have ha' : a ∈ archimedeanSubgroup.toSubmodule (UpperSet.Ioi A) :=
      (archimedeanSubgroup.mem_iff (by apply archimedeanClass.Ioi_nonempty hA) a).mpr hlt
    exact (Submodule.disjoint_def.mp (disjoint_iff.mpr (disj_Ioi hA))) a ha' ha

instance archimedean (A : archimedeanClass M) : Archimedean (archimedeanGrade A) := by
  by_cases hA : A = 0
  · rw [eq_of_zero hA]
    apply archimedeanClass.archimedean_of_mk_eq_mk
    intro a b ha hb
    obtain ha' := a.prop
    simp only [Submodule.mem_bot, ZeroMemClass.coe_eq_zero] at ha'
    contradiction
  · apply archimedeanClass.archimedean_of_mk_eq_mk
    intro a b ha hb
    suffices archimedeanClass.mk a.val = archimedeanClass.mk b.val by
      rw [archimedeanClass.eq] at this ⊢
      exact this
    rw [mem_class_of_nonzero hA (by simp) (by simpa using ha)]
    rw [mem_class_of_nonzero hA (by simp) (by simpa using hb)]

noncomputable
def embedReal (A : archimedeanClass M) : archimedeanGrade A →+o ℝ :=
  Archimedean.embedReal (archimedeanGrade A)

theorem embedReal_injective (A : archimedeanClass M) : Function.Injective (embedReal A) :=
  Archimedean.embedReal_injective (archimedeanGrade A)

noncomputable
def embedReal_orderEmbedding (A : archimedeanClass M) : archimedeanGrade A ↪o ℝ :=
  Archimedean.embedReal_orderEmbedding (archimedeanGrade A)

noncomputable
def embedReal_linear (A : archimedeanClass M) : archimedeanGrade A →ₗ[ℚ] ℝ := {
  embedReal A with
  map_smul' (q) (a) := by
    have (x) : ((embedReal A).toAddMonoidHom).toFun x = (embedReal A) x := by rfl
    rw [this, this]
    simp only [eq_ratCast, Rat.cast_eq_id, id_eq]
    apply smul_right_injective ℝ (by simp : q.den ≠ 0)
    simp only
    rw [← map_nsmul]
    rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ]
    rw [smul_smul, Rat.den_mul_eq_num, Int.cast_smul_eq_zsmul]
    rw [smul_smul, Rat.den_mul_eq_num, Int.cast_smul_eq_zsmul]
    rw [← map_zsmul]

}

theorem embedReal_linear_eq_orderEmbedding {A : archimedeanClass M} (a : archimedeanGrade A):
  (embedReal_linear A) a = (embedReal_orderEmbedding A) a := by rfl

end archimedeanGrade

end Divisible
