/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.SetLike.Fintype
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Sylow theorems

The Sylow theorems are the following results for every finite group `G` and every prime number `p`.

* There exists a Sylow `p`-subgroup of `G`.
* All Sylow `p`-subgroups of `G` are conjugate to each other.
* Let `nₚ` be the number of Sylow `p`-subgroups of `G`, then `nₚ` divides the index of the Sylow
  `p`-subgroup, `nₚ ≡ 1 [MOD p]`, and `nₚ` is equal to the index of the normalizer of the Sylow
  `p`-subgroup in `G`.

## Main definitions

* `Sylow p G` : The type of Sylow `p`-subgroups of `G`.

## Main statements

* `Sylow.exists_subgroup_card_pow_prime`: A generalization of Sylow's first theorem:
  For every prime power `pⁿ` dividing the cardinality of `G`,
  there exists a subgroup of `G` of order `pⁿ`.
* `IsPGroup.exists_le_sylow`: A generalization of Sylow's first theorem:
  Every `p`-subgroup is contained in a Sylow `p`-subgroup.
* `Sylow.card_eq_multiplicity`: The cardinality of a Sylow subgroup is `p ^ n`
  where `n` is the multiplicity of `p` in the group order.
* `Sylow.isPretransitive_of_finite`: a generalization of Sylow's second theorem:
  If the number of Sylow `p`-subgroups is finite, then all Sylow `p`-subgroups are conjugate.
* `card_sylow_modEq_one`: a generalization of Sylow's third theorem:
  If the number of Sylow `p`-subgroups is finite, then it is congruent to `1` modulo `p`.
-/


open MulAction Subgroup

section InfiniteSylow

variable (p : ℕ) (G : Type*) [Group G]

/-- A Sylow `p`-subgroup is a maximal `p`-subgroup. -/
structure Sylow extends Subgroup G where
  isPGroup' : IsPGroup p toSubgroup
  is_maximal' : ∀ {Q : Subgroup G}, IsPGroup p Q → toSubgroup ≤ Q → Q = toSubgroup

variable {p} {G}

namespace Sylow

attribute [coe] toSubgroup

instance : CoeOut (Sylow p G) (Subgroup G) :=
  ⟨toSubgroup⟩

@[ext]
theorem ext {P Q : Sylow p G} (h : (P : Subgroup G) = Q) : P = Q := by cases P; cases Q; congr

instance : SetLike (Sylow p G) G where
  coe := (↑)
  coe_injective' _ _ h := ext (SetLike.coe_injective h)

instance : SubgroupClass (Sylow p G) G where
  mul_mem := Subgroup.mul_mem _
  one_mem _ := Subgroup.one_mem _
  inv_mem := Subgroup.inv_mem _

/-- A `p`-subgroup with index indivisible by `p` is a Sylow subgroup. -/
def _root_.IsPGroup.toSylow [Fact p.Prime] {P : Subgroup G}
    (hP1 : IsPGroup p P) (hP2 : ¬ p ∣ P.index) : Sylow p G :=
  { P with
    isPGroup' := hP1
    is_maximal' := by
      intro Q hQ hPQ
      have : P.FiniteIndex := ⟨fun h ↦ hP2 (h ▸ (dvd_zero p))⟩
      obtain ⟨k, hk⟩ := (hQ.to_quotient (P.normalCore.subgroupOf Q)).exists_card_eq
      have h := hk ▸ Nat.Prime.coprime_pow_of_not_dvd (m := k) Fact.out hP2
      exact le_antisymm (Subgroup.relIndex_eq_one.mp
        (Nat.eq_one_of_dvd_coprimes h (Subgroup.relIndex_dvd_index_of_le hPQ)
        (Subgroup.relIndex_dvd_of_le_left Q P.normalCore_le))) hPQ }

@[simp] theorem _root_.IsPGroup.toSylow_coe [Fact p.Prime] {P : Subgroup G}
    (hP1 : IsPGroup p P) (hP2 : ¬ p ∣ P.index) : (hP1.toSylow hP2) = P :=
  rfl

@[simp] theorem _root_.IsPGroup.mem_toSylow [Fact p.Prime] {P : Subgroup G}
    (hP1 : IsPGroup p P) (hP2 : ¬ p ∣ P.index) {g : G} : g ∈ hP1.toSylow hP2 ↔ g ∈ P :=
  .rfl

/-- A subgroup with cardinality `p ^ n` is a Sylow subgroup
where `n` is the multiplicity of `p` in the group order. -/
def ofCard [Finite G] {p : ℕ} [Fact p.Prime] (H : Subgroup G)
    (card_eq : Nat.card H = p ^ (Nat.card G).factorization p) : Sylow p G :=
  (IsPGroup.of_card card_eq).toSylow (by
    rw [← mul_dvd_mul_iff_left (Nat.card_pos (α := H)).ne', card_mul_index, card_eq, ← pow_succ]
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' Fact.out)

@[simp, norm_cast]
theorem coe_ofCard [Finite G] {p : ℕ} [Fact p.Prime] (H : Subgroup G)
    (card_eq : Nat.card H = p ^ (Nat.card G).factorization p) : ofCard H card_eq = H :=
  rfl

variable (P : Sylow p G)

variable {K : Type*} [Group K] (ϕ : K →* G) {N : Subgroup G}

/-- The preimage of a Sylow subgroup under a p-group-kernel homomorphism is a Sylow subgroup. -/
def comapOfKerIsPGroup (hϕ : IsPGroup p ϕ.ker) (h : P ≤ ϕ.range) : Sylow p K :=
  { P.1.comap ϕ with
    isPGroup' := P.2.comap_of_ker_isPGroup ϕ hϕ
    is_maximal' := fun {Q} hQ hle => by
      show Q = P.1.comap ϕ
      rw [← P.3 (hQ.map ϕ) (le_trans (ge_of_eq (map_comap_eq_self h)) (map_mono hle))]
      exact (comap_map_eq_self ((P.1.ker_le_comap ϕ).trans hle)).symm }

@[simp]
theorem coe_comapOfKerIsPGroup (hϕ : IsPGroup p ϕ.ker) (h : P ≤ ϕ.range) :
    P.comapOfKerIsPGroup ϕ hϕ h = P.comap ϕ :=
  rfl

/-- The preimage of a Sylow subgroup under an injective homomorphism is a Sylow subgroup. -/
def comapOfInjective (hϕ : Function.Injective ϕ) (h : P ≤ ϕ.range) : Sylow p K :=
  P.comapOfKerIsPGroup ϕ (IsPGroup.ker_isPGroup_of_injective hϕ) h

@[simp]
theorem coe_comapOfInjective (hϕ : Function.Injective ϕ) (h : P ≤ ϕ.range) :
    P.comapOfInjective ϕ hϕ h = P.comap ϕ :=
  rfl

/-- A sylow subgroup of G is also a sylow subgroup of a subgroup of G. -/
protected def subtype (h : P ≤ N) : Sylow p N :=
  P.comapOfInjective N.subtype Subtype.coe_injective (by rwa [range_subtype])

@[simp]
theorem coe_subtype (h : P ≤ N) : P.subtype h = subgroupOf P N :=
  rfl

theorem subtype_injective {P Q : Sylow p G} {hP : P ≤ N} {hQ : Q ≤ N}
    (h : P.subtype hP = Q.subtype hQ) : P = Q := by
  rw [SetLike.ext_iff] at h ⊢
  exact fun g => ⟨fun hg => (h ⟨g, hP hg⟩).mp hg, fun hg => (h ⟨g, hQ hg⟩).mpr hg⟩

end Sylow

/-- A generalization of **Sylow's first theorem**.
  Every `p`-subgroup is contained in a Sylow `p`-subgroup. -/
theorem IsPGroup.exists_le_sylow {P : Subgroup G} (hP : IsPGroup p P) : ∃ Q : Sylow p G, P ≤ Q :=
  Exists.elim
    (zorn_le_nonempty₀ { Q : Subgroup G | IsPGroup p Q }
      (fun c hc1 hc2 Q hQ =>
        ⟨{  carrier := ⋃ R : c, R
            one_mem' := ⟨Q, ⟨⟨Q, hQ⟩, rfl⟩, Q.one_mem⟩
            inv_mem' := fun {_} ⟨_, ⟨R, rfl⟩, hg⟩ => ⟨R, ⟨R, rfl⟩, R.1.inv_mem hg⟩
            mul_mem' := fun {_} _ ⟨_, ⟨R, rfl⟩, hg⟩ ⟨_, ⟨S, rfl⟩, hh⟩ =>
              (hc2.total R.2 S.2).elim (fun T => ⟨S, ⟨S, rfl⟩, S.1.mul_mem (T hg) hh⟩) fun T =>
                ⟨R, ⟨R, rfl⟩, R.1.mul_mem hg (T hh)⟩ },
          fun ⟨g, _, ⟨S, rfl⟩, hg⟩ => by
          refine Exists.imp (fun k hk => ?_) (hc1 S.2 ⟨g, hg⟩)
          rwa [Subtype.ext_iff, coe_pow] at hk ⊢, fun M hM _ hg => ⟨M, ⟨⟨M, hM⟩, rfl⟩, hg⟩⟩)
      P hP)
    fun {Q} h => ⟨⟨Q, h.2.prop, h.2.eq_of_ge⟩, h.1⟩

namespace Sylow

instance nonempty : Nonempty (Sylow p G) :=
  IsPGroup.of_bot.exists_le_sylow.nonempty

noncomputable instance inhabited : Inhabited (Sylow p G) :=
  Classical.inhabited_of_nonempty nonempty

theorem exists_comap_eq_of_ker_isPGroup {H : Type*} [Group H] (P : Sylow p H) {f : H →* G}
    (hf : IsPGroup p f.ker) : ∃ Q : Sylow p G, Q.comap f = P :=
  Exists.imp (fun Q hQ => P.3 (Q.2.comap_of_ker_isPGroup f hf) (map_le_iff_le_comap.mp hQ))
    (P.2.map f).exists_le_sylow

theorem exists_comap_eq_of_injective {H : Type*} [Group H] (P : Sylow p H) {f : H →* G}
    (hf : Function.Injective f) : ∃ Q : Sylow p G, Q.comap f = P :=
  P.exists_comap_eq_of_ker_isPGroup (IsPGroup.ker_isPGroup_of_injective hf)

theorem exists_comap_subtype_eq {H : Subgroup G} (P : Sylow p H) :
    ∃ Q : Sylow p G, Q.comap H.subtype = P :=
  P.exists_comap_eq_of_injective Subtype.coe_injective

/-- If the kernel of `f : H →* G` is a `p`-group,
  then `Finite (Sylow p G)` implies `Finite (Sylow p H)`. -/
theorem finite_of_ker_is_pGroup {H : Type*} [Group H] {f : H →* G}
    (hf : IsPGroup p f.ker) [Finite (Sylow p G)] : Finite (Sylow p H) :=
  let h_exists := fun P : Sylow p H => P.exists_comap_eq_of_ker_isPGroup hf
  let g : Sylow p H → Sylow p G := fun P => Classical.choose (h_exists P)
  have hg : ∀ P : Sylow p H, (g P).1.comap f = P := fun P => Classical.choose_spec (h_exists P)
  Finite.of_injective g fun P Q h => ext (by rw [← hg, h]; exact (h_exists Q).choose_spec)

/-- If `f : H →* G` is injective, then `Finite (Sylow p G)` implies `Finite (Sylow p H)`. -/
theorem finite_of_injective {H : Type*} [Group H] {f : H →* G}
    (hf : Function.Injective f) [Finite (Sylow p G)] : Finite (Sylow p H) :=
  finite_of_ker_is_pGroup (IsPGroup.ker_isPGroup_of_injective hf)

/-- If `H` is a subgroup of `G`, then `Finite (Sylow p G)` implies `Finite (Sylow p H)`. -/
instance (H : Subgroup G) [Finite (Sylow p G)] : Finite (Sylow p H) :=
  finite_of_injective H.subtype_injective

open Pointwise

/-- `Subgroup.pointwiseMulAction` preserves Sylow subgroups. -/
instance pointwiseMulAction {α : Type*} [Group α] [MulDistribMulAction α G] :
    MulAction α (Sylow p G) where
  smul g P :=
    ⟨g • P.toSubgroup, P.2.map _, fun {Q} hQ hS =>
      inv_smul_eq_iff.mp
        (P.3 (hQ.map _) fun s hs =>
          (congr_arg (· ∈ g⁻¹ • Q) (inv_smul_smul g s)).mp
            (smul_mem_pointwise_smul (g • s) g⁻¹ Q (hS (smul_mem_pointwise_smul s g P hs))))⟩
  one_smul P := ext (one_smul α P.toSubgroup)
  mul_smul g h P := ext (mul_smul g h P.toSubgroup)

theorem pointwise_smul_def {α : Type*} [Group α] [MulDistribMulAction α G] {g : α}
    {P : Sylow p G} : ↑(g • P) = g • (P : Subgroup G) :=
  rfl

instance mulAction : MulAction G (Sylow p G) :=
  compHom _ MulAut.conj

theorem smul_def {g : G} {P : Sylow p G} : g • P = MulAut.conj g • P :=
  rfl

theorem coe_subgroup_smul {g : G} {P : Sylow p G} :
    ↑(g • P) = MulAut.conj g • (P : Subgroup G) :=
  rfl

theorem coe_smul {g : G} {P : Sylow p G} : ↑(g • P) = MulAut.conj g • (P : Set G) :=
  rfl

theorem smul_le {P : Sylow p G} {H : Subgroup G} (hP : P ≤ H) (h : H) : ↑(h • P) ≤ H :=
  Subgroup.conj_smul_le_of_le hP h

theorem smul_subtype {P : Sylow p G} {H : Subgroup G} (hP : P ≤ H) (h : H) :
    h • P.subtype hP = (h • P).subtype (smul_le hP h) :=
  ext (Subgroup.conj_smul_subgroupOf hP h)

theorem smul_eq_iff_mem_normalizer {g : G} {P : Sylow p G} :
    g • P = P ↔ g ∈ P.normalizer := by
  rw [eq_comm, SetLike.ext_iff, ← inv_mem_iff (G := G) (H := normalizer P.toSubgroup),
      mem_normalizer_iff, inv_inv]
  exact
    forall_congr' fun h =>
      iff_congr Iff.rfl
        ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
          fun hh => ⟨(MulAut.conj g)⁻¹ h, hh, MulAut.apply_inv_self G (MulAut.conj g) h⟩⟩

theorem smul_eq_of_normal {g : G} {P : Sylow p G} [h : P.Normal] :
    g • P = P := by simp only [smul_eq_iff_mem_normalizer, P.normalizer_eq_top, mem_top]

end Sylow

theorem Subgroup.sylow_mem_fixedPoints_iff (H : Subgroup G) {P : Sylow p G} :
    P ∈ fixedPoints H (Sylow p G) ↔ H ≤ P.normalizer := by
  simp_rw [SetLike.le_def, ← Sylow.smul_eq_iff_mem_normalizer]; exact Subtype.forall

theorem IsPGroup.inf_normalizer_sylow {P : Subgroup G} (hP : IsPGroup p P) (Q : Sylow p G) :
    P ⊓ Q.normalizer = P ⊓ Q :=
  le_antisymm
    (le_inf inf_le_left
      (sup_eq_right.mp
        (Q.3 (hP.to_inf_left.to_sup_of_normal_right' Q.2 inf_le_right) le_sup_right)))
    (inf_le_inf_left P le_normalizer)

theorem IsPGroup.sylow_mem_fixedPoints_iff {P : Subgroup G} (hP : IsPGroup p P) {Q : Sylow p G} :
    Q ∈ fixedPoints P (Sylow p G) ↔ P ≤ Q := by
  rw [P.sylow_mem_fixedPoints_iff, ← inf_eq_left, hP.inf_normalizer_sylow, inf_eq_left]

/-- A generalization of **Sylow's second theorem**.
  If the number of Sylow `p`-subgroups is finite, then all Sylow `p`-subgroups are conjugate. -/
instance Sylow.isPretransitive_of_finite [hp : Fact p.Prime] [Finite (Sylow p G)] :
    IsPretransitive G (Sylow p G) :=
  ⟨fun P Q => by
    classical
      have H := fun {R : Sylow p G} {S : orbit G P} =>
        calc
          S ∈ fixedPoints R (orbit G P) ↔ S.1 ∈ fixedPoints R (Sylow p G) :=
            forall_congr' fun a => Subtype.ext_iff
          _ ↔ R.1 ≤ S := R.2.sylow_mem_fixedPoints_iff
          _ ↔ S.1.1 = R := ⟨fun h => R.3 S.1.2 h, ge_of_eq⟩
      suffices Set.Nonempty (fixedPoints Q (orbit G P)) by
        exact Exists.elim this fun R hR => by
          rw [← Sylow.ext (H.mp hR)]
          exact R.2
      apply Q.2.nonempty_fixed_point_of_prime_not_dvd_card
      refine fun h => hp.out.not_dvd_one (Nat.modEq_zero_iff_dvd.mp ?_)
      calc
        1 = Nat.card (fixedPoints P (orbit G P)) := ?_
        _ ≡ Nat.card (orbit G P) [MOD p] := (P.2.card_modEq_card_fixedPoints (orbit G P)).symm
        _ ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h
      rw [← Nat.card_unique (α := ({⟨P, mem_orbit_self P⟩} : Set (orbit G P))), eq_comm]
      congr
      rw [Set.eq_singleton_iff_unique_mem]
      exact ⟨H.mpr rfl, fun R h => Subtype.ext (Sylow.ext (H.mp h))⟩⟩

variable (p) (G)

/-- A generalization of **Sylow's third theorem**.
  If the number of Sylow `p`-subgroups is finite, then it is congruent to `1` modulo `p`. -/
theorem card_sylow_modEq_one [Fact p.Prime] [Finite (Sylow p G)] :
    Nat.card (Sylow p G) ≡ 1 [MOD p] := by
  refine Sylow.nonempty.elim fun P : Sylow p G => ?_
  have : fixedPoints P.1 (Sylow p G) = {P} :=
    Set.ext fun Q : Sylow p G =>
      calc
        Q ∈ fixedPoints P (Sylow p G) ↔ P.1 ≤ Q := P.2.sylow_mem_fixedPoints_iff
        _ ↔ Q.1 = P.1 := ⟨P.3 Q.2, ge_of_eq⟩
        _ ↔ Q ∈ {P} := Sylow.ext_iff.symm.trans Set.mem_singleton_iff.symm
  have : Nat.card (fixedPoints P.1 (Sylow p G)) = 1 := by simp [this]
  exact (P.2.card_modEq_card_fixedPoints (Sylow p G)).trans (by rw [this])

theorem not_dvd_card_sylow [hp : Fact p.Prime] [Finite (Sylow p G)] : ¬p ∣ Nat.card (Sylow p G) :=
  fun h =>
  hp.1.ne_one
    (Nat.dvd_one.mp
      ((Nat.modEq_iff_dvd' zero_le_one).mp
        ((Nat.modEq_zero_iff_dvd.mpr h).symm.trans (card_sylow_modEq_one p G))))

variable {p} {G}

namespace Sylow

/-- Sylow subgroups are isomorphic -/
nonrec def equivSMul (P : Sylow p G) (g : G) : P ≃* (g • P : Sylow p G) :=
  equivSMul (MulAut.conj g) P.toSubgroup

/-- Sylow subgroups are isomorphic -/
noncomputable def equiv [Fact p.Prime] [Finite (Sylow p G)] (P Q : Sylow p G) : P ≃* Q := by
  rw [← Classical.choose_spec (exists_smul_eq G P Q)]
  exact P.equivSMul (Classical.choose (exists_smul_eq G P Q))

@[simp]
theorem orbit_eq_top [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) : orbit G P = ⊤ :=
  top_le_iff.mp fun Q _ => exists_smul_eq G P Q

theorem stabilizer_eq_normalizer (P : Sylow p G) :
    stabilizer G P = P.normalizer := by
  ext; simp [smul_eq_iff_mem_normalizer]

theorem conj_eq_normalizer_conj_of_mem_centralizer [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) (x g : G) (hx : x ∈ centralizer P)
    (hy : g⁻¹ * x * g ∈ centralizer P) :
    ∃ n ∈ P.normalizer, g⁻¹ * x * g = n⁻¹ * x * n := by
  have h1 : P ≤ centralizer (zpowers x : Set G) := by rwa [le_centralizer_iff, zpowers_le]
  have h2 : ↑(g • P) ≤ centralizer (zpowers x : Set G) := by
    rw [le_centralizer_iff, zpowers_le]
    rintro - ⟨z, hz, rfl⟩
    specialize hy z hz
    rwa [← mul_assoc, ← eq_mul_inv_iff_mul_eq, mul_assoc, mul_assoc, mul_assoc, ← mul_assoc,
      eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_assoc] at hy
  obtain ⟨h, hh⟩ :=
    exists_smul_eq (centralizer (zpowers x : Set G)) ((g • P).subtype h2) (P.subtype h1)
  simp_rw [smul_subtype, Subgroup.smul_def, smul_smul] at hh
  refine ⟨h * g, smul_eq_iff_mem_normalizer.mp (subtype_injective hh), ?_⟩
  rw [← mul_assoc, Commute.right_comm (h.prop x (mem_zpowers x)), mul_inv_rev, inv_mul_cancel_right]

theorem conj_eq_normalizer_conj_of_mem [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    [_hP : IsMulCommutative P] (x g : G) (hx : x ∈ P) (hy : g⁻¹ * x * g ∈ P) :
    ∃ n ∈ P.normalizer, g⁻¹ * x * g = n⁻¹ * x * n :=
  P.conj_eq_normalizer_conj_of_mem_centralizer x g
    (P.le_centralizer hx) (P.le_centralizer hy)

/-- Sylow `p`-subgroups are in bijection with cosets of the normalizer of a Sylow `p`-subgroup -/
noncomputable def equivQuotientNormalizer [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) : Sylow p G ≃ G ⧸ P.normalizer :=
  calc
    Sylow p G ≃ (⊤ : Set (Sylow p G)) := (Equiv.Set.univ (Sylow p G)).symm
    _ ≃ orbit G P := Equiv.setCongr P.orbit_eq_top.symm
    _ ≃ G ⧸ stabilizer G P := orbitEquivQuotientStabilizer G P
    _ ≃ G ⧸ P.normalizer := by rw [P.stabilizer_eq_normalizer]

instance [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    Finite (G ⧸ P.normalizer) :=
  Finite.of_equiv (Sylow p G) P.equivQuotientNormalizer

theorem card_eq_card_quotient_normalizer [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) : Nat.card (Sylow p G) = Nat.card (G ⧸ P.normalizer) :=
  Nat.card_congr P.equivQuotientNormalizer

theorem card_eq_index_normalizer [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    Nat.card (Sylow p G) = P.normalizer.index :=
  P.card_eq_card_quotient_normalizer

theorem card_dvd_index [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    Nat.card (Sylow p G) ∣ P.index :=
  ((congr_arg _ P.card_eq_index_normalizer).mp dvd_rfl).trans
    (index_dvd_of_le le_normalizer)

/-- Auxiliary lemma for `Sylow.not_dvd_index` which is strictly stronger. -/
private theorem not_dvd_index_aux [hp : Fact p.Prime] (P : Sylow p G) [P.Normal]
    [P.FiniteIndex] : ¬ p ∣ P.index := by
  intro h
  rw [P.index_eq_card] at h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G ⧸ (P : Subgroup G)) p h
  have h := IsPGroup.of_card (((Nat.card_zpowers x).trans hx).trans (pow_one p).symm)
  let Q := (zpowers x).comap (QuotientGroup.mk' (P : Subgroup G))
  have hQ : IsPGroup p Q := by
    apply h.comap_of_ker_isPGroup
    rw [QuotientGroup.ker_mk']
    exact P.2
  replace hp := mt orderOf_eq_one_iff.mpr (ne_of_eq_of_ne hx hp.1.ne_one)
  rw [← zpowers_eq_bot, ← Ne, ← bot_lt_iff_ne_bot, ←
    comap_lt_comap_of_surjective (QuotientGroup.mk'_surjective _), MonoidHom.comap_bot,
    QuotientGroup.ker_mk'] at hp
  exact hp.ne' (P.3 hQ hp.le)

/-- A Sylow p-subgroup has index indivisible by `p`, assuming [N(P) : P] < ∞. -/
theorem not_dvd_index' [hp : Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (hP : P.relIndex P.normalizer ≠ 0) : ¬ p ∣ P.index := by
  rw [← relIndex_mul_index le_normalizer, ← card_eq_index_normalizer]
  haveI : (P.subtype le_normalizer).Normal :=
    Subgroup.normal_in_normalizer
  haveI : (P.subtype le_normalizer).FiniteIndex := ⟨hP⟩
  replace hP := not_dvd_index_aux (P.subtype le_normalizer)
  exact hp.1.not_dvd_mul hP (not_dvd_card_sylow p G)

/-- A Sylow p-subgroup has index indivisible by `p`. -/
theorem not_dvd_index [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) [P.FiniteIndex] :
    ¬ p ∣ P.index :=
  P.not_dvd_index' Nat.card_pos.ne'

section mapSurjective

variable [Finite G] {G' : Type*} [Group G'] {f : G →* G'} (hf : Function.Surjective f)

/-- Surjective group homomorphisms map Sylow subgroups to Sylow subgroups. -/
def mapSurjective [Fact p.Prime] (P : Sylow p G) : Sylow p G' :=
  { P.1.map f with
    isPGroup' := P.2.map f
    is_maximal' := fun hQ hPQ ↦ ((P.2.map f).toSylow
      (fun h ↦ P.not_dvd_index (h.trans (P.index_map_dvd hf)))).3 hQ hPQ }

@[simp] theorem coe_mapSurjective [Fact p.Prime] (P : Sylow p G) : P.mapSurjective hf = P.map f :=
  rfl

theorem mapSurjective_surjective (p : ℕ) [Fact p.Prime] :
    Function.Surjective (Sylow.mapSurjective hf : Sylow p G → Sylow p G') := by
  have : Finite G' := Finite.of_surjective f hf
  intro P
  let Q₀ : Sylow p (P.comap f) := Sylow.nonempty.some
  let Q : Subgroup G := Q₀.map (P.comap f).subtype
  have hPQ : Q.map f ≤ P := Subgroup.map_le_iff_le_comap.mpr (Subgroup.map_subtype_le Q₀.1)
  have hpQ : IsPGroup p Q := Q₀.2.map (P.comap f).subtype
  have hQ : ¬ p ∣ Q.index := by
    rw [Subgroup.index_map_subtype Q₀.1, P.index_comap_of_surjective hf]
    exact Nat.Prime.not_dvd_mul Fact.out Q₀.not_dvd_index P.not_dvd_index
  use hpQ.toSylow hQ
  rw [Sylow.ext_iff, Sylow.coe_mapSurjective, eq_comm]
  exact ((hpQ.map f).toSylow (fun h ↦ hQ (h.trans (Q.index_map_dvd hf)))).3 P.2 hPQ

end mapSurjective

/-- **Frattini's Argument**: If `N` is a normal subgroup of `G`, and if `P` is a Sylow `p`-subgroup
  of `N`, then `N_G(P) ⊔ N = G`. -/
theorem normalizer_sup_eq_top {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal]
    [Finite (Sylow p N)] (P : Sylow p N) :
    (P.map N.subtype).normalizer ⊔ N = ⊤ := by
  refine top_le_iff.mp fun g _ => ?_
  obtain ⟨n, hn⟩ := exists_smul_eq N ((MulAut.conjNormal g : MulAut N) • P) P
  rw [← inv_mul_cancel_left (↑n) g, sup_comm]
  apply mul_mem_sup (N.inv_mem n.2)
  rw [smul_def, ← mul_smul, ← MulAut.conjNormal_val, ← MulAut.conjNormal.map_mul,
    Sylow.ext_iff, pointwise_smul_def, Subgroup.pointwise_smul_def] at hn
  have : Function.Injective (MulAut.conj (n * g)).toMonoidHom := (MulAut.conj (n * g)).injective
  refine fun x ↦ (mem_map_iff_mem this).symm.trans ?_
  rw [map_map, ← congr_arg (map N.subtype) hn, map_map]
  rfl

/-- **Frattini's Argument**: If `N` is a normal subgroup of `G`, and if `P` is a Sylow `p`-subgroup
  of `N`, then `N_G(P) ⊔ N = G`. -/
theorem normalizer_sup_eq_top' {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal]
    [Finite (Sylow p N)] (P : Sylow p G) (hP : P ≤ N) : P.normalizer ⊔ N = ⊤ := by
  rw [← normalizer_sup_eq_top (P.subtype hP), P.coe_subtype, subgroupOf_map_subtype,
    inf_of_le_left hP]

end Sylow

end InfiniteSylow

open Equiv Equiv.Perm Finset Function List QuotientGroup

universe u

variable {G : Type u} [Group G]

theorem QuotientGroup.card_preimage_mk (s : Subgroup G) (t : Set (G ⧸ s)) :
    Nat.card (QuotientGroup.mk ⁻¹' t) = Nat.card s * Nat.card t := by
  rw [← Nat.card_prod, Nat.card_congr (preimageMkEquivSubgroupProdSet _ _)]

namespace Sylow
theorem mem_fixedPoints_mul_left_cosets_iff_mem_normalizer {H : Subgroup G} [Finite (H : Set G)]
    {x : G} : (x : G ⧸ H) ∈ MulAction.fixedPoints H (G ⧸ H) ↔ x ∈ normalizer H :=
  ⟨fun hx =>
    have ha : ∀ {y : G ⧸ H}, y ∈ orbit H (x : G ⧸ H) → y = x := mem_fixedPoints'.1 hx _
    (inv_mem_iff (G := G)).1
      (mem_normalizer_fintype fun n (hn : n ∈ H) =>
        have : (n⁻¹ * x)⁻¹ * x ∈ H := QuotientGroup.eq.1 (ha ⟨⟨n⁻¹, inv_mem hn⟩, rfl⟩)
        show _ ∈ H by
          rw [mul_inv_rev, inv_inv] at this
          convert this
          rw [inv_inv]),
    fun hx : ∀ n : G, n ∈ H ↔ x * n * x⁻¹ ∈ H =>
    mem_fixedPoints'.2 fun y =>
      Quotient.inductionOn' y fun y hy =>
        QuotientGroup.eq.2
          (let ⟨⟨b, hb₁⟩, hb₂⟩ := hy
          have hb₂ : (b * x)⁻¹ * y ∈ H := QuotientGroup.eq.1 hb₂
          (inv_mem_iff (G := G)).1 <|
            (hx _).2 <|
              (mul_mem_cancel_left (inv_mem hb₁)).1 <| by
                rw [hx] at hb₂; simpa [mul_inv_rev, mul_assoc] using hb₂)⟩

/-- The fixed points of the action of `H` on its cosets correspond to `normalizer H / H`. -/
def fixedPointsMulLeftCosetsEquivQuotient (H : Subgroup G) [Finite (H : Set G)] :
    MulAction.fixedPoints H (G ⧸ H) ≃
      normalizer H ⧸ Subgroup.comap ((normalizer H).subtype : normalizer H →* G) H :=
  @subtypeQuotientEquivQuotientSubtype G (normalizer H : Set G) (_) (_)
    (MulAction.fixedPoints H (G ⧸ H))
    (fun _ => (@mem_fixedPoints_mul_left_cosets_iff_mem_normalizer _ _ _ ‹_› _).symm)
    (by
      intros
      unfold_projs
      rw [leftRel_apply (α := normalizer H), leftRel_apply]
      rfl)

/-- If `H` is a `p`-subgroup of `G`, then the index of `H` inside its normalizer is congruent
  mod `p` to the index of `H`. -/
theorem card_quotient_normalizer_modEq_card_quotient [Finite G] {p : ℕ} {n : ℕ} [hp : Fact p.Prime]
    {H : Subgroup G} (hH : Nat.card H = p ^ n) :
    Nat.card (normalizer H ⧸ Subgroup.comap ((normalizer H).subtype : normalizer H →* G) H) ≡
      Nat.card (G ⧸ H) [MOD p] := by
  rw [← Nat.card_congr (fixedPointsMulLeftCosetsEquivQuotient H)]
  exact ((IsPGroup.of_card hH).card_modEq_card_fixedPoints _).symm

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`, then the cardinality of the
  normalizer of `H` is congruent mod `p ^ (n + 1)` to the cardinality of `G`. -/
theorem card_normalizer_modEq_card [Finite G] {p : ℕ} {n : ℕ} [hp : Fact p.Prime] {H : Subgroup G}
    (hH : Nat.card H = p ^ n) : Nat.card (normalizer H) ≡ Nat.card G [MOD p ^ (n + 1)] := by
  have : H.subgroupOf (normalizer H) ≃ H := (subgroupOfEquivOfLe le_normalizer).toEquiv
  rw [card_eq_card_quotient_mul_card_subgroup H,
    card_eq_card_quotient_mul_card_subgroup (H.subgroupOf (normalizer H)), Nat.card_congr this,
    hH, pow_succ']
  exact (card_quotient_normalizer_modEq_card_quotient hH).mul_right' _

/-- If `H` is a `p`-subgroup but not a Sylow `p`-subgroup, then `p` divides the
  index of `H` inside its normalizer. -/
theorem prime_dvd_card_quotient_normalizer [Finite G] {p : ℕ} {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ (n + 1) ∣ Nat.card G) {H : Subgroup G} (hH : Nat.card H = p ^ n) :
    p ∣ Nat.card (normalizer H ⧸ Subgroup.comap ((normalizer H).subtype : normalizer H →* G) H) :=
  let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd
  have hcard : Nat.card (G ⧸ H) = s * p :=
    (mul_left_inj' (show Nat.card H ≠ 0 from Nat.card_pos.ne')).1
      (by
        rw [← card_eq_card_quotient_mul_card_subgroup H, hH, hs, pow_succ', mul_assoc, mul_comm p])
  have hm :
    s * p % p =
      Nat.card (normalizer H ⧸ Subgroup.comap ((normalizer H).subtype : normalizer H →* G) H) % p :=
    hcard ▸ (card_quotient_normalizer_modEq_card_quotient hH).symm
  Nat.dvd_of_mod_eq_zero (by rwa [Nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm)

/-- If `H` is a `p`-subgroup but not a Sylow `p`-subgroup of cardinality `p ^ n`,
  then `p ^ (n + 1)` divides the cardinality of the normalizer of `H`. -/
theorem prime_pow_dvd_card_normalizer [Finite G] {p : ℕ} {n : ℕ} [_hp : Fact p.Prime]
    (hdvd : p ^ (n + 1) ∣ Nat.card G) {H : Subgroup G} (hH : Nat.card H = p ^ n) :
    p ^ (n + 1) ∣ Nat.card (normalizer H) :=
  Nat.modEq_zero_iff_dvd.1 ((card_normalizer_modEq_card hH).trans hdvd.modEq_zero_nat)

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ (n + 1)`
  if `p ^ (n + 1)` divides the cardinality of `G` -/
theorem exists_subgroup_card_pow_succ [Finite G] {p : ℕ} {n : ℕ} [hp : Fact p.Prime]
    (hdvd : p ^ (n + 1) ∣ Nat.card G) {H : Subgroup G} (hH : Nat.card H = p ^ n) :
    ∃ K : Subgroup G, Nat.card K = p ^ (n + 1) ∧ H ≤ K :=
  let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd
  have hcard : Nat.card (G ⧸ H) = s * p :=
    (mul_left_inj' (show Nat.card H ≠ 0 from Nat.card_pos.ne')).1
      (by
        rw [← card_eq_card_quotient_mul_card_subgroup H, hH, hs, pow_succ', mul_assoc, mul_comm p])
  have hm : s * p % p = Nat.card (normalizer H ⧸ H.subgroupOf H.normalizer) % p :=
    Nat.card_congr (fixedPointsMulLeftCosetsEquivQuotient H) ▸
      hcard ▸ (IsPGroup.of_card hH).card_modEq_card_fixedPoints _
  have hm' : p ∣ Nat.card (normalizer H ⧸ H.subgroupOf H.normalizer) :=
    Nat.dvd_of_mod_eq_zero (by rwa [Nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm)
  let ⟨x, hx⟩ := @exists_prime_orderOf_dvd_card' _ (QuotientGroup.Quotient.group _) _ _ hp hm'
  have hequiv : H ≃ H.subgroupOf H.normalizer := (subgroupOfEquivOfLe le_normalizer).symm.toEquiv
  ⟨Subgroup.map (normalizer H).subtype
      (Subgroup.comap (mk' (H.subgroupOf H.normalizer)) (zpowers x)), by
    show Nat.card (Subgroup.map H.normalizer.subtype
              (comap (mk' (H.subgroupOf H.normalizer)) (Subgroup.zpowers x))) = p ^ (n + 1)
    suffices Nat.card (Subtype.val ''
              (Subgroup.comap (mk' (H.subgroupOf H.normalizer)) (zpowers x) : Set H.normalizer)) =
        p ^ (n + 1)
      by convert this using 2
    rw [Nat.card_image_of_injective Subtype.val_injective
        (Subgroup.comap (mk' (H.subgroupOf H.normalizer)) (zpowers x) : Set H.normalizer),
      pow_succ, ← hH, Nat.card_congr hequiv, ← hx, ← Nat.card_zpowers, ←
      Nat.card_prod]
    exact Nat.card_congr
      (preimageMkEquivSubgroupProdSet (H.subgroupOf H.normalizer) (zpowers x)), by
    intro y hy
    simp only [Subgroup.coe_subtype, mk'_apply, Subgroup.mem_map, Subgroup.mem_comap]
    refine ⟨⟨y, le_normalizer hy⟩, ⟨0, ?_⟩, rfl⟩
    dsimp only
    rw [zpow_zero, eq_comm, QuotientGroup.eq_one_iff]
    simpa using hy⟩

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ m`
  if `n ≤ m` and `p ^ m` divides the cardinality of `G` -/
theorem exists_subgroup_card_pow_prime_le [Finite G] (p : ℕ) :
    ∀ {n m : ℕ} [_hp : Fact p.Prime] (_hdvd : p ^ m ∣ Nat.card G) (H : Subgroup G)
      (_hH : Nat.card H = p ^ n) (_hnm : n ≤ m), ∃ K : Subgroup G, Nat.card K = p ^ m ∧ H ≤ K
  | n, m => fun {hdvd H hH hnm} =>
    (lt_or_eq_of_le hnm).elim
      (fun hnm : n < m =>
        have h0m : 0 < m := lt_of_le_of_lt n.zero_le hnm
        have hnm1 : n ≤ m - 1 := le_tsub_of_add_le_right hnm
        let ⟨K, hK⟩ :=
          @exists_subgroup_card_pow_prime_le _ _ n (m - 1) _
            (Nat.pow_dvd_of_le_of_pow_dvd tsub_le_self hdvd) H hH hnm1
        have hdvd' : p ^ (m - 1 + 1) ∣ Nat.card G := by rwa [tsub_add_cancel_of_le h0m.nat_succ_le]
        let ⟨K', hK'⟩ := @exists_subgroup_card_pow_succ _ _ _ _ _ _ hdvd' K hK.1
        ⟨K', by rw [hK'.1, tsub_add_cancel_of_le h0m.nat_succ_le], le_trans hK.2 hK'.2⟩)
      fun hnm : n = m => ⟨H, by simp [hH, hnm]⟩

/-- A generalisation of **Sylow's first theorem**. If `p ^ n` divides
  the cardinality of `G`, then there is a subgroup of cardinality `p ^ n` -/
theorem exists_subgroup_card_pow_prime [Finite G] (p : ℕ) {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ n ∣ Nat.card G) : ∃ K : Subgroup G, Nat.card K = p ^ n :=
  let ⟨K, hK⟩ := exists_subgroup_card_pow_prime_le p hdvd ⊥
    (by rw [card_bot, pow_zero]) n.zero_le
  ⟨K, hK.1⟩

/-- A special case of **Sylow's first theorem**. If `G` is a `p`-group of size at least `p ^ n`
then there is a subgroup of cardinality `p ^ n`. -/
lemma exists_subgroup_card_pow_prime_of_le_card {n p : ℕ} (hp : p.Prime) (h : IsPGroup p G)
    (hn : p ^ n ≤ Nat.card G) : ∃ H : Subgroup G, Nat.card H = p ^ n := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite G := Nat.finite_of_card_ne_zero <| by linarith [Nat.one_le_pow n p hp.pos]
  obtain ⟨m, hm⟩ := h.exists_card_eq
  refine exists_subgroup_card_pow_prime _ ?_
  rw [hm] at hn ⊢
  exact pow_dvd_pow _ <| (Nat.pow_le_pow_iff_right hp.one_lt).1 hn

/-- A special case of **Sylow's first theorem**. If `G` is a `p`-group and `H` a subgroup of size at
least `p ^ n` then there is a subgroup of `H` of cardinality `p ^ n`. -/
lemma exists_subgroup_le_card_pow_prime_of_le_card {n p : ℕ} (hp : p.Prime) (h : IsPGroup p G)
    {H : Subgroup G} (hn : p ^ n ≤ Nat.card H) : ∃ H' ≤ H, Nat.card H' = p ^ n := by
  obtain ⟨H', H'card⟩ := exists_subgroup_card_pow_prime_of_le_card hp (h.to_subgroup H) hn
  refine ⟨H'.map H.subtype, map_subtype_le _, ?_⟩
  rw [← H'card]
  let e : H' ≃* H'.map H.subtype := H'.equivMapOfInjective (Subgroup.subtype H) H.subtype_injective
  exact Nat.card_congr e.symm.toEquiv

/-- A special case of **Sylow's first theorem**. If `G` is a `p`-group and `H` a subgroup of size at
least `k` then there is a subgroup of `H` of cardinality between `k / p` and `k`. -/
lemma exists_subgroup_le_card_le {k p : ℕ} (hp : p.Prime) (h : IsPGroup p G) {H : Subgroup G}
    (hk : k ≤ Nat.card H) (hk₀ : k ≠ 0) : ∃ H' ≤ H, Nat.card H' ≤ k ∧ k < p * Nat.card H' := by
  obtain ⟨m, hmk, hkm⟩ : ∃ s, p ^ s ≤ k ∧ k < p ^ (s + 1) :=
    exists_nat_pow_near (Nat.one_le_iff_ne_zero.2 hk₀) hp.one_lt
  obtain ⟨H', H'H, H'card⟩ := exists_subgroup_le_card_pow_prime_of_le_card hp h (hmk.trans hk)
  refine ⟨H', H'H, ?_⟩
  simpa only [pow_succ', H'card] using And.intro hmk hkm

theorem pow_dvd_card_of_pow_dvd_card [Finite G] {p n : ℕ} [hp : Fact p.Prime] (P : Sylow p G)
    (hdvd : p ^ n ∣ Nat.card G) : p ^ n ∣ Nat.card P := by
  rw [← index_mul_card P.1] at hdvd
  exact (hp.1.coprime_pow_of_not_dvd P.not_dvd_index).symm.dvd_of_dvd_mul_left hdvd

theorem dvd_card_of_dvd_card [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hdvd : p ∣ Nat.card G) : p ∣ Nat.card P := by
  rw [← pow_one p] at hdvd
  have key := P.pow_dvd_card_of_pow_dvd_card hdvd
  rwa [pow_one] at key

/-- Sylow subgroups are Hall subgroups. -/
theorem card_coprime_index [Finite G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G) :
    (Nat.card P).Coprime P.index :=
  let ⟨_n, hn⟩ := IsPGroup.iff_card.mp P.2
  hn.symm ▸ (hp.1.coprime_pow_of_not_dvd P.not_dvd_index).symm

theorem ne_bot_of_dvd_card [Finite G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G)
    (hdvd : p ∣ Nat.card G) : (P : Subgroup G) ≠ ⊥ := by
  refine fun h => hp.out.not_dvd_one ?_
  have key : p ∣ Nat.card P := P.dvd_card_of_dvd_card hdvd
  rwa [h, card_bot] at key

/-- The cardinality of a Sylow subgroup is `p ^ n`
where `n` is the multiplicity of `p` in the group order. -/
theorem card_eq_multiplicity [Finite G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G) :
    Nat.card P = p ^ Nat.factorization (Nat.card G) p := by
  obtain ⟨n, heq : Nat.card P = _⟩ := IsPGroup.iff_card.mp P.isPGroup'
  refine Nat.dvd_antisymm ?_ (P.pow_dvd_card_of_pow_dvd_card (Nat.ordProj_dvd _ p))
  rw [heq, ← hp.out.pow_dvd_iff_dvd_ordProj (show Nat.card G ≠ 0 from Nat.card_pos.ne'), ← heq]
  exact P.1.card_subgroup_dvd_card

/-- If `G` has a normal Sylow `p`-subgroup, then it is the only Sylow `p`-subgroup. -/
noncomputable def unique_of_normal {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (h : P.Normal) : Unique (Sylow p G) := by
  refine { uniq := fun Q ↦ ?_ }
  obtain ⟨x, h1⟩ := exists_smul_eq G P Q
  obtain ⟨x, h2⟩ := exists_smul_eq G P default
  rw [smul_eq_of_normal] at h1 h2
  rw [← h1, ← h2]

instance characteristic_of_subsingleton {p : ℕ} [Subsingleton (Sylow p G)] (P : Sylow p G) :
    P.Characteristic := by
  refine Subgroup.characteristic_iff_map_eq.mpr fun ϕ ↦ ?_
  have h := Subgroup.pointwise_smul_def (a := ϕ) (P : Subgroup G)
  rwa [← pointwise_smul_def, Subsingleton.elim (ϕ • P) P, eq_comm] at h

theorem normal_of_subsingleton {p : ℕ} [Subsingleton (Sylow p G)] (P : Sylow p G) :
    P.Normal :=
  Subgroup.normal_of_characteristic _

theorem characteristic_of_normal {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (h : P.Normal) : P.Characteristic := by
  have _ := unique_of_normal P h
  exact characteristic_of_subsingleton _

theorem normal_of_normalizer_normal {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (hn : P.normalizer.Normal) : P.Normal := by
  rw [← normalizer_eq_top_iff, ← normalizer_sup_eq_top' P le_normalizer, sup_idem]

@[simp]
theorem normalizer_normalizer {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    P.normalizer.normalizer = P.normalizer := by
  have := normal_of_normalizer_normal (P.subtype (le_normalizer.trans le_normalizer))
  rw [coe_subtype, normal_subgroupOf_iff_le_normalizer (le_normalizer.trans le_normalizer),
    ← subgroupOf_normalizer_eq (le_normalizer.trans le_normalizer)] at this
  exact le_antisymm (this normal_in_normalizer) le_normalizer

theorem normal_of_all_max_subgroups_normal [Finite G]
    (hnc : ∀ H : Subgroup G, IsCoatom H → H.Normal) {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) : P.Normal :=
  normalizer_eq_top_iff.mp
    (by
      rcases eq_top_or_exists_le_coatom P.normalizer with (heq | ⟨K, hK, hNK⟩)
      · exact heq
      · haveI := hnc _ hK
        have hPK : P ≤ K := le_trans le_normalizer hNK
        refine (hK.1 ?_).elim
        rw [← sup_of_le_right hNK, P.normalizer_sup_eq_top' hPK])

theorem normal_of_normalizerCondition (hnc : NormalizerCondition G) {p : ℕ} [Fact p.Prime]
    [Finite (Sylow p G)] (P : Sylow p G) : P.Normal :=
  normalizer_eq_top_iff.mp <|
    normalizerCondition_iff_only_full_group_self_normalizing.mp hnc _ <| normalizer_normalizer _

/-- If all its Sylow subgroups are normal, then a finite group is isomorphic to the direct product
of these Sylow subgroups.
-/
noncomputable def directProductOfNormal [Finite G]
    (hn : ∀ {p : ℕ} [Fact p.Prime] (P : Sylow p G), P.Normal) :
    (∀ p : (Nat.card G).primeFactors, ∀ P : Sylow p G, P) ≃* G := by
  have := Fintype.ofFinite G
  set ps := (Nat.card G).primeFactors
  -- “The” Sylow subgroup for p
  let P : ∀ p, Sylow p G := default
  have : ∀ p, Fintype (P p) := fun p ↦ Fintype.ofFinite (P p)
  have hcomm : Pairwise fun p₁ p₂ : ps => ∀ x y : G, x ∈ P p₁ → y ∈ P p₂ → Commute x y := by
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    haveI hp₁' := Fact.mk (Nat.prime_of_mem_primeFactors hp₁)
    haveI hp₂' := Fact.mk (Nat.prime_of_mem_primeFactors hp₂)
    have hne' : p₁ ≠ p₂ := by simpa using hne
    apply Subgroup.commute_of_normal_of_disjoint _ _ (hn (P p₁)) (hn (P p₂))
    apply IsPGroup.disjoint_of_ne p₁ p₂ hne' _ _ (P p₁).isPGroup' (P p₂).isPGroup'
  refine MulEquiv.trans (N := ∀ p : ps, P p) ?_ ?_
  -- There is only one Sylow subgroup for each p, so the inner product is trivial
  · -- here we need to help the elaborator with an explicit instantiation
    apply @MulEquiv.piCongrRight ps (fun p => ∀ P : Sylow p G, P) (fun p => P p) _ _
    rintro ⟨p, hp⟩
    haveI hp' := Fact.mk (Nat.prime_of_mem_primeFactors hp)
    letI := unique_of_normal _ (hn (P p))
    apply MulEquiv.piUnique
  apply MulEquiv.ofBijective (Subgroup.noncommPiCoprod hcomm)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · apply Subgroup.injective_noncommPiCoprod_of_iSupIndep
    apply independent_of_coprime_order hcomm
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    haveI hp₁' := Fact.mk (Nat.prime_of_mem_primeFactors hp₁)
    haveI hp₂' := Fact.mk (Nat.prime_of_mem_primeFactors hp₂)
    have hne' : p₁ ≠ p₂ := by simpa using hne
    simp only [← Nat.card_eq_fintype_card]
    apply IsPGroup.coprime_card_of_ne p₁ p₂ hne' _ _ (P p₁).isPGroup' (P p₂).isPGroup'
  · simp only [← Nat.card_eq_fintype_card]
    calc
      Nat.card (∀ p : ps, P p) = ∏ p : ps, Nat.card (P p) := Nat.card_pi
      _ = ∏ p : ps, p.1 ^ (Nat.card G).factorization p.1 := by
        congr 1 with ⟨p, hp⟩
        exact @card_eq_multiplicity _ _ _ p ⟨Nat.prime_of_mem_primeFactors hp⟩ (P p)
      _ = ∏ p ∈ ps, p ^ (Nat.card G).factorization p :=
        (Finset.prod_finset_coe (fun p => p ^ (Nat.card G).factorization p) _)
      _ = (Nat.card G).factorization.prod (· ^ ·) := rfl
      _ = Nat.card G := Nat.factorization_prod_pow_eq_self Nat.card_pos.ne'

end Sylow
