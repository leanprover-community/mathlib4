import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Order.RelSeries
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Module.Torsion
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.AssociatedPrime

section ModuleCat

universe u v

variable {R : Type u} [Ring R]

lemma span_lemma {M : Type*} [AddCommGroup M] [Module R M] (S T : Set M) (a : M)
  (hins : insert a T = S) (hspan : Submodule.span R S = ⊤) :
    Submodule.span R {Submodule.Quotient.mk a} =
      (⊤ : Submodule R (M ⧸ Submodule.span R T)) := by
  have := Submodule.span_image (Submodule.mkQ (Submodule.span R T)) (s := S)
  rw [hspan, Submodule.map_top, Submodule.range_mkQ,
    ← hins, Set.image_insert_eq] at this
  have sub_zero : ((Submodule.mkQ (Submodule.span R T)) '' T) ⊆ {0} := by
    rintro y ⟨hy₁, hy₂⟩
    rw [← hy₂.2, Submodule.mkQ_apply, Set.mem_singleton_iff,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_span.2 fun _ a ↦ a hy₂.1
  by_cases hempty : IsEmpty T
  · replace hempty : T = ∅ := Set.isEmpty_coe_sort.mp hempty
    rw [hempty] at this ⊢
    rwa [Set.image_empty, insert_empty_eq] at this
  · replace sub_zero : ((Submodule.mkQ (Submodule.span R T)) '' T) = {0} := by
      refine (Set.Nonempty.subset_singleton_iff ?_).mp sub_zero
      simp only [Submodule.mkQ_apply, Set.image_nonempty]
      refine Set.nonempty_iff_ne_empty.2 ?_
      rwa [Set.isEmpty_coe_sort] at hempty
    rw [← this, sub_zero, Set.pair_comm]
    exact Submodule.span_insert_zero.symm

theorem fg_induction (P : ModuleCat.{v, u} R → Prop)
    (h_zero : ∀ (N : ModuleCat.{v, u} R), Subsingleton N → P N)
    (h_base : ∀ (N : ModuleCat.{v, u} R), (⊤ : Submodule R N).IsPrincipal → P N)
    (h_ext : ∀ (M : ModuleCat.{v, u} R), ∀ (N : Submodule R M),
      P (ModuleCat.of R N) → P (ModuleCat.of R (M ⧸ N)) → P M)
    (M : ModuleCat.{v, u} R) (hM : Module.Finite R M) : P M := by
  have (n : ℕ) : ∀ (L : ModuleCat.{v, u} R), (∃ (S : Set L.carrier),
      S.Finite ∧ Nat.card S = n ∧ Submodule.span R S = ⊤) → P L := by
    induction' n using Nat.strongRecOn with n ih
    · by_cases n_zero : n = 0
      · intro L ⟨S, SFin, card, Sspan⟩
        have empty : S = ∅ := Set.isEmpty_coe_sort.1 <|
          (@Finite.card_eq_zero_iff _ SFin).1 <| nonpos_iff_eq_zero.1
            <| by rw [card, n_zero]
        have h_zero_aux : Subsingleton (ModuleCat.of R (⊤ : Submodule R L)) := by
          refine {allEq := fun ⟨a, a_prop⟩ ⟨b, b_prop⟩ ↦ ?_}
          simp_rw [← Sspan, empty, Submodule.span_empty, Submodule.mem_bot]
            at a_prop b_prop
          rwa [← b_prop, ← Subtype.mk_eq_mk] at a_prop
        have h_zero₁ := h_zero (ModuleCat.of R (⊤ : Submodule R L)) h_zero_aux
        have h_zero₂ := h_zero (ModuleCat.of R (L.carrier ⧸ (⊤ : Submodule R L))) <|
          Submodule.subsingleton_quotient_iff_eq_top.2 rfl
        exact h_ext L ⊤ h_zero₁ h_zero₂
      · intro L ⟨S, SFin, card_eq, Sspan⟩
        set m : ℕ := n - 1
        have card_eq : Nat.card S = m + 1 := by
          simpa only [card_eq] using (Nat.succ_pred_eq_of_ne_zero n_zero).symm
        rcases Set.eq_insert_of_ncard_eq_succ card_eq with ⟨s, T, sT, ins, Tcard⟩
        have PT : P (ModuleCat.of R (Submodule.span R T)) := by
          refine ih m (Nat.sub_one_lt n_zero) (ModuleCat.of R (Submodule.span R T)) ?_
          haveI : Finite T := Set.Finite.subset SFin (by simp only [← ins, Set.subset_insert])
          set f : T → Submodule.span R T := fun t : T ↦ ⟨t,
            Submodule.span_mono (by simp only [Set.singleton_subset_iff, Subtype.coe_prop])
            (Submodule.mem_span_singleton_self (t : L))⟩
          refine ⟨Set.range f, Set.finite_range f, ?_⟩
          constructor
          · have finj : Function.Injective f := by
              intro x y feq
              simp only [Subtype.mk.injEq, f] at feq
              exact SetCoe.ext feq
            simpa only [Nat.card_range_of_injective finj] using Tcard
          · have : Set.range f = {t : Submodule.span R T | (t : L) ∈ T} := by
              ext t
              constructor <;> intro ht
              · rcases Subtype.exists.mp <| Set.mem_range.mp ht with ⟨_, b, feq⟩
                exact Set.mem_of_eq_of_mem (id (Eq.symm feq)) b
              · exact Set.mem_range.mp <| Subtype.exists.mpr ⟨t, ht, rfl⟩
            simp only [this, Submodule.span_setOf_mem_eq_top]
        have P1 : P (ModuleCat.of R (L ⧸ Submodule.span R T)) := by
          refine h_base (ModuleCat.of R (L ⧸ Submodule.span R T)) ?_
          simp only [← span_lemma S T s ins Sspan]
          exact (Submodule.isPrincipal_iff _).mpr ⟨Submodule.Quotient.mk s, rfl⟩
        exact h_ext L (Submodule.span R T) PT P1
  rcases Submodule.fg_def.mp (Module.finite_def.mp hM) with ⟨S, SFin, Sspan⟩
  exact this (Nat.card S) M ⟨S, SFin, rfl, Sspan⟩

end ModuleCat

universe u v
variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

section helper

noncomputable def quotTorsionOfEquivSpanSingleton' (x : M) (hM : ⊤ = Submodule.span R {x}) :
    ((⊤ : Submodule R M) ⧸ LinearMap.ker (⊤ : Submodule R M).subtype) ≃ₗ[R] R ⧸ Ideal.torsionOf R M x := by
  have equiv : (LinearMap.range (⊤ : Submodule R M).subtype) ≃ₗ[R]
      R ⧸ (Ideal.torsionOf R M x) := by
    rw [Submodule.range_subtype, hM]
    exact (Ideal.quotTorsionOfEquivSpanSingleton R M x).symm
  exact (LinearMap.quotKerEquivRange <| Submodule.subtype _).trans equiv

variable (N : Submodule R M)

private theorem RelSeries_smash_helper {α : Type*} {r : α → α → Prop} {s : α → α → Prop}
    (p : RelSeries r) (q : RelSeries r) (connect : p.last = q.head)
    (hp : ∀ (i : Fin p.length), s (p (Fin.castSucc i)) (p i.succ))
    (hq : ∀ (i : Fin q.length), s (q (Fin.castSucc i)) (q i.succ)) :
    ∀ (i : Fin (RelSeries.smash p q connect).length), s ((RelSeries.smash p q connect) (Fin.castSucc i)) ((RelSeries.smash p q connect) i.succ) := by
  let p' : RelSeries (r ⊓ s) := ⟨p.length, p.toFun, fun i ↦ ⟨p.step i, hp i⟩⟩
  let q' : RelSeries (r ⊓ s) := ⟨q.length, q.toFun, fun i ↦ ⟨q.step i, hq i⟩⟩
  let pq' : RelSeries (r ⊓ s) := RelSeries.smash p' q' connect
  exact fun i ↦ (pq'.step i).2

def submodule_equiv (N1 N2 : Submodule R N) : ((Submodule.map N.subtype N1) ⧸
    Submodule.comap (Submodule.map N.subtype N1).subtype (Submodule.map N.subtype N2))
    ≃ₗ[R] N1 ⧸ Submodule.comap N1.subtype N2 := by
  refine Submodule.Quotient.equiv
    (Submodule.comap (Submodule.map N.subtype N1).subtype (Submodule.map N.subtype N2))
    (Submodule.comap N1.subtype N2) (N.equivSubtypeMap N1).symm ?_
  ext x
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, Subtype.exists,
    exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨a, ⟨⟨haN, haN1⟩, ⟨_, haN2⟩, rfl⟩⟩
    exact haN2
  · intro hx
    refine ⟨x.1, ⟨x.1.2, x.2⟩, ⟨⟨x.1.2, hx⟩, rfl⟩⟩

noncomputable def mkQ_equiv (N1 N2 : Submodule R (M ⧸ N)) : ((Submodule.comap N.mkQ N1) ⧸
    Submodule.comap (Submodule.comap N.mkQ N1).subtype (Submodule.comap N.mkQ N2))
    ≃ₗ[R] N1 ⧸ Submodule.comap N1.subtype N2 := by
  let f : (Submodule.comap N.mkQ N1) →ₗ[R] N1 ⧸ Submodule.comap N1.subtype N2 :=
    (Submodule.comap N1.subtype N2).mkQ ∘ₗ N.mkQ.restrict (fun x a ↦ a)
  have : Function.Surjective f := by
    simp only [f, LinearMap.coe_comp]
    refine Function.Surjective.comp (Submodule.mkQ_surjective (Submodule.comap N1.subtype N2)) ?_
    intro x
    obtain ⟨y, hy⟩ := N.mkQ_surjective x.1
    simp only [Subtype.exists, Submodule.mem_comap, Submodule.mkQ_apply, f]
    exact ⟨y, ⟨show N.mkQ y ∈ N1 from hy ▸ x.2, Subtype.ext hy⟩⟩
  have : LinearMap.ker f = Submodule.comap (Submodule.comap N.mkQ N1).subtype (Submodule.comap N.mkQ N2) := by
    ext x; simp [f]
  rw [← this]
  exact LinearMap.quotKerEquivOfSurjective f (by assumption)

end helper

section calculation

open LinearMap in
lemma AssociatedPrimes.ideal_quotient_prime_eq_singleton (p : Ideal R) [hp : p.IsPrime]
    (q : Submodule R (R ⧸ p)) (hq : q ≠ ⊥) : associatedPrimes R q = {p} := by
  have h0 : ker (toSpanSingleton R q 0) = ⊤ := by simp
  have h1 (x : q) (h : x ≠ 0) : ker (toSpanSingleton R q x) = p := by
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective x.1
    ext y
    simp only [mem_ker, toSpanSingleton, smulRight, id_apply]
    show y • x = 0 ↔ y ∈ p
    rw [show y • x = 0 ↔ (y • x).1 = 0 from Iff.symm Submodule.coe_eq_zero,
      show (y • x).1 = y • x.1 from rfl, ← hz]
    show (Ideal.Quotient.mk p (y * z)) = 0 ↔ y ∈ p
    simp only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] at h ⊢
    have : z ∉ p := by rw [← Ideal.Quotient.eq_zero_iff_mem, hz, Submodule.coe_eq_zero]; exact h
    exact ⟨fun h' ↦ by simpa [this] using (hp.mem_or_mem h'), fun h ↦ Ideal.IsTwoSided.mul_mem_of_left z h⟩
  ext y
  simp only [associatedPrimes, IsAssociatedPrime, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy, ⟨x, hx⟩⟩
    by_cases h : x = 0
    · simp_rw [h, h0] at hx
      exact False.elim (hy.1 hx)
    · exact hx.trans (h1 x h)
  · obtain ⟨x, hx⟩ : ∃ x : q, x ≠ 0 :=
      Submodule.nonzero_mem_of_bot_lt <| Ne.bot_lt' (Ne.symm hq)
    exact fun h' ↦ ⟨h' ▸ hp, ⟨x, h'.trans (h1 x hx).symm⟩⟩

open LinearMap in
lemma AssociatedPrimes.quotient_prime_eq_singleton (p : Ideal R) [hp : p.IsPrime] :
    associatedPrimes R (R ⧸ p) = {p} := by
  rw [LinearEquiv.AssociatedPrimes.eq Submodule.topEquiv.symm]
  apply AssociatedPrimes.ideal_quotient_prime_eq_singleton
  simp

end calculation

section mono

lemma associatedPrimes_mono {M : Type*} [AddCommGroup M] [Module R M] (N1 N2 : Submodule R M) (h : N1 ≤ N2):
    associatedPrimes R N1 ⊆ associatedPrimes R N2 := by
  intro p ⟨hp, ⟨x, eq⟩⟩
  constructor
  · exact hp
  · use ⟨x.1, h x.2⟩
    ext t
    simp only [eq, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    exact ⟨fun h' ↦ Subtype.ext <| (AddSubmonoid.mk_eq_zero N1.toAddSubmonoid).mp h',
      fun h ↦ Submodule.coe_eq_zero.mp congr($h.1)⟩

lemma associatedPrimes_subset_of_submodule {M : Type*} [AddCommGroup M] [Module R M] (N : Submodule R M) :
    associatedPrimes R N ⊆ associatedPrimes R M := by
  have : associatedPrimes R M = associatedPrimes R (⊤ : Submodule R M) :=
    LinearEquiv.AssociatedPrimes.eq Submodule.topEquiv.symm
  rw [this]
  apply associatedPrimes_mono R N ⊤ (fun {x} a ↦ trivial)

end mono

section extension

lemma associatedPrimes_subset_union_of_exact {L M N: Type*} [AddCommGroup L] [AddCommGroup M]
    [AddCommGroup N] [Module R L] [Module R M] [Module R N] (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (finj : Function.Injective f) (hexact : Function.Exact f g) :
    (associatedPrimes R M) ⊆ (associatedPrimes R L) ∪ (associatedPrimes R N) := by
  intro p ⟨hp, ⟨x, eq⟩⟩
  set M' := LinearMap.range (LinearMap.toSpanSingleton R M x) with hM'
  have hx (y : R) : y • x = 0 ↔ y ∈ p := by simp [eq]
  by_cases ch : LinearMap.range f ⊓ M'= ⊥
  · refine Or.inr ⟨hp, g x, ?_⟩
    ext y
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← map_smul, hexact (y • x),
      ← hx y, ← Submodule.mem_bot R, ← ch, Submodule.mem_inf]
    simp [hM']
  · obtain ⟨y, hy⟩ : ∃ y : L, f y ∈ M' ∧ f y ≠ 0 := by
      obtain ⟨_, ⟨⟨y, rfl⟩, hz2⟩, hz3⟩ : ∃ z : M, (z ∈ LinearMap.range f ⊓ M') ∧ z ≠ 0 :=
        Submodule.exists_mem_ne_zero_of_ne_bot ch
      exact ⟨y, ⟨hz2, hz3⟩⟩
    refine Or.inl ⟨hp, y, ?_⟩
    ext r
    simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    rw [← finj.eq_iff (a := (r • y)) (b := 0), map_zero, map_smul]
    obtain ⟨z, hz⟩ : ∃ z : R, z • x = f y := hy.1
    have hzne : z ∉ p := fun h ↦ (by rw [(hx z).mpr h] at hz; exact hy.2 hz.symm)
    rw [← hz, smul_smul, hx]
    exact ⟨fun h ↦ Ideal.IsTwoSided.mul_mem_of_left z h, fun h ↦ by simpa [hzne] using (Ideal.IsPrime.mem_or_mem hp h)⟩

lemma AssociatedPrimes.subset_union_of_injective {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hinj : Function.Injective f) :
    associatedPrimes R N ⊆ associatedPrimes R M ∪ associatedPrimes R (N ⧸ Submodule.map f ⊤) :=
  associatedPrimes_subset_union_of_exact R f ((Submodule.map f ⊤).mkQ) hinj (by simp [LinearMap.exact_iff])

lemma AssociatedPrimes.subset_union_quotient {M : Type*} [AddCommGroup M] [Module R M]
    (p q : Submodule R M) (hpq : p ≤ q) :
    (associatedPrimes R q) ⊆ (associatedPrimes R p) ∪ (associatedPrimes R (q ⧸ (Submodule.comap q.subtype p))) := by
  apply associatedPrimes_subset_union_of_exact R (Submodule.inclusion hpq) (Submodule.comap q.subtype p).mkQ
  · exact Submodule.inclusion_injective hpq
  · simp only [LinearMap.exact_iff, Submodule.ker_mkQ]
    exact (Submodule.range_inclusion p q hpq).symm

end extension

section chain

lemma AssociatedPrimes.subset_iUnion_quotient (p : LTSeries (Submodule R M)) (h_head : p.head = ⊥)
    (h_last : p.last = ⊤) : associatedPrimes R M ⊆ ⋃ i : Fin p.length,
    associatedPrimes R ((p i.succ) ⧸ (Submodule.comap (p i.succ).subtype (p (Fin.castSucc i)))) := by
  rw [← LinearEquiv.AssociatedPrimes.eq (Submodule.topEquiv), ← h_last]
  clear h_last
  induction p using RelSeries.inductionOn'
  case singleton N =>
    simp only [RelSeries.head_singleton] at h_head
    simp only [RelSeries.singleton_length, RelSeries.singleton_toFun, Set.iUnion_of_empty,
      Set.subset_empty_iff]
    erw [RelSeries.last_singleton, h_head]
    apply associatedPrimes.eq_empty_of_subsingleton
  case snoc p N hN ih =>
    simp only [RelSeries.head_snoc] at h_head
    specialize ih h_head
    rw [RelSeries.last_snoc]
    apply Set.Subset.trans (AssociatedPrimes.subset_union_quotient R p.last N (le_of_lt hN))
    apply Set.Subset.trans (Set.union_subset_union_left _ ih)
    intro x hx
    simp only [Set.mem_union, Set.mem_iUnion, RelSeries.snoc_length] at hx ⊢
    rcases hx with (⟨i, hx⟩ | hx)
    · refine ⟨i.castSucc, ?_⟩
      rw [Fin.succ_castSucc, RelSeries.snoc_castSucc p N hN i.succ, RelSeries.snoc_castSucc p N hN i.castSucc]
      exact hx
    · refine ⟨Fin.last _, ?_⟩
      have : (p.snoc N hN).toFun (Fin.last p.length).castSucc = p.last := by
        simp only [RelSeries.snoc, RelSeries.append, RelSeries.singleton_length, Nat.add_zero,
          Nat.reduceAdd, show (Fin.last p.length).castSucc = (Fin.last p.length).castAdd 1 from rfl,
          Fin.cast_refl, Function.comp_apply, id_eq, Fin.append_left]
        rfl
      simp only [Fin.succ_last, Nat.succ_eq_add_one]
      rw [RelSeries.last_snoc', this]
      exact hx

theorem AssociatedPrimes.of_quotient_iso_quotient_prime (p : LTSeries (Submodule R M)) (h_head : p.head = ⊥)
    (h_last : p.last = ⊤) (P : Fin p.length → Ideal R) (hPprime : ∀ (i : Fin p.length), (P i).IsPrime)
    (hP : ∀ (i : Fin p.length), Nonempty
      (((p i.succ) ⧸ (Submodule.comap (p i.succ).subtype (p (Fin.castSucc i)))) ≃ₗ[R] (R ⧸ (P i)))) :
    (associatedPrimes R M) ⊆ P '' Set.univ := by
  have heq1 : ∀ (i : Fin p.length), associatedPrimes R ((p i.succ) ⧸ (Submodule.comap (p i.succ).subtype (p (Fin.castSucc i)))) = associatedPrimes R (R ⧸ (P i)) := by
    intro i
    let e := Classical.choice (hP i)
    exact LinearEquiv.AssociatedPrimes.eq e
  have heq1' := Set.iUnion_congr heq1
  have heq2 : ∀ (i : Fin p.length), associatedPrimes R (R ⧸ (P i)) = {P i} := by
    intro i
    exact AssociatedPrimes.quotient_prime_eq_singleton R _
  have heq2' := Set.iUnion_congr heq2
  have hmem : ⋃ i : Fin p.length, {P i} ⊆ P '' Set.univ := by
    rw[Set.iUnion_subset_iff]
    intro i
    rw [Set.image_univ, Set.singleton_subset_iff, Set.mem_range]
    use i
  apply subset_trans (AssociatedPrimes.subset_iUnion_quotient _ _ p h_head h_last)
  rw [heq1', heq2']
  exact hmem

end chain

section noetherian

variable [Module.Finite R M]

-- [Stacks 00KZ]
theorem exists_LTSeries_quotient_cyclic:
    ∃ (p : LTSeries (Submodule R M)), p.head = ⊥ ∧ p.last = ⊤ ∧
    ∀ (i : Fin p.length), ∃ P : Ideal R, Nonempty (
    ((p i.succ) ⧸ (Submodule.comap (p i.succ).subtype (p (Fin.castSucc i)))) ≃ₗ[R] (R ⧸ P)) := by
  let P : (ModuleCat.{v, u} R) → Prop := fun M ↦
    ∃ (p : LTSeries (Submodule R M)), p.head = ⊥ ∧ p.last = ⊤ ∧
    ∀ (i : Fin p.length), ∃ P : Ideal R, Nonempty (
    ((p i.succ) ⧸ (Submodule.comap (p i.succ).subtype (p (Fin.castSucc i)))) ≃ₗ[R] (R ⧸ P))
  show P (ModuleCat.of R M)
  have P_zero : ∀ (N : ModuleCat.{v, u} R), Subsingleton N → P N := fun _ _ ↦ ⟨⟨0, fun i ↦ ⊥, fun i ↦ Fin.elim0 i⟩,
      ⟨rfl, ⟨Submodule.eq_bot_of_subsingleton.symm, fun i ↦ Fin.elim0 i⟩⟩⟩
  have P_base : ∀ (N : ModuleCat.{v, u} R), (⊤ : Submodule R N).IsPrincipal → P N := by
    rintro N ⟨a, hN⟩
    by_cases htri : Nontrivial (Submodule R N)
    · refine ⟨⟨1, fun i ↦ match i with | 0 => ⊥ | 1 => ⊤,
        fun i ↦ match i with | 0 => bot_lt_top⟩, ⟨rfl, ⟨rfl, fun i ↦ ?_⟩⟩⟩
      match i with
      | 0 =>
        refine ⟨Ideal.torsionOf R N a, ⟨?_⟩⟩
        apply quotTorsionOfEquivSpanSingleton' ..
        assumption
    · exact ⟨⟨0, fun i ↦ ⊥, fun i ↦ Fin.elim0 i⟩,
      ⟨rfl, ⟨subsingleton_iff_bot_eq_top.2 <|
        not_nontrivial_iff_subsingleton.1 htri, fun i ↦ Fin.elim0 i⟩⟩⟩
  have P_ext : ∀ (M : ModuleCat.{v, u} R), ∀ (N : Submodule R M), P (ModuleCat.of R N) → P (ModuleCat.of R (M ⧸ N)) → P M := by
    rintro M N ⟨pN, hpN1, hpN2, hpN3⟩ ⟨pMN, hpMN1, hpMN2, hpMN3⟩
    let q : M →ₗ[R] M ⧸ N := Submodule.mkQ N
    let pN' : LTSeries (Submodule R M) := (LTSeries.map pN (Submodule.map (Submodule.subtype N))
      (Submodule.map_strictMono_of_injective <| Submodule.subtype_injective _))
    let pMN' : LTSeries (Submodule R M) := LTSeries.map pMN (Submodule.comap (Submodule.mkQ N))
      (Submodule.comap_strictMono_of_surjective <| Submodule.mkQ_surjective N)
    refine ⟨RelSeries.smash pN' pMN' (by simp [pN', pMN', hpN2, hpMN1]), by simp [pN', hpN1], by simp [pMN', hpMN2], ?_⟩
    apply RelSeries_smash_helper (α := Submodule R M) (s := fun M1 M2 ↦ ∃ P : Ideal R,
      Nonempty ((M2 ⧸ (Submodule.comap M2.subtype M1)) ≃ₗ[R] (R ⧸ P)))
    · intro i
      obtain ⟨P, ⟨hP'⟩⟩ := hpN3 i
      refine ⟨P, ⟨LinearEquiv.trans (show (_ ≃ₗ[R] _) from ?_) hP'⟩⟩
      simp only [LTSeries.map_length, LTSeries.map_toFun, pN', pMN']
      exact submodule_equiv ..
    · intro i
      obtain ⟨P, ⟨hP'⟩⟩ := hpMN3 i
      refine ⟨P, ⟨LinearEquiv.trans (show (_ ≃ₗ[R] _) from ?_) hP'⟩⟩
      simp only [LTSeries.map_length, LTSeries.map_toFun, pMN']
      exact mkQ_equiv ..
  exact fg_induction P P_zero P_base P_ext _ inferInstance

-- [Stacks 00L0]
theorem exists_LTSeries_quotient_iso_quotient_prime [IsNoetherianRing R] :
    ∃ (p : LTSeries (Submodule R M)), p.head = ⊥ ∧ p.last = ⊤ ∧
    ∀ (i : Fin p.length), ∃ P : Ideal R, P.IsPrime ∧ Nonempty (
    ((p i.succ) ⧸ (Submodule.comap (p i.succ).subtype (p (Fin.castSucc i)))) ≃ₗ[R] (R ⧸ P)) := by
  let P : ModuleCat.{v, u} R → Prop := fun M ↦
    ∃ (p : LTSeries (Submodule R M)), p.head = ⊥ ∧ p.last = ⊤ ∧
    ∀ (i : Fin p.length), ∃ P : Ideal R, P.IsPrime ∧ Nonempty (
    ((p i.succ) ⧸ (Submodule.comap (p i.succ).subtype (p (Fin.castSucc i)))) ≃ₗ[R] (R ⧸ P))
  show P (ModuleCat.of R M)
  have P_zero : ∀ (N : ModuleCat.{v, u} R), Subsingleton N → P N := fun _ _ ↦ ⟨⟨0, fun i ↦ ⊥, fun i ↦ Fin.elim0 i⟩,
    ⟨rfl, ⟨Submodule.eq_bot_of_subsingleton.symm, fun i ↦ Fin.elim0 i⟩⟩⟩
  have P_ext : ∀ (M : ModuleCat.{v, u} R), ∀ (N : Submodule R M), P (ModuleCat.of R N) → P (ModuleCat.of R (M ⧸ N)) → P M := by
    rintro M N ⟨pN, hpN1, hpN2, hpN3⟩ ⟨pMN, hpMN1, hpMN2, hpMN3⟩
    let q : M →ₗ[R] M ⧸ N := Submodule.mkQ N
    let pN' : LTSeries (Submodule R M) := (LTSeries.map pN (Submodule.map (Submodule.subtype N))
      (Submodule.map_strictMono_of_injective <| Submodule.subtype_injective _))
    let pMN' : LTSeries (Submodule R M) := LTSeries.map pMN (Submodule.comap (Submodule.mkQ N))
      (Submodule.comap_strictMono_of_surjective <| Submodule.mkQ_surjective N)
    refine ⟨RelSeries.smash pN' pMN' (by simp [pN', pMN', hpN2, hpMN1]), by simp [pN', hpN1], by simp [pMN', hpMN2], ?_⟩
    apply RelSeries_smash_helper (α := Submodule R M) (s := fun M1 M2 ↦ ∃ P : Ideal R, P.IsPrime ∧ Nonempty ((M2 ⧸ (Submodule.comap M2.subtype M1)) ≃ₗ[R] (R ⧸ P)))
    · intro i
      obtain ⟨P, hP, ⟨hP'⟩⟩ := hpN3 i
      refine ⟨P, hP, ⟨LinearEquiv.trans (show (_ ≃ₗ[R] _) from ?_) hP'⟩⟩
      simp only [LTSeries.map_length, LTSeries.map_toFun, pN', pMN']
      exact submodule_equiv ..
    · intro i
      obtain ⟨P, hP, ⟨hP'⟩⟩ := hpMN3 i
      refine ⟨P, hP, ⟨LinearEquiv.trans (show (_ ≃ₗ[R] _) from ?_) hP'⟩⟩
      simp only [LTSeries.map_length, LTSeries.map_toFun, pMN']
      exact mkQ_equiv ..
  have P_base : ∀ (N : ModuleCat.{v, u} R), (⊤ : Submodule R N).IsPrincipal → P N := by
    rintro N ⟨a, hN⟩
    generalize hI : Ideal.torsionOf R N a = I
    induction I using WellFoundedGT.induction generalizing N a
    rename_i I ih
    by_cases h_triv : I = ⊤
    · have : Subsingleton N := by
        rw [← Submodule.subsingleton_iff R]
        apply subsingleton_of_bot_eq_top
        simp_all
      exact P_zero N this
    · have : Nontrivial N := by
        rw [← hI, Ideal.torsionOf_eq_top_iff] at h_triv
        exact nontrivial_of_ne a 0 h_triv
      by_cases h : I.IsPrime
      · refine ⟨⟨1, fun i ↦ match i with | 0 => ⊥ | 1 => ⊤,
          fun i ↦ match i with | 0 => bot_lt_top⟩, ⟨rfl, ⟨rfl, fun i ↦ ?_⟩⟩⟩
        match i with
        | 0 =>
          refine ⟨I, h, ⟨hI ▸ ?_⟩⟩
          apply quotTorsionOfEquivSpanSingleton' ..
          assumption
      · rw [Ideal.isPrime_iff] at h
        simp only [ne_eq, h_triv, not_false_eq_true, true_and, not_forall, Classical.not_imp,
        not_or] at h
        obtain ⟨y, x, hxy, hy, hx⟩ := h
        let N' := Submodule.span R {x • a}
        apply P_ext _ N'
        · apply ih (Ideal.torsionOf R N (x • a)) ?_ (ModuleCat.of R N')
           ⟨x • a, Submodule.mem_span_singleton_self (x • a)⟩
          · ext y
            simp only [Submodule.mem_top, true_iff]
            obtain ⟨z, hz⟩ := y
            simp only [N', Submodule.mem_span_singleton] at hz ⊢
            obtain ⟨b, hb⟩ := hz
            exact ⟨b, Subtype.ext hb⟩
          · ext b
            simp
          · rw [← hI, lt_iff_le_not_le]
            constructor
            · intro z hz
              rw [Ideal.mem_torsionOf_iff] at hz ⊢
              rw [smul_smul, mul_comm, ← smul_smul, hz, smul_zero]
            · show ¬ ((Ideal.torsionOf R (↑N) (x • a)) : Set R) ⊆ (Ideal.torsionOf R (↑N) a)
              simp only [Ideal.coe_torsionOf, Set.not_subset, Set.mem_preimage,
                LinearMap.toSpanSingleton_apply, Set.mem_singleton_iff, N']
              use y
              rw [smul_smul, ← Ideal.mem_torsionOf_iff, ← Ideal.mem_torsionOf_iff, hI]
              exact ⟨hxy, hy⟩
        · refine ih (Ideal.torsionOf R (N ⧸ N') (N'.mkQ a)) ?_ (ModuleCat.of R (N ⧸ N')) (N'.mkQ a) ?_ rfl
          · rw [← hI, lt_iff_le_not_le]
            constructor
            · intro z hz
              rw [Ideal.mem_torsionOf_iff] at hz ⊢
              rw [← map_smul, hz, map_zero]
            · show ¬ ((Ideal.torsionOf R (N ⧸ N') (N'.mkQ a)) : Set R) ⊆ (Ideal.torsionOf R N a)
              simp only [Ideal.coe_torsionOf, Set.not_subset, Set.mem_preimage,
                LinearMap.toSpanSingleton_apply, Set.mem_singleton_iff, N']
              refine ⟨x, ⟨?_, by rw [← Ideal.mem_torsionOf_iff, hI]; exact hx⟩⟩
              rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
              exact Submodule.mem_span_singleton_self (x • a)
          · ext y
            simp only [Submodule.mem_top, true_iff]
            obtain ⟨z, hz⟩ := N'.mkQ_surjective y
            simp only [N', Submodule.mem_span_singleton] at ⊢
            obtain ⟨b, hb⟩ : ∃ b : R, b • a = z := by
              rw [← Submodule.mem_span_singleton, ← hN]; trivial
            exact ⟨b, by rw [← hz, ← hb, map_smul]⟩
  exact fg_induction P P_zero P_base P_ext _ inferInstance

theorem AssociatedPrimes.finite_of_noetherian [IsNoetherianRing R] : (associatedPrimes R M).Finite := by
  obtain ⟨p, h_head, h_tail, h⟩:= exists_LTSeries_quotient_iso_quotient_prime R M
  choose P h1 h2 using h
  refine Set.Finite.subset ?_ (AssociatedPrimes.of_quotient_iso_quotient_prime R M p h_head h_tail P h1 h2)
  exact Set.toFinite (P '' Set.univ)

end noetherian
