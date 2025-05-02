import Mathlib.Tactic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Sylow
import Mathlib
/-
open Classical
variable {G : Type*} [Group G] [Fintype G] (A : Subgroup G) (AN : A.Normal)

lemma conj_ker : (@MulAut.conjNormal G _ A).ker = Subgroup.centralizer A := by
  ext x; constructor
  · -- Suppose fisrt $x \in \ker\phi$ and $a \in A$,
    intro xker a aA
    -- to show $x$ and $a$ commute it suffices to prove $xax^{-1} = a$.
    suffices x * a * x⁻¹ = a from by
      nth_rw 1 [← this]; group
    have : ∃ b : A, a = (b : G) := SetCoe.exists.mpr ⟨a, aA, rfl⟩
    rcases this with ⟨b, hb⟩
    -- which follows from $x \in \ker\phi$.
    rw [hb, ← MulAut.conjNormal_apply, (IsGroupHom.mem_ker _).mp xker]; rfl
  · -- Conversely, let $x \in C_G(A)$. This means that for all $a \in A$, $ax = xa$,
    intro xcen; apply Subgroup.mem_centralizer_iff.mp at xcen
    -- implying that $\phi(x)(a) = xax^{-1} = a$ for all $a \in A$ and $x \in \ker\phi$.
    apply (IsGroupHom.mem_ker _).mpr
    ext a; rw [MulAut.conjNormal_apply, ← xcen a a.2, mul_inv_cancel_right]; rfl

lemma card_dvd_cen_mul_aut : Nat.card G ∣ Nat.card (Subgroup.centralizer (A : Set G)) * Nat.card (MulAut A) := by
  -- First notice that $C_G(A) \unlhd G$.
  have centralizer_normal : (Subgroup.centralizer (A : Set G)).Normal := {
    conj_mem := by
      -- For $x \in C_G(A), g \in G$ and arbitrary element $a \in A$,
      intro x xcenA g a aA
      -- $gxg^{-1} \in C_G(A)$ is equivalent to $(g^{-1}ag)x = x(g^{-1}ag)$.
      nth_rw 1 [← one_mul a]; nth_rw 2 [← mul_one a]; rw [← mul_inv_self g]; simp only [← mul_assoc]
      suffices g⁻¹ * a * g * x = x * g⁻¹ * a * g from by
        rw [mul_assoc g, mul_assoc g, mul_assoc g, this, ← mul_assoc, ← mul_assoc, ← mul_assoc]
      -- We know that $g^{-1}ag \in A$ since $A$ is normal,
      have inv_conj : g⁻¹ * a * g ∈ A := by
        nth_rw 2 [← inv_inv g]
        exact AN.conj_mem a aA g⁻¹
      -- hence the equation is trivial because $x \in C_G(A)$.
      rw [mul_assoc x, mul_assoc x]; apply xcenA _ inv_conj
  }
  -- Combining the first isomorphism theorem and lemma 1, we derive that $G / C_G(A) \cong \mathrm{Im}(\phi)$.
  have GroupIso : G ⧸ (Subgroup.centralizer A) ≃* (@MulAut.conjNormal G _ A).range :=
    MulEquiv.trans (QuotientGroup.quotientMulEquivOfEq (conj_ker A AN)).symm (QuotientGroup.quotientKerEquivRange MulAut.conjNormal)
  -- Therefore, $|G / C_G(A)| \mid |\mathrm{Aut}(A)|$, suggesting that $|G| \mid |C_G(A)| \cdot |\mathrm{Aut}(A)|$.
  apply Nat.dvd_mul_of_div_dvd (Subgroup.card_subgroup_dvd_card _) ?_
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.centralizer A), Nat.mul_div_left _ Nat.card_pos, Nat.card_congr GroupIso.toEquiv]
  apply Subgroup.card_subgroup_dvd_card

variable (p : ℕ) [Fact p.Prime] (A_card : Nat.card A = p)

lemma map_cyclic : ∀ σ : (MulAut A), ∃ k : ℕ, 1 ≤ k ∧ k < p ∧ ∀ a : A, σ a = a ^ k := by
  intro σ
  -- $A$ is cyclic because $|A| = p$ is a prime, we note it here for usage later.
  rw [Nat.card_eq_fintype_card] at A_card
  -- It is known (and easy to prove) that $\exist m \in \Z$, $\sigma (a) = a ^ m, \forall a \in A$, we prove $m \mod p$ satisfies our requirements.
  have A_cyclic : IsCyclic A := isCyclic_of_prime_card A_card
  rcases (@MonoidHom.map_cyclic _ _ A_cyclic σ) with ⟨m, hm⟩
  use (m % p).natAbs; constructor
  · -- We first prove $1 \le m \mod p$, i.e. $m \mod p \ne 0$.
    apply Nat.one_le_iff_ne_zero.mpr; by_contra mod_eq_zero
    -- Assume the contrast, if $m \mod p = 0$ we have $p \mid m$, then $m = p \cdot t$ for some $t \in \N$.
    apply Int.natAbs_eq_zero.mp at mod_eq_zero
    have dvd_m : (p : ℤ) ∣ m := (Int.dvd_iff_emod_eq_zero _ m).mpr mod_eq_zero
    rcases dvd_m with ⟨t, ht⟩
    -- Let $g$ be an element in $A$ such that $g \ne 1$ (It exists since $|A| = p > 1$),
    have ne_one : ∃ g : A, g ≠ 1 := by
      apply Subgroup.ne_bot_iff_exists_ne_one.mp ((Subgroup.one_lt_card_iff_ne_bot A).mp _)
      rw [A_card]; exact Nat.Prime.one_lt Fact.out
    rcases ne_one with ⟨g, gn1⟩
    -- $\sigma (g) = g ^ m = (g ^ p) ^ t$ implies that $\sigma (g) = 1$, a contradiction, hence $1 \le m \mod p$.
    have gto1 : σ g = 1 := by
      show (σ : A →* A) g = 1; rw [hm g, ht, zpow_mul, ← A_card, zpow_natCast, pow_card_eq_one, one_zpow]
    absurd gto1; push_neg; simp [hm g, gn1]
  · constructor
    · -- By definition $m \mod p < p$,
      apply Int.ofNat_lt.mp
      rw [← Int.eq_natAbs_of_zero_le (Int.emod_nonneg m (Int.ofNat_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)))]
      apply Int.emod_lt_of_pos m (Int.ofNat_pos.mpr (Nat.Prime.pos Fact.out))
    · -- and we are left to prove $\sigma (a) = a ^ {m \mod p}$ for all $a$.
      intro a; show (σ : A →* A) a = a ^ ((m % p).natAbs); rw [hm a]
      rw [← zpow_natCast, ← Int.eq_natAbs_of_zero_le (Int.emod_nonneg m (Int.ofNat_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)))]
      -- This is because $m \equiv (m \mod p) (\mod p)$ and $a ^ p = 1$.
      apply zpow_eq_zpow_emod'
      rw [← A_card, pow_card_eq_one]

-- We define the map from $\mathrm{Aut}(A)$ to $\{0, 1, \cdots, p - 2\}$ by mapping an automorphism to $k - 1$ where $k$ is as mentioned in lemma 3,
noncomputable def aut_to_p : MulAut A → Finset.range (p - 1) := by
  intro σ
  use Classical.choose (map_cyclic A p A_card σ) - 1
  apply Finset.mem_range.mpr
  exact Nat.sub_lt_sub_right (Classical.choose_spec (map_cyclic A p A_card σ)).1 (Classical.choose_spec (map_cyclic A p A_card σ)).2.1

lemma card_of_aut : Nat.card (MulAut A) ≤ p - 1 := by
  -- and we need to prove the map is injective.
  rw [← Finset.card_range (p - 1), ← Nat.card_eq_finsetCard]
  apply Nat.card_le_card_of_injective (aut_to_p A p A_card)
  -- Suppose $\sigma_1, \sigma_2$ maps to $k_1, k_2$ respectively and $k_1 - 1 = k_2 - 1$,
  intro σ₁ σ₂ eq; apply congrArg Subtype.val at eq
  set k₁ := Classical.choose (map_cyclic A p A_card σ₁) with hk₁
  have d₁ : aut_to_p A p A_card σ₁ = k₁ - 1:= by simp [aut_to_p, hk₁]
  set k₂ := Classical.choose (map_cyclic A p A_card σ₂) with hk₂
  have d₂ : aut_to_p A p A_card σ₂ = k₂ - 1:= by simp [aut_to_p, hk₂]
  rw [d₁, d₂] at eq
  -- then for every $a \in A$, $\sigma_1(a) = a ^ {k_1} = a ^ {k_2} = \sigma_2(a)$, hence $\sigma_1 = \sigma_2$.
  ext a; apply Subtype.ext_iff.mp
  rw [(Classical.choose_spec (map_cyclic A p A_card σ₁)).2.2 a, ← hk₁]
  rw [(Classical.choose_spec (map_cyclic A p A_card σ₂)).2.2 a, ← hk₂]
  replace d₁ : k₁ = (k₁ - 1) + 1 := (Nat.sub_eq_iff_eq_add (Classical.choose_spec (map_cyclic A p A_card σ₁)).1).mp rfl
  replace d₂ : k₂ = (k₂ - 1) + 1 := (Nat.sub_eq_iff_eq_add (Classical.choose_spec (map_cyclic A p A_card σ₂)).1).mp rfl
  rw [d₁, d₂, eq]

theorem in_center (p_min : p = (Nat.card G).minFac) : A ≤ Subgroup.center G := by
  -- It is equivalent to prove $C_G(A) = G$.
  show (A : Set G) ⊆ Subgroup.center G; apply Subgroup.centralizer_eq_top_iff_subset.mp
  have card_dvd : Nat.card G ∣ Nat.card (Subgroup.centralizer (A : Set G)) * Nat.card (MulAut A) := card_dvd_cen_mul_aut A AN
  -- We first prove that $|G|$ and $|\mathrm{Aut}(A)|$ are coprime.
  have card_coprime : Nat.Coprime (Nat.card G) (Nat.card (MulAut A)) := by
    -- It suffices to prove these two have disjoint sets of prime factors.
    apply (Nat.disjoint_primeFactors _ _).mp
    · intro S SleG SleAut
      -- Suppose there is a common prime factor $q$ of $|G|$ and $|\mathrm{Aut}(A)|$,
      intro q qS
      have qP : q.Prime := Nat.prime_of_mem_primeFactors (SleG qS)
      have q_dvd_G : q ∣ Nat.card G := Nat.dvd_of_mem_primeFactors (SleG qS)
      have q_dvd_Aut : q ∣ Nat.card (MulAut A) := Nat.dvd_of_mem_primeFactors (SleAut qS)
      -- we know $q < p$ because $|\mathrm{Aut}(A)| \le p - 1$ by lemma 4.
      have qltp : q < p:= Nat.lt_of_le_sub_one (Nat.Prime.pos Fact.out) (le_trans (Nat.le_of_dvd (Nat.card_pos_iff.mpr ⟨instNonemptyOfInhabited, DFunLike.finite (MulAut ↥A)⟩) q_dvd_Aut) (card_of_aut A p A_card))
      -- However because $p$ is the minimal prime factor of $|G|$ we deduce that $p \le q$,
      have pleq : p ≤ q := by
        rw [p_min]; apply Nat.minFac_le_of_dvd (Nat.Prime.two_le qP) q_dvd_G
      apply not_lt_of_le at pleq
      -- a contradiction. Hence $|G|$ and $|\mathrm{Aut}(A)|$ are indeed coprime.
      contradiction
    · rw [Nat.card_eq_fintype_card]; exact Fintype.card_ne_zero
    · apply Nat.card_ne_zero.mpr ⟨instNonemptyOfInhabited, DFunLike.finite (MulAut ↥A)⟩
  -- Furthermore, lemma 2 claimed that $|G| \mid |C_G(A)| \cdot |\mathrm{Aut}(A)|$, so $|G|$ must divide $|C_G(A)|$.
  apply Nat.Coprime.dvd_of_dvd_mul_right card_coprime at card_dvd
  -- Therefore $|G| = |C_G(A)|$ and $G = C_G(A)$.
  have card_eq : Nat.card G = Nat.card (Subgroup.centralizer (A : Set G)) := dvd_antisymm card_dvd (Subgroup.card_subgroup_dvd_card _)
  exact Subgroup.eq_top_of_card_eq (Subgroup.centralizer (A : Set G)) card_eq.symm
-/


open Classical

variable {G : Type*} [Group G] [Fintype G] (H : Subgroup G) (p : ℕ) [Fact p.Prime] (P : Sylow p G) (PN : P.Normal)

-- We start by proving that the intersection of $P$ and $H$ is indeed a Sylow $p$-subgroup of $H$.
def inf_sylow : Sylow p H where
  carrier := (P.subgroupOf H)
  mul_mem' := mul_mem
  one_mem' := one_mem (P.subgroupOf H)
  inv_mem' := inv_mem
  isPGroup' := by
    -- First, we need to show that $(P \cap H)$ is indeed a $p$-group.
    apply IsPGroup.iff_card.mpr
    -- Suppose $|P| = p ^ n$ since $P$ is a $p$-group,
    rcases P with ⟨P, IsP, PMax⟩
    rcases (IsPGroup.exists_card_eq IsP) with ⟨n, card_P⟩
    -- and we can let $|P| = |P \cap H| \cdot k$ because $P \cap H$ is a sugroup of $P$.
    rcases (Subgroup.card_subgroup_dvd_card (H.subgroupOf P)) with ⟨k, hk⟩
    -- $p ^ n = k |P \cap H|$.
    rw [card_P] at hk
    have : Nat.card (P.subgroupOf H) = Nat.card (H.subgroupOf P) := by
      rw [← Subgroup.inf_subgroupOf_left P H, ← Subgroup.inf_subgroupOf_right H P]
      apply Nat.card_congr (Equiv.trans (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv.symm)
    simp; rw [← Nat.card_eq_fintype_card, this]
    -- From $p ^ n = k |P \cap H|$ we know $|P \cap H| = p ^ m$ for some $m \in \N$, hence $|P \cap H|$ is a $p$-group.
    rcases (Nat.dvd_prime_pow Fact.out).mp (dvd_of_mul_right_eq k hk.symm) with ⟨m, _, hm⟩
    rw [Nat.card_eq_fintype_card]
    exact ⟨m, hm⟩
  -- Next, we show that $(P \cap H)$ is a maximal $p$-subgroup of $H$.
  is_maximal' := by
    -- Notice the normal subgroup $P$ is the unique Sylow $p$-subgroup of $G$.
    have PU : Unique (Sylow p G) := Sylow.unique_of_normal P PN
    -- Suppose there's a Sylow $p$-subgroup $Q$ of $H$ and $P \cap H \subseteq Q$, we aim to prove $P \cap H = Q$.
    intro Q Qpg PleQ
    set Q' := Subgroup.map H.subtype Q with hQ'
    have Q'pg : IsPGroup p Q' := IsPGroup.map Qpg H.subtype
    -- By Sylow's theorem, $Q$ is contained in some Sylow $p$-subgroup $P'$ of G,
    rcases (IsPGroup.exists_le_sylow Q'pg) with ⟨P', hP'⟩
    -- but from the uniqueness we know $P' = P$.
    have PeqP' : P = P' := le_antisymm le_of_subsingleton le_of_subsingleton
    rw [← PeqP'] at hP'
    -- Hence $Q \subseteq P' = P$, combining the hypothesis we are done.
    apply le_antisymm _ PleQ; show Q ≤ (P.subgroupOf H)
    have : (Q'.subgroupOf H) ≤ (P.subgroupOf H) := (fun _ x => hP' x)
    apply le_trans _ this; rw [hQ']
    intro x hx; exact ⟨x, hx, rfl⟩

-- The uniqueness of $P \cap H$ follows from the fact that $P \cap H$ is normal since $P$ is normal.
noncomputable def unique_inf_sylow : Unique (Sylow p H) := Sylow.unique_of_normal (inf_sylow H p P PN) Subgroup.normal_subgroupOf
