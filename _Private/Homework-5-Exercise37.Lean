import Mathlib

--37 : 群 $G$ 没有非平凡子群的充分必要条件是 $G=\\{1\\}$ 或是素数阶循环群
--case →
--Prove by contradiction
--$ G \ne {1} $ exist $g0 \in G, g0 \ne 1$
--then any $g \ne 1 $, then $\< g \> = G $ because $\< g \> \ne 1$
--Pick $g0$,we got $G$ cyclic
--If $order of g0 = 0 $ $ 1 \ne g0 * g0 $
--Then $\< g0 * g0 \> = G $ thus contain $g0$
--We have some $k$ ,$ (g0 * g0) ^ k = g0$ so $ g0 ^ (2 * k -1) = 1$
--This contradicts with order zero
--If $order of g0 > 0$ and $ |G| $ is not a prime
--Any $ g \ne 1 $, then $\< g \> = G $ so $ order of g = |G| $ is all the same
--$order of g0 = |G|$ thus not a prime and fnite,exist $1 < a < order of g0, a | order of g0 $
--Especially $ 1 \ne g0 ^ a $ because $a < |G| = order of g0$
--But $(g0 ^ a)^(order of g0/a) = 1$ the order isn't equal to $|G|$ contradicts
--case ←
--If $G$ is trival, every subgroup is equal to ${1}$
--If $G$ is cyclic and of prime order
--when $H = {1}$, trivial
--when not, prove that $H = G$
--there is an element $h \in H$ that is different from $1$ because $H$ is not ${1}$
--because $G$ is cyclic, $h$ is equal to the generater $g$ to the k th power
--we first show that $k$ and the card of $G$ is coprime
--the gcd of $k$ and the card of $G$ divides the card of $G$, which is prime, thus can only be $1$ or the card of $G$
--equal to one is what we want, when equal to the card of $G$, it also divides $k$, we got $g ^ k = 1$, this contradicts with $h$ is not $1$
--now proof that any $x \in G$ is also in $H$, thus $H = G$
--because $G$ is cyclic, $x = g ^ n$ for some $n$
--using the Bezout's lemma we got an $l$ and $m$ which satisfies $k * l + m * card(G) = n$ (multipliy it by $n$)
--$x = h ^ l$ thus in $H$

theorem exercise37 {G : Type*} [Group G] (h : ∀ H : Subgroup G, H = ⊥ ∨ H = ⊤) : Nat.card G = 1 ∨ (IsCyclic G ∧ (Nat.card G).Prime) := by
  --Prove by contradiction
  by_contra
  --$ G \ne {1} $ exist $g \in G, g \ne 1$
  have ntriv : ¬ Nat.card G = 1 := by tauto
  have ne1 : ∃ g₀ : G, g₀ ≠ 1 := by
    by_contra all1
    absurd ntriv
    push_neg at all1
    haveI : Unique G := {
      default := 1
      uniq := all1 }
    apply Nat.card_unique
  have ncardp : ¬ (IsCyclic G ∧ (Nat.card G).Prime) := by tauto
  rcases ne1 with ⟨g₀,hg₀⟩
  --then any $g \ne 1 $, then $\< g \> = G $ because $\< g \> \ne 1$
  have eqtop : ∀ g : G , g ≠ 1 → ↑(Subgroup.zpowers g) = ⊤ := by
    intro g hg
    have gptriv : ↑(Subgroup.zpowers g) = ⊥ ∨ ↑(Subgroup.zpowers g) = ⊤ := h ↑(Subgroup.zpowers g)
    by_contra netop
    simp only [Subgroup.zpowers_eq_bot, netop, or_false] at gptriv
    absurd gptriv
    exact hg
  --Pick $g0$,we got $G$ cyclic
  have eqtop0 : ↑(Subgroup.zpowers g₀) = ⊤ := eqtop g₀ hg₀
  have cyc : IsCyclic G := ⟨by
    show ∃ g : G, ∀ x, x ∈ Subgroup.zpowers g
    use g₀
    simp only [eqtop0,Subgroup.mem_top, forall_const]⟩
  simp only [cyc, true_and] at ncardp
  by_cases ord0 : orderOf g₀ = 0
  --If $order of g0 = 0 $ $ 1 \ne g0 * g0 $
  · have : g₀ * g₀ ≠ 1 := by
      rw [ Eq.symm (pow_two g₀) ]
      apply orderOf_eq_zero_iff'.mp ord0 2
      norm_num
    --Then $\< g0 * g0 \> = G $ thus contain $g0$
    have eqtop':  ↑(Subgroup.zpowers (g₀ * g₀)) = ⊤ := eqtop (g₀ * g₀) this
    have : g₀ ∈ (Subgroup.zpowers (g₀ * g₀)) := by simp only [eqtop',Subgroup.mem_top]
    --We have some $k$ ,$ (g0 * g0) ^ k = g0$
    have existk : ∃ k : ℤ , (g₀ * g₀) ^ k = g₀ := by apply Subgroup.mem_zpowers_iff.mp this
    rcases existk with ⟨k,hk⟩
    --so $ g0 ^ (2 * k -1) = 1$
    have : (g₀ * g₀) ^ k = g₀ ^ (2 * k) := by
      calc
      _ = (g₀^2) ^ k := by congr; exact Eq.symm (zpow_two g₀)
      _ = _ := (zpow_mul _ _ _).symm
    rw[this] at hk
    have : g₀ ^ (2 * k - 1) = 1 := by
      calc
      _= g₀ ^ (2 * k - 1) * g₀ * g₀⁻¹ := by group
      _= g₀ ^ (2 * k) * g₀⁻¹ := by simp only [mul_zpow_self g₀ (2 * k - 1), sub_add_cancel]
      _=_ := by simp only [hk, mul_right_inv]
    --This contradicts with order zero
    absurd this
    have : 2 * k - 1 ≠ 0 := by omega
    apply orderOf_eq_zero_iff.mp at ord0
    apply isOfFinOrder_iff_zpow_eq_one.mpr.mt at ord0
    push_neg at ord0
    exact ord0 (2 * k -1) this
  --If $order of g0 > 0$ and $ |G| $ is not a prime
  · have ordFin : 0 < orderOf g₀ := Nat.pos_iff_ne_zero.mpr ord0
    --Any $ g \ne 1 $, then $\< g \> = G $ so $ order of g = |G| $ is all the same
    have : ∀ g : G , g ≠ 1 → orderOf g = Nat.card G := by
      intro g hg
      have :∀ x, x ∈ Subgroup.zpowers g := by simp only [eqtop g hg,Subgroup.mem_top, forall_const]
      rw [← Nat.card_zpowers g, (Subgroup.eq_top_iff' (Subgroup.zpowers g)).mpr this]
      exact Nat.card_congr (Equiv.Set.univ _)
    have ntriv' : Nat.card G ≥ 2 := by
      apply (Nat.two_le_iff (Nat.card G)).mpr
      simp only [ne_eq, ntriv, not_false_eq_true, and_true]
      simp only [← this g₀ hg₀, ord0, not_false_eq_true]
    rw[← this g₀ hg₀] at ncardp
    rw[← this g₀ hg₀] at ntriv'
    --$order of g0 = |G|$ thus not a prime and fnite,exist $1 < a < order of g0, a | order of g0 $
    have np : ∃ m, m ∣ (orderOf g₀) ∧ 2 ≤ m ∧ m < (orderOf g₀) := Nat.exists_dvd_of_not_prime2 ntriv' ncardp
    rcases np with ⟨m,hm,ge2,ltord⟩
    --Especially $ 1 \ne g0 ^ a $ because $a < |G| = order of g0$
    have mne0 : m ≠ 0 := by linarith
    have ne1 : g₀ ^ m ≠ 1 := pow_ne_one_of_lt_orderOf' mne0 ltord
    --But $(g0 ^ a)^(order of g0/a) = 1$ the order isn't equal to $|G|$ contradicts
    have ordne: orderOf (g₀ ^ m) = (orderOf g₀) / m := orderOf_pow_of_dvd mne0 hm
    rw[this (g₀ ^ m) ne1, ← this g₀ hg₀] at ordne
    absurd ordne
    apply Nat.ne_of_gt
    exact Nat.div_lt_self ordFin ge2

theorem exercise37' {G : Type*} [Group G] (h : Nat.card G = 1 ∨ (IsCyclic G ∧ (Nat.card G).Prime) ) : ∀ H : Subgroup G, H = ⊥ ∨ H = ⊤ := by
  rcases h with l|r
  · --If $G$ is trival, every subgroup is equal to ${1}$
    haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp l).1
    have : ∀ x : G, x = 1 := fun x => Subsingleton.eq_one x
    intro H
    simp only [(Subgroup.eq_bot_iff_forall H).mpr fun x _ => this x, true_or]
  · --If $G$ is cyclic and of prime order
    rcases r.1 with ⟨g,hg⟩
    intro H
    by_cases hyp : H = ⊥
    · --when $H = {1}$, trivial
      simp only [hyp, true_or]
    · --when not, prove that $H = G$
      right
      --there is an element $h \in H$ that is different from $1$ because $H$ is not ${1}$
      have : ∃ h ∈ H, h ≠ 1 := by
        by_contra all1
        push_neg at all1
        absurd hyp
        exact ((Subgroup.eq_bot_iff_forall H).mpr all1)
      --because $G$ is cyclic, $h$ is equal to the generater $g$ to the k th power
      rcases this with ⟨h,hh1,hh2⟩
      rcases hg h with ⟨k,hk⟩
      dsimp at hk
      --we first show that $k$ and the card of $G$ is coprime
      have : Int.gcd k (Nat.card G) = 1 := by
        --the gcd of $k$ and the card of $G$ divides the card of $G$, which is prime, thus can only be $1$ or the card of $G$
        have : Int.gcd k (Nat.card G) ∣ Nat.card G := Int.ofNat_dvd.mp Int.gcd_dvd_right
        rcases (Nat.dvd_prime r.2).mp this with l1|r1
        · --equal to one is what we want
          exact l1
        · --when equal to the card of $G$, it also divides $k$
          have : (Int.gcd k (Nat.card G) : ℤ) ∣ k := Int.gcd_dvd_left
          rw [r1] at this
          --we got $g ^ k = 1$, this contradicts with $h$ is not $1$
          absurd hh2
          rcases this with ⟨l,hl⟩
          rw [←hk,hl, zpow_mul g ((Nat.card G) : ℤ) l, zpow_natCast g (Nat.card G), pow_card_eq_one', one_zpow]
      --now proof that any $x \in G$ is also in $H$, thus $H = G$
      apply (Subgroup.eq_top_iff' H).mpr
      intro x
      --because $G$ is cyclic, $x = g ^ n$ for some $n$
      rcases hg x with ⟨n,hn⟩
      dsimp at hn
      --using the Bezout's lemma we got an $l$ and $m$ which satisfies $k * l + m * card(G) = n$ (multipliy it by $n$)
      obtain ⟨l,m,hlm⟩ : ∃ l m : ℤ, k * l + (Nat.card G : ℤ) * m = n := by
        use (Int.gcdA k (Nat.card G : ℤ)) * n, (Int.gcdB k (Nat.card G : ℤ)) * n
        calc
          _= ((k * k.gcdA (Nat.card G : ℤ)) + ((Nat.card G : ℤ ) * k.gcdB ↑(Nat.card G))) * n := by ring
          _= _ := by simp only [←Int.gcd_eq_gcd_ab k (Nat.card G : ℤ),this, Nat.cast_one, one_mul]
      --$x = h ^ l$ thus in $H$
      convert Subgroup.zpow_mem H hh1 l
      rw [←hn, ←hk, ←zpow_mul,←hlm, zpow_add g (k * l) (((Nat.card G) : ℤ) * m), zpow_mul g (Nat.card G : ℤ) m, zpow_natCast g (Nat.card G), pow_card_eq_one', one_zpow, mul_one]


theorem exercise37_final {G : Type*} [Group G]  : ( ∀ H : Subgroup G, H = ⊥ ∨ H = ⊤ ) ↔ Nat.card G = 1 ∨ (IsCyclic G ∧ (Nat.card G).Prime) := by
  constructor
  · intro h
    --Prove by contradiction
    by_contra
    --$ G \ne {1} $ exist $g \in G, g \ne 1$
    have ne1 : ∃ g₀ : G, g₀ ≠ 1 := by
      by_contra all1
      push_neg at all1
      haveI : Unique G := {
        default := 1
        uniq := all1 }
      have ntriv : ¬ Nat.card G = 1 := by tauto
      exact ntriv Nat.card_unique
    have ncardp : ¬ (IsCyclic G ∧ (Nat.card G).Prime) := by tauto
    rcases ne1 with ⟨g₀,hg₀⟩
    --then any $g \ne 1 $, then $\< g \> = G $ because $\< g \> \ne 1$
    have eqtop : ∀ g : G , g ≠ 1 → ↑(Subgroup.zpowers g) = ⊤ := by
      intro g hg
      have gptriv : (Subgroup.zpowers g) = ⊥ ∨ ↑(Subgroup.zpowers g) = ⊤ := h (Subgroup.zpowers g)
      by_contra netop
      simp only [Subgroup.zpowers_eq_bot, netop, or_false] at gptriv
      exact hg gptriv
    --Pick $g0$,we got $G$ cyclic
    have cyc : IsCyclic G := ⟨by
      use g₀
      simp only [eqtop g₀ hg₀,Subgroup.mem_top, forall_const]⟩
    simp only [cyc, true_and] at ncardp
    by_cases ord0 : orderOf g₀ = 0
    --If $order of g0 = 0 $ $ 1 \ne g0 * g0 $
    · have : g₀ * g₀ ≠ 1 := by
        rw [←(pow_two g₀) ]
        apply orderOf_eq_zero_iff'.mp ord0 2 Nat.zero_lt_two
      --Then $\< g0 * g0 \> = G $ thus contain $g0$
      have : g₀ ∈ (Subgroup.zpowers (g₀ * g₀)) := by simp only [eqtop (g₀ * g₀) this,Subgroup.mem_top]
      --We have some $k$ ,$ (g0 * g0) ^ k = g0$
      rcases (Subgroup.mem_zpowers_iff.mp this) with ⟨k,hk⟩
      --so $ g0 ^ (2 * k -1) = 1$
      rw[←zpow_two g₀, ←zpow_mul] at hk
      have pow_eq1 : g₀ ^ (2 * k - 1) = 1 := by
        calc
        _= g₀ ^ (2 * k - 1) * g₀ * g₀⁻¹ := by group
        _=_ := by simp only [mul_zpow_self g₀ (2 * k - 1), sub_add_cancel, hk, mul_right_inv]
      --This contradicts with order zero
      have : 2 * k - 1 ≠ 0 := by omega
      apply orderOf_eq_zero_iff.mp at ord0
      apply isOfFinOrder_iff_zpow_eq_one.mpr.mt at ord0
      push_neg at ord0
      exact (ord0 (2 * k -1) this) pow_eq1
    --If $order of g0 > 0$ and $ |G| $ is not a prime
    · --Any $ g \ne 1 $, then $\< g \> = G $ so $ order of g = |G| $ is all the same
      have ordeq : ∀ g : G , g ≠ 1 → orderOf g = Nat.card G := by
        intro g hg
        have :∀ x, x ∈ Subgroup.zpowers g := by simp only [eqtop g hg,Subgroup.mem_top, forall_const]
        rw [← Nat.card_zpowers g, (Subgroup.eq_top_iff' (Subgroup.zpowers g)).mpr this]
        exact Nat.card_congr (Equiv.Set.univ _)
      have ntriv' : Nat.card G ≥ 2 := by
        apply (Nat.two_le_iff (Nat.card G)).mpr
        simp only [← ordeq g₀ hg₀, ne_eq, ord0, not_false_eq_true, orderOf_eq_one_iff, hg₀, and_self]
      rw[← ordeq g₀ hg₀] at ncardp ntriv'
      --$order of g0 = |G|$ thus not a prime and fnite,exist $1 < a < order of g0, a | order of g0 $
      rcases (Nat.exists_dvd_of_not_prime2 ntriv' ncardp) with ⟨m,hm,ge2,ltord⟩
      --Especially $ 1 \ne g0 ^ a $ because $a < |G| = order of g0$
      have ne1 : g₀ ^ m ≠ 1 := pow_ne_one_of_lt_orderOf' (Nat.not_eq_zero_of_lt ge2) ltord
      --But $order of (g0 ^ a) = (order of g0/a)$ the order isn't equal to $|G|$ contradicts
      have ordne: orderOf (g₀ ^ m) = (orderOf g₀) / m := orderOf_pow_of_dvd (Nat.not_eq_zero_of_lt ge2) hm
      rw[ordeq (g₀ ^ m) ne1, ← ordeq g₀ hg₀] at ordne
      absurd ordne
      apply Nat.ne_of_gt (Nat.div_lt_self (Nat.pos_iff_ne_zero.mpr ord0) ge2)
  · intro h
    rcases h with l|r
    · --If $G$ is trival, every subgroup is equal to ${1}$
      haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp l).1
      have : ∀ x : G, x = 1 := fun x => Subsingleton.eq_one x
      intro H
      simp only [(Subgroup.eq_bot_iff_forall H).mpr fun x _ => this x, true_or]
    · intro H
      --It is obvious that $G$ and $H$ are finite
      have : Finite G := (Nat.card_pos_iff.mp (Nat.Prime.pos r.2)).2
      haveI : Fintype G := Fintype.ofFinite G
      haveI : Fintype H := Fintype.ofFinite ↥H
      --use the lagrange theorem on $H$, we got the card of $H$ divides the card of $G$ which is prime
      have := Subgroup.card_subgroup_dvd_card H
      simp only [←Nat.card_eq_fintype_card] at this
      --thus the card of $H$ can only be $1$ or the card of $G$
      rcases (Nat.dvd_prime r.2).mp this with one|p
      · --when equal to $1$, $H = {1}$
        simp only [Subgroup.card_eq_one.mp one, true_or]
      · --when equal to the card of $G$, $H = G$
        simp only [Nat.card_eq_fintype_card] at p
        simp only [Subgroup.eq_top_of_card_eq H p, or_true]
