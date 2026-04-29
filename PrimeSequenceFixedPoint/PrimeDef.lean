import PrimeSequenceFixedPoint.Common

/-!
# PrimeDef.lean (M1b): Prime definition and basic tests

Dependency: Common (M1a, divisibility).
-/

/-- `Prime p`: `p ≥ 2` and only divisible by 1 and itself -/
def Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p

namespace Prime

variable {p a b m n : Nat}

theorem two_le (hp : Prime p) : 2 ≤ p := hp.1

theorem eq_one_or_self (hp : Prime p) (h : m ∣ p) : m = 1 ∨ m = p := hp.2 m h

theorem one_lt (hp : Prime p) : 1 < p :=
  Nat.lt_of_lt_of_le (by decide : 1 < 2) hp.1

theorem ne_zero (hp : Prime p) : p ≠ 0 :=
  Nat.ne_zero_of_lt (hp.one_lt)

theorem pos (hp : Prime p) : 0 < p :=
  Nat.lt_of_lt_of_le (by decide : 0 < 2) hp.1

theorem not_dvd_one (hp : Prime p) : ¬ p ∣ 1 := by
  intro h
  have hle : p ≤ 1 := Nat.le_of_dvd Nat.one_pos h
  have : 2 ≤ 1 := Nat.le_trans hp.1 hle
  exact Nat.not_succ_le_self 1 this

theorem coprime_of_not_dvd (hp : Prime p) (h : ¬ p ∣ a) : Nat.Coprime p a := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hgcd_dvd_p : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
  rcases hp.eq_one_or_self hgcd_dvd_p with (h1 | hp')
  · exact h1
  · have hgcd_dvd_a : Nat.gcd p a ∣ a := Nat.gcd_dvd_right p a
    rw [hp'] at hgcd_dvd_a
    exact (h hgcd_dvd_a).elim

theorem dvd_mul (hp : Prime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases hpa : p ∣ a
  · exact Or.inl hpa
  · have hcop : Nat.Coprime p a := hp.coprime_of_not_dvd hpa
    have hpb : p ∣ b := hcop.dvd_of_dvd_mul_left h
    exact Or.inr hpb

theorem dvd_mul_of_dvd_mul_left (hp : Prime p) (h : p ∣ a * b) (hnot : ¬ p ∣ a) : p ∣ b := by
  rcases hp.dvd_mul h with (ha | hb)
  · exact (hnot ha).elim
  · exact hb

theorem dvd_mul_of_dvd_mul_right (hp : Prime p) (h : p ∣ a * b) (hnot : ¬ p ∣ b) : p ∣ a := by
  rcases hp.dvd_mul h with (ha | hb)
  · exact ha
  · exact (hnot hb).elim

theorem dvd_pow (hp : Prime p) {a n : Nat} (h : p ∣ a ^ n) : p ∣ a := by
  induction n with
  | zero =>
      rw [Nat.pow_zero] at h
      exact (hp.not_dvd_one h).elim
  | succ k ih =>
      rw [Nat.pow_succ] at h
      rcases hp.dvd_mul h with (ha_pow | ha)
      · exact ih ha_pow
      · exact ha

end Prime

/-! ## Existence of prime factor -/

theorem exists_prime_factor (n : Nat) (h : n > 1) : ∃ p, Prime p ∧ p ∣ n :=
  Nat.strongRecOn (motive := λ k => 1 < k → ∃ p, Prime p ∧ p ∣ k) n
    (λ m ih hm_gt_one => by
      by_cases hprime : Prime m
      · exact ⟨m, hprime, Nat.dvd_refl m⟩
      · have hm_two_le : 2 ≤ m := Nat.succ_le_of_lt hm_gt_one
        have h_not_all : ¬ (∀ d, d ∣ m → d = 1 ∨ d = m) := by
          intro h_all; exact hprime ⟨hm_two_le, h_all⟩
        have h_exists_proper : ∃ d, d ∣ m ∧ d ≠ 1 ∧ d ≠ m := by
          by_cases h_ex : ∃ d, d ∣ m ∧ d ≠ 1 ∧ d ≠ m
          · exact h_ex
          · exfalso; apply h_not_all
            intro d hd_div
            by_cases hd1 : d = 1
            · exact Or.inl hd1
            · by_cases hdm : d = m
              · exact Or.inr hdm
              · exfalso; apply h_ex; exact ⟨d, hd_div, hd1, hdm⟩
        rcases h_exists_proper with ⟨d, hd_div, hd_ne_one, hd_ne_m⟩
        have hd_pos : 0 < d := by
          by_cases hpos : 0 < d
          · exact hpos
          · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hpos
            subst hd0
            rcases hd_div with ⟨k, hk⟩; simp at hk
            have hm0 : m = 0 := hk; subst hm0
            omega
        have hd_gt_one : 1 < d := by
          have hge1 : 1 ≤ d := Nat.succ_le_of_lt hd_pos
          rcases Nat.lt_or_eq_of_le hge1 with (hlt | heq)
          · exact hlt
          · exact (hd_ne_one heq.symm).elim
        have hd_lt_m : d < m := by
          have hle : d ≤ m :=
            Nat.le_of_dvd (Nat.lt_trans (by decide : 0 < 1) hm_gt_one) hd_div
          exact Nat.lt_of_le_of_ne hle hd_ne_m
        rcases ih d hd_lt_m hd_gt_one with ⟨p, hp_prime, hp_div_d⟩
        exact ⟨p, hp_prime, Nat.dvd_trans hp_div_d hd_div⟩
    ) h

/-! ## No smaller prime divisor implies primality -/

theorem no_smaller_prime_dvd (m : Nat) (hm : 2 ≤ m) (h : ∀ q, Prime q → q < m → ¬ q ∣ m) :
    Prime m := by
  have hm_pos : 0 < m := Nat.lt_of_lt_of_le (by decide : 0 < 2) hm
  refine ⟨hm, λ d hd_div => ?_⟩
  by_cases hd1 : d = 1
  · exact Or.inl hd1
  · by_cases hd0 : d = 0
    · subst hd0
      have hm0 : m = 0 := by
        rcases hd_div with ⟨k, hk⟩
        simp at hk
        exact hk
      subst hm0
      exact Or.inr rfl
    · have hd_pos : 0 < d := Nat.pos_of_ne_zero hd0
      have hd_gt1 : 1 < d := by
        have hle : 1 ≤ d := Nat.succ_le_of_lt hd_pos
        rcases Nat.lt_or_eq_of_le hle with (hlt | heq)
        · exact hlt
        · exact (hd1 heq.symm).elim
      by_cases hdm : d = m
      · exact Or.inr hdm
      · have hd_le_m : d ≤ m := Nat.le_of_dvd hm_pos hd_div
        have hd_lt_m : d < m := Nat.lt_of_le_of_ne hd_le_m hdm
        rcases exists_prime_factor d hd_gt1 with ⟨q, hq_prime, hq_div_d⟩
        have hq_div_m : q ∣ m := Nat.dvd_trans hq_div_d hd_div
        have hq_le_d : q ≤ d := Nat.le_of_dvd (Nat.lt_trans (by decide : 0 < 1) hd_gt1) hq_div_d
        have hq_lt_m : q < m := Nat.lt_of_le_of_lt hq_le_d hd_lt_m
        exact (h q hq_prime hq_lt_m hq_div_m).elim
