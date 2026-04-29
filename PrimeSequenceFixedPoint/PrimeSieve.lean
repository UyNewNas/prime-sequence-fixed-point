import PrimeSequenceFixedPoint.Common
import PrimeSequenceFixedPoint.PrimeDef

open Prime

/-!
# PrimeSieve.lean (M4): Core sieve lemma

Dependency: Common (M1a) + PrimeDef (M1b).
-/

axiom primeSeq : Nat → Nat
axiom primeSeq_zero : primeSeq 0 = 2
axiom primeSeq_one : primeSeq 1 = 3

axiom primeSeq_step (n : Nat) :
  primeSeq (n+1) > primeSeq n ∧
  (∀ k ≤ n, ¬ primeSeq k ∣ primeSeq (n+1)) ∧
  (∀ m, m > primeSeq n → (∀ k ≤ n, ¬ primeSeq k ∣ m) → primeSeq (n+1) ≤ m)

theorem primeSeq_base1 : primeSeq 0 = 2 := primeSeq_zero
theorem primeSeq_base2 : primeSeq 1 = 3 := primeSeq_one

theorem primeSeq_pos (n : Nat) : 0 < primeSeq n := by
  induction n with
  | zero => rw [primeSeq_zero]; decide
  | succ n _ => have h := (primeSeq_step n).1; omega

theorem primeSeq_gt_one (n : Nat) : 1 < primeSeq n := by
  induction n with
  | zero => rw [primeSeq_zero]; decide
  | succ n ih => have h := (primeSeq_step n).1; omega

theorem primeSeq_strictMono : StrictMono primeSeq := by
  intro i j hij
  induction hij with
  | refl => simpa [Nat.succ_eq_add_one] using (primeSeq_step i).1
  | step _ h_ih => exact Nat.lt_trans h_ih (primeSeq_step _).1

theorem primeSeq_injective (i j : Nat) (heq : primeSeq i = primeSeq j) : i = j := by
  by_cases hne : i ≠ j
  · rcases Nat.lt_or_gt_of_ne hne with (hlt | hgt)
    · have h_lt_seq := primeSeq_strictMono hlt; rw [heq] at h_lt_seq; exact (Nat.lt_irrefl _ h_lt_seq).elim
    · have h_lt_seq := primeSeq_strictMono hgt; rw [heq] at h_lt_seq; exact (Nat.lt_irrefl _ h_lt_seq).elim
  · omega

theorem primeSeq_complete : ∀ n q, Prime q → q ≤ primeSeq n → ∃ i, i ≤ n ∧ primeSeq i = q := by
  intro n
  induction n with
  | zero =>
      intro q hq_prime hq_le
      rw [primeSeq_zero] at hq_le
      have hq_eq_2 : q = 2 := by
        have hq_ge_2 : 2 ≤ q := hq_prime.1
        omega
      subst hq_eq_2
      exact ⟨0, Nat.zero_le _, primeSeq_zero⟩
  | succ n ih =>
      intro q hq_prime hq_le
      have h_step := primeSeq_step n
      by_cases hq_le_n : q ≤ primeSeq n
      · rcases ih q hq_prime hq_le_n with ⟨i, hi, hi_eq⟩
        exact ⟨i, Nat.le_succ_of_le hi, hi_eq⟩
      · have hq_gt_n : primeSeq n < q := Nat.lt_of_not_ge hq_le_n
        by_cases hq_lt_succ : q < primeSeq (n+1)
        · have h_not_sieve : ¬ (∀ k ≤ n, ¬ primeSeq k ∣ q) := by
            intro h_sieve
            have h_le := h_step.2.2 q hq_gt_n h_sieve
            omega
          have h_exists : ∃ k, k ≤ n ∧ primeSeq k ∣ q := by
            apply Classical.byContradiction
            intro h_no
            have h_all : ∀ k ≤ n, ¬ primeSeq k ∣ q := by
              intro k hk_le; intro h_div; exact h_no ⟨k, hk_le, h_div⟩
            exact h_not_sieve h_all
          rcases h_exists with ⟨k, hk_le_n, hk_div_q⟩
          rcases hq_prime.eq_one_or_self hk_div_q with (h1 | heq')
          · have : 1 < primeSeq k := primeSeq_gt_one k; omega
          · exact ⟨k, Nat.le_succ_of_le hk_le_n, heq'⟩
        · have heq : q = primeSeq (n+1) := by omega
          exact ⟨n+1, Nat.le_refl _, heq.symm⟩

theorem primeSeq_prime (n : Nat) : Prime (primeSeq n) := by
  induction n with
  | zero =>
      rw [primeSeq_zero]
      exact ⟨by decide, λ m hm => by
        have hm_le : m ≤ 2 := Nat.le_of_dvd (by decide) hm
        have : m = 0 ∨ m = 1 ∨ m = 2 := by omega
        rcases this with (h0 | h1 | h2)
        · subst h0; rcases hm with ⟨k, hk⟩; simp at hk
        · exact Or.inl h1
        · exact Or.inr h2⟩
  | succ n ih =>
      rcases primeSeq_step n with ⟨h_gt, h_not_div, h_min⟩
      have h_two_le : 2 ≤ primeSeq (n+1) := by
        have : 2 ≤ primeSeq n := ih.1; omega
      apply no_smaller_prime_dvd (primeSeq (n+1)) h_two_le
      intro q hq_prime hq_lt
      have hq_le : q ≤ primeSeq (n+1) := Nat.le_of_lt hq_lt
      rcases primeSeq_complete (n+1) q hq_prime hq_le with ⟨i, hi_le_succ, hi_eq⟩
      have h_not_div_i : ¬ primeSeq i ∣ primeSeq (n+1) := by
        by_cases hi_eq_succ : i = n+1
        · subst hi_eq_succ
          rw [hi_eq] at hq_lt
          exact (Nat.lt_irrefl _ hq_lt).elim
        · have hi_le_n : i ≤ n := by omega
          exact h_not_div i hi_le_n
      rw [← hi_eq]; exact h_not_div_i

theorem primeSeq_indivisible (i j : Nat) (hij : i < j) : ¬ primeSeq i ∣ primeSeq j := by
  have hp_j := primeSeq_prime j
  intro hdiv
  rcases hp_j.eq_one_or_self hdiv with (h1 | heq)
  · have : 2 ≤ primeSeq i := (primeSeq_prime i).1; omega
  · have hlt := primeSeq_strictMono hij; rw [← heq] at hlt; exact Nat.lt_irrefl _ hlt

theorem next_prime_eq_min (n m : Nat) :
    (m = primeSeq (n+1)) ↔
    (m > primeSeq n ∧ (∀ k ≤ n, ¬ primeSeq k ∣ m) ∧
     (∀ m', m' > primeSeq n → (∀ k ≤ n, ¬ primeSeq k ∣ m') → m ≤ m')) := by
  constructor
  · intro hm; subst hm; exact primeSeq_step n
  · intro ⟨h_gt, h_not_div, h_min⟩
    have h_step := primeSeq_step n
    apply Nat.le_antisymm
    · exact h_min (primeSeq (n+1)) h_step.1 h_step.2.1
    · exact h_step.2.2 m h_gt h_not_div

theorem next_prime_eq_min_explicit (n : Nat) :
    primeSeq (n+1) > primeSeq n ∧
    (∀ k ≤ n, ¬ primeSeq k ∣ primeSeq (n+1)) ∧
    (∀ m, m > primeSeq n → (∀ k ≤ n, ¬ primeSeq k ∣ m) → primeSeq (n+1) ≤ m) :=
  primeSeq_step n

theorem primeSeq_good : Indivisible primeSeq ∧ StrictMono primeSeq :=
  ⟨primeSeq_indivisible, primeSeq_strictMono⟩
