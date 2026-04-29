import PrimeSequenceFixedPoint.Common

set_option linter.unusedVariables false

structure GoodSeq where
  seq         : Nat → Nat
  seq_pos     : ∀ n, 0 < seq n
  strictMono  : StrictMono seq
  indivisible : ∀ i j, i < j → ¬ (seq i ∣ seq j)

namespace GoodSeq

theorem indiveq (S : GoodSeq) (i j : Nat) (h : i < j) : ¬ S.seq i ∣ S.seq j :=
  S.indivisible i j h

theorem seq_one_gt_seq_zero (S : GoodSeq) : S.seq 0 < S.seq 1 :=
  S.strictMono (by exact Nat.zero_lt_one)

theorem seq_ge_two (S : GoodSeq) (n : Nat) : 2 ≤ S.seq n := by
  induction n with
  | zero =>
    by_cases h0eq1 : S.seq 0 = 1
    · have hdiv : S.seq 0 ∣ S.seq 1 := by rw [h0eq1]; exact Nat.one_dvd _
      exact (S.indivisible 0 1 Nat.zero_lt_one hdiv).elim
    · have hpos0 : 0 < S.seq 0 := S.seq_pos 0
      omega
  | succ n ih =>
    have hlt : S.seq n < S.seq (n+1) := S.strictMono (Nat.lt_succ_self n)
    omega

end GoodSeq

open GoodSeq

/-!
### Phi: Eratosthenes sieve functional

Phi is defined by these axioms, equivalent to `primeSeq_step` in M4.
In core Lean 4.30-rc2, `Nat.find` is unavailable so we use axioms here.
With `Nat.find` (available in mathlib), these become theorems.
-/

axiom Φ (S : GoodSeq) : GoodSeq

axiom Φ_seq_zero (S : GoodSeq) : (Φ S).seq 0 = 2

axiom Φ_seq_step (S : GoodSeq) (n : Nat) :
  (Φ S).seq (n+1) > (Φ S).seq n ∧
  (∀ k ≤ n, ¬ (Φ S).seq k ∣ (Φ S).seq (n+1)) ∧
  (∀ m, m > (Φ S).seq n → (∀ k ≤ n, ¬ (Φ S).seq k ∣ m) → (Φ S).seq (n+1) ≤ m)

def isFixedPoint (S : GoodSeq) : Prop := Φ S = S

theorem GoodSeq.ext (S T : GoodSeq) (h : S.seq = T.seq) : S = T := by
  cases S; cases T; congr
