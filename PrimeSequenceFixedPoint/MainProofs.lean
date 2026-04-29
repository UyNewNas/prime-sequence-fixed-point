import PrimeSequenceFixedPoint.Common
import PrimeSequenceFixedPoint.PrimeDef
import PrimeSequenceFixedPoint.SeqFixedPoint
import PrimeSequenceFixedPoint.RealCoding
import PrimeSequenceFixedPoint.PrimeSieve

/-!
# MainProofs.lean (M5): Integration proofs (Conjectures A, B, C)

Dependencies: SeqFixedPoint + RealCoding + PrimeSieve
-/

open Prime

noncomputable def primeGoodSeq : GoodSeq :=
  { seq         := primeSeq
    seq_pos     := primeSeq_pos
    strictMono  := primeSeq_strictMono
    indivisible := primeSeq_indivisible
  }

noncomputable def Liouville_Erdos_constant : ℝ := Ψ primeGoodSeq

/-! ## Core lemma: Phi outputs primeSeq pointwise -/

theorem Φ_all_eq_primeSeq (S : GoodSeq) : ∀ n m, m ≤ n → (Φ S).seq m = primeSeq m := by
  intro n
  induction n with
  | zero =>
      intro m hm
      have hm0 : m = 0 := by omega
      rw [hm0, Φ_seq_zero S, primeSeq_zero]
  | succ n ih =>
      intro m hm
      rcases Nat.lt_or_eq_of_le hm with (hlt | heq)
      · exact ih m (Nat.le_of_lt_succ hlt)
      · rw [heq]
        have ha_step := Φ_seq_step S n
        have hp_step := primeSeq_step n
        rcases ha_step with ⟨ha_gt, ha_not_div, ha_min⟩
        rcases hp_step with ⟨hp_gt, hp_not_div, hp_min⟩
        have hseq_n_eq : (Φ S).seq n = primeSeq n := ih n (Nat.le_refl n)
        have ha_gt' : (Φ S).seq (n+1) > primeSeq n := by
          rw [← hseq_n_eq]; exact ha_gt
        have ha_min' : ∀ m', m' > primeSeq n → (∀ k ≤ n, ¬ primeSeq k ∣ m') → (Φ S).seq (n+1) ≤ m' := by
          intro m' hm'_gt hm'_not_div
          apply ha_min m'
          · rw [hseq_n_eq]; exact hm'_gt
          · intro k hk; rw [ih k hk]; exact hm'_not_div k hk
        have hp_min' : ∀ m', m' > primeSeq n → (∀ k ≤ n, ¬ (Φ S).seq k ∣ m') → primeSeq (n+1) ≤ m' := by
          intro m' hm'_gt hm'_not_div
          apply hp_min m' hm'_gt
          intro k hk; rw [← ih k hk]; exact hm'_not_div k hk
        have hp_le_a : primeSeq (n+1) ≤ (Φ S).seq (n+1) :=
          hp_min' ((Φ S).seq (n+1)) ha_gt' ha_not_div
        have ha_le_p : (Φ S).seq (n+1) ≤ primeSeq (n+1) :=
          ha_min' (primeSeq (n+1)) hp_gt hp_not_div
        exact Nat.le_antisymm ha_le_p hp_le_a

theorem Φ_seq_eq_primeSeq (S : GoodSeq) (n : Nat) : (Φ S).seq n = primeSeq n :=
  Φ_all_eq_primeSeq S n n (Nat.le_refl n)

/-! ## Phi equals primeGoodSeq -/

theorem Φ_eq_primeGoodSeq (S : GoodSeq) : Φ S = primeGoodSeq := by
  apply GoodSeq.ext
  ext n
  calc
    (Φ S).seq n = primeSeq n := Φ_seq_eq_primeSeq S n
    _ = primeGoodSeq.seq n := rfl

/-!
## Conjecture A: unique fixed point
-/

theorem primeGoodSeq_is_fixedPoint : isFixedPoint primeGoodSeq :=
  Φ_eq_primeGoodSeq primeGoodSeq

theorem fixed_point_is_primeGoodSeq (S : GoodSeq) (h : isFixedPoint S) : S = primeGoodSeq :=
  calc
    S = Φ S := h.symm
    _ = primeGoodSeq := Φ_eq_primeGoodSeq S

theorem conjecture_A : ∃ (S : GoodSeq), isFixedPoint S ∧ (∀ (T : GoodSeq), isFixedPoint T → T = S) :=
  ⟨primeGoodSeq, primeGoodSeq_is_fixedPoint, λ T hFix => fixed_point_is_primeGoodSeq T hFix⟩

/-!
## Conjecture B: self-referential constant
-/

theorem L_eq : Liouville_Erdos_constant = Ψ primeGoodSeq := rfl

theorem conjecture_B : ∃ (x : ℝ), (∃ (S : GoodSeq), Ψ S = x ∧ isFixedPoint S) ∧
  (∀ (y : ℝ), (∃ (S : GoodSeq), Ψ S = y ∧ isFixedPoint S) → y = x) :=
  ⟨Liouville_Erdos_constant,
    ⟨primeGoodSeq, rfl, primeGoodSeq_is_fixedPoint⟩,
    λ y ⟨S, hΨ, hFix⟩ => by
      have hS : S = primeGoodSeq := fixed_point_is_primeGoodSeq S hFix
      subst hS; rw [L_eq, hΨ]⟩

/-!
## Conjecture C: strong self-reference
-/

theorem conjecture_C : ∃ (x : ℝ), (∃ (S : GoodSeq), Ψ S = x ∧ Φ S = S) ∧
  (∀ (y : ℝ), (∃ (S : GoodSeq), Ψ S = y ∧ Φ S = S) → y = x) :=
  ⟨Liouville_Erdos_constant,
    ⟨primeGoodSeq, rfl, Φ_eq_primeGoodSeq primeGoodSeq⟩,
    λ y ⟨S, hΨ, hΦ⟩ => by
      have hFix : isFixedPoint S := hΦ
      have hS : S = primeGoodSeq := fixed_point_is_primeGoodSeq S hFix
      subst hS; rw [L_eq, hΨ]⟩
