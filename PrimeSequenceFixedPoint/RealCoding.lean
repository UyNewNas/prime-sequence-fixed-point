import PrimeSequenceFixedPoint.SeqFixedPoint

/-!
# RealCoding.lean (M3): Real coding Psi

Dependency: SeqFixedPoint (GoodSeq type).

Independent axiomatic real number system.
-/

/-! ### Real axioms -/

axiom ℝ : Type

namespace ℝ

axiom zero : ℝ
axiom one  : ℝ
axiom add  : ℝ → ℝ → ℝ
axiom mul  : ℝ → ℝ → ℝ
axiom neg  : ℝ → ℝ
axiom sub  : ℝ → ℝ → ℝ
axiom div  : ℝ → ℝ → ℝ
axiom le   : ℝ → ℝ → Prop
axiom lt   : ℝ → ℝ → Prop

noncomputable instance : OfNat ℝ 0 := ⟨zero⟩
noncomputable instance : OfNat ℝ 1 := ⟨one⟩
noncomputable instance : Add ℝ := ⟨add⟩
noncomputable instance : Mul ℝ := ⟨mul⟩
noncomputable instance : Neg ℝ := ⟨neg⟩
noncomputable instance : Sub ℝ := ⟨sub⟩
noncomputable instance : Div ℝ := ⟨div⟩
instance : LE ℝ := ⟨le⟩
instance : LT ℝ := ⟨lt⟩

axiom zero_ne_one : zero ≠ one

axiom add_comm     (a b : ℝ)   : a + b = b + a
axiom add_assoc    (a b c : ℝ) : a + b + c = a + (b + c)
axiom mul_comm     (a b : ℝ)   : a * b = b * a
axiom mul_assoc    (a b c : ℝ) : a * b * c = a * (b * c)
axiom add_zero     (a : ℝ)     : a + 0 = a
axiom zero_add     (a : ℝ)     : 0 + a = a
axiom mul_one      (a : ℝ)     : a * 1 = a
axiom one_mul      (a : ℝ)     : 1 * a = a
axiom mul_add      (a b c : ℝ) : a * (b + c) = a * b + a * c
axiom add_mul      (a b c : ℝ) : (a + b) * c = a * c + b * c
axiom sub_eq_add_neg (a b : ℝ) : a - b = a + (-b)

axiom le_refl         (a : ℝ)     : a ≤ a
axiom le_trans        {a b c : ℝ} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c
axiom le_antisymm     {a b : ℝ} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b
axiom le_total        (a b : ℝ)   : a ≤ b ∨ b ≤ a
axiom add_le_add_left {a b : ℝ} (h : a ≤ b) (c : ℝ) : c + a ≤ c + b

axiom zero_lt_one : zero < one

noncomputable def ofNat (n : Nat) : ℝ :=
  match n with
  | 0 => zero
  | n+1 => add (ofNat n) one

noncomputable instance (n : Nat) : OfNat ℝ n := ⟨ofNat n⟩

noncomputable def powNat (r : ℝ) : Nat → ℝ
  | 0     => 1
  | n+1   => powNat r n * r

noncomputable instance : Pow ℝ Nat := ⟨powNat⟩

theorem powNat_zero (r : ℝ) : r ^ (0 : Nat) = 1 := rfl
theorem powNat_succ (r : ℝ) (n : Nat) : r ^ (n+1 : Nat) = (r ^ n) * r := rfl

end ℝ

open ℝ

axiom ten_pos : (0 : ℝ) < (10 : ℝ)
axiom pow_pos_ax (a : ℝ) (ha : 0 < a) (n : Nat) : 0 < a ^ n

noncomputable def natCast (n : Nat) : ℝ := ofNat n

noncomputable instance : Coe Nat ℝ := ⟨natCast⟩

axiom natCast_nonneg (n : Nat) : (0 : ℝ) ≤ (natCast n : ℝ)

/-! ### Series axioms -/

axiom tsum     : (Nat → ℝ) → ℝ
axiom Summable : (Nat → ℝ) → Prop
axiom tsum_nonneg {f : Nat → ℝ} (hf : ∀ n, 0 ≤ f n) : 0 ≤ tsum f
axiom Summable.of_nonneg_of_le {f g : Nat → ℝ}
  (hf : ∀ n, 0 ≤ f n) (hle : ∀ n, f n ≤ g n) (hg : Summable g) : Summable f
axiom summable_geometric_of_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
  Summable (λ n : Nat => r ^ n)
axiom Summable.const_mul {f : Nat → ℝ} (c : ℝ) (hf : Summable f) :
  Summable (λ n => c * f n)
axiom Summable.tail {f : Nat → ℝ} (hf : Summable f) (n : Nat) : Summable (λ i => f (n + i))
axiom tsum_succ (f : Nat → ℝ) (hf : Summable f) : tsum f = f 0 + tsum (λ n => f (n+1))

/-! ### Psi definition -/

noncomputable def psi_term (S : Nat → Nat) (k : Nat) : ℝ :=
  (natCast (S (k+1) % 10 : Nat) : ℝ) / ((10 : ℝ) ^ ((k+1)^2))

noncomputable def Ψ (S : GoodSeq) : ℝ :=
  tsum (psi_term S.seq)
