/-
# Common.lean (M1a): Divisibility and basic properties

No dependencies, uses only Lean built-in `Nat`.
Shared by M2 (sequence structure & Phi) and M4 (core sieve lemma).
-/

open Function
-- StrictMono defined below (not using Function.StrictMono)

/-- Strictly monotone increasing: if `a < b` then `f a < f b` -/
def StrictMono (f : Nat → Nat) : Prop :=
  ∀ ⦃a b : Nat⦄, a < b → f a < f b

/-! ## 1. Basic divisibility lemmas -/

section DivBase

variable {a b c d m n : Nat}

theorem dvd_refl (a : Nat) : a ∣ a := Nat.dvd_refl a

theorem dvd_trans (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := Nat.dvd_trans h₁ h₂

theorem dvd_antisymm (h₁ : a ∣ b) (h₂ : b ∣ a) : a = b := Nat.dvd_antisymm h₁ h₂

theorem dvd_mul_right (a b : Nat) : a ∣ a * b := Nat.dvd_mul_right a b

theorem dvd_mul_left (a b : Nat) : a ∣ b * a := Nat.dvd_mul_left a b

theorem dvd_add (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c := Nat.dvd_add h₁ h₂

theorem one_dvd (a : Nat) : 1 ∣ a := Nat.one_dvd a

theorem dvd_zero (a : Nat) : a ∣ 0 := Nat.dvd_zero a

theorem le_of_dvd (hb : 0 < b) (h : a ∣ b) : a ≤ b := Nat.le_of_dvd hb h

theorem le_of_dvd_ne_zero (h : a ∣ b) (hb : b ≠ 0) : a ≤ b :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hb) h

theorem dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ (b - c) := by
  rcases h₁ with ⟨k, hk⟩
  rcases h₂ with ⟨l, hl⟩
  by_cases hle : l ≤ k
  · rw [hk, hl]
    rw [← Nat.mul_sub_left_distrib a k l]
    exact Nat.dvd_mul_right a (k - l)
  · have hle' : k < l := Nat.lt_of_not_ge hle
    by_cases ha0 : a = 0
    · subst ha0; simp [hk, hl]
    · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha0
      have h_lt : a * k < a * l := by
        simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right hle' ha_pos
      have hsub : (a * k) - (a * l) = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt h_lt)
      rw [hk, hl, hsub]
      exact Nat.dvd_zero a

theorem dvd_of_dvd_add_left (h₁ : a ∣ b) (h₂ : a ∣ b + c) : a ∣ c := by
  rcases h₁ with ⟨x, hx⟩
  rcases h₂ with ⟨y, hy⟩
  rw [hx] at hy
  by_cases ha0 : a = 0
  · subst ha0; simp at hy; rw [hy]; exact Nat.dvd_zero 0
  · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha0
    by_cases hle : x ≤ y
    · have hc : c = a * (y - x) :=
        calc
          c = (a*x + c) - a*x := by rw [Nat.add_sub_cancel_left]
          _ = a*y - a*x := by rw [← hy]
          _ = a * (y - x) := by rw [← Nat.mul_sub_left_distrib a y x]
      rw [hc]
      exact Nat.dvd_mul_right a (y - x)
    · have h_lt : y < x := Nat.lt_of_not_ge hle
      have h_lt_mul : a*y < a*x := by
        simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right h_lt ha_pos
      have h_le_add : a*x ≤ a*x + c := Nat.le_add_right (a*x) c
      rw [hy] at h_le_add
      exact absurd h_le_add (Nat.not_le_of_lt h_lt_mul)

theorem dvd_of_dvd_add_right (h₁ : a ∣ c) (h₂ : a ∣ b + c) : a ∣ b := by
  rw [Nat.add_comm b c] at h₂
  exact dvd_of_dvd_add_left h₁ h₂

end DivBase

/-! ## 2. Supplementary divisibility lemmas -/

section DivSupplement

variable {a b c d m n : Nat}

theorem not_dvd_of_lt (ha : 0 < a) (hlt : a < b) : ¬ b ∣ a := by
  intro hdiv
  have hle := Nat.le_of_dvd ha hdiv
  exact Nat.not_lt.mpr hle hlt

theorem not_dvd_of_lt' (hdiv : a ∣ b) (hb : 0 < b) (hlt : b < a) : False := by
  have hle := Nat.le_of_dvd hb hdiv
  exact Nat.not_lt.mpr hle hlt

theorem not_dvd_add_of_not_dvd_left (hnot : ¬ a ∣ b) (hc : a ∣ c) : ¬ a ∣ (b + c) := by
  intro hsum
  exact hnot (dvd_of_dvd_add_right hc hsum)

theorem not_dvd_add_of_not_dvd_right (hnot : ¬ a ∣ c) (hb : a ∣ b) : ¬ a ∣ (b + c) := by
  intro hsum
  exact hnot (dvd_of_dvd_add_left hb hsum)

theorem dvd_mul_of_dvd_left (h : a ∣ b) (c : Nat) : a ∣ b * c := by
  rcases h with ⟨k, hk⟩
  rw [hk, Nat.mul_assoc]
  exact Nat.dvd_mul_right a (k * c)

theorem dvd_mul_of_dvd_right (h : a ∣ c) (b : Nat) : a ∣ b * c := by
  rw [Nat.mul_comm b c]
  exact dvd_mul_of_dvd_left h b

theorem lt_of_dvd_ne (hdvd : a ∣ m) (hne : a ≠ m) (hm : m ≠ 0) : a < m := by
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd
  exact Nat.lt_of_le_of_ne hle hne

theorem not_dvd_of_dvd_add_not_dvd_right (hsum : a ∣ b + c) (hnotc : ¬ a ∣ c) : ¬ a ∣ b := by
  intro hb
  exact hnotc (dvd_of_dvd_add_left hb hsum)

theorem not_dvd_of_dvd_add_not_dvd_left (hsum : a ∣ b + c) (hnotb : ¬ a ∣ b) : ¬ a ∣ c := by
  intro hc
  exact hnotb (dvd_of_dvd_add_right hc hsum)

end DivSupplement

/-! ## 3. Indivisible predicate -/

def Indivisible (s : Nat → Nat) : Prop :=
  ∀ i j, i < j → ¬ s i ∣ s j

namespace Indivisible

variable {s t : Nat → Nat}

theorem not_dvd (h : Indivisible s) {i j : Nat} (hij : i < j) : ¬ s i ∣ s j := h i j hij

theorem comp_strictMono (h : Indivisible s) {f : Nat → Nat} (hf : StrictMono f) : Indivisible (s ∘ f) := by
  intro i j hij
  have hfij : f i < f j := hf hij
  exact h (f i) (f j) hfij

end Indivisible

/-- StrictMono sequence order equivalence: `i < j` iff `s i < s j` -/
theorem strictMono_lt_iff {s : Nat → Nat} (hmono : StrictMono s) {i j : Nat} : i < j ↔ s i < s j := by
  constructor
  · exact fun hlt => hmono hlt
  · intro hslt
    by_cases hij : i < j
    · exact hij
    · have hji : j ≤ i := Nat.le_of_not_gt hij
      rcases Nat.lt_or_eq_of_le hji with (hlt | heq)
      · have hsji : s j < s i := hmono hlt
        exact (Nat.lt_asymm hsji hslt).elim
      · subst heq; exact (Nat.lt_irrefl _ hslt).elim
