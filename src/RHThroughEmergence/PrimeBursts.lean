import Mathlib.NumberTheory.LSeries.Dirichlet

namespace RHThroughEmergence.Minkowski

noncomputable section

/-- The impulse amplitude at log depth log n in the normalized prime sum. -/
def burst (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n / Real.sqrt n

theorem burst_prime_power {p j : ℕ} (hp : p.Prime) (hj : 0 < j) :
    burst (p ^ j) = Real.log p / Real.sqrt ((p : ℝ) ^ j) := by
  rw [burst, ArithmeticFunction.vonMangoldt_apply_pow hj.ne',
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow]

theorem burst_pos_iff (n : ℕ) : 0 < burst n ↔ IsPrimePow n := by
  rcases n with _ | n
  · simp [burst, not_isPrimePow_zero]
  · rw [burst, div_pos_iff_of_pos_right (by positivity), ArithmeticFunction.vonMangoldt_pos_iff]

theorem burst_zero_iff (n : ℕ) : burst n = 0 ↔ ¬IsPrimePow n := by
  constructor
  · intro h hn
    exact (ne_of_gt ((burst_pos_iff n).mpr hn)) h
  · intro hn
    simp [burst, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]

theorem recover_weight (n : ℕ) :
    burst n * Real.sqrt n = ArithmeticFunction.vonMangoldt n := by
  rcases n with _ | n
  · simp [burst]
  · exact div_mul_cancel₀ _ (by positivity)

/-- A prime clock repeats at equally spaced log depths. -/
theorem prime_power_depth (p j : ℕ) : Real.log ((p ^ j : ℕ) : ℝ) = j * Real.log p := by
  rw [Nat.cast_pow, Real.log_pow]

end

end RHThroughEmergence.Minkowski
