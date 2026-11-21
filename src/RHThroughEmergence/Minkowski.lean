import RHThroughEmergence.GaussianLattice

/-! The two reflected scale modes in light-cone coordinates. An integer labels a boost
from rest. Its prime divisors supply the elementary rapidities; in an ordered scan
the von Mangoldt weight gives a discrete impulse at every positive prime power. -/

namespace RHThroughEmergence.Minkowski

noncomputable section

/-- The coordinates are ordered as (exp η, exp (-η)) on the vacuum orbit. -/
def boost (η : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (Real.exp η * v.1, Real.exp (-η) * v.2)

def time (v : ℝ × ℝ) : ℝ := (v.1 + v.2) / 2
def space (v : ℝ × ℝ) : ℝ := (v.1 - v.2) / 2

theorem interval_eq (v : ℝ × ℝ) : time v ^ 2 - space v ^ 2 = v.1 * v.2 := by
  unfold time space
  ring

theorem boost_preserves_interval (η : ℝ) (v : ℝ × ℝ) :
    time (boost η v) ^ 2 - space (boost η v) ^ 2 = time v ^ 2 - space v ^ 2 := by
  rw [interval_eq, interval_eq]
  simp only [boost, Real.exp_neg]
  field_simp

/-- Before normalization, multiplying the growing light-cone coordinate by p
advances both T and X by the same strictly positive amount. -/
theorem prime_null_step {p : ℕ} (hp : p.Prime) (v : ℝ × ℝ) (hv : 0 < v.1) :
    let w : ℝ × ℝ := ((p : ℝ) * v.1, v.2)
    time w - time v = ((p : ℝ) - 1) * v.1 / 2 ∧
      space w - space v = time w - time v ∧ 0 < time w - time v := by
  dsimp [time, space]
  have hp' : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  constructor
  · ring
  constructor
  · ring
  · nlinarith [mul_pos (sub_pos.mpr hp') hv]

def rapidity (n : ℕ) : ℝ := Real.log n / 2

def event (n : ℕ) : ℝ × ℝ := boost (rapidity n) (1, 1)

theorem event_coordinates {n : ℕ} (hn : 0 < n) :
    event n = (Real.sqrt n, (Real.sqrt n)⁻¹) := by
  have h : 0 < (n : ℝ) := by exact_mod_cast hn
  have he : Real.exp (rapidity n) = Real.sqrt n := by
    rw [rapidity, ← Real.log_sqrt h.le, Real.exp_log (Real.sqrt_pos.2 h)]
  simp [event, boost, Real.exp_neg, he]

/-- Rescaling the raw dilation by 1/√n gives the interval-preserving boost. -/
theorem normalized_dilation {n : ℕ} (hn : 0 < n) (v : ℝ × ℝ) :
    boost (rapidity n) v = ((n : ℝ) * v.1 / Real.sqrt n, v.2 / Real.sqrt n) := by
  have h : Real.exp (rapidity n) = Real.sqrt n := by
    simpa [event, boost] using congrArg Prod.fst (event_coordinates hn)
  have hs : 0 < Real.sqrt (n : ℝ) := by positivity
  apply Prod.ext
  · change Real.exp (rapidity n) * v.1 = _
    rw [h, eq_div_iff hs.ne']
    linear_combination v.1 * Real.sq_sqrt (Nat.cast_nonneg n)
  · change Real.exp (-rapidity n) * v.2 = v.2 / Real.sqrt n
    rw [Real.exp_neg, h, div_eq_mul_inv, mul_comm]

theorem event_unit_interval (n : ℕ) : time (event n) ^ 2 - space (event n) ^ 2 = 1 := by
  simpa [event, time, space] using boost_preserves_interval (rapidity n) (1, 1)

theorem rapidity_mul {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    rapidity (n * m) = rapidity n + rapidity m := by
  simp only [rapidity, Nat.cast_mul, Real.log_mul (by positivity : (n : ℝ) ≠ 0)
    (by positivity : (m : ℝ) ≠ 0)]
  ring

theorem event_mul {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    event (n * m) = boost (rapidity m) (event n) := by
  simp [event, boost, rapidity_mul hn hm, Real.exp_add, mul_comm]

theorem prime_advances_time {n p : ℕ} (hn : 0 < n) (hp : p.Prime) :
    time (event n) < time (event (n * p)) := by
  have ht (k : ℕ) : time (event k) = Real.cosh (rapidity k) := by
    simp [time, event, boost, Real.cosh_eq]
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hp' : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hnη : 0 ≤ rapidity n := div_nonneg (Real.log_nonneg hn') (by norm_num)
  have hpη : 0 < rapidity p := div_pos (Real.log_pos hp') (by norm_num)
  rw [ht, ht, rapidity_mul hn hp.pos]
  exact Real.cosh_strictMonoOn hnη (add_nonneg hnη hpη.le) (lt_add_of_pos_right _ hpη)

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

/-- The forward vacuum response of one address, starting at depth log n. -/
def response (n : ℕ) (u : ℝ) : ℝ :=
  if Real.log n ≤ u then 2 * burst n * Real.sinh ((u - Real.log n) / 2) else 0

/-- The left slope at the tick is zero and the right slope is its impulse amplitude. -/
theorem response_slopes (n : ℕ) :
    HasDerivWithinAt (response n) 0 (Set.Iic (Real.log n)) (Real.log n) ∧
    HasDerivWithinAt (response n) (burst n) (Set.Ici (Real.log n)) (Real.log n) := by
  let v := Real.log (n : ℝ)
  have h0 : response n v = 0 := by simp [response, v]
  constructor
  · apply (hasDerivAt_const v (0 : ℝ)).hasDerivWithinAt.congr _ h0
    intro u hu
    rcases (show u ≤ v from hu).lt_or_eq with h | rfl
    · exact if_neg (not_le.mpr h)
    · exact h0
  · have hd : HasDerivAt (fun u : ℝ => (u - v) / 2) (1 / 2) v :=
      ((hasDerivAt_id v).sub_const v).div_const 2
    have hr : HasDerivAt (fun u => 2 * burst n * Real.sinh ((u - v) / 2)) (burst n) v := by
      convert hd.sinh.const_mul (2 * burst n) using 1
      simp
      ring
    exact hr.hasDerivWithinAt.congr (fun u hu => if_pos hu) (if_pos le_rfl)

/-- Each clock contributes once for each of its powers dividing the address. -/
theorem divisor_bursts (n : ℕ) :
    (∑ d ∈ n.divisors, burst d * Real.sqrt d) / 2 = rapidity n := by
  simp only [recover_weight, ArithmeticFunction.vonMangoldt_sum, rapidity]

/-- These are the coefficients of the prime-power series for the negative logarithmic derivative of zeta. -/
theorem burst_LSeries {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => ((burst n * Real.sqrt n : ℝ) : ℂ)) s =
      -deriv riemannZeta s / riemannZeta s := by
  simpa only [recover_weight] using GaussianLattice.bosons_force hs

/-- Light-cone coordinates of the reflected and original scale modes, in that
order. Multiplication by √x normalizes each magnitude by the vacuum magnitude. -/
def reflectedPair (ρ : ℂ) (x : ℝ) : ℝ × ℝ :=
  (Real.sqrt x * ‖(x : ℂ) ^ (-(1 - ρ))‖, Real.sqrt x * ‖(x : ℂ) ^ (-ρ)‖)

theorem reflectedPair_eq_boost (ρ : ℂ) {x : ℝ} (hx : 0 < x) :
    reflectedPair ρ x = boost ((ρ.re - 1 / 2) * Real.log x) (1, 1) := by
  have hnorm (w : ℂ) : Real.sqrt x * ‖(x : ℂ) ^ w‖ =
      Real.exp ((1 / 2 + w.re) * Real.log x) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Real.sqrt_eq_rpow,
      Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx, ← Real.exp_add]
    congr 1
    ring
  apply Prod.ext <;>
    simp only [reflectedPair, boost, hnorm, Complex.neg_re, Complex.sub_re, Complex.one_re,
      mul_one] <;> congr 1 <;> ring

theorem reflectedPair_unit_interval (ρ : ℂ) {x : ℝ} (hx : 0 < x) :
    time (reflectedPair ρ x) ^ 2 - space (reflectedPair ρ x) ^ 2 = 1 := by
  rw [reflectedPair_eq_boost ρ hx, boost_preserves_interval, interval_eq]
  norm_num

/-- The first doubling is enough to distinguish the rest point on the unit hyperbola. -/
theorem rest_at_two_iff (ρ : ℂ) : space (reflectedPair ρ 2) = 0 ↔ ρ.re = 1 / 2 := by
  rw [reflectedPair_eq_boost ρ two_pos]
  let η := (ρ.re - 1 / 2) * Real.log 2
  change (Real.exp η * 1 - Real.exp (-η) * 1) / 2 = 0 ↔ _
  simp only [mul_one]
  constructor
  · intro h
    have he : η = -η := Real.exp_injective (by linarith)
    have hz : (ρ.re - 1 / 2) * Real.log 2 = 0 := by change η = 0; linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (Real.log_pos (by norm_num)).ne')
  · intro h
    simp [η, h]

/-- RH expressed as rest of the normalized reflected pair for every nontrivial
zeta zero at scale two, using Mathlib's exclusions for trivial zeros and the pole. -/
theorem riemannHypothesis_iff_rest_at_two :
    RiemannHypothesis ↔ ∀ ρ : ℂ, riemannZeta ρ = 0 →
      (¬∃ n : ℕ, ρ = -2 * (n + 1)) → ρ ≠ 1 → space (reflectedPair ρ 2) = 0 := by
  constructor
  · intro hRH ρ hz hn h1
    exact (rest_at_two_iff ρ).mpr (hRH ρ hz hn h1)
  · intro h ρ hz hn h1
    exact (rest_at_two_iff ρ).mp (h ρ hz hn h1)

end

end RHThroughEmergence.Minkowski
