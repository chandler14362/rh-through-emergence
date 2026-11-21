import RHThroughEmergence.PrimeBursts
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Data.Nat.Factorization.PrimePow

/-! The Gaussian Fourier test and the absolutely convergent prime term in Weil's formula. -/

namespace RHThroughEmergence.WeilHeat

open Complex MeasureTheory

noncomputable section

def heatKernel (τ u : ℝ) : ℝ := Real.exp (-u ^ 2 / (4 * τ)) / Real.sqrt (4 * Real.pi * τ)

/-- Angular-frequency Fourier inversion with the normalization used in the explicit formula. -/
theorem gaussian_test_transform {τ : ℝ} (hτ : 0 < τ) (u : ℝ) :
    (∫ r : ℝ, Complex.exp (Complex.I * u * r) * Complex.exp (-(τ : ℂ) * r ^ 2)) /
      (2 * Real.pi) = (heatKernel τ u : ℂ) := by
  rw [fourierIntegral_gaussian (b := (τ : ℂ)) hτ]
  have hroot : ((Real.pi : ℂ) / τ) ^ (1 / 2 : ℂ) = (Real.sqrt (Real.pi / τ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (div_nonneg Real.pi_pos.le hτ.le)]
    push_cast
    rfl
  rw [hroot]
  have hnorm : Real.sqrt (Real.pi / τ) * Real.sqrt (4 * Real.pi * τ) = 2 * Real.pi := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show Real.pi / τ * (4 * Real.pi * τ) = (2 * Real.pi) ^ 2 by field_simp; ring,
      Real.sqrt_sq (by positivity)]
  have hc := congrArg (fun v : ℝ ↦ (v : ℂ)) hnorm
  push_cast at hc
  rw [heatKernel, Complex.ofReal_div, Complex.ofReal_exp]
  push_cast
  apply (div_eq_div_iff (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (by exact_mod_cast
    (Real.sqrt_pos.mpr (by positivity : 0 < 4 * Real.pi * τ)).ne')).mpr
  linear_combination Complex.exp (-(u : ℂ) ^ 2 / (4 * τ)) * hc

/-- Completing the square gives a summable majorant even after the von Mangoldt weighting. -/
theorem prime_heat_summable {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ ↦ Minkowski.burst n * heatKernel τ (Real.log n)) := by
  have hmaj := (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left (Real.exp (9 * τ))
  have hsum : Summable (fun n : ℕ ↦ Minkowski.burst n * Real.exp (-(Real.log n)^2 / (4 * τ))) := by
    apply Summable.of_nonneg_of_le (fun n ↦ by
      exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
        (Real.exp_pos _).le) _ hmaj
    intro n
    rcases n with _ | n
    · simp [Minkowski.burst]
    let x : ℝ := (↑(n + 1 : ℕ) : ℝ)
    have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ n + 1 by omega)
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hb : Minkowski.burst (n + 1) ≤ x := by
      unfold Minkowski.burst
      have hs : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx
      change ArithmeticFunction.vonMangoldt (n + 1) / Real.sqrt x ≤ x
      refine (div_le_self ArithmeticFunction.vonMangoldt_nonneg hs).trans ?_
      exact ArithmeticFunction.vonMangoldt_le_log.trans (by
        change Real.log x ≤ x
        linarith [Real.log_le_sub_one_of_pos hx0])
    have hexp : Real.exp (-(Real.log x)^2 / (4 * τ)) ≤ Real.exp (9 * τ) / x ^ 3 := by
      have he : -(Real.log x)^2 / (4 * τ) ≤ 9 * τ - 3 * Real.log x := by
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith [sq_nonneg (Real.log x - 6 * τ)]
      convert Real.exp_le_exp.mpr he using 1
      rw [Real.exp_sub, show 3 * Real.log x = Real.log (x^3) by simp,
        Real.exp_log (by positivity : 0 < x ^ 3)]
    change Minkowski.burst (n + 1) * Real.exp (-(Real.log (↑(n+1 : ℕ)))^2 / (4*τ)) ≤
      Real.exp (9*τ) * (1 / (↑(n+1 : ℕ) : ℝ)^2)
    change Minkowski.burst (n + 1) * Real.exp (-(Real.log x)^2 / (4*τ)) ≤ Real.exp (9*τ) * (1 / x^2)
    calc
      _ ≤ x * (Real.exp (9 * τ) / x^3) :=
        mul_le_mul hb hexp (Real.exp_pos _).le hx0.le
      _ = _ := by field_simp
  simpa only [heatKernel, div_eq_mul_inv, mul_assoc] using
    hsum.mul_right (Real.sqrt (4 * Real.pi * τ))⁻¹

/-- The integer series is the unordered sum over the prime clocks and all their positive ticks. -/
theorem prime_heat_reindex {τ : ℝ} (hτ : 0 < τ) :
    HasSum (fun pk : Nat.Primes × ℕ ↦
      Real.log pk.1 / Real.sqrt ((pk.1 : ℝ) ^ (pk.2 + 1)) *
        heatKernel τ ((pk.2 + 1) * Real.log pk.1))
      (∑' n : ℕ, Minkowski.burst n * heatKernel τ (Real.log n)) := by
  let f := fun n : ℕ ↦ Minkowski.burst n * heatKernel τ (Real.log n)
  have hs : Function.support f ⊆ {n | IsPrimePow n} := by
    intro n hn
    by_contra h
    exact hn (by simp [f, Minkowski.burst_zero_iff n |>.mpr h])
  have h := Nat.Primes.prodNatEquiv.hasSum_iff.mpr
    ((hasSum_subtype_iff_of_support_subset hs).mpr (prime_heat_summable hτ).hasSum)
  convert h using 1
  funext ⟨p,k⟩
  change _ = Minkowski.burst ((p : ℕ) ^ (k+1)) * heatKernel τ (Real.log ↑((p : ℕ) ^ (k+1)))
  rw [Minkowski.burst_prime_power p.prop (Nat.succ_pos k), Minkowski.prime_power_depth]
  push_cast
  rfl

/-- The entire Gaussian test integrates to the same kernel on every shifted vertical line.
Taking a=c-1/2 and u=log n evaluates one Dirichlet mode of the prime term. -/
theorem shifted_gaussian_test {τ : ℝ} (hτ : 0 < τ) (a u : ℝ) :
    (∫ r : ℝ, Complex.exp ((τ : ℂ) * (a + r * I)^2 - (a + r * I) * u)) /
      (2 * Real.pi) = (heatKernel τ u : ℂ) := by
  let c := τ * a^2 - a*u
  let w := 2 * τ * a - u
  have hsplit (r : ℝ) :
      Complex.exp ((τ : ℂ) * (a + r * I)^2 - (a + r * I) * u) =
      (Real.exp c : ℂ) * (Complex.exp (I * w * r) * Complex.exp (-(τ : ℂ) * r^2)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    dsimp [c, w]
    push_cast
    ring_nf
    simp [I_sq]
    ring
  simp_rw [hsplit]
  rw [integral_const_mul, mul_div_assoc, gaussian_test_transform hτ, ← Complex.ofReal_mul]
  apply congrArg ((↑) : ℝ → ℂ)
  unfold heatKernel
  rw [← mul_div_assoc, ← Real.exp_add]
  congr 2
  dsimp [c, w]
  field_simp
  ring

/-- The Gaussian test on the line Re(s)=c in spectral coordinates. -/
def verticalWeight (τ c r : ℝ) : ℂ := Complex.exp ((τ : ℂ) * (c - 1/2 + r * I)^2)

private abbrev primeCoefficient (n : ℕ) : ℂ := ArithmeticFunction.vonMangoldt n

private theorem term_exp {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    LSeries.term primeCoefficient s n =
      primeCoefficient n * Complex.exp (-s * (Real.log n : ℂ)) := by
  rw [LSeries.term_def₀ (by simp [primeCoefficient]),
    Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)]
  rw [show Complex.log (n : ℂ) = (Real.log n : ℂ) from
    (Complex.ofReal_log (Nat.cast_nonneg n)).symm, mul_comm _ (-s)]

private theorem single_prime_integral {τ : ℝ} (hτ : 0 < τ) (c : ℝ) (n : ℕ) :
    (∫ r : ℝ, verticalWeight τ c r * LSeries.term primeCoefficient (c + r*I) n) / (2 * Real.pi) =
      ((Minkowski.burst n * heatKernel τ (Real.log n) : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Minkowski.burst]
  have hx : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hcoef : (Minkowski.burst n : ℂ) = primeCoefficient n *
      Complex.exp (-(Real.log n : ℂ)/2) := by
    have he : Real.exp (-(Real.log n)/2) = (Real.sqrt n)⁻¹ := by
      rw [neg_div, Real.exp_neg, ← Real.log_sqrt hx.le, Real.exp_log (Real.sqrt_pos.mpr hx)]
    rw [show -(Real.log n : ℂ)/2 = ((-(Real.log n)/2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_exp, he]
    simp [Minkowski.burst, primeCoefficient, div_eq_mul_inv]
  have hsplit (r : ℝ) :
      verticalWeight τ c r * LSeries.term primeCoefficient (c + r*I) n =
      (Minkowski.burst n : ℂ) * Complex.exp ((τ : ℂ) *
        (↑(c - 1/2 : ℝ) + r*I)^2 - (↑(c-1/2 : ℝ) + r*I) * (Real.log n : ℂ)) := by
    rw [term_exp hn, hcoef]
    unfold verticalWeight
    rw [mul_left_comm, mul_assoc (primeCoefficient n), ← Complex.exp_add, ← Complex.exp_add]
    push_cast
    congr 2
    ring
  simp_rw [hsplit]
  rw [integral_const_mul, mul_div_assoc, shifted_gaussian_test hτ, Complex.ofReal_mul]

/-- On every line c>1 the integral of -ζ'/ζ against the Gaussian gives precisely the
convergent prime term (before the factor of two from reflection). -/
theorem prime_heat_integral {τ c : ℝ} (hτ : 0 < τ) (hc : 1 < c) :
    (∫ r : ℝ, verticalWeight τ c r * (-deriv riemannZeta (c + r*I) / riemannZeta (c + r*I))) /
      (2 * Real.pi) = ∑' n : ℕ, ((Minkowski.burst n * heatKernel τ (Real.log n) : ℝ) : ℂ) := by
  let F := fun (n : ℕ) (r : ℝ) ↦ verticalWeight τ c r * LSeries.term primeCoefficient (c + r*I) n
  let G := fun r : ℝ ↦ Real.exp (τ * (c-1/2)^2) * Real.exp (-τ * r^2)
  have hG : Integrable G := (integrable_exp_neg_mul_sq hτ).const_mul _
  have hnrm (n : ℕ) (r : ℝ) : ‖F n r‖ = G r * ‖LSeries.term primeCoefficient c n‖ := by
    simp only [F, norm_mul, verticalWeight, Complex.norm_exp, LSeries.norm_term_eq, Complex.add_re,
      Complex.mul_I_re, Complex.ofReal_im, Complex.ofReal_re, neg_zero, add_zero]
    congr 1
    rw [show G r = Real.exp (τ * (c-1/2)^2 + -τ * r^2) by rw [Real.exp_add]]
    congr 1
    simp [pow_two, Complex.mul_re, Complex.sub_re, Complex.mul_im, Complex.sub_im]
    ring
  have hint (n : ℕ) : Integrable (F n) := by
    have hcont : Continuous (F n) := by
      rcases eq_or_ne n 0 with rfl | hn
      · simpa [F] using (continuous_const : Continuous fun _ : ℝ ↦ (0 : ℂ))
      · simp only [F, term_exp hn, verticalWeight]
        fun_prop
    apply (integrable_norm_iff hcont.aestronglyMeasurable).mp
    simpa only [hnrm] using hG.mul_const ‖LSeries.term primeCoefficient c n‖
  have hsum : Summable fun n ↦ ∫ r, ‖F n r‖ := by
    simp_rw [hnrm, integral_mul_const]
    exact (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (c : ℂ)) hc).norm.mul_left _
  have hseries (r : ℝ) : verticalWeight τ c r * (-deriv riemannZeta (c + r*I) / riemannZeta (c + r*I)) =
      ∑' n : ℕ, F n r := by
    rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hc : 1 < ((c : ℂ) + r*I).re)]
    simp only [F, LSeries, tsum_mul_left]
  simp_rw [hseries]
  rw [← integral_tsum_of_summable_integral_norm hint hsum, div_eq_mul_inv, ← tsum_mul_right]
  exact tsum_congr fun n ↦ by simpa only [F, ← div_eq_mul_inv] using single_prime_integral hτ c n

end

end RHThroughEmergence.WeilHeat
