import Mathlib.NumberTheory.LSeries.RiemannZeta
import EmergenceMathlib
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The lattice Gaussian and its inverse Mellin reconstruction. -/

noncomputable section

open Complex MeasureTheory Set HurwitzZeta
open scoped Real Topology

namespace RHThroughEmergence.Reconstruction

/-- The positive half of the lattice theta sum. -/
def sampled (a : ℝ) : ℝ := (cosKernel 0 a - 1) / 2

/-- The Mellin transform of the sampled vacuum background is completed zeta at twice the Mellin variable. -/
theorem theta_hasMellin {z : ℂ} (hz : 1 / 2 < z.re) :
    HasMellin (fun a ↦ (sampled a : ℂ)) z (completedRiemannZeta (2*z)) := by
  have h := (hurwitzEvenFEPair (0 : UnitAddCircle)).symm.hasMellin
    (s := z) (show (hurwitzEvenFEPair (0 : UnitAddCircle)).symm.k < z.re from hz)
  constructor
  · simpa only [MellinConvergent, sampled, ofReal_div, ofReal_sub, ofReal_one, ofReal_ofNat,
      smul_eq_mul, WeakFEPair.symm, hurwitzEvenFEPair, Function.comp_apply]
      using h.1.div_const 2
  · simp only [sampled, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_ofNat, mellin_div_const, ← completedCosZeta_zero, completedCosZeta,
      mul_div_cancel_left₀ z (two_ne_zero : (2:ℂ) ≠ 0)]
    exact congrArg (· / 2) h.2

private theorem norm_gamma_le_real {z : ℂ} (hz : 0 < z.re) :
    ‖Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Gamma_eq_integral hz, Real.Gamma_eq_integral hz]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
    norm_cpow_eq_rpow_re_of_pos hx]
  simp

private theorem vertical_zeta_bound {z : ℂ} (hz : 1 < z.re) :
    ‖riemannZeta z‖ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ z.re := by
  rw [zeta_eq_tsum_one_div_nat_cpow hz]
  apply (norm_tsum_le_tsum_norm ((Complex.summable_one_div_nat_cpow.mpr hz).norm)).trans_eq
  apply tsum_congr
  intro n
  rw [norm_div, norm_one, ← Complex.ofReal_natCast,
    norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n) (by linarith : z.re ≠ 0)]

/-- Two applications of the gamma recurrence give integrable decay up a vertical line. -/
private theorem gamma_decay {c : ℝ} (hc : 0 < c) (y : ℝ) :
    ‖Gamma (c + y * I)‖ ≤
      (Real.Gamma (c + 2) / min 1 (c ^ 2)) * (1 + y ^ 2)⁻¹ := by
  let z : ℂ := c + y * I
  have hre : z.re = c := by simp [z]
  have him : z.im = y := by simp [z]
  have h0 : z ≠ 0 := fun h ↦ by simp [h] at hre; linarith
  have h1 : z + 1 ≠ 0 := fun h ↦ by
    have := congrArg Complex.re h
    simp [hre] at this
    linarith
  have hg := norm_gamma_le_real (z := (z + 1) + 1) (by simp [hre]; linarith)
  rw [Gamma_add_one _ h1, Gamma_add_one _ h0, norm_mul, norm_mul] at hg
  have hreal : ((z + 1) + 1).re = c + 2 := by simp [hre]; ring
  rw [hreal] at hg
  have n0 : ‖z‖ ^ 2 = c ^ 2 + y ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; ring
  have n1 : ‖z+1‖ ^ 2 = (c+1)^2 + y^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [hre, him]; ring
  have le_norm : ‖z‖ ≤ ‖z+1‖ := by nlinarith [norm_nonneg (z+1), norm_nonneg z]
  have hb : 0 < min 1 (c ^ 2) := lt_min one_pos (sq_pos_of_pos hc)
  have hmin : min 1 (c^2) * (1+y^2) ≤ ‖z+1‖ * ‖z‖ := by
    calc
      _ ≤ c^2 + y^2 := by
        nlinarith [min_le_right (1:ℝ) (c^2), mul_le_mul_of_nonneg_right
          (min_le_left (1:ℝ) (c^2)) (sq_nonneg y)]
      _ = ‖z‖ * ‖z‖ := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right le_norm (norm_nonneg _)
  change ‖Gamma z‖ ≤ _
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), le_div_iff₀ hb]
  calc
    _ = (min 1 (c^2) * (1+y^2)) * ‖Gamma z‖ := by ring
    _ ≤ (‖z+1‖ * ‖z‖) * ‖Gamma z‖ := mul_le_mul_of_nonneg_right hmin (norm_nonneg _)
    _ ≤ _ := by simpa [mul_assoc] using hg

private theorem completed_on_line {c : ℝ} (hc : 1 / 2 < c) :
    VerticalIntegrable (fun z ↦ completedRiemannZeta (2*z)) c := by
  let P := Real.pi ^ (-c)
  let G := Real.Gamma (c+2) / min 1 (c^2)
  let S := ∑' n : ℕ, 1 / (n : ℝ) ^ (2*c)
  have hc0 : 0 < c := by linarith
  have hS : 0 ≤ S := tsum_nonneg fun n ↦ by positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  apply (integrable_inv_one_add_sq.const_mul (P*G*S)).mono'
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro y
    apply ContinuousAt.comp (f := fun t : ℝ ↦ 2 * ((c : ℂ) + t * I))
      (differentiableAt_completedZeta _ _).continuousAt (by fun_prop)
    all_goals intro h; have := congrArg Complex.re h; simp at this; linarith
  · filter_upwards with y
    let z : ℂ := c + y * I
    have hre : z.re = c := by simp [z]
    have h2 : (2*z).re = 2*c := by simp [hre]
    have hs : 1 < (2*z).re := by rw [h2]; linarith
    change ‖completedRiemannZeta (2*z)‖ ≤ _
    rw [completedZeta_eq_tsum_of_one_lt_re hs, ← zeta_eq_tsum_one_div_nat_cpow hs,
      show 2*z/2 = z by ring, show -(2*z)/2 = -z by ring, norm_mul, norm_mul,
      norm_cpow_eq_rpow_re_of_pos Real.pi_pos, neg_re, hre]
    have hzeta := vertical_zeta_bound hs
    rw [h2] at hzeta
    calc
      _ ≤ P * (G * (1 + y^2)⁻¹) * S := by
        apply mul_le_mul _ hzeta (norm_nonneg _) (mul_nonneg hP _)
        · exact mul_le_mul_of_nonneg_left (gamma_decay hc0 y) hP
        · exact (norm_nonneg _).trans (gamma_decay hc0 y)
      _ = _ := by ring

/-- Inverse Mellin reconstruction with Mellin coordinate z=s/2.
The line Re z=c corresponds to Re s=2c>1 in the completed zeta function. -/
theorem zeta_reconstruction {a c : ℝ} (ha : 0 < a) (hc : 1/2 < c) :
    mellinInv c (fun z ↦ completedRiemannZeta (2*z)) a = (sampled a : ℂ) := by
  have hconv := (theta_hasMellin (z := (c : ℂ)) hc).1
  have hline (y : ℝ) := (theta_hasMellin (z := c + y * I) (by simpa using hc)).2
  have hvertical := completed_on_line hc
  have hcont : ContinuousAt (fun a ↦ (sampled a : ℂ)) a := by
    apply continuous_ofReal.continuousAt.comp
    exact (((continuousOn_cosKernel 0).continuousAt (Ioi_mem_nhds ha)).sub
      continuousAt_const).div_const 2
  have hf : VerticalIntegrable (mellin (fun a ↦ (sampled a : ℂ))) c := by
    unfold VerticalIntegrable at hvertical ⊢
    simpa only [hline] using hvertical
  have he : mellinInv c (mellin (fun a ↦ (sampled a : ℂ))) a = (sampled a : ℂ) := by
    exact RHThroughEmergence.mellinInversion c _ ha hconv hf hcont
  simpa only [mellinInv, hline] using he

/-- Any formula for completed zeta on the open convergence half-plane reconstructs the sampled vacuum background. -/
theorem reconstruction_of_completed_on_right (F : ℂ → ℂ)
    (hF : ∀ s : ℂ, 1 < s.re → F s = completedRiemannZeta s)
    {a c : ℝ} (ha : 0 < a) (hc : 1/2 < c) :
    mellinInv c (fun z ↦ F (2*z)) a = (sampled a : ℂ) := by
  have hline (y : ℝ) : F (2*((c : ℂ) + y*I)) =
      completedRiemannZeta (2*((c : ℂ) + y*I)) := by
    apply hF
    simp
    linarith
  simpa only [mellinInv, hline] using (zeta_reconstruction ha hc)

end RHThroughEmergence.Reconstruction
