import PairedZeros
import GaussianContour

/-! Summing the single-pole contour identity with the xi divisor's analytic multiplicities. -/

noncomputable section
open Complex MeasureTheory Filter Set
open scoped Topology

namespace RHThroughEmergence.GaussianTrace
open GaussianContour ZeroReconstruction

private def term (z ρ : ℂ) := 1/(z-ρ) + 1/ρ
def pairedTerm (z ρ : ℂ) := 1/(z-ρ) + 1/(z-(1-ρ))

private theorem term_sub (z ρ : ℂ) : term z ρ - term (1-z) ρ = pairedTerm z ρ := by
  have h : 1-z-ρ = -(z-(1-ρ)) := by ring
  unfold term pairedTerm
  rw [h, div_neg]
  ring

private theorem log_reflect (z : ℂ) : logDeriv riemannXi (1-z) = -logDeriv riemannXi z := by
  have d := (differentiable_riemannXi (1-z)).hasDerivAt.comp z ((hasDerivAt_id z).const_sub 1)
  have d' : HasDerivAt riemannXi (deriv riemannXi (1-z) * (-1)) z := by
    simpa [Function.comp_def, riemannXi_one_sub] using d
  simp only [logDeriv_apply, riemannXi_one_sub, d'.deriv, mul_neg_one, neg_div, neg_neg]

private theorem zero_strip (i : XiIndex) : 0 < (zeroAt i).re ∧ (zeroAt i).re < 1 := by
  obtain ⟨h,h',_⟩ := xi_zero_iff.mp (zeroAt_is_zero i)
  exact ⟨h,h'⟩

theorem hasSum_paired_logDeriv (t : ℝ) :
    HasSum (fun i : XiIndex ↦ pairedTerm (line 2 t) (zeroAt i)) (2*logDeriv riemannXi (line 2 t)) := by
  let z := line 2 t
  have hr : z.re = 2 := by simp [z,line]
  have hl : (1-z).re = -1 := by norm_num [hr]
  have h₁ (i : XiIndex) : z ≠ zeroAt i := fun h ↦ by have := (zero_strip i).2; rw [← h,hr] at this; linarith
  have h₂ (i : XiIndex) : 1-z ≠ zeroAt i := fun h ↦ by have := (zero_strip i).1; rw [← h,hl] at this; linarith
  obtain ⟨p,hdeg,hfac⟩ := riemannXi_hadamard_factorization_no_monomial
  have hconst (w : ℂ) : p.derivative.eval w = p.coeff 1 := by
    conv_lhs => rw [Polynomial.eq_X_add_C_of_degree_le_one hdeg]
    simp
  have hdiff := (summable_riemannXi_logDerivTerms_divisorZeroIndex₀ h₁).hasSum.sub
    (summable_riemannXi_logDerivTerms_divisorZeroIndex₀ h₂).hasSum
  have hR := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac h₁
  have hL := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac h₂
  rw [hconst] at hR hL
  rw [log_reflect] at hL
  convert! hdiff using 1
  · funext i; exact (term_sub z (zeroAt i)).symm
  · linear_combination hR - hL

private theorem bound_term (z ρ : ℂ) (hd : 1 ≤ ‖z-ρ‖) (hρ : ρ ≠ 0) :
    ‖term z ρ‖ ≤ ‖z‖*(1+‖z‖)*(‖ρ‖⁻¹^2) := by
  have hd0 : z-ρ ≠ 0 := norm_pos_iff.mp (by linarith)
  have hr := norm_sub_le z (z-ρ)
  rw [sub_sub_cancel] at hr
  have hcomp : ‖ρ‖ ≤ (1+‖z‖)*‖z-ρ‖ := by nlinarith [mul_le_mul_of_nonneg_left hd (norm_nonneg z)]
  rw [show term z ρ = z/((z-ρ)*ρ) by unfold term; field_simp; ring, norm_div,norm_mul]
  have hr0 := norm_pos_iff.mpr hρ
  rw [inv_pow, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hcomp (mul_nonneg (norm_nonneg z) hr0.le)]

private theorem bound_paired (t : ℝ) (i : XiIndex) :
    ‖pairedTerm (line 2 t) (zeroAt i)‖ ≤ 40*(1+t^2)*(‖zeroAt i‖⁻¹^2) := by
  let z := line 2 t
  let ρ := zeroAt i
  have hr : z.re = 2 := by simp [z,line]
  have hz : ‖z‖ ≤ 2+|t| := by simpa [z,line, norm_mul] using norm_add_le (2 : ℂ) ((t:ℂ)*I)
  have hz' : ‖1-z‖ ≤ 3+|t| := (norm_sub_le _ _).trans (by simp; linarith)
  have h₁ := abs_re_le_norm (z-ρ)
  have h₂ := abs_re_le_norm (1-z-ρ)
  have hpos := zero_strip i
  have hrho : 0 < ρ.re ∧ ρ.re < 1 := hpos
  simp [hr] at h₁ h₂
  have hb (w : ℂ) (hw : ‖w‖ ≤ 3+|t|) (hd : 1 ≤ ‖w-ρ‖) :
      ‖term w ρ‖ ≤ (20*(1+t^2))*(‖ρ‖⁻¹^2) := by
    apply (bound_term w ρ hd i.property).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    calc
      _ ≤ (3+|t|)*(1+(3+|t|)) := by gcongr
      _ ≤ _ := by nlinarith [sq_abs t, sq_nonneg (|t|-1)]
  rw [← term_sub]
  apply (norm_sub_le _ _).trans
  have a := hb z (by linarith) (by linarith [le_abs_self (2-ρ.re)])
  have b := hb (1-z) hz' (by linarith [neg_le_abs (1-2-ρ.re)])
  linarith

private theorem integral_pair {τ : ℝ} (hτ : 0 < τ) (p : ℂ) (hp : -1 < p.re ∧ p.re < 2) :
    GaussianContour.average (fun z ↦ weight τ z * pairedTerm z p) 2 = weight τ p := by
  let f := fun z ↦ weight τ z/(z-p)
  let g := fun z ↦ weight τ z/(z-(1-p))
  have h₁ := weight_div_integrable (c := 2) hτ p hp.2.ne'
  have h₂ := weight_div_integrable (c := 2) hτ (1-p) (by simp; linarith [hp.1])
  have hsplit : GaussianContour.average (fun z ↦ weight τ z * pairedTerm z p) 2 = GaussianContour.average f 2 + GaussianContour.average g 2 := by
    have he : (fun z ↦ weight τ z * pairedTerm z p) = fun z ↦ f z + g z := by
      funext z; unfold f g pairedTerm; ring
    rw [he]; unfold GaussianContour.average
    rw [integral_add h₁ h₂, add_div]
  have href := average_reflect f 2
  have hn : (fun z ↦ f (1-z)) = fun z ↦ -g z := by
    funext z; unfold f g; rw [weight_reflect, show 1-z-p = -(z-(1-p)) by ring, div_neg]
  rw [hn, show (1:ℝ)-2 = -1 by norm_num] at href
  have hneg : GaussianContour.average (fun z ↦ -g z) 2 = -GaussianContour.average g 2 := by unfold GaussianContour.average; rw [integral_neg,neg_div]
  rw [hneg] at href
  rw [hsplit]
  have h := single_pole hτ p hp
  change GaussianContour.average f 2 - GaussianContour.average f (-1) = _ at h
  linear_combination h + href * (-1)

private theorem series_integrable {τ : ℝ} (hτ : 0 < τ) (i : XiIndex) :
    Integrable (fun t ↦ weight τ (line 2 t) * pairedTerm (line 2 t) (zeroAt i)) := by
  have hp := zero_strip i
  have h₁ := weight_div_integrable (c := 2) hτ (zeroAt i) (by linarith [hp.2])
  have h₂ := weight_div_integrable (c := 2) hτ (1-zeroAt i) (by simp; linarith [hp.1])
  convert! h₁.add h₂ using 1
  funext t; simp only [Pi.add_apply]; unfold pairedTerm; ring

private theorem integral_norm_sum {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun i : XiIndex ↦ ∫ t, ‖weight τ (line 2 t)*pairedTerm (line 2 t) (zeroAt i)‖) := by
  let C := Real.exp (τ*(2-1/2)^2)*40
  have hG := (majorant_integrable hτ).const_mul C
  have hm := summable_riemannXi_divisorZeroIndex₀_norm_inv_sq.mul_left (∫ t, C*majorant τ t)
  apply Summable.of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) _ hm
  intro i
  rw [← integral_mul_const]
  apply integral_mono (series_integrable hτ i).norm (hG.mul_const _)
  intro t
  dsimp only
  rw [norm_mul,weight_norm]
  apply (mul_le_mul_of_nonneg_left (bound_paired t i) (by positivity : 0 ≤ Real.exp (τ*(2-1/2)^2)*Real.exp (-τ*t^2))).trans_eq
  unfold C majorant; ring

/-- Integrating the log derivative of xi recovers every Gaussian-weighted zero with its multiplicity. -/
theorem gaussian_zero_trace {τ : ℝ} (hτ : 0 < τ) :
    HasSum (fun i : XiIndex ↦ weight τ (zeroAt i)) (2*GaussianContour.average (fun z ↦ weight τ z * logDeriv riemannXi z) 2) := by
  let F := fun i (t : ℝ) ↦ weight τ (line 2 t) * pairedTerm (line 2 t) (zeroAt i)
  have hL (t : ℝ) : HasSum (fun i ↦ F i t) (2*(weight τ (line 2 t)*logDeriv riemannXi (line 2 t))) := by
    convert! (hasSum_paired_logDeriv t).mul_left (weight τ (line 2 t)) using 1; ring
  have hi : Summable fun i ↦ ∫ t, F i t := by
    apply (integral_norm_sum hτ).of_norm_bounded
    intro i
    exact norm_integral_le_integral_norm _
  have : Countable XiIndex := by
    apply Set.countable_univ_iff.mp
    apply summable_riemannXi_divisorZeroIndex₀_norm_inv_sq.countable_support.mono
    intro i _; exact pow_ne_zero _ (inv_ne_zero (norm_ne_zero_iff.mpr i.property))
  have sum := integral_tsum_of_summable_integral_norm (series_integrable hτ) (integral_norm_sum hτ)
  change (∑' i, ∫ t, F i t) = ∫ t, ∑' i, F i t at sum
  simp_rw [(hL _).tsum_eq] at sum
  rw [integral_const_mul] at sum
  have hv (i : XiIndex) : (∫ t, F i t)/(2*(Real.pi : ℂ)) = weight τ (zeroAt i) :=
    integral_pair hτ _ ⟨by linarith [(zero_strip i).1],by linarith [(zero_strip i).2]⟩
  convert! (hi.hasSum.mul_right (2*(Real.pi : ℂ))⁻¹) using 1
  · funext i; rw [← hv i,div_eq_mul_inv]
  · rw [sum]; unfold GaussianContour.average; ring
/-- The poles at 0 and 1 give one reflected pair on the right-hand contour. -/
theorem pole_pair {τ : ℝ} (hτ : 0 < τ) :
    GaussianContour.average (fun z ↦ weight τ z * (1/z + 1/(z-1))) 2 = (Real.exp (τ/4) : ℂ) := by
  have h := integral_pair hτ (0 : ℂ) (by norm_num)
  simpa only [pairedTerm,sub_zero,weight,ofReal_exp,ofReal_div,ofReal_ofNat,
    show (τ : ℂ)*(0-1/2)^2 = (τ:ℂ)/4 by ring] using h


end RHThroughEmergence.GaussianTrace

