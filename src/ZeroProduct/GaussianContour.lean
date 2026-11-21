import PrimeNumberTheoremAnd.PerronFormula
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Vertical Gaussian integrals across a simple pole and across the real gamma factor. -/

noncomputable section
open Complex MeasureTheory Filter Asymptotics Set
open scoped Topology

namespace RHThroughEmergence.GaussianContour

def weight (τ : ℝ) (z : ℂ) : ℂ := exp ((τ : ℂ)*(z-1/2)^2)
abbrev line (c t : ℝ) : ℂ := (c : ℂ) + t*I
def average (f : ℂ → ℂ) (c : ℝ) : ℂ := (∫ t : ℝ, f (line c t))/(2*Real.pi)

@[simp] theorem weight_reflect (τ : ℝ) (z : ℂ) : weight τ (1-z) = weight τ z := by
  unfold weight; congr 1; ring

theorem weight_norm (τ c t : ℝ) :
    ‖weight τ (line c t)‖ = Real.exp (τ*(c-1/2)^2) * Real.exp (-τ*t^2) := by
  rw [weight, norm_exp, ← Real.exp_add]
  congr 1
  simp [line, pow_two, mul_re, mul_im, sub_re, sub_im]
  ring

def majorant (τ t : ℝ) := (1+t^2)*Real.exp (-τ*t^2)

theorem majorant_integrable {τ : ℝ} (hτ : 0 < τ) : Integrable (majorant τ) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq hτ (s := (2 : ℕ)) (by norm_num)
  change Integrable (fun t : ℝ ↦ (1+t^2)*Real.exp (-τ*t^2))
  simpa [majorant, add_mul, Real.rpow_natCast, Pi.add_def] using (integrable_exp_neg_mul_sq hτ).add h

private theorem horizontal {τ a b K R : ℝ} {f : ℂ → ℂ} (hτ : 0 < τ) (hab : a ≤ b)
    (h : ∀ x ∈ Icc a b, ∀ t : ℝ, R ≤ |t| → ‖f (line x t)‖ ≤ K*majorant τ t)
    (l : Filter ℝ) (hl : Tendsto (fun t : ℝ ↦ t^2) l atTop) :
    Tendsto (fun t : ℝ ↦ ∫ x in a..b, f (line x t)) l (nhds 0) := by
  have hdec (n : ℕ) : Tendsto (fun t : ℝ ↦ (t^2)^n * Real.exp (-τ*t^2)) l (nhds 0) := by
    simpa [Function.comp_def, Real.rpow_natCast] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n:ℝ) τ hτ).comp hl
  have hm : Tendsto (majorant τ) l (nhds 0) := by
    change Tendsto (fun t : ℝ ↦ (1+t^2)*Real.exp (-τ*t^2)) l (nhds 0)
    simpa [add_mul] using (hdec 0).add (hdec 1)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun t ↦ K*majorant τ t*|b-a|) l (nhds 0) by simpa using (hm.const_mul K).mul_const |b-a|)
    (.of_forall fun _ ↦ norm_nonneg _)
  filter_upwards [hl.eventually_ge_atTop (R^2)] with t ht
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  rw [uIoc_of_le hab] at hx
  exact h x ⟨hx.1.le,hx.2⟩ t (by nlinarith [sq_abs t,abs_nonneg t])

private theorem sq_bot : Tendsto (fun t : ℝ ↦ t^2) atBot atTop := by
  simpa [Function.comp_def] using (tendsto_pow_atTop (α := ℝ) (n := 2) (by decide)).comp tendsto_neg_atBot_atTop

theorem average_reflect (f : ℂ → ℂ) (c : ℝ) :
    average (fun z ↦ f (1-z)) c = average f (1-c) := by
  unfold average
  rw [← integral_neg_eq_self (fun t : ℝ ↦ f (line (1-c) t))]
  congr 1
  apply integral_congr_ae
  exact .of_forall fun t ↦ congrArg f (by simp [line]; ring)

private theorem norm_weight_le {τ x t : ℝ} (hτ : 0 < τ) (hx : x ∈ Icc (-1 : ℝ) 2) :
    ‖weight τ (line x t)‖ ≤ Real.exp (τ*3) * Real.exp (-τ*t^2) := by
  rw [weight_norm]
  gcongr
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)]

private theorem pole_bound (p : ℂ) (x t : ℝ) (ht : |p.im|+1 ≤ |t|) :
    1 ≤ ‖line x t-p‖ := by
  have h := Complex.abs_im_le_norm (line x t - p)
  have htri := abs_sub_abs_le_abs_sub t p.im
  apply le_trans _ h
  simp [line]; linarith

theorem weight_div_integrable {τ c : ℝ} (hτ : 0 < τ) (p : ℂ) (hc : c ≠ p.re) :
    Integrable (fun t ↦ weight τ (line c t)/(line c t-p)) := by
  have hn (t : ℝ) : line c t-p ≠ 0 := sub_ne_zero.mpr fun h ↦ hc (by simpa [line] using congrArg re h)
  apply ((integrable_exp_neg_mul_sq hτ).const_mul (Real.exp (τ*(c-1/2)^2)/|c-p.re|)).mono'
    (Continuous.aestronglyMeasurable (by unfold weight line; fun_prop (disch := exact hn _)))
  apply Filter.Eventually.of_forall
  intro t
  rw [norm_div, weight_norm, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr (sub_ne_zero.mpr hc))
  simpa [line] using (abs_re_le_norm (line c t-p))

/-- Moving the Gaussian integral from -1 to 2 picks up a single pole with residue its Gaussian weight. -/
theorem single_pole {τ : ℝ} (hτ : 0 < τ) (p : ℂ) (hp : -1 < p.re ∧ p.re < 2) :
    average (fun z ↦ weight τ z/(z-p)) 2 - average (fun z ↦ weight τ z/(z-p)) (-1) = weight τ p := by
  let f := fun z ↦ weight τ z/(z-p)
  have hf : HolomorphicOn f (Icc (-1 : ℝ) 2 ×ℂ univ \ {p}) := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    dsimp [f, weight]; fun_prop (disch := exact sub_ne_zero.mpr hz.2)
  have hd : DifferentiableAt ℂ (weight τ) p := by unfold weight; fun_prop
  have hpole : (f - (fun z ↦ weight τ p/(z-p))) =O[nhdsWithin p {p}ᶜ] (1 : ℂ → ℂ) := by
    have hs := hd.hasDerivAt.tendsto_slope.isBigO_one ℂ
    convert! hs using 1
    funext z
    simp [f, slope_def_field, sub_div]
  have hb : ∀ x ∈ Icc (-1:ℝ) 2, ∀ t : ℝ, |p.im|+1 ≤ |t| →
      ‖f (line x t)‖ ≤ Real.exp (τ*3) * majorant τ t := by
    intro x hx t ht
    calc
      _ ≤ ‖weight τ (line x t)‖ := by dsimp [f]; rw [norm_div]; exact div_le_self (norm_nonneg _) (pole_bound p x t ht)
      _ ≤ _ := (norm_weight_le hτ hx).trans (by unfold majorant; gcongr; exact le_mul_of_one_le_left (Real.exp_pos _).le (by nlinarith [sq_nonneg t]))
  have h := tendsto_truncated_vertical_shift_with_simple_pole hp hf hpole
    (horizontal hτ (by norm_num) hb atBot sq_bot)
    (horizontal hτ (by norm_num) hb atTop (tendsto_pow_atTop (by decide)))
    (weight_div_integrable hτ p hp.2.ne')
  have hleft := intervalIntegral_tendsto_integral (weight_div_integrable hτ p hp.1.ne)
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto (fun x : ℝ ↦ x) atTop atTop)
  have eq := tendsto_nhds_unique (((hleft.const_smul I).const_smul (1/(2*(Real.pi:ℂ)*I)))) h
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul] at eq
  have normI (z : ℂ) : 1/(2*(Real.pi:ℂ)*I)*(I*z) = z/(2*(Real.pi:ℂ)) := by field_simp
  simp only [normI] at eq
  unfold average
  linear_combination -eq

theorem weight_line_integrable {τ : ℝ} (hτ : 0 < τ) (c : ℝ) :
    Integrable (fun t ↦ weight τ (line c t)) := by
  apply (integrable_norm_iff (Continuous.aestronglyMeasurable (by unfold weight line; fun_prop))).mp
  simp_rw [weight_norm]
  exact (integrable_exp_neg_mul_sq hτ).const_mul _

private theorem gamma_control {τ : ℝ} (hτ : 0 < τ) :
    ∃ K : ℝ, ∀ x ∈ Icc (1/2 : ℝ) 2, ∀ t : ℝ,
      ‖weight τ (line x t) * digamma (line x t/2)‖ ≤ K*majorant τ t := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_digamma_div_two_le_log (a := 1/2) (b := 2) (by norm_num)
  refine ⟨Real.exp (τ*3)*(3*C), ?_⟩
  intro x hx t
  have hd := hbound (line x t) (by simpa [line] using hx.1) (by simpa [line] using hx.2)
  simp only [line, add_im, ofReal_im, mul_I_im, ofReal_re, zero_add] at hd
  have hlog : Real.log (|t|+2) ≤ 3*(1+t^2) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < |t|+2 by positivity)
    nlinarith [sq_abs t,sq_nonneg (|t|-1),sq_nonneg t]
  change ‖weight τ (line x t) * digamma (line x t/2)‖ ≤ _
  rw [norm_mul]
  have h := mul_le_mul (norm_weight_le (t := t) hτ ⟨by linarith [hx.1],hx.2⟩)
    (hd.trans (mul_le_mul_of_nonneg_left hlog hC.le)) (norm_nonneg _) (by positivity)
  exact h.trans_eq (by unfold majorant; ring)

private theorem weight_gamma_diff (τ : ℝ) (z : ℂ) (hz : 0 < z.re) :
  DifferentiableAt ℂ (fun z ↦ weight τ z * digamma (z/2)) z := by
  have hs : 0 < (z/2).re := by simp [div_ofNat_re]; linarith
  exact (by unfold weight; fun_prop : DifferentiableAt ℂ (weight τ) z).mul
    ((differentiableAt_digamma_of_re_pos hs).comp z (by fun_prop))

theorem gamma_integrable {τ : ℝ} (hτ : 0 < τ) (x : ℝ) (hx : x ∈ Icc (1/2 : ℝ) 2) :
  Integrable (fun t ↦ weight τ (line x t) * digamma (line x t/2)) := by
  obtain ⟨K, hb⟩ := gamma_control hτ
  let f := fun z ↦ weight τ z * digamma (z/2)
  have hc : Continuous (fun t ↦ f (line x t)) := continuous_iff_continuousAt.mpr fun t ↦
    (weight_gamma_diff τ _ (by simp [line]; linarith [hx.1])).continuousAt.comp (by unfold line; fun_prop)
  exact ((majorant_integrable hτ).const_mul _).mono' hc.aestronglyMeasurable (.of_forall (hb x hx))

theorem gamma_shift {τ : ℝ} (hτ : 0 < τ) :
    average (fun z ↦ weight τ z * digamma (z/2)) 2 =
      average (fun z ↦ weight τ z * digamma (z/2)) (1/2) := by
  let f := fun z ↦ weight τ z * digamma (z/2)
  obtain ⟨K, hb⟩ := gamma_control hτ
  have h := verticalIntegral_eq_verticalIntegral (σ := 1/2) (σ' := 2) (f := f)
    (fun z hz ↦ (weight_gamma_diff τ z (by have hh := hz.1; rw [uIcc_of_le (by norm_num)] at hh; linarith [hh.1])).differentiableWithinAt)
    (horizontal (K := K) (R := 0) hτ (by norm_num) (fun x hx t _ ↦ hb x hx t) atBot sq_bot)
    (horizontal (K := K) (R := 0) hτ (by norm_num) (fun x hx t _ ↦ hb x hx t) atTop (tendsto_pow_atTop (by decide)))
    (gamma_integrable hτ _ ⟨le_rfl,by norm_num⟩) (gamma_integrable hτ _ ⟨by norm_num,le_rfl⟩)
  unfold VerticalIntegral at h
  have h' := smul_right_injective (M := ℂ) (show I ≠ 0 from I_ne_zero) h
  unfold average
  rw [show (∫ t, weight τ (line 2 t) * digamma (line 2 t / 2)) = _ from h'.symm]

end RHThroughEmergence.GaussianContour
