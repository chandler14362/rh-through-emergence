import GaussianTrace
import RHThroughEmergence.WeilHeat

/-! Weil's explicit formula for a Gaussian, with the full divisor of Riemann xi. -/

noncomputable section
open Complex MeasureTheory Filter Set
open scoped Topology ComplexConjugate

namespace RHThroughEmergence.GaussianWeil
open GaussianContour ZeroReconstruction

private theorem right_logDeriv {z : ℂ} (hz : 1 < z.re) :
    logDeriv riemannXi z = 1/z + 1/(z-1) + (digamma (z/2)-(Real.log Real.pi : ℂ))/2 +
      logDeriv riemannZeta z := by
  have h0 : z ≠ 0 := by rintro rfl; norm_num at hz
  have h1 : z ≠ 1 := by rintro rfl; norm_num at hz
  let A := fun s : ℂ ↦ exp ((Real.log Real.pi : ℂ)*(-s/2))
  let G := fun s : ℂ ↦ Gamma (s/2)
  have hZ := riemannZeta_ne_zero_of_one_lt_re hz
  have hz2 : 0 < (z/2).re := by simp; linarith
  have hG := Gamma_ne_zero_of_re_pos hz2
  have hD := differentiableAt_Gamma (z/2) (fun n h ↦ by rw [h] at hz2; simp at hz2; linarith [Nat.cast_nonneg (α := ℝ) n])
  have dG := hD.hasDerivAt.comp z ((hasDerivAt_id z).div_const 2)
  have dA : HasDerivAt A (A z * (-(Real.log Real.pi : ℂ)/2)) z := by
    convert! (((((hasDerivAt_id z).neg).div_const 2).const_mul (Real.log Real.pi : ℂ)).cexp) using 1; dsimp [A]; ring
  have hA : A z ≠ 0 := exp_ne_zero _
  have hfun : riemannXi =ᶠ[nhds z] (fun s ↦ (1/2:ℂ)*(s*(s-1)*A s*G s*riemannZeta s)) := by
    filter_upwards [continuous_re.continuousAt (lt_mem_nhds hz)] with s hs
    change 1 < s.re at hs
    have s0 : s ≠ 0 := by rintro rfl; norm_num at hs
    have s1 : s ≠ 1 := by rintro rfl; norm_num at hs
    rw [riemannXi_eq_mul_completedRiemannZeta s0 s1,riemannZeta_def_of_ne_zero s0]
    have hgam := Gammaℝ_ne_zero_of_re_pos (s := s) (by linarith)
    have he : Gammaℝ s = A s * G s := by
      rw [Gammaℝ_def, Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.pi_ne_zero), ← ofReal_log Real.pi_pos.le]
    field_simp [hgam]; rw [he]; ring
  rw [logDeriv_apply,hfun.deriv_eq,hfun.eq_of_nhds]
  change logDeriv (fun s ↦ (1/2:ℂ)*(s*(s-1)*A s*G s*riemannZeta s)) z = _
  rw [logDeriv_const_mul _ _ (by norm_num)]
  have dZ := differentiableAt_riemannZeta h1
  have dG' : DifferentiableAt ℂ G z := dG.differentiableAt
  have ds : DifferentiableAt ℂ (fun s : ℂ ↦ s-1) z := by fun_prop
  have hs := sub_ne_zero.mpr h1
  have dA' := dA.differentiableAt
  rw [logDeriv_fun_mul (f := fun s : ℂ ↦ s*(s-1)*A s*G s) (g := riemannZeta) z (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 hs) hA) hG) hZ (by fun_prop (disch := assumption)) dZ,
      logDeriv_fun_mul (f := fun s : ℂ ↦ s*(s-1)*A s) (g := G) z (mul_ne_zero (mul_ne_zero h0 hs) hA) hG (by fun_prop (disch := assumption)) dG',
      logDeriv_fun_mul (f := fun s : ℂ ↦ s*(s-1)) (g := A) z (mul_ne_zero h0 hs) hA (by fun_prop) dA.differentiableAt,
      logDeriv_fun_mul (f := fun x : ℂ ↦ x) (g := fun s : ℂ ↦ s-1) z h0 hs differentiableAt_id ds]
  have lA : logDeriv A z = -(Real.log Real.pi : ℂ)/2 := by rw [logDeriv_apply,dA.deriv]; field_simp
  have lG : logDeriv G z = digamma (z/2)/2 := by
    rw [digamma_def,logDeriv_apply,logDeriv_apply]
    change deriv (Gamma ∘ fun s : ℂ ↦ id s/2) z / Gamma (z/2) = _
    rw [dG.deriv]; ring
  rw [lA,lG]
  simp [logDeriv_apply]; ring

private theorem prime_integrable {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun t ↦ weight τ (line 2 t)*logDeriv riemannZeta (line 2 t)) := by
  let a := fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ)
  let K := ∑' n, ‖LSeries.term a 2 n‖
  have hb (t : ℝ) : ‖logDeriv riemannZeta (line 2 t)‖ ≤ K := by
    have hz : 1 < (line 2 t).re := by norm_num [line]
    rw [logDeriv_apply, ← norm_neg, ← neg_div, ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz]
    apply (norm_tsum_le_tsum_norm (ArithmeticFunction.LSeriesSummable_vonMangoldt hz).norm).trans_eq
    exact tsum_congr fun n ↦ by simp [a,line,LSeries.norm_term_eq]
  have hc : Continuous (fun t ↦ weight τ (line 2 t)*logDeriv riemannZeta (line 2 t)) := by
    apply continuous_iff_continuousAt.mpr; intro t
    have h1 : line 2 t ≠ 1 := by intro h; have := congrArg re h; norm_num [line] at this
    have hZ := (analyticOn_riemannZeta _ (by simpa using h1 : line 2 t ∈ ({1}:Set ℂ)ᶜ))
    have hn := riemannZeta_ne_zero_of_one_lt_re (s := line 2 t) (by norm_num [line])
    exact (by unfold weight line; fun_prop : ContinuousAt (fun t ↦ weight τ (line 2 t)) t).mul
      ((hZ.deriv.continuousAt.div hZ.continuousAt hn).comp (by unfold line; fun_prop))
  apply ((weight_line_integrable hτ 2).norm.mul_const K).mono' hc.aestronglyMeasurable
  exact .of_forall fun t ↦ (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _))

private theorem weight_mid (τ t : ℝ) : weight τ (line (1/2) t) = (Real.exp (-τ*t^2) : ℂ) := by
  rw [weight,ofReal_exp]
  congr 1; simp [line, mul_pow, I_sq]

private theorem digamma_conj_pos {z : ℂ} (hz : 0 < z.re) : digamma (conj z) = conj (digamma z) := by
  have hp (w : ℂ) (hw : 0 < w.re) (n : ℕ) : w ≠ -n := by rintro rfl; simp at hw; linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [digamma_eq_tsum (hp _ (by simpa using hz)), digamma_eq_tsum (hp _ hz), map_add,conj_tsum]
  simp

private theorem gamma_mid {τ : ℝ} (hτ : 0 < τ) :
    GaussianContour.average (fun z ↦ weight τ z * digamma (z/2)) (1/2) =
      ((∫ t : ℝ, Real.exp (-τ*t^2)*(digamma (line (1/2) t / 2)).re : ℝ) : ℂ)/(2*Real.pi) := by
  let f := fun t : ℝ ↦ weight τ (line (1/2) t) * digamma (line (1/2) t/2)
  have hi : Integrable f := gamma_integrable hτ _ ⟨le_rfl,by norm_num⟩
  have hc (t : ℝ) : f (-t) = conj (f t) := by
    have he : line (1/2) (-t)/2 = conj (line (1/2) t/2) := by norm_num [line, map_ofNat]
    simp only [f,weight_mid,he,digamma_conj_pos (by norm_num [line] : 0 < (line (1/2) t/2).re)]
    rw [map_mul, conj_ofReal, neg_sq]
  have hreal : conj (∫ t, f t) = ∫ t, f t := by
    rw [← integral_conj, ← integral_neg_eq_self f]; exact integral_congr_ae (.of_forall fun t ↦ (hc t).symm)
  unfold GaussianContour.average
  congr 1
  change (∫ t, f t) = _
  rw [← conj_eq_iff_re.mp hreal]
  apply congrArg ((↑) : ℝ → ℂ)
  change RCLike.re (∫ t, f t) = _
  rw [← integral_re hi]
  apply integral_congr_ae
  exact .of_forall fun t ↦ by dsimp only [f]; rw [weight_mid]; simp only [RCLike.re_to_complex, mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]

private theorem mass (τ c : ℝ) (hτ : 0 < τ) :
    GaussianContour.average (weight τ) c = (WeilHeat.heatKernel τ 0 : ℂ) := by
  have h := WeilHeat.shifted_gaussian_test hτ (c-1/2) 0
  unfold GaussianContour.average weight line
  convert! h using 3
  funext t
  push_cast; congr 1; ring

private theorem archimedean {τ : ℝ} (hτ : 0 < τ) :
    GaussianContour.average (fun z ↦ weight τ z * (digamma (z/2) - (Real.log Real.pi : ℂ))) 2 =
      ((∫ t : ℝ, Real.exp (-τ*t^2)*((digamma (line (1/2) t / 2)).re - Real.log Real.pi) : ℝ) : ℂ)/(2*Real.pi) := by
  let L : ℂ := Real.log Real.pi
  have split (c : ℝ) (hc : c ∈ Icc (1/2 : ℝ) 2) :
      GaussianContour.average (fun z ↦ weight τ z * (digamma (z/2)- L)) c =
      GaussianContour.average (fun z ↦ weight τ z * digamma (z/2)) c -
        GaussianContour.average (weight τ) c * L := by
    unfold GaussianContour.average
    simp_rw [mul_sub]
    rw [integral_sub (gamma_integrable hτ c hc) ((weight_line_integrable hτ c).mul_const L),integral_mul_const]
    ring
  rw [split 2 ⟨by norm_num,le_rfl⟩,gamma_shift hτ, mass _ _ hτ, ← mass τ (1/2) hτ,gamma_mid hτ]
  have hg := (gamma_integrable hτ (1/2) ⟨le_rfl,by norm_num⟩).re
  have hg' : Integrable (fun t : ℝ ↦ Real.exp (-τ*t^2)*(digamma (line (1/2) t/2)).re) := by
    convert! hg using 1
    funext t
    rw [weight_mid]
    simp only [RCLike.re_to_complex,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
  simp_rw [mul_sub]
  rw [integral_sub hg' ((integrable_exp_neg_mul_sq hτ).mul_const _),integral_mul_const]
  unfold GaussianContour.average
  simp_rw [weight_mid]
  have castInt : (∫ t : ℝ, (Real.exp (-τ*t^2) : ℂ)) = ((∫ t : ℝ, Real.exp (-τ*t^2) : ℝ) : ℂ) := integral_ofReal
  rw [castInt, ofReal_sub,ofReal_mul]
  dsimp [L]; ring

private theorem average_prime {τ : ℝ} (hτ : 0 < τ) :
    GaussianContour.average (fun z ↦ weight τ z * (-logDeriv riemannZeta z)) 2 =
      (∑' n : ℕ, ((Minkowski.burst n * WeilHeat.heatKernel τ (Real.log n) : ℝ) : ℂ)) := by
  have h := WeilHeat.prime_heat_integral hτ (c := 2) (by norm_num)
  unfold GaussianContour.average
  rw [← h]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  simp only [weight,line,WeilHeat.verticalWeight, logDeriv_apply, neg_div]
  ring_nf

/-- Gaussian Weil explicit formula, summed over nontrivial zeros with their analytic multiplicities. -/
theorem gaussian_weil {τ : ℝ} (hτ : 0 < τ) :
    HasSum (fun i : XiIndex ↦ exp (-(τ : ℂ)*((zeroAt i-1/2)/I)^2))
      (2*(Real.exp (τ/4) : ℂ) +
        ((∫ t : ℝ, Real.exp (-τ*t^2)*((digamma (line (1/2) t/2)).re - Real.log Real.pi) : ℝ) : ℂ) /
          (2*Real.pi) -
        2*(∑' pk : Nat.Primes × ℕ, ((Real.log pk.1 / Real.sqrt ((pk.1 : ℝ)^(pk.2+1)) *
          WeilHeat.heatKernel τ ((pk.2+1)*Real.log pk.1) : ℝ) : ℂ))) := by
  let W := weight τ
  let P := fun z : ℂ ↦ W z*(1/z + 1/(z-1))
  let G := fun z : ℂ ↦ W z*(digamma (z/2) - (Real.log Real.pi : ℂ))
  let A := fun z : ℂ ↦ W z*(-logDeriv riemannZeta z)
  have hP : Integrable (fun t ↦ P (line 2 t)) := by
    have h := (weight_div_integrable (c := 2) hτ 0 (by norm_num)).add
      (weight_div_integrable (c := 2) hτ 1 (by norm_num))
    convert! h using 1; funext t; simp [P,W,div_eq_mul_inv,mul_add]
  have hG : Integrable (fun t ↦ G (line 2 t)) := by
    simpa only [G,W,mul_sub,Pi.sub_def] using
      (gamma_integrable hτ 2 ⟨by norm_num,le_rfl⟩).sub ((weight_line_integrable hτ 2).mul_const (Real.log Real.pi : ℂ))
  have hA : Integrable (fun t ↦ A (line 2 t)) := by
    simpa only [A,W,mul_neg,Pi.neg_def] using (prime_integrable hτ).neg
  have hs : 2*GaussianContour.average (fun z ↦ W z*logDeriv riemannXi z) 2 =
      2*GaussianContour.average P 2 + GaussianContour.average G 2 - 2*GaussianContour.average A 2 := by
    have point (t : ℝ) : W (line 2 t)*logDeriv riemannXi (line 2 t) =
        P (line 2 t) + G (line 2 t)*(1/2) - A (line 2 t) := by
      rw [right_logDeriv (by norm_num [line] : 1 < (line 2 t).re)]
      unfold P G A; ring
    unfold GaussianContour.average
    simp_rw [point]
    have hPG : Integrable (fun t ↦ P (line 2 t)+G (line 2 t)*(1/2:ℂ)) := hP.add (hG.mul_const _)
    rw [integral_sub hPG hA, integral_add hP (hG.mul_const (1/2:ℂ)), integral_mul_const]
    ring
  have hp := WeilHeat.prime_heat_reindex hτ
  have eqp := (Complex.hasSum_ofReal.mpr hp).tsum_eq
  have htrace := GaussianTrace.gaussian_zero_trace hτ
  convert! htrace using 1
  · funext i
    unfold weight
    congr 1; rw [div_pow,I_sq]; ring
  · change _ = 2*GaussianContour.average (fun z ↦ W z * logDeriv riemannXi z) 2
    rw [hs, show GaussianContour.average P 2 = _ from GaussianTrace.pole_pair hτ,
      show GaussianContour.average G 2 = _ from archimedean hτ, show GaussianContour.average A 2 = _ from average_prime hτ,
      eqp,Complex.ofReal_tsum]

end RHThroughEmergence.GaussianWeil

