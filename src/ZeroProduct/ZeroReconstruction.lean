import RHThroughEmergence.Reconstruction
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! Recover the sampled Gaussian from the nontrivial zero divisor, with no free constants. -/

noncomputable section

open Complex
open RHThroughEmergence.Reconstruction

namespace RHThroughEmergence.ZeroReconstruction

/-- The genus-one product of Riemann xi's zeros, counted with their multiplicities. -/
def zeroProduct : ℂ → ℂ :=
  Hadamard.divisorCanonicalProduct 1 riemannXi Set.univ

private theorem right_nonzero {s : ℂ} (hs : 1 < s.re) :
    s ≠ 0 ∧ s ≠ 1 := by
  constructor <;> rintro rfl <;> norm_num at hs

private theorem xi_ne_zero_on_right {s : ℂ} (hs : 1 < s.re) : riemannXi s ≠ 0 := by
  obtain ⟨h0, h1⟩ := right_nonzero hs
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  rw [riemannZeta_def_of_ne_zero h0] at hz
  rw [riemannXi_eq_mul_completedRiemannZeta h0 h1]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1))
    (fun h ↦ hz (by simp [h]))) (by norm_num)

/-- Reflection at the two half-arguments cancels the linear exponential in Hadamard's theorem. -/
theorem xi_from_zeros {s : ℂ} (hs : 1 < s.re) :
    riemannXi s = (1/2 : ℂ) * zeroProduct s * zeroProduct ((1-s)/2) /
      zeroProduct ((1+s)/2) := by
  obtain ⟨P, hdeg, hfac⟩ := riemannXi_hadamard_factorization_no_monomial
  let A := P.coeff 0
  let B := P.coeff 1
  have fac (w : ℂ) : riemannXi w = exp (A + B*w) * zeroProduct w := by
    rw [hfac w]
    congr 2
    conv_lhs => rw [Polynomial.eq_X_add_C_of_degree_le_one hdeg]
    simp [A, B, add_comm]
  have origin : exp A = 1/2 := by
    simpa [zeroProduct, Hadamard.divisorCanonicalProduct_zero, riemannXi_zero] using (fac 0).symm
  let u := (1+s)/2
  let v := (1-s)/2
  have hu : 1 < u.re := by dsimp [u]; simp; linarith
  have huD : zeroProduct u ≠ 0 := by
    intro h
    exact xi_ne_zero_on_right hu (by rw [fac, h, mul_zero])
  have hfold : riemannXi u = riemannXi v := by
    rw [← riemannXi_one_sub u]
    congr 1
    dsimp [u,v]
    ring
  have shift : exp (B*s) * zeroProduct u = zeroProduct v := by
    rw [fac, fac] at hfold
    apply mul_left_cancel₀ (exp_ne_zero (A+B*v))
    calc
      _ = exp (A+B*u) * zeroProduct u := by
        rw [← mul_assoc, ← Complex.exp_add]
        congr 2
        dsimp [u,v]
        ring
      _ = _ := hfold
  change _ = (1/2 : ℂ) * zeroProduct s * zeroProduct v / zeroProduct u
  rw [fac, Complex.exp_add, origin, eq_div_iff huD, ← shift]
  ring

/-- Completed zeta on the inversion line, expressed using only the canonical zero product. -/
def completedFromZeros (s : ℂ) : ℂ :=
  zeroProduct s * zeroProduct ((1-s)/2) / (zeroProduct ((1+s)/2) * s * (s-1))

theorem completed_from_zeros {s : ℂ} (hs : 1 < s.re) :
    completedFromZeros s = completedRiemannZeta s := by
  obtain ⟨h0, h1⟩ := right_nonzero hs
  have he := xi_from_zeros hs
  rw [riemannXi_eq_mul_completedRiemannZeta h0 h1] at he
  rw [completedFromZeros]
  have he' : s * (s-1) * completedRiemannZeta s =
      zeroProduct s * zeroProduct ((1-s)/2) / zeroProduct ((1+s)/2) := by
    linear_combination 2 * he
  rw [← div_div, ← div_div, ← he']
  field_simp [h0, sub_ne_zero.mpr h1]

/-- For every positive spacing the nontrivial zeros reconstruct the positive Gaussian lattice. -/
theorem zero_reconstruction {a c : ℝ} (ha : 0 < a) (hc : 1/2 < c) :
    mellinInv c (fun z ↦ completedFromZeros (2*z)) a = (sampled a : ℂ) :=
  reconstruction_of_completed_on_right completedFromZeros (fun _ ↦ completed_from_zeros) ha hc

/-- At every positive scale the prime-exponent sum converges to the very same zero integral. -/
theorem primes_equal_zeros {a c : ℝ} (ha : 0 < a) (hc : 1/2 < c) :
    HasSum (fun k : {f : ℕ →₀ ℕ // ∀ p ∈ f.support, Nat.Prime p} ↦
      (Real.exp (-Real.pi * ((k.val.prod (· ^ ·) : ℕ) : ℝ)^2 * a) : ℂ))
      (mellinInv c (fun z ↦ completedFromZeros (2*z)) a) := by
  rw [zero_reconstruction ha hc]
  exact Complex.hasSum_ofReal.mpr (prime_reconstruction ha)

/-- Möbius inversion of the zero integrals recovers one unsampled Gaussian. -/
theorem gaussian_from_zeros {a c : ℝ} (ha : 0 < a) (hc : 1/2 < c) :
    HasSum (fun d : ℕ+ ↦ (ArithmeticFunction.moebius d : ℂ) *
      mellinInv c (fun z ↦ completedFromZeros (2*z)) ((d : ℝ)^2 * a))
      (Real.exp (-Real.pi * a) : ℂ) := by
  have h := Complex.hasSum_ofReal.mpr (moebius_reconstruction ha)
  apply h.congr_fun
  intro d
  have hd : 0 < (d : ℝ) := by exact_mod_cast d.2
  rw [zero_reconstruction (by positivity) hc]
  push_cast
  rfl

private theorem xi_eq_unit_mul_zeta {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    riemannXi s = (s * (s-1) * Gammaℝ s / 2) * riemannZeta s := by
  have h0 : s ≠ 0 := by rintro rfl; simp at hs
  rw [riemannXi_eq_mul_completedRiemannZeta h0 h1, riemannZeta_def_of_ne_zero h0]
  field_simp [Gammaℝ_ne_zero_of_re_pos hs]

/-- The zeros of the entire xi function are exactly the zeta zeros in the open critical strip. -/
theorem xi_zero_iff {s : ℂ} :
    riemannXi s = 0 ↔ 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 := by
  have outside (w : ℂ) (hw : 1 ≤ w.re) : riemannXi w ≠ 0 := by
    by_cases h1 : w = 1
    · subst w
      rw [show (1:ℂ) = 1-0 by ring, riemannXi_one_sub, riemannXi_zero]
      norm_num
    have hw0 : 0 < w.re := by linarith
    have w0 : w ≠ 0 := by rintro rfl; simp at hw0
    rw [xi_eq_unit_mul_zeta hw0 h1]
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (mul_ne_zero w0 (sub_ne_zero.mpr h1))
      (Gammaℝ_ne_zero_of_re_pos hw0)) (by norm_num)) (riemannZeta_ne_zero_of_one_le_re hw)
  constructor
  · intro h
    have hlt : s.re < 1 := lt_of_not_ge (fun hs ↦ outside s hs h)
    have hpos : 0 < s.re := by
      by_contra! hn
      exact outside (1-s) (by simp; linarith) (by rwa [riemannXi_one_sub])
    have h0 : s ≠ 0 := by rintro rfl; simp at hpos
    have h1 : s ≠ 1 := by rintro rfl; simp at hlt
    rw [xi_eq_unit_mul_zeta hpos h1] at h
    exact ⟨hpos, hlt, (mul_eq_zero.mp h).resolve_left
      (div_ne_zero (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1))
        (Gammaℝ_ne_zero_of_re_pos hpos)) (by norm_num))⟩
  · rintro ⟨hpos,hlt,hz⟩
    have h1 : s ≠ 1 := by rintro rfl; simp at hlt
    rw [xi_eq_unit_mul_zeta hpos h1, hz, mul_zero]

/-- Removing the nonvanishing factors preserves each zeta zero's analytic multiplicity. -/
theorem xi_zeta_order {s : ℂ} (hs : 0 < s.re) (hlt : s.re < 1) :
    analyticOrderAt riemannXi s = analyticOrderAt riemannZeta s := by
  let U := fun w : ℂ ↦ w * (w-1) * Gammaℝ w / 2
  have h0 : s ≠ 0 := by rintro rfl; simp at hs
  have h1 : s ≠ 1 := by rintro rfl; simp at hlt
  have hg := Gammaℝ_ne_zero_of_re_pos hs
  have hU : U s ≠ 0 := div_ne_zero (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) hg)
    (by norm_num)
  have hG : AnalyticAt ℂ Gammaℝ s := by
    have han := (differentiable_Gammaℝ_inv.analyticAt s).inv (inv_ne_zero hg)
    convert han using 1
    funext w
    exact (inv_inv (Gammaℝ w)).symm
  have aU : AnalyticAt ℂ U s :=
    (((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul hG).div
      analyticAt_const (by norm_num : (2 : ℂ) ≠ 0))
  have hnear : riemannXi =ᶠ[nhds s] U * riemannZeta := by
    filter_upwards [continuous_re.continuousAt (lt_mem_nhds hs),
      eventually_ne_nhds h1] with w hw hw1
    exact xi_eq_unit_mul_zeta hw hw1
  rw [analyticOrderAt_congr hnear, analyticOrderAt_mul aU (analyticOn_riemannZeta s h1),
    analyticOrderAt_eq_zero.mpr (.inr hU), zero_add]

/-- The zero product converges locally uniformly on the entire complex plane. -/
theorem zero_product_converges :
    HasProdLocallyUniformlyOn
      (fun (p : Hadamard.divisorZeroIndex₀ riemannXi Set.univ) (s : ℂ) ↦
        (1 - s / Hadamard.divisorZeroIndex₀_val p) * exp (s / Hadamard.divisorZeroIndex₀_val p))
      zeroProduct Set.univ := by
  simpa [zeroProduct, weierstrassFactor, partialLogSum, logTaylor, Finset.sum_range_succ] using
    Hadamard.hasProdLocallyUniformlyOn_divisorCanonicalProduct_univ 1 riemannXi
      summable_riemannXi_divisorZeroIndex₀_norm_inv_sq

/-- The limit of the recovered Gaussian at zero gives its vacuum normalization. -/
theorem gaussian_from_zeros_at_origin {c : ℝ} (hc : 1/2 < c) :
    Filter.Tendsto (fun a : ℝ ↦ ∑' d : ℕ+, (ArithmeticFunction.moebius d : ℂ) *
      mellinInv c (fun z ↦ completedFromZeros (2*z)) ((d : ℝ)^2 * a))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have he : (fun a : ℝ ↦ ∑' d : ℕ+, (ArithmeticFunction.moebius d : ℂ) *
      mellinInv c (fun z ↦ completedFromZeros (2*z)) ((d : ℝ)^2 * a)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun a : ℝ ↦ (Real.exp (-Real.pi * a) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with a ha using (gaussian_from_zeros ha hc).tsum_eq
  have hcont : Continuous (fun a : ℝ ↦ (Real.exp (-Real.pi * a) : ℂ)) := by fun_prop
  apply Filter.Tendsto.congr' he.symm
  simpa using (hcont.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))

end RHThroughEmergence.ZeroReconstruction
