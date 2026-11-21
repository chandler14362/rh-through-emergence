import Mathlib

/-! The Fourier-fixed Gaussian, its lattice fold, the Mellin factor and the prime logarithmic derivative. -/

namespace RHThroughEmergence.GaussianLattice

open Complex FourierTransform

/-! ## 1–3. The Gaussian ground state, its lattice samples and the real Mellin factor -/

/-- Fourier transformation fixes the Gaussian ground state. -/
theorem gaussian_self_dual :
    (𝓕 fun x : ℝ => cexp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)) = fun t : ℝ => cexp (-(Real.pi : ℂ) * (t : ℂ) ^ 2) := by
  have h := fourierIntegral_gaussian_pi (b := 1) (by simp)
  simpa using h

/-- **The fold on the lattice (Poisson summation):** `θ(t) = t^(−½) θ(1/t)`. -/
theorem gaussian_lattice_fold {t : ℝ} (ht : 0 < t) :
    ∑' n : ℤ, Real.exp (-Real.pi * t * (n : ℝ) ^ 2)
      = 1 / t ^ (1 / 2 : ℝ) * ∑' n : ℤ, Real.exp (-Real.pi / t * (n : ℝ) ^ 2) :=
  Real.tsum_exp_neg_mul_int_sq ht

/-- The positive-half Mellin transform of the Gaussian ground state is `∫₀^∞ x^(s−1) e^(−πx²) dx = π^(−s/2) · ½ · Γ(s/2)`, i.e.
`½ Γ_ℝ(s)`. -/
theorem gaussian_mellin {s : ℝ} (hs : 0 < s) :
    ∫ x in Set.Ioi (0 : ℝ), x ^ (s - 1) * Real.exp (-Real.pi * x ^ (2 : ℝ))
      = Real.pi ^ (-s / 2) * (1 / 2) * Real.Gamma (s / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := s - 1) (b := Real.pi) two_pos (by linarith)
    Real.pi_pos
  rw [show s - 1 + 1 = s by ring] at h
  exact h

/-! ## 4–5. The two reflected poles and the factorization of completed zeta -/

/-- The two reflected origin terms give the poles in `Λ(s) = Λ₀(s) − 1/s − 1/(1 − s)`.
In the collision interpretation, these terms come from the two weights that agree at unit scale. -/
theorem completed_zeta_pole_decomposition (s : ℂ) :
    completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) :=
  completedRiemannZeta_eq s

/-- Removing the two pole terms leaves an entire function. -/
theorem regular_part_entire : Differentiable ℂ completedRiemannZeta₀ :=
  differentiable_completedZeta₀

/-- ... and fold-symmetric. -/
theorem regular_part_fold (s : ℂ) : completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s :=
  completedRiemannZeta₀_one_sub s

/-- The fold swaps the two poles, so `Λ` itself is fold-symmetric. -/
theorem fold (s : ℂ) : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

/-- The pole of completed zeta at `s = 1` has residue `1`. -/
theorem completed_zeta_residue_at_one :
    Filter.Tendsto (fun s ↦ (s - 1) * completedRiemannZeta s) (nhdsWithin 1 {1}ᶜ) (nhds 1) :=
  completedRiemannZeta_residue_one

/-- **Floor times lattice:** away from the poles, `Λ = Γ_ℝ · ζ`. -/
theorem floor_times_lattice {s : ℂ} (hs : s ≠ 0) (hG : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  rw [riemannZeta_def_of_ne_zero hs]
  field_simp

/-! ## 6–7. The Euler product and the logarithmic derivative of completed zeta -/

/-- The prime Euler factors give `ζ = ∏_p (1 − p^(−s))^(−1)` on `Re s > 1`. -/
theorem bosons_euler_product {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
  riemannZeta_eulerProduct_tprod hs

/-- The prime-power Dirichlet series satisfies `∑ Λ(n) n^(−s) = −ζ′/ζ` on `Re s > 1`. -/
theorem bosons_force {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s = -deriv riemannZeta s / riemannZeta s :=
  ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

/-- `Γ_ℝ` is differentiable on `Re s > 0`. -/
lemma differentiableAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℝ s := by
  have hfun : Gammaℝ = fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2) := funext Gammaℝ_def
  rw [hfun]
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
    (differentiableAt_id.neg.div_const 2).const_cpow (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Gamma (z / 2)) s := by
    refine (differentiableAt_Gamma (s / 2) ?_).comp s (differentiableAt_id.div_const 2)
    intro m hm
    have hs2 : s = -(m : ℂ) * 2 := (div_eq_iff two_ne_zero).mp hm
    have hre : s.re = -(m : ℝ) * 2 := by rw [hs2]; simp
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  exact h1.mul h2

/-- **The completed force is floor minus primes.** On `Re s > 1`, `Λ′/Λ = Γ_ℝ′/Γ_ℝ − ∑ Λ(n) n^(−s)`: the floor's
log-derivative (from the Mellin transform of the Gaussian ground state) minus the primes' force. The explicit formula's analytic core, before the
zeros enter. -/
theorem completed_force_eq_floor_sub_primes {s : ℂ} (hs : 1 < s.re) :
    deriv completedRiemannZeta s / completedRiemannZeta s
      = deriv Gammaℝ s / Gammaℝ s - LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, one_re] at hs
    exact lt_irrefl _ hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hZ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hEq : completedRiemannZeta =ᶠ[nhds s] (Gammaℝ * riemannZeta) := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz
    have hz' : 1 < z.re := hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, zero_re] at hz'
      linarith
    show completedRiemannZeta z = Gammaℝ z * riemannZeta z
    exact floor_times_lattice hz0 (Gammaℝ_ne_zero_of_re_pos (by linarith))
  have hval : completedRiemannZeta s = Gammaℝ s * riemannZeta s := hEq.eq_of_nhds
  have hGd : DifferentiableAt ℂ Gammaℝ s := differentiableAt_Gammaℝ (by linarith)
  have hZd : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  rw [hEq.deriv_eq, deriv_mul hGd hZd, hval, bosons_force hs]
  field_simp
  ring

end RHThroughEmergence.GaussianLattice
