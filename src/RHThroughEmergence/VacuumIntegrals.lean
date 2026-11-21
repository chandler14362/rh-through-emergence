import RHThroughEmergence.GaussianLattice

/-! The local Fourier vacuum and the Tate integral in valuation-shell coordinates. -/

namespace RHThroughEmergence.VacuumIntegrals

open Complex MeasureTheory

noncomputable section

/-- Fourier transform of the p-adic unit ball with any character of conductor ℤ_p
and any Haar probability measure on the ball. -/
theorem unit_ball_fourier {p : ℕ} [Fact p.Prime]
    [MeasurableSpace ℤ_[p]] [BorelSpace ℤ_[p]] (μ : Measure ℤ_[p])
    [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant] (χ : AddChar ℚ_[p] ℂ)
    (hχ : ∀ y, χ y = 1 ↔ ‖y‖ ≤ 1) (ξ : ℚ_[p]) :
    (∫ x : ℤ_[p], χ (ξ * (x : ℚ_[p])) ∂μ) = if ‖ξ‖ ≤ 1 then 1 else 0 := by
  by_cases hξ : ‖ξ‖ ≤ 1
  · rw [if_pos hξ]
    have hx (x : ℤ_[p]) : χ (ξ * (x : ℚ_[p])) = 1 := (hχ _).mpr <| by
      rw [norm_mul]
      exact mul_le_one₀ hξ (norm_nonneg _) x.norm_le_one
    simp [hx]
  · rw [if_neg hξ]
    let f := fun x : ℤ_[p] ↦ χ (ξ * (x : ℚ_[p]))
    have hshift (x : ℤ_[p]) : f (1 + x) = χ ξ * f x := by
      simp [f, mul_add, χ.map_add_eq_mul]
    have h := integral_add_left_eq_self (μ := μ) f 1
    simp_rw [hshift, integral_const_mul] at h
    exact (mul_eq_zero.mp (show (χ ξ - 1) * (∫ x, f x ∂μ) = 0 by
      rw [sub_mul, one_mul, h, sub_self])).resolve_left (sub_ne_zero.mpr (fun h ↦ hξ ((hχ ξ).mp h)))

/-- Squaring the real absolute value, u=|x|², absorbs both signs and gives du/u. -/
def realShell (s : ℂ) : ℂ :=
  ∫ u : ℝ in Set.Ioi 0, (u : ℂ) ^ (s / 2 - 1) * Complex.exp (-(Real.pi * (u : ℂ)))

theorem realShell_eq_gamma {s : ℂ} (hs : 0 < s.re) : realShell s = Gammaℝ s := by
  rw [realShell, Complex.integral_cpow_mul_exp_neg_mul_Ioi (by simpa using hs) Real.pi_pos,
    Complex.Gammaℝ_def, one_div, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg Real.pi_nonneg]; exact Real.pi_ne_zero.symm),
    ← Complex.cpow_neg]
  congr 2
  ring

/-- Each finite integral-unit coset has unit mass. The surviving shells are indexed by n≥1,
with finite norm 1/n. Their archimedean integrals sum to completed zeta. -/
theorem vacuum_shells_hasSum {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ+ ↦ realShell s / (n : ℂ) ^ s) (completedRiemannZeta s) := by
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hG := Complex.Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hs)
  rw [GaussianLattice.floor_times_lattice h0 hG, ← realShell_eq_gamma (lt_trans zero_lt_one hs)]
  have hζ := (Complex.summable_one_div_nat_cpow.mpr hs).hasSum
  rw [← zeta_eq_tsum_one_div_nat_cpow hs] at hζ
  have htail := (hasSum_nat_add_iff' 1).mpr hζ
  simp [Complex.zero_cpow h0] at htail
  apply Equiv.pnatEquivNat.symm.hasSum_iff.mp
  simpa [Function.comp_def, div_eq_mul_inv] using htail.mul_left (realShell s)

end

end RHThroughEmergence.VacuumIntegrals
