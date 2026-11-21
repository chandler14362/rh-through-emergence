import RHThroughEmergence.MellinReconstruction

/-! Reconstruction of the positive half of the sampled Gaussian from its arithmetic data. -/

noncomputable section

open Complex MeasureTheory Set HurwitzZeta
open scoped Real Topology

namespace RHThroughEmergence.Reconstruction

private theorem gaussian_hasSum {a : ℝ} (ha : 0 < a) :
    HasSum (fun n : ℕ ↦ Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * a)) (sampled a) := by
  simpa [sampled] using (hasSum_nat_cosKernel₀ 0 ha).div_const 2

/-- Prime exponent vectors enumerate the terms of the convergent theta sum exactly once. -/
theorem prime_reconstruction {a : ℝ} (ha : 0 < a) :
    HasSum (fun k : {f : ℕ →₀ ℕ // ∀ p ∈ f.support, Nat.Prime p} ↦
      Real.exp (-Real.pi * ((k.val.prod (· ^ ·) : ℕ) : ℝ) ^ 2 * a)) (sampled a) := by
  apply Nat.factorizationEquiv.hasSum_iff.mp
  apply Equiv.pnatEquivNat.symm.hasSum_iff.mp
  change HasSum (fun n : ℕ ↦ Real.exp (-Real.pi *
    (((n + 1).factorization.prod (· ^ ·) : ℕ) : ℝ) ^ 2 * a)) (sampled a)
  have hsite (n : ℕ) : (n+1).factorization.prod (· ^ ·) = n+1 :=
    congrArg (fun j : ℕ+ ↦ (j : ℕ)) (Nat.factorizationEquiv.symm_apply_apply ⟨n+1, by omega⟩)
  simpa only [hsite, Nat.cast_add_one] using gaussian_hasSum ha

private theorem positive_gaussian_hasSum {a : ℝ} (ha : 0 < a) :
    HasSum (fun n : ℕ+ ↦ Real.exp (-Real.pi * (n : ℝ)^2 * a)) (sampled a) := by
  apply Equiv.pnatEquivNat.symm.hasSum_iff.mp
  simpa [Function.comp_def] using gaussian_hasSum ha

private theorem moebius_pairs_summable {a : ℝ} (ha : 0 < a) :
    Summable (fun ij : ℕ+ × ℕ+ ↦ (ArithmeticFunction.moebius ij.1 : ℝ) *
      Real.exp (-Real.pi * ((ij.1 : ℝ)*(ij.2 : ℝ))^2 * a)) := by
  let r := Real.exp (-Real.pi*a)
  have hr : ‖r‖ < 1 := by simp [r, Real.norm_eq_abs, abs_of_pos, Real.exp_pos, ha, Real.pi_pos]
  have hmaj := summable_prod_mul_pow 0 hr
  simp only [pow_zero, one_mul] at hmaj
  apply hmaj.of_norm_bounded
  intro ij
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hmu : |(ArithmeticFunction.moebius ij.1 : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := ij.1))
  have hx : 1 ≤ (ij.1 : ℝ) * (ij.2 : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero ij.1.ne_zero ij.2.ne_zero))
  calc
    _ ≤ Real.exp (-Real.pi * ((ij.1 : ℝ)*(ij.2 : ℝ))^2 * a) := by
      simpa using mul_le_mul_of_nonneg_right hmu (Real.exp_pos _).le
    _ ≤ _ := by
      dsimp [r]
      rw [← Real.exp_nat_mul]
      push_cast
      apply Real.exp_le_exp.mpr
      have hsq : (ij.1 : ℝ)*(ij.2 : ℝ) ≤ ((ij.1 : ℝ)*(ij.2 : ℝ))^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hsq (mul_pos Real.pi_pos ha).le]

private theorem moebius_fiber (n : ℕ+) :
    (∑ ij ∈ (n : ℕ).divisorsAntidiagonal, (ArithmeticFunction.moebius ij.1 : ℝ)) =
      if n = 1 then 1 else 0 := by
  rw [Nat.sum_divisorsAntidiagonal (fun i _ ↦ (ArithmeticFunction.moebius i : ℝ))]
  have h := congrArg (fun f : ArithmeticFunction ℤ ↦ f (n : ℕ))
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  have he : (n : ℕ) = 1 ↔ n = 1 := by norm_cast
  by_cases h1 : n = 1
  · subst n; simp
  · simp [he, h1] at h
    simp [h1]
    exact_mod_cast h

/-- Möbius inversion of the resampled lattices isolates the single Gaussian at sqrt a. -/
theorem moebius_reconstruction {a : ℝ} (ha : 0 < a) :
    HasSum (fun d : ℕ+ ↦ (ArithmeticFunction.moebius d : ℝ) * sampled ((d : ℝ)^2 * a))
      (Real.exp (-Real.pi * a)) := by
  let F (ij : ℕ+ × ℕ+) := (ArithmeticFunction.moebius ij.1 : ℝ) *
    Real.exp (-Real.pi * ((ij.1 : ℝ)*(ij.2 : ℝ))^2 * a)
  have hF : Summable F := moebius_pairs_summable ha
  have row (d : ℕ+) : HasSum (fun j : ℕ+ ↦ F (d,j))
      ((ArithmeticFunction.moebius d : ℝ) * sampled ((d : ℝ)^2*a)) := by
    have hd : 0 < (d : ℝ) := by exact_mod_cast d.2
    apply ((positive_gaussian_hasSum (a := (d : ℝ)^2*a) (by positivity)).mul_left
      (ArithmeticFunction.moebius d : ℝ)).congr_fun
    intro j
    simp only [F]
    congr 2
    ring
  have fiber (n : ℕ+) :
      ∑' ij : (n : ℕ).divisorsAntidiagonal, F (divisorsAntidiagonalFactors n ij) =
      (if n = 1 then Real.exp (-Real.pi*a) else 0) := by
    rw [tsum_fintype, Finset.univ_eq_attach]
    calc
      _ = ∑ ij ∈ (n : ℕ).divisorsAntidiagonal,
            (ArithmeticFunction.moebius ij.1 : ℝ) * Real.exp (-Real.pi * (n : ℝ)^2*a) := by
        conv_rhs => rw [← Finset.sum_attach]
        apply Finset.sum_congr rfl
        intro ij _
        have he := divisorsAntidiagonalFactors_eq (n := n) ij
        have hr : (((divisorsAntidiagonalFactors n ij).1 : ℕ) : ℝ) *
            (((divisorsAntidiagonalFactors n ij).2 : ℕ) : ℝ) = (n : ℝ) := by
          rw [← Nat.cast_mul]
          exact congrArg (fun m : ℕ ↦ (m : ℝ)) he
        simp only [F, hr]
        rfl
      _ = _ := by rw [← Finset.sum_mul, moebius_fiber]; split_ifs with h <;> simp [*]
  have hSigma := sigmaAntidiagonalEquivProd.summable_iff.mpr hF
  have ht : ∑' ij, F ij = Real.exp (-Real.pi*a) := by
    rw [← sigmaAntidiagonalEquivProd.tsum_eq F]
    change ∑' q, (F ∘ sigmaAntidiagonalEquivProd) q = _
    rw [hSigma.tsum_sigma]
    change (∑' n : ℕ+, ∑' ij, F (divisorsAntidiagonalFactors n ij)) = _
    simp_rw [fiber]
    simp
  exact (ht ▸ hF.hasSum).prod_fiberwise row

end RHThroughEmergence.Reconstruction
