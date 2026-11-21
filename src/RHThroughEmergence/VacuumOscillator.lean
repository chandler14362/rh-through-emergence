import Mathlib

/-! The oscillator vacuum and its dilation generator. The two reflected scale modes have eigenvalues ±½. -/

namespace RHThroughEmergence.VacuumOscillator

/-- The Gaussian ground state of the vacuum background, normalized at the origin. -/
noncomputable def gaussianGroundState (x : ℝ) : ℝ := Real.exp (-Real.pi * x ^ 2)

lemma hasDerivAt_gaussianGroundState (x : ℝ) : HasDerivAt gaussianGroundState ((-2 * Real.pi * x) * gaussianGroundState x) x := by
  have h := ((hasDerivAt_pow 2 x).const_mul (-Real.pi)).exp
  have hf : gaussianGroundState = fun y => Real.exp (-Real.pi * y ^ 2) := rfl
  rw [hf]
  convert h using 1
  simp
  ring

/-- **The vacuum background equation in oscillator coordinates is** `x φ + (1/2π) φ′ = 0`. -/
theorem vacuum_background_equation (x : ℝ) : x * gaussianGroundState x + (1 / (2 * Real.pi)) * deriv gaussianGroundState x = 0 := by
  have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
  rw [(hasDerivAt_gaussianGroundState x).deriv]
  field_simp
  ring

/-- **The slide is the anticommutator of the two odd generators:** `½(x∂ + ∂x) f = x f′ + ½ f`. -/
theorem slide_eq_anticommutator {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    (1 / 2) * (x * deriv f x + deriv (fun y => y * f y) x) = x * deriv f x + (1 / 2) * f x := by
  have h : deriv (fun y => y * f y) x = f x + x * deriv f x := by
    have := ((hasDerivAt_id x).mul hf.hasDerivAt).deriv
    simpa using this
  rw [h]
  ring

/-- **The slide's eigenmodes:** `(x∂ + ½) x^(−s) = (½ − s) x^(−s)` for `x > 0`. -/
theorem slide_eigen (s : ℝ) {x : ℝ} (hx : 0 < x) :
    x * deriv (fun y => y ^ (-s)) x + (1 / 2) * x ^ (-s) = (1 / 2 - s) * x ^ (-s) := by
  rw [Real.deriv_rpow_const (Or.inl hx.ne')]
  have h1 : x * x ^ (-s - 1) = x ^ (-s) := by
    have h := Real.rpow_add hx 1 (-s - 1)
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  calc x * (-s * x ^ (-s - 1)) + 1 / 2 * x ^ (-s) = -s * (x * x ^ (-s - 1)) + 1 / 2 * x ^ (-s) := by ring
    _ = (1 / 2 - s) * x ^ (-s) := by rw [h1]; ring

/-- The constant and reciprocal modes have eigenvalues `½` and `−½`.
Their scale factors give the two weights used to describe a particle pair collision. -/
theorem reflected_scale_modes {x : ℝ} (hx : 0 < x) :
    (x * deriv (fun y => y ^ (-(0 : ℝ))) x + (1 / 2) * x ^ (-(0 : ℝ)) = (1 / 2) * x ^ (-(0 : ℝ))) ∧
      (x * deriv (fun y => y ^ (-(1 : ℝ))) x + (1 / 2) * x ^ (-(1 : ℝ)) = -(1 / 2) * x ^ (-(1 : ℝ))) := by
  constructor
  · rw [slide_eigen 0 hx]; ring
  · rw [slide_eigen 1 hx]; ring

/-- The derivative of the constant mode 1 vanishes. -/
theorem deriv_constant_mode (x : ℝ) : deriv (fun _ : ℝ => (1 : ℝ)) x = 0 := deriv_const x 1

/-- The even Taylor modes of the Gaussian ground state satisfy `(x∂ + ½) x^(2k) = (2k + ½) x^(2k)` (`s = −2k`). -/
theorem floor_mode (k : ℕ) {x : ℝ} (hx : 0 < x) :
    x * deriv (fun y => y ^ (2 * (k : ℝ))) x + (1 / 2) * x ^ (2 * (k : ℝ)) = (2 * k + 1 / 2) * x ^ (2 * (k : ℝ)) := by
  have h := slide_eigen (-(2 * (k : ℝ))) hx
  simp only [neg_neg] at h
  rw [h]
  ring

/-- **The fold reverses the slide:** the eigenvalue at `1 − s` is minus the eigenvalue at `s`. -/
theorem fold_reverses_slide (s : ℝ) : (1 / 2 - (1 - s)) = -(1 / 2 - s) := by ring

/-- The oscillator equation and one initial value determine the vacuum on the whole real line. -/
theorem vacuum_background_unique {f : ℝ → ℝ} (hf : Differentiable ℝ f) (h₀ : f 0 = 1)
    (hA : ∀ x, deriv f x + 2 * Real.pi * x * f x = 0) : f = gaussianGroundState := by
  let ratio := fun x ↦ f x / gaussianGroundState x
  have hpos (x : ℝ) : 0 < gaussianGroundState x := Real.exp_pos _
  have hd (x : ℝ) : HasDerivAt ratio 0 x := by
    convert (hf x).hasDerivAt.div (hasDerivAt_gaussianGroundState x) (hpos x).ne' using 1
    rw [show deriv f x = -2 * Real.pi * x * f x by linarith [hA x]]
    ring
  funext x
  have hc : ratio x = ratio 0 := by
    apply is_const_of_deriv_eq_zero (fun y ↦ (hd y).differentiableAt) (fun y ↦ (hd y).deriv)
  have hr : f x / gaussianGroundState x = 1 := by simpa [ratio, gaussianGroundState, h₀] using hc
  simpa using (div_eq_iff (hpos x).ne').mp hr

/-- The reciprocal fold on the positive real axis. -/
noncomputable def fold (f : ℝ → ℝ) (x : ℝ) : ℝ := x⁻¹ * f x⁻¹

theorem fold_fold (f : ℝ → ℝ) {x : ℝ} (hx : x ≠ 0) : fold (fold f) x = f x := by
  unfold fold
  rw [inv_inv, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]

theorem fold_mode (s : ℝ) {x : ℝ} (hx : 0 < x) :
    fold (fun y ↦ y ^ (-s)) x = x ^ (-(1 - s)) := by
  have h : x⁻¹ ^ (-s) = x ^ s := by rw [Real.inv_rpow hx.le, Real.rpow_neg hx.le, inv_inv]
  simp only [fold]
  rw [h, ← Real.rpow_neg_one x, ← Real.rpow_add hx]
  congr 1
  ring

/-- On twice differentiable functions, the even oscillator commutator is four times H. -/
theorem oscillator_commutator {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f)) (x : ℝ) :
    deriv (deriv (fun y ↦ y ^ 2 * f y)) x - x ^ 2 * deriv (deriv f) x =
      4 * (x * deriv f x + (1 / 2) * f x) := by
  have hfirst : deriv (fun y ↦ y ^ 2 * f y) = fun y ↦ 2 * y * f y + y ^ 2 * deriv f y := by
    funext y
    simpa using ((hasDerivAt_pow 2 y).mul (hf y).hasDerivAt).deriv
  rw [hfirst]
  have h := ((((hasDerivAt_id x).const_mul 2).mul (hf x).hasDerivAt).add
    ((hasDerivAt_pow 2 x).mul (hf' x).hasDerivAt)).deriv
  change deriv (fun y ↦ 2 * y * f y + y ^ 2 * deriv f y) x = _ at h
  rw [h]
  simp only [id_eq]
  ring

/-- Differentiating the normalized dilation at depth zero gives H. -/
theorem dilation_generator {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun u : ℝ ↦ Real.exp (u / 2) * f (Real.exp u * x))
      (x * deriv f x + (1 / 2) * f x) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).div_const 2).exp).mul
    ((show HasDerivAt f (deriv f x) (Real.exp 0 * x) by simpa using hf.hasDerivAt).comp 0
      ((Real.hasDerivAt_exp 0).mul_const x))
  convert h using 1
  simp
  ring

/-- Reciprocal folding of the complex Mellin mode at positive real position. -/
theorem fold_complex_mode (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ)⁻¹ * (↑(x⁻¹) : ℂ) ^ (-s) = (x : ℂ) ^ (-(1 - s)) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm),
    Complex.cpow_neg, inv_inv, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ (by exact_mod_cast hx.ne')]
  congr 1
  ring

end RHThroughEmergence.VacuumOscillator
