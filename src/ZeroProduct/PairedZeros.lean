import ZeroReconstruction
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! Reflection groups the divisor of Riemann xi into pairs, including multiplicities. -/

noncomputable section

open Complex MeasureTheory Filter
open scoped Topology

namespace RHThroughEmergence.ZeroReconstruction

abbrev XiIndex := Hadamard.divisorZeroIndex₀ riemannXi Set.univ
abbrev zeroAt (i : XiIndex) : ℂ := Hadamard.divisorZeroIndex₀_val i
abbrev UpperZero := {i : XiIndex // 0 < (zeroAt i).im}

private theorem xiAnalytic : AnalyticOnNhd ℂ riemannXi Set.univ :=
  fun z _ ↦ differentiable_riemannXi.analyticAt z

theorem zeroAt_is_zero (i : XiIndex) : riemannXi (zeroAt i) = 0 := by
  by_contra hn
  have h := Hadamard.divisorZeroIndex₀_val_mem_divisor_support i
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply xiAnalytic (Set.mem_univ _), analyticOrderAt_eq_zero.mpr (.inr hn)] at h
  simp at h

private theorem zeta_real_nonzero {x : ℝ} (hx : 1/2 ≤ x) (h1 : x < 1) :
    riemannZeta (x : ℂ) ≠ 0 := by
  have hdom : (x : ℂ) ∈ zetaAbelContinuationDomain :=
    ⟨by exact_mod_cast ne_of_lt h1, by change (1/10 : ℝ) < x; linarith⟩
  let J := ∫ u in Set.Ioi (1:ℝ), Int.fract u * u ^ (-x-1)
  have hJ : 0 ≤ J := integral_nonneg_of_ae <| by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
    exact mul_nonneg (Int.fract_nonneg _) (Real.rpow_nonneg (by linarith [Set.mem_Ioi.mp hu]) _)
  have he : (∫ u in Set.Ioi (1:ℝ), zetaAbelFractKernel (x:ℂ) u) = (J : ℂ) := by
    rw [show (J : ℂ) = ∫ u in Set.Ioi (1:ℝ), ((Int.fract u * u ^ (-x-1) : ℝ) : ℂ) from
      integral_ofReal.symm]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
    simp only [zetaAbelFractKernel, ofReal_mul, ofReal_cpow (by linarith [Set.mem_Ioi.mp hu] : 0 ≤ u), ofReal_sub, ofReal_neg, ofReal_one]
  rw [riemannZeta_eq_zetaAbelContinuationFormula _ hdom, zetaAbelContinuationFormula, he]
  have hr : 1 + 1 / (x - 1) - x * J < 0 := by
    have hdiv : 1 + 1 / (x - 1) = x / (x - 1) := by field_simp [ne_of_lt (sub_neg.mpr h1)]; ring
    rw [hdiv]
    exact sub_neg_of_lt (lt_of_lt_of_le (div_neg_of_pos_of_neg (by linarith) (by linarith)) (mul_nonneg (by linarith) hJ))
  exact_mod_cast ne_of_lt hr

private theorem index_im_ne_zero (i : XiIndex) : (zeroAt i).im ≠ 0 := by
  let z := zeroAt i
  have hz : riemannXi z = 0 := zeroAt_is_zero i
  have hz' := xi_zero_iff.mp hz
  intro him
  have hreal : (z.re : ℂ) = z := Complex.ext rfl (by simpa [z] using him.symm)
  by_cases hr : 1/2 ≤ z.re
  · exact zeta_real_nonzero hr hz'.2.1 (hreal ▸ hz'.2.2)
  · have hsym : riemannXi (1-z) = 0 := (riemannXi_one_sub z).trans hz
    have hz'' := xi_zero_iff.mp hsym
    have hre : ((1-z.re : ℝ) : ℂ) = 1-z := by push_cast; rw [hreal]
    apply zeta_real_nonzero (x := 1-z.re) (by linarith) (by linarith [hz'.1])
    rw [hre]
    exact hz''.2.2

private theorem divisor_reflect (z : ℂ) :
    MeromorphicOn.divisor riemannXi Set.univ z = MeromorphicOn.divisor riemannXi Set.univ (1-z) := by
  have h : analyticOrderAt riemannXi z = analyticOrderAt riemannXi (1-z) := by
    have hc := analyticOrderAt_comp_of_deriv_ne_zero (f := riemannXi) (g := fun w : ℂ ↦ 1-w)
      (z₀ := z) (by fun_prop) (by simp)
    simpa [Function.comp_def, riemannXi_one_sub] using hc
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply xiAnalytic (Set.mem_univ _), MeromorphicOn.AnalyticOnNhd.divisor_apply xiAnalytic (Set.mem_univ _), h]

private def reflectIndex (i : XiIndex) : XiIndex :=
  ⟨⟨1 - zeroAt i, i.val.2.cast (congrArg Int.toNat (divisor_reflect (zeroAt i)))⟩,
    sub_ne_zero.mpr (fun h ↦ index_im_ne_zero i (by rw [← h]; simp))⟩

@[simp] private theorem reflect_val (i : XiIndex) : zeroAt (reflectIndex i) = 1 - zeroAt i := rfl

@[simp] private theorem reflect_twice (i : XiIndex) : reflectIndex (reflectIndex i) = i := by
  apply Subtype.ext
  apply Sigma.ext (show 1 - (1-zeroAt i) = zeroAt i by ring)
  apply (Fin.heq_ext_iff (by change (MeromorphicOn.divisor riemannXi _ (1-(1-zeroAt i))).toNat = _; rw [sub_sub_cancel])).2
  rfl

private def pairIndex (j : UpperZero × Bool) : XiIndex :=
  if j.2 then reflectIndex j.1.val else j.1.val

private theorem below (i : UpperZero) : (zeroAt (reflectIndex i.val)).im < 0 := by
  simpa using i.property

private def pairEquiv : UpperZero × Bool ≃ XiIndex := Equiv.ofBijective pairIndex <| by
  constructor
  · rintro ⟨a, x⟩ ⟨b, y⟩ h
    cases x <;> cases y <;> simp [pairIndex] at h ⊢
    · exact Subtype.ext h
    · exact absurd (h ▸ a.property) (not_lt.mpr (below b).le)
    · exact absurd (h.symm ▸ b.property) (not_lt.mpr (below a).le)
    · exact Subtype.ext (by simpa using congrArg reflectIndex h)
  · intro i
    by_cases h : 0 < (zeroAt i).im
    · exact ⟨(⟨i,h⟩,false), rfl⟩
    · have hl : (zeroAt i).im < 0 := lt_of_le_of_ne (le_of_not_gt h) (index_im_ne_zero i)
      exact ⟨(⟨reflectIndex i, by simpa using hl⟩,true), reflect_twice i⟩

private def q (i : UpperZero) : ℂ := (zeroAt i.val * (1-zeroAt i.val))⁻¹

private theorem q_summable : Summable q := by
  let f : XiIndex → ℝ := fun i ↦ ‖zeroAt i‖⁻¹ ^ 2
  have hf : Summable f := summable_riemannXi_divisorZeroIndex₀_norm_inv_sq
  have ha := hf.comp_injective (Subtype.val_injective (p := fun i : XiIndex ↦ 0 < (zeroAt i).im))
  have inj : Function.Injective (fun i : UpperZero ↦ reflectIndex i.val) := by
    intro a b h; exact Subtype.ext (by simpa using congrArg reflectIndex h)
  have hb := hf.comp_injective inj
  apply (ha.add hb).of_norm_bounded
  intro i
  simp only [q, norm_inv, norm_mul, mul_inv, Function.comp_apply, f, reflect_val]
  nlinarith [sq_nonneg (‖zeroAt i.val‖⁻¹ - ‖1-zeroAt i.val‖⁻¹),
    sq_nonneg ‖zeroAt i.val‖⁻¹, sq_nonneg ‖1-zeroAt i.val‖⁻¹]

private def factor (s : ℂ) (i : UpperZero) := 1 - s*(1-s)*q i

private theorem factor_multipliable (s : ℂ) : Multipliable (factor s) := by
  change Multipliable (fun i : UpperZero ↦ 1 - s*(1-s)*q i)
  simpa [sub_eq_add_neg, neg_mul] using
    Complex.multipliable_one_add_of_summable (q_summable.mul_left (-(s*(1-s))))

private theorem canonical_pairs (s : ℂ) :
    HasProd (fun i : UpperZero ↦ factor s i * exp (s*q i)) (zeroProduct s) := by
  let F : XiIndex → ℂ := fun i ↦ (1-s/zeroAt i)*exp (s/zeroAt i)
  have hF : HasProd F (zeroProduct s) := zero_product_converges.hasProd (Set.mem_univ s)
  apply (pairEquiv.hasProd_iff.mpr hF).prod_fiberwise
  intro i
  convert! hasProd_fintype (fun b : Bool ↦ F (pairEquiv (i,b))) using 1
  change _ = ∏ b : Bool, F (pairIndex (i,b))
  rw [Fintype.prod_bool]
  simp only [F, pairIndex, Bool.false_eq_true, ite_false, ite_true, reflect_val]
  have h0 := i.val.property
  have h1 := (reflectIndex i.val).property
  change 1-zeroAt i.val ≠ 0 at h1
  dsimp [factor,q]
  rw [show s*(zeroAt i.val*(1-zeroAt i.val))⁻¹ = s/(1-zeroAt i.val) + s/zeroAt i.val by
    field_simp [h0,h1]; ring, exp_add]
  field_simp [h0,h1]
  ring

/-- The product over upper-half-plane zeros has one factor for each reflected pair.
The divisor index repeats each pair according to its analytic multiplicity. -/
theorem xi_paired_product (s : ℂ) :
    HasProd (fun i : UpperZero ↦ 1 - s*(1-s)/(zeroAt i.val*(1-zeroAt i.val))) (2*riemannXi s) := by
  let P := fun z : ℂ ↦ ∏' i, factor z i
  let Q := ∑' i, q i
  have hp (z : ℂ) : HasProd (factor z) (P z) := (factor_multipliable z).hasProd
  have hcanon (z : ℂ) : zeroProduct z = P z * exp (z*Q) :=
    (canonical_pairs z).unique ((hp z).mul ((q_summable.hasSum.mul_left z).cexp))
  obtain ⟨poly, hdegree, hfac⟩ := riemannXi_hadamard_factorization_no_monomial
  let C := poly.coeff 1 + Q
  have hconst : exp (poly.coeff 0) = 1/2 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero, Hadamard.divisorCanonicalProduct_zero, riemannXi_zero] using (hfac 0).symm
  have hz (z : ℂ) : riemannXi z = (1/2 : ℂ) * exp (C*z) * P z := by
    rw [hfac]
    change exp (poly.eval z) * zeroProduct z = _
    rw [hcanon, Polynomial.eq_X_add_C_of_degree_le_one hdegree]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    rw [exp_add]
    simp only [hconst]
    rw [show C*z = poly.coeff 1*z + z*Q by dsimp [C]; ring, exp_add, mul_comm (poly.coeff 1) z]
    ring
  have hsym (z : ℂ) : P (1-z) = P z := by
    apply tprod_congr
    intro i
    dsimp [factor]
    ring
  have h0 : riemannXi 0 ≠ 0 := by rw [riemannXi_zero]; norm_num
  have heq : (fun z : ℂ ↦ exp (C*z)) =ᶠ[nhds 0] (fun z ↦ exp (C*(1-z))) := by
    filter_upwards [differentiable_riemannXi.continuous.continuousAt.eventually_ne h0] with z hn
    have hP : P z ≠ 0 := fun h ↦ hn (by rw [hz, h, mul_zero])
    have eq := riemannXi_one_sub z
    rw [hz (1-z), hz z, hsym] at eq
    exact mul_left_cancel₀ (by norm_num : (1/2 : ℂ) ≠ 0) (mul_right_cancel₀ hP eq.symm)
  have hExp : exp C = 1 := by simpa using heq.eq_of_nhds.symm
  have d₁ := ((hasDerivAt_id (0 : ℂ)).const_mul C).cexp
  have d₂ := (((hasDerivAt_id (0 : ℂ)).const_sub 1).const_mul C).cexp
  have hd := (d₁.congr_of_eventuallyEq heq.symm).unique d₂
  simp [hExp] at hd
  have hC : C = 0 := by linear_combination hd / 2
  have hval : 2 * riemannXi s = P s := by rw [hz, hC]; ring_nf; simp
  rw [hval]
  exact (hp s).congr (fun i ↦ by simp [factor,q,div_eq_mul_inv])

end RHThroughEmergence.ZeroReconstruction

