import RHThroughEmergence.Minkowski

/-! Compare the additive prime-power clocks and the multiplicative prime exponents
at an integer address, then read the two reflected spectral radii at that address. -/

namespace RHThroughEmergence.TorusClocks

noncomputable section

/-- The additive clock of period p^k is home exactly for the powers listed by
the multiplicative address. The two input addresses can be chosen independently. -/
def addressesAgree (n m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k : ℕ, n % (p ^ k) = 0 ↔ k ≤ m.factorization p

theorem addressesAgree_iff {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    addressesAgree n m ↔ n = m := by
  have home (p : ℕ) (hp : p.Prime) (k : ℕ) :
      n % (p ^ k) = 0 ↔ k ≤ n.factorization p := by
    rw [← Nat.dvd_iff_mod_eq_zero, hp.pow_dvd_iff_le_factorization hn.ne']
  constructor
  · intro h
    have hf : n.factorization = m.factorization := by
      ext p
      by_cases hp : p.Prime
      · have cut (k : ℕ) : k ≤ n.factorization p ↔ k ≤ m.factorization p :=
          (home p hp k).symm.trans (h p hp k)
        exact le_antisymm ((cut _).mp le_rfl) ((cut _).mpr le_rfl)
      · simp [Nat.factorization_eq_zero_of_non_prime _ hp]
    calc
      n = n.factorization.prod (· ^ ·) := (Nat.factorization_prod_pow_eq_self hn.ne').symm
      _ = m.factorization.prod (· ^ ·) := by rw [hf]
      _ = m := Nat.factorization_prod_pow_eq_self hm.ne'
  · rintro rfl
    exact home

/-- Each additive period q at home contributes Λ(q), equal to log p for q=p^k. -/
def additiveRadius (n : ℕ) (σ : ℝ) : ℝ :=
  Real.exp ((σ - 1 / 2) * ∑ q ∈ n.divisors, ArithmeticFunction.vonMangoldt q)

/-- Each multiplicative clock contributes its prime log once per factor. -/
def multiplicativeRadius (n : ℕ) (σ : ℝ) : ℝ :=
  Real.exp ((1 / 2 - σ) * n.factorization.sum (fun p k ↦ (k : ℝ) * Real.log p))

/-- The two arithmetic clock sums give the existing vacuum-normalized mode magnitudes. -/
theorem radii_eq_reflectedPair {n : ℕ} (hn : 0 < n) (s : ℂ) :
    (additiveRadius n s.re, multiplicativeRadius n s.re) = Minkowski.reflectedPair s n := by
  rw [Minkowski.reflectedPair_eq_boost s (by exact_mod_cast hn)]
  simp only [additiveRadius, multiplicativeRadius, ArithmeticFunction.vonMangoldt_sum,
    ← Real.log_nat_eq_sum_factorization, Minkowski.boost, mul_one, ← neg_mul, neg_sub]

theorem radii_eq_iff {n : ℕ} (hn : 1 < n) (σ : ℝ) :
    additiveRadius n σ = multiplicativeRadius n σ ↔ σ = 1 / 2 := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  simp only [additiveRadius, multiplicativeRadius, ArithmeticFunction.vonMangoldt_sum,
    ← Real.log_nat_eq_sum_factorization, Real.exp_eq_exp]
  rw [mul_left_inj' hlog.ne']
  constructor <;> intro h <;> linarith

/-- At addresses above the unit scale, matching clock addresses and matching reflected radii select
exactly one multiplicative address and one real part. -/
theorem contact_iff {n m : ℕ} (hn : 1 < n) (hm : 0 < m) (σ : ℝ) :
    (addressesAgree n m ∧ additiveRadius n σ = multiplicativeRadius m σ) ↔
      n = m ∧ σ = 1 / 2 := by
  rw [addressesAgree_iff (by omega) hm]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, (radii_eq_iff hn σ).mp h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, (radii_eq_iff hn σ).mpr h⟩

/-- In the common (real part, normalized radius) plane, the intersection
of the two graphs at every address greater than 1 is the same singleton. -/
theorem radial_graph_intersection {n : ℕ} (hn : 1 < n) :
    {z : ℝ × ℝ | z.2 = additiveRadius n z.1} ∩
      {z : ℝ × ℝ | z.2 = multiplicativeRadius n z.1} = {((1 / 2, 1) : ℝ × ℝ)} := by
  ext ⟨σ, r⟩
  change (r = additiveRadius n σ ∧ r = multiplicativeRadius n σ) ↔ (σ, r) = (1 / 2, 1)
  constructor
  · rintro ⟨ha, hm⟩
    have hs := (radii_eq_iff hn σ).mp (ha.symm.trans hm)
    subst σ
    simpa [additiveRadius] using congrArg (fun a : ℝ ↦ ((1 / 2 : ℝ), a)) ha
  · intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp [additiveRadius, multiplicativeRadius]

/-- Retaining the imaginary coordinate lifts the singleton radial contact to the
whole critical line at unit radius. -/
theorem spectral_graph_intersection {n : ℕ} (hn : 1 < n) :
    {z : ℂ × ℝ | z.2 = additiveRadius n z.1.re} ∩
      {z : ℂ × ℝ | z.2 = multiplicativeRadius n z.1.re} =
      {z : ℂ × ℝ | z.1.re = 1 / 2 ∧ z.2 = 1} := by
  ext ⟨s, r⟩
  have h := Set.ext_iff.mp (radial_graph_intersection hn) (s.re, r)
  change (_ ∧ _) ↔ (s.re, r) = ((1 / 2, 1) : ℝ × ℝ) at h
  change (_ ∧ _) ↔ s.re = 1 / 2 ∧ r = 1
  simpa only [Prod.mk.injEq] using h

/-- At unit scale both radii are one for every spectral real part. -/
theorem radii_at_one (σ : ℝ) :
    additiveRadius 1 σ = 1 ∧ multiplicativeRadius 1 σ = 1 := by
  simp [additiveRadius, multiplicativeRadius]

/-- Rotation by angle t log x. The original mode uses -t, the reflected mode +t. -/
def phase (x t : ℝ) : ℂ := Complex.exp (((t * Real.log x : ℝ) : ℂ) * Complex.I)

theorem phase_unit (x t : ℝ) : ‖phase x t‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem phase_conj (x t : ℝ) : star (phase x t) = phase x (-t) := by
  simp [phase, ← Complex.exp_conj, neg_mul]

/-- At a prime step the angle changes by t log p; the same law holds for any positive factor. -/
theorem phase_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    phase (x * y) t = phase x t * phase y t := by
  simp [phase, Real.log_mul hx.ne' hy.ne', mul_add, add_mul, Complex.exp_add]

/-- Prime exponents determine the entire rotation at an integer address. -/
theorem phase_prime_product (n : ℕ) (t : ℝ) :
    phase n t = n.factorization.prod (fun p k ↦ phase p t ^ k) := by
  unfold phase
  rw [Real.log_nat_eq_sum_factorization]
  simp only [Finsupp.sum, Finsupp.prod, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul,
    Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro p _
  rw [← Complex.exp_nat_mul]
  push_cast
  congr 1
  ring

/-- The two actual complex powers, normalized by the vacuum magnitude, retain opposite phases. -/
theorem normalized_modes_on_line {x : ℝ} (hx : 0 < x) (t : ℝ) :
    let s : ℂ := 1 / 2 + (t : ℂ) * Complex.I
    (Real.sqrt x * (x : ℂ) ^ (-s), Real.sqrt x * (x : ℂ) ^ (-(1-s))) =
      (phase x (-t), phase x t) := by
  have hroot : (Real.sqrt x : ℂ) = Complex.exp ((Real.log x : ℂ) / 2) := by
    calc
      _ = ((Real.exp (Real.log x / 2) : ℝ) : ℂ) := by
        rw [← Real.log_sqrt hx.le, Real.exp_log (Real.sqrt_pos.2 hx)]
      _ = _ := by push_cast; rfl
  dsimp only
  rw [hroot, Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le,
    ← Complex.exp_add, ← Complex.exp_add]
  unfold phase
  push_cast
  congr 2 <;> ring

end

end RHThroughEmergence.TorusClocks
