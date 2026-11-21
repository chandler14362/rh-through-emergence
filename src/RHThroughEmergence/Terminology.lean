import RHThroughEmergence.VacuumOscillator
import RHThroughEmergence.Minkowski

/-! The real background profile, the number-line tree and the local depth of a pair collision. -/

namespace RHThroughEmergence

/-- The real-coordinate profile of the vacuum background. -/
noncomputable def vacuumBackgroundProfile : ℝ → ℝ := VacuumOscillator.gaussianGroundState

/-- The real vacuum background profile satisfies the oscillator equation with unit value at the origin. -/
theorem vacuumBackgroundProfile_equation :
    (∀ x : ℝ, deriv vacuumBackgroundProfile x + 2 * Real.pi * x * vacuumBackgroundProfile x = 0) ∧
      vacuumBackgroundProfile 0 = 1 := by
  constructor
  · intro x
    unfold vacuumBackgroundProfile
    rw [(VacuumOscillator.hasDerivAt_gaussianGroundState x).deriv]
    ring
  · simp [vacuumBackgroundProfile, VacuumOscillator.gaussianGroundState]

/-- The address reached from 1 along a chain reaction path. Each bit chooses the even or odd child. -/
def chainReactionAddress (path : List Bool) : ℕ+ :=
  path.foldl (fun n bit ↦ if bit then 2 * n + 1 else 2 * n) 1

theorem chainReactionAddress_append_bit (path : List Bool) (bit : Bool) :
    chainReactionAddress (path ++ [bit]) =
      if bit then 2 * chainReactionAddress path + 1 else 2 * chainReactionAddress path := by
  simp [chainReactionAddress, List.foldl_append]

/-- The addresses of the two first-generation participants. -/
def birthPair : ℕ+ × ℕ+ := (chainReactionAddress [false], chainReactionAddress [true])

theorem birthPair_addresses : birthPair = (2, 3) := by decide

/-- A specified contact between two participants on the number line, at a chosen global depth. -/
structure ParticlePairCollision where
  participants : ℕ+ × ℕ+
  depth : ℝ

/-- The birth pair provides the initial contact and the origin for global depth. -/
def initialParticlePairCollision : ParticlePairCollision := ⟨birthPair, 0⟩

namespace ParticlePairCollision

/-- The two reflected weights at global depth `u`, measured relative to this contact. -/
noncomputable def weightsAt (contact : ParticlePairCollision) (u : ℝ) : ℝ × ℝ :=
  Minkowski.boost ((u - contact.depth) / 2) (1, 1)

theorem weightsAt_contact (contact : ParticlePairCollision) :
    contact.weightsAt contact.depth = (1, 1) := by
  simp [weightsAt, Minkowski.boost]

theorem weightsAt_equal_iff (contact : ParticlePairCollision) (u : ℝ) :
    (contact.weightsAt u).1 = (contact.weightsAt u).2 ↔ u = contact.depth := by
  simp only [weightsAt, Minkowski.boost, mul_one, Real.exp_eq_exp]
  constructor <;> intro h <;> linarith

theorem weightsAt_sum (contact : ParticlePairCollision) (u : ℝ) :
    (contact.weightsAt u).1 + (contact.weightsAt u).2 =
      2 * Real.cosh ((u - contact.depth) / 2) := by
  simp only [weightsAt, Minkowski.boost, mul_one, Real.cosh_eq]
  ring

end ParticlePairCollision

/-- The birth pair makes its initial contact at depth zero, where both reflected weights are one. -/
theorem initialParticlePairCollision_contact :
    initialParticlePairCollision.participants = birthPair ∧ initialParticlePairCollision.depth = 0 ∧
      initialParticlePairCollision.weightsAt 0 = (1, 1) :=
  ⟨rfl, rfl, initialParticlePairCollision.weightsAt_contact⟩

/-- Read the address backwards, dropping its final binary digit until reaching 1. -/
private def pathTo (n : ℕ) : List Bool :=
  if n ≤ 1 then [] else pathTo (n / 2) ++ [decide (n % 2 = 1)]
termination_by n
decreasing_by omega

private theorem address_append (path : List Bool) (bit : Bool) :
    (chainReactionAddress (path ++ [bit]) : ℕ) = 2 * (chainReactionAddress path : ℕ) + bit.toNat := by
  rw [chainReactionAddress_append_bit]
  cases bit <;> rfl

private theorem address_of_pathTo (n : ℕ) (hn : 0 < n) :
    (chainReactionAddress (pathTo n) : ℕ) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n ≤ 1
    · obtain rfl : n = 1 := by omega
      rw [pathTo]
      rfl
    · rw [pathTo, if_neg h, address_append, ih (n / 2) (by omega) (by omega)]
      by_cases hodd : n % 2 = 1 <;> simp [hodd] <;> omega

private theorem pathTo_address (path : List Bool) : pathTo (chainReactionAddress path) = path := by
  induction path using List.reverseRecOn with
  | nil => rw [show (chainReactionAddress [] : ℕ) = 1 from rfl, pathTo]; rfl
  | append_singleton path bit ih =>
    have hp : 0 < (chainReactionAddress path : ℕ) := (chainReactionAddress path).property
    have hlarge : ¬2 * (chainReactionAddress path : ℕ) + bit.toNat ≤ 1 := by omega
    rw [address_append, pathTo, if_neg hlarge]
    rw [show (2 * (chainReactionAddress path : ℕ) + bit.toNat) / 2 = chainReactionAddress path by
      cases bit <;> simp
      omega, ih]
    cases bit <;> simp [Nat.add_mod]

/-- The finite binary paths from 1 enumerate every positive address exactly once. -/
theorem chainReactionAddress_bijective : Function.Bijective chainReactionAddress := by
  constructor
  · intro a b h
    simpa only [pathTo_address] using congrArg (fun n : ℕ+ ↦ pathTo n) h
  · intro n
    exact ⟨pathTo n, Subtype.ext (address_of_pathTo n n.property)⟩

end RHThroughEmergence
