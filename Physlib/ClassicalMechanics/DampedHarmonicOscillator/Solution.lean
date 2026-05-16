/-
Copyright (c) 2026 Benedikt Fauseweh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benedikt Fauseweh
-/
module

public import Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
/-!

# Solutions to the Damped Harmonic Oscillator

## i. Overview

In this module we define the solutions to the damped harmonic oscillator (DHO) for each of the
three damping regimes, prove that they satisfy the equation of motion, and study their
energy and special geometric properties.

The equation of motion is

    m ẍ + γ ẋ + k x = 0,

where `x : Time → ℝ`, and the solutions are expressed in terms of the two derived quantities

    β  := γ / (2 m)       (decay rate / half-damping)
    ω₀ := √(k / m)        (natural angular frequency)

The three cases are determined by the sign of the discriminant γ² - 4mk, or equivalently
by the sign of β² - ω₀²:

- **Underdamped** (β² < ω₀²):
    x(t) = e^(−β t) [x₀ cos(ω₁ t) + c/ω₁ sin(ω₁ t)],
  where  ω₁ := √(ω₀² − β²)  and  c := v₀ + β x₀.

- **Critically damped** (β² = ω₀²):
    x(t) = e^(−β t) [x₀ + c t],
  where  c := v₀ + β x₀.

- **Overdamped** (β² > ω₀²):
    x(t) = e^(−β t) [x₀ cosh(β₁ t) + c/β₁ sinh(β₁ t)],
  where  β₁ := √(β² − ω₀²)  and  c := v₀ + β x₀.

## ii. Key results

- `InitialConditions`: structure with initial position `x₀ : ℝ` and velocity `v₀ : ℝ`.
- `trajectoryUnderdamped / trajectoryCritical / trajectoryOverdamped`: the three solution
  families parametrised by `InitialConditions`.
- `trajectory*_equationOfMotion`: each trajectory satisfies the DHO equation of motion.
- `trajectory*_energy_at_zero`: the initial energy equals `½ m v₀² + ½ k x₀²`.
- `trajectory*_energy_nonneg`: the energy is non-negative at all times.
- Special-points results: amplitude envelope (underdamped), at-most-one-zero
  (critically/overdamped).

## iii. Table of contents

- A. The initial conditions
  - A.1. Definition of the initial conditions
    - A.1.1. Extensionality lemma
  - A.2. The zero initial conditions
    - A.2.1. Simple results for the zero initial conditions
- B. Case-specific auxiliary quantities
  - B.1. Underdamped: the damped angular frequency ω₁
  - B.2. Overdamped: the auxiliary rate β₁
- C. Trajectories
  - C.1. Underdamped trajectory
  - C.2. Critically damped trajectory
  - C.3. Overdamped trajectory
- D. Uniqueness
  - D.1. Underdamped uniqueness
  - D.2. Critically damped uniqueness
  - D.3. Overdamped uniqueness
- E. Energy of the trajectories
  - E.1. Initial energy
  - E.2. Non-negativity of energy
- F. Special points in the trajectories
  - F.1. Underdamped: amplitude envelope
  - F.2. Critically damped: at most one positive zero
  - F.3. Overdamped: at most one positive zero

## iv. References

- Landau & Lifshitz, Mechanics, §25 (page 76).
- Goldstein, Classical Mechanics, Chapter 2.

-/

@[expose] public section

namespace ClassicalMechanics
open Real Time ContDiff

namespace DampedHarmonicOscillator

variable (S : DampedHarmonicOscillator)

/-!
## A. The initial conditions

The initial conditions specify the position `x₀` and the velocity `v₀` at time `t = 0`.

-/

/-!

### A.1. Definition of the initial conditions

-/

/-- Initial conditions for the damped harmonic oscillator:
  an initial position `x₀ : ℝ` and an initial velocity `v₀ : ℝ`. -/
@[ext] structure InitialConditions where
  /-- The initial position of the harmonic oscillator. -/
  x₀ : EuclideanSpace ℝ (Fin 1)
  /-- The initial velocity of the harmonic oscillator. -/
  v₀ : EuclideanSpace ℝ (Fin 1)

/-!
### A.2. The zero initial conditions

-/

namespace InitialConditions

/-- The zero initial condition (particle at rest at the origin). -/
instance : Zero InitialConditions := ⟨0, 0⟩

/-!

#### A.2.1. Simple results for the zero initial conditions

-/

@[simp]
lemma x₀_zero : x₀ 0 = 0 := rfl

@[simp]
lemma v₀_zero : v₀ 0 = 0 := rfl

end InitialConditions

TODO "Implement `InitialConditionsAtTime` for the damped harmonic oscillator:
  specify position and velocity at an arbitrary time t₀ and convert to the standard form."

/-!

## B. Case-specific auxiliary quantities

-/

/-!

### B.1. Underdamped: damped angular frequency ω₁

When `S.IsUnderdamped` (equivalently β² < ω₀²), the quantity
    ω₁ := √(ω₀² − β²) > 0
is the frequency of oscillation of the damped solution.

-/

/-- The damped angular frequency ω₁ = √(ω₀² − β²), defined when the system is underdamped. -/
noncomputable def ω₁ (hS : S.IsUnderdamped) : ℝ :=
  √(S.ω₀ ^ 2 - S.β ^ 2)


/-- The damped angular frequency ω₁ is positive in the underdamped case. -/
lemma ω₁_pos (hS : S.IsUnderdamped) : 0 < S.ω₁ hS := by
  unfold ω₁
  suffices h' : 0 < S.ω₀ ^ 2 - S.β ^ 2 by positivity
  suffices h2' : 0 > 4 * S.m ^ 2 * (S.β ^ 2 - S.ω₀ ^ 2) by nlinarith
  rw [← S.discriminant_eq]
  exact hS

/-- The square of ω₁ equals ω₀² − β². -/
lemma ω₁_sq (hS : S.IsUnderdamped) : S.ω₁ hS ^ 2 = S.ω₀ ^ 2 - S.β ^ 2 := by
  unfold ω₁
  rw [Real.sq_sqrt]
  suffices h2' : 0 > 4 * S.m ^ 2 * (S.β ^ 2 - S.ω₀ ^ 2) by nlinarith
  rw [← S.discriminant_eq]
  exact hS

--/-- ω₁ is non-zero in the underdamped case. -/
--lemma ω₁_ne_zero (hS : S.IsUnderdamped) : S.ω₁ hS ≠ 0 :=
--  Ne.symm (ne_of_lt (S.ω₁_pos hS))
--

/-!

### B.2. Overdamped: auxiliary rate β₁

When `S.IsOverdamped` (equivalently β² > ω₀²), the quantity
    β₁ := √(β² − ω₀²) > 0
controls the two exponential decay rates of the overdamped solution.

-/

/-- The auxiliary rate β₁ = √(β² − ω₀²), defined when the system is overdamped. -/
noncomputable def β₁ (hS : S.IsOverdamped) : ℝ :=
  √(S.β ^ 2 - S.ω₀ ^ 2)

/-- β₁ is positive in the overdamped case. -/
lemma β₁_pos (hS : S.IsOverdamped) : 0 < S.β₁ hS := by
  apply Real.sqrt_pos.mpr
  have := S.discriminant_eq
  unfold IsOverdamped at hS
  nlinarith [S.m_pos]

/-- The square of β₁ equals β² − ω₀². -/
lemma β₁_sq (hS : S.IsOverdamped) : S.β₁ hS ^ 2 = S.β ^ 2 - S.ω₀ ^ 2 := by
  apply Real.sq_sqrt
  have := S.discriminant_eq
  simp only [IsOverdamped] at hS
  nlinarith [S.m_pos]

/-- β₁ is non-zero in the overdamped case. -/
lemma β₁_ne_zero (hS : S.IsOverdamped) : S.β₁ hS ≠ 0 :=
  Ne.symm (ne_of_lt (S.β₁_pos hS))

/-!

## C. Trajectories

For each damping regime we define the corresponding solution family and establish its
key properties: smoothness, velocity, acceleration, recovery of initial conditions,
and satisfaction of the equation of motion.

We use the shorthand `c := v₀ + β x₀` throughout (the "shifted" initial velocity).

-/

namespace InitialConditions

variable (IC : InitialConditions)

/-!

### C.1. Underdamped trajectory

Solution formula:
    x(t) = e^(−β t) [x₀ cos(ω₁ t) + c/ω₁ sin(ω₁ t)],
where c = v₀ + β x₀.

-/

/-- The solution trajectory for the underdamped damped harmonic oscillator.

  Given initial conditions `IC`, the solution is
      x(t) = exp(−β t) · (x₀ · cos(ω₁ t) + (v₀ + β x₀)/ω₁ · sin(ω₁ t)). -/

noncomputable def trajectoryUnderdamped (hS : S.IsUnderdamped) : Time → EuclideanSpace ℝ (Fin 1)
  := fun (t : Time) =>
  Real.exp (- S.β * t) • (cos (S.ω₁ hS * t) • IC.x₀  +
    (sin (S.ω₁ hS * t) / S.ω₁ hS) • (IC.v₀ + S.β • IC.x₀))

lemma trajectoryUnderdamped_eq (hS : S.IsUnderdamped) :
    IC.trajectoryUnderdamped S hS =
    fun (t : Time) => Real.exp (- S.β * t) • (cos (S.ω₁ hS * t) • IC.x₀  +
    (sin (S.ω₁ hS * t) / S.ω₁ hS) • (IC.v₀ + S.β • IC.x₀)) := rfl

/-!

# Smoothness

-/
@[fun_prop]
lemma trajectoryUnderdamped_contDiff (hS : S.IsUnderdamped) :
    ContDiff ℝ ∞ (IC.trajectoryUnderdamped S hS) := by
    rw [trajectoryUnderdamped_eq]
    have hval : ContDiff ℝ ∞ (Time.val : Time → ℝ) := Time.toRealCLM.contDiff
    fun_prop [Time.toRealCLM.contDiff]

/-!

#### C.1.3. Velocity

-/

/-- The velocity of the underdamped trajectory.

    ẋ(t) = e^(−β t) · (v₀ · cos(ω₁ t) − (ω₀² x₀ + β v₀)/ω₁ · sin(ω₁ t)). -/
lemma trajectoryUnderdamped_velocity (hS : S.IsUnderdamped) :
  ∂ₜ (IC.trajectoryUnderdamped S hS) = fun (t : Time) =>
     Real.exp (- S.β * ↑t) • (cos (S.ω₁ hS * ↑t) • IC.v₀ -
      (sin (S.ω₁ hS * ↑t) / (S.ω₁ hS)) • (S.ω₀ ^ 2 • IC.x₀ + S.β • IC.v₀)) := by
  unfold trajectoryUnderdamped
  funext t
  rw [Time.deriv]







  sorry

/-!

#### C.1.4. Acceleration

-/

/-- The acceleration of the underdamped trajectory.

    ẍ(t) = e^(−β t) · (−(ω₀² x₀ + 2β v₀) · cos(ω₁ t)
             + (β ω₀² x₀ + v₀ (2β²−ω₀²))/ω₁ · sin(ω₁ t)). -/
lemma trajectoryUnderdamped_acceleration (hS : S.IsUnderdamped) :
    ∂ₜ (∂ₜ (IC.trajectoryUnderdamped S hS)) = fun (t : Time) =>
      Real.exp (- S.β * ↑t) *
        ((-(S.ω₀ ^ 2 * IC.x₀) - 2 * S.β * IC.v₀) * cos (S.ω₁ hS * ↑t) +
         (S.β * S.ω₀ ^ 2 * IC.x₀ + IC.v₀ * (2 * S.β ^ 2 - S.ω₀ ^ 2)) / S.ω₁ hS *
           sin (S.ω₁ hS * ↑t)) := by
  sorry

/-!

#### C.1.5. Initial conditions recovery

-/

/-- The underdamped trajectory starts at the initial position `x₀`. -/
@[simp]
lemma trajectoryUnderdamped_at_zero (hS : S.IsUnderdamped) :
    IC.trajectoryUnderdamped S hS 0 = IC.x₀ := by
  simp [trajectoryUnderdamped_eq]

/-- The velocity of the underdamped trajectory at `t = 0` equals the initial velocity `v₀`. -/
@[simp]
lemma trajectoryUnderdamped_velocity_at_zero (hS : S.IsUnderdamped) :
    ∂ₜ (IC.trajectoryUnderdamped S hS) 0 = IC.v₀ := by
  rw [trajectoryUnderdamped_velocity]
  simp

/-!

#### C.1.6. Equation of motion

-/

/-- The underdamped trajectory satisfies the damped harmonic oscillator equation of motion. -/
lemma trajectoryUnderdamped_equationOfMotion (hS : S.IsUnderdamped) :
    S.EquationOfMotion (IC.trajectoryUnderdamped S hS) := by
  -- Key identities: γ = 2mβ, k = mω₀²
  have hβ : S.γ = 2 * S.m * S.β := by rw [β]; field_simp
  have hkm : S.k = S.m * S.ω₀ ^ 2 := by rw [ω₀_sq]; field_simp
  intro t
  have hv := congr_fun (IC.trajectoryUnderdamped_velocity S hS) t
  have ha := congr_fun (IC.trajectoryUnderdamped_acceleration S hS) t
  have hx := congr_fun (IC.trajectoryUnderdamped_eq S hS) t
  simp only at hv ha hx
  rw [hv, ha, hx, hβ, hkm]
  field_simp [S.ω₁_ne_zero hS]
  ring

/-!

### C.2. Critically damped trajectory

Solution formula:
    x(t) = e^(−β t) · (x₀ + c t),
where c = v₀ + β x₀.

-/

/-!

#### C.2.1. Definition

-/

/-- The solution trajectory for the critically damped harmonic oscillator.

  Given initial conditions `IC`, the solution is
      x(t) = exp(−β t) · (x₀ + (v₀ + β x₀) · t). -/
noncomputable def trajectoryCritical (hS : S.IsCriticallyDamped) : Time → ℝ := fun (t : Time) =>
  Real.exp (- S.β * ↑t) * (IC.x₀ + (IC.v₀ + S.β * IC.x₀) * ↑t)

lemma trajectoryCritical_eq (hS : S.IsCriticallyDamped) :
    IC.trajectoryCritical S hS =
    fun (t : Time) => Real.exp (- S.β * ↑t) * (IC.x₀ + (IC.v₀ + S.β * IC.x₀) * ↑t) := rfl

/-!

#### C.2.2. Smoothness

-/

@[fun_prop]
lemma trajectoryCritical_contDiff (hS : S.IsCriticallyDamped) :
    ContDiff ℝ ∞ (IC.trajectoryCritical S hS) := by
  rw [trajectoryCritical_eq]
  have hval : ContDiff ℝ ∞ (Time.val : Time → ℝ) := Time.toRealCLM.contDiff
  apply ContDiff.mul
  · exact Real.contDiff_exp.comp (ContDiff.mul contDiff_const hval)
  · exact ContDiff.add contDiff_const (ContDiff.mul contDiff_const hval)

/-!

#### C.2.3. Velocity

-/

/-- The velocity of the critically damped trajectory.

    ẋ(t) = e^(−β t) · (v₀ − β (v₀ + β x₀) t − β x₀ + (v₀ + β x₀))
         = e^(−β t) · (v₀ + c (1 − β t))    where c = v₀ + β x₀. -/
lemma trajectoryCritical_velocity (hS : S.IsCriticallyDamped) :
    ∂ₜ (IC.trajectoryCritical S hS) = fun (t : Time) =>
      Real.exp (- S.β * ↑t) * (IC.v₀ - S.β * (IC.v₀ + S.β * IC.x₀) * ↑t) := by
  sorry

/-!

#### C.2.4. Acceleration

-/

/-- The acceleration of the critically damped trajectory.

    ẍ(t) = e^(−β t) · (β² c t − 2β v₀ − β² x₀),   where c = v₀ + β x₀. -/
lemma trajectoryCritical_acceleration (hS : S.IsCriticallyDamped) :
    ∂ₜ (∂ₜ (IC.trajectoryCritical S hS)) = fun (t : Time) =>
      Real.exp (- S.β * ↑t) *
        (S.β ^ 2 * (IC.v₀ + S.β * IC.x₀) * ↑t - 2 * S.β * IC.v₀ - S.β ^ 2 * IC.x₀) := by
  sorry

/-!

#### C.2.5. Initial conditions recovery

-/

/-- The critically damped trajectory starts at the initial position `x₀`. -/
@[simp]
lemma trajectoryCritical_at_zero (hS : S.IsCriticallyDamped) :
    IC.trajectoryCritical S hS 0 = IC.x₀ := by
  simp [trajectoryCritical_eq]

/-- The velocity of the critically damped trajectory at `t = 0` equals the initial velocity `v₀`. -/
@[simp]
lemma trajectoryCritical_velocity_at_zero (hS : S.IsCriticallyDamped) :
    ∂ₜ (IC.trajectoryCritical S hS) 0 = IC.v₀ := by
  rw [trajectoryCritical_velocity]; simp

/-!

#### C.2.6. Equation of motion

-/

/-- The critically damped trajectory satisfies the damped harmonic oscillator equation of motion. -/
lemma trajectoryCritical_equationOfMotion (hS : S.IsCriticallyDamped) :
    S.EquationOfMotion (IC.trajectoryCritical S hS) := by
  -- Key identities: γ = 2mβ and β² = ω₀² = k/m (from IsCriticallyDamped)
  have hβ : S.γ = 2 * S.m * S.β := by rw [β]; field_simp
  have hβω : S.β ^ 2 = S.ω₀ ^ 2 := by
    have hd : 4 * S.m ^ 2 * (S.β ^ 2 - S.ω₀ ^ 2) = 0 := by
      have := S.discriminant_eq; rw [hS] at this; linarith
    nlinarith [sq_pos_of_pos S.m_pos]
  have hkm : S.k = S.m * S.β ^ 2 := by rw [hβω, ω₀_sq]; field_simp [ne_of_gt S.m_pos]
  intro t
  have hv := congr_fun (IC.trajectoryCritical_velocity S hS) t
  have ha := congr_fun (IC.trajectoryCritical_acceleration S hS) t
  have hx := congr_fun (IC.trajectoryCritical_eq S hS) t
  simp only at hv ha hx
  rw [hv, ha, hx, hβ, hkm]
  ring

/-!

### C.3. Overdamped trajectory

Solution formula:
    x(t) = e^(−β t) · (x₀ · cosh(β₁ t) + c/β₁ · sinh(β₁ t)),
where c = v₀ + β x₀.

-/

/-!

#### C.3.1. Definition

-/

/-- The solution trajectory for the overdamped harmonic oscillator.

  Given initial conditions `IC`, the solution is
      x(t) = exp(−β t) · (x₀ · cosh(β₁ t) + (v₀ + β x₀)/β₁ · sinh(β₁ t)). -/
noncomputable def trajectoryOverdamped (hS : S.IsOverdamped) : Time → ℝ := fun (t : Time) =>
  Real.exp (- S.β * ↑t) *
    (IC.x₀ * Real.cosh (S.β₁ hS * ↑t) +
     (IC.v₀ + S.β * IC.x₀) / S.β₁ hS * Real.sinh (S.β₁ hS * ↑t))

lemma trajectoryOverdamped_eq (hS : S.IsOverdamped) :
    IC.trajectoryOverdamped S hS =
    fun (t : Time) => Real.exp (- S.β * ↑t) *
      (IC.x₀ * Real.cosh (S.β₁ hS * ↑t) +
       (IC.v₀ + S.β * IC.x₀) / S.β₁ hS * Real.sinh (S.β₁ hS * ↑t)) := rfl

/-!

#### C.3.2. Smoothness

-/

@[fun_prop]
lemma trajectoryOverdamped_contDiff (hS : S.IsOverdamped) :
    ContDiff ℝ ∞ (IC.trajectoryOverdamped S hS) := by
  rw [trajectoryOverdamped_eq]
  have hval : ContDiff ℝ ∞ (Time.val : Time → ℝ) := Time.toRealCLM.contDiff
  have hlin : ContDiff ℝ ∞ (fun t : Time => S.β₁ hS * t.val) :=
    ContDiff.mul contDiff_const hval
  have hcosh : ContDiff ℝ ∞ (fun t : Time => Real.cosh (S.β₁ hS * t.val)) := by
    have : (fun t : Time => Real.cosh (S.β₁ hS * t.val)) =
        (fun t : Time => (Real.exp (S.β₁ hS * t.val) + Real.exp (-(S.β₁ hS * t.val))) / 2) := by
      ext t; rw [Real.cosh_eq]
    rw [this]
    exact ((Real.contDiff_exp.comp hlin).add
           (Real.contDiff_exp.comp (ContDiff.neg hlin))).div_const 2
  have hsinh : ContDiff ℝ ∞ (fun t : Time => Real.sinh (S.β₁ hS * t.val)) := by
    have : (fun t : Time => Real.sinh (S.β₁ hS * t.val)) =
        (fun t : Time => (Real.exp (S.β₁ hS * t.val) - Real.exp (-(S.β₁ hS * t.val))) / 2) := by
      ext t; rw [Real.sinh_eq]
    rw [this]
    exact ((Real.contDiff_exp.comp hlin).sub
           (Real.contDiff_exp.comp (ContDiff.neg hlin))).div_const 2
  apply ContDiff.mul
  · exact Real.contDiff_exp.comp (ContDiff.mul contDiff_const hval)
  · exact ContDiff.add (ContDiff.mul contDiff_const hcosh) (ContDiff.mul contDiff_const hsinh)

/-!

#### C.3.3. Velocity

-/

/-- The velocity of the overdamped trajectory.

    ẋ(t) = e^(−β t) · (v₀ · cosh(β₁ t) − (ω₀² x₀ + β v₀)/β₁ · sinh(β₁ t)). -/
lemma trajectoryOverdamped_velocity (hS : S.IsOverdamped) :
    ∂ₜ (IC.trajectoryOverdamped S hS) = fun (t : Time) =>
      Real.exp (- S.β * ↑t) *
        (IC.v₀ * Real.cosh (S.β₁ hS * ↑t) -
         (S.ω₀ ^ 2 * IC.x₀ + S.β * IC.v₀) / S.β₁ hS * Real.sinh (S.β₁ hS * ↑t)) := by
  sorry

/-!

#### C.3.4. Acceleration

-/

/-- The acceleration of the overdamped trajectory.

    ẍ(t) = e^(−β t) · (−(ω₀² x₀ + 2β v₀) · cosh(β₁ t)
             + ((2β²−ω₀²) v₀ + β ω₀² x₀)/β₁ · sinh(β₁ t)). -/
lemma trajectoryOverdamped_acceleration (hS : S.IsOverdamped) :
    ∂ₜ (∂ₜ (IC.trajectoryOverdamped S hS)) = fun (t : Time) =>
      Real.exp (- S.β * ↑t) *
        ((-(S.ω₀ ^ 2 * IC.x₀) - 2 * S.β * IC.v₀) * Real.cosh (S.β₁ hS * ↑t) +
         ((2 * S.β ^ 2 - S.ω₀ ^ 2) * IC.v₀ + S.β * S.ω₀ ^ 2 * IC.x₀) / S.β₁ hS *
           Real.sinh (S.β₁ hS * ↑t)) := by
  sorry

/-!

#### C.3.5. Initial conditions recovery

-/

/-- The overdamped trajectory starts at the initial position `x₀`. -/
@[simp]
lemma trajectoryOverdamped_at_zero (hS : S.IsOverdamped) :
    IC.trajectoryOverdamped S hS 0 = IC.x₀ := by
  simp [trajectoryOverdamped_eq]

/-- The velocity of the overdamped trajectory at `t = 0` equals the initial velocity `v₀`. -/
@[simp]
lemma trajectoryOverdamped_velocity_at_zero (hS : S.IsOverdamped) :
    ∂ₜ (IC.trajectoryOverdamped S hS) 0 = IC.v₀ := by
  rw [trajectoryOverdamped_velocity]
  simp

/-!

#### C.3.6. Equation of motion

-/

/-- The overdamped trajectory satisfies the damped harmonic oscillator equation of motion. -/
lemma trajectoryOverdamped_equationOfMotion (hS : S.IsOverdamped) :
    S.EquationOfMotion (IC.trajectoryOverdamped S hS) := by
  -- Key identities: γ = 2mβ and k = mω₀² = m(β² − β₁²)
  have hβ : S.γ = 2 * S.m * S.β := by rw [β]; field_simp
  have hkm : S.k = S.m * S.ω₀ ^ 2 := by rw [ω₀_sq]; field_simp
  intro t
  have hv := congr_fun (IC.trajectoryOverdamped_velocity S hS) t
  have ha := congr_fun (IC.trajectoryOverdamped_acceleration S hS) t
  have hx := congr_fun (IC.trajectoryOverdamped_eq S hS) t
  simp only at hv ha hx
  rw [hv, ha, hx, hβ, hkm]
  field_simp [S.β₁_ne_zero hS]
  ring

/-!

## D. Uniqueness (TODO stubs)

In all three cases the solution with given initial conditions is unique among smooth solutions
of the equation of motion. The argument is: if `y` is any other smooth solution with the same
initial conditions, the difference `z = x - y` satisfies the equation of motion with zero
initial conditions. By the energy argument (`energy_dissipation_rate` in `Basic.lean`), the energy
of `z` is non-increasing; since `energy z 0 = 0` and `energy ≥ 0`, we get `energy z = 0`
for all time, which forces `z = 0`.

-/

TODO "Prove uniqueness for the underdamped case.
  Strategy: let z = x - trajectoryUnderdamped. z satisfies S.EquationOfMotion with z(0)=0, ∂ₜz(0)=0.
  By `energy_dissipation_rate`, ∂ₜ(S.energy z) = -γ(∂ₜz)² ≤ 0.
  Since S.energy z 0 = 0 and energy ≥ 0, we get S.energy z t = 0 for all t.
  Then ½m(∂ₜz)² = 0 and ½kz² = 0 imply z = 0."

TODO "Prove uniqueness for the critically damped case.
  Same strategy as the underdamped case."

TODO "Prove uniqueness for the overdamped case.
  Same strategy as the underdamped case."

/-!

## E. Energy of the trajectories

For each damping regime we compute the initial mechanical energy and show that the
energy is non-negative at all times.

-/

/-!

### E.1. Initial energy

The mechanical energy at `t = 0` depends only on the initial conditions, and is the same
in all three damping regimes:
    E(0) = ½ m v₀² + ½ k x₀².

-/

/-- The initial mechanical energy of the underdamped trajectory. -/
lemma trajectoryUnderdamped_energy_at_zero (hS : S.IsUnderdamped) :
    S.energy (IC.trajectoryUnderdamped S hS) 0 =
    1 / 2 * S.m * IC.v₀ ^ 2 + 1 / 2 * S.k * IC.x₀ ^ 2 := by
  unfold energy kineticEnergy potentialEnergy
  simp [IC.trajectoryUnderdamped_at_zero S hS,
        IC.trajectoryUnderdamped_velocity_at_zero S hS]

/-- The initial mechanical energy of the critically damped trajectory. -/
lemma trajectoryCritical_energy_at_zero (hS : S.IsCriticallyDamped) :
    S.energy (IC.trajectoryCritical S hS) 0 =
    1 / 2 * S.m * IC.v₀ ^ 2 + 1 / 2 * S.k * IC.x₀ ^ 2 := by
  unfold energy kineticEnergy potentialEnergy
  simp [IC.trajectoryCritical_at_zero S hS,
        IC.trajectoryCritical_velocity_at_zero S hS]

/-- The initial mechanical energy of the overdamped trajectory. -/
lemma trajectoryOverdamped_energy_at_zero (hS : S.IsOverdamped) :
    S.energy (IC.trajectoryOverdamped S hS) 0 =
    1 / 2 * S.m * IC.v₀ ^ 2 + 1 / 2 * S.k * IC.x₀ ^ 2 := by
  unfold energy kineticEnergy potentialEnergy
  simp [IC.trajectoryOverdamped_at_zero S hS,
        IC.trajectoryOverdamped_velocity_at_zero S hS]

/-!

### E.2. Non-negativity of energy

The mechanical energy is non-negative at every time for any trajectory (this follows
directly from the definitions and positivity of `m` and `k`, independently of the EOM).

-/

/-- The mechanical energy is non-negative at all times. -/
lemma energy_nonneg (x : Time → ℝ) (t : Time) : 0 ≤ S.energy x t := by
  unfold energy kineticEnergy potentialEnergy
  simp only [Pi.add_apply]
  have hm : 0 ≤ 1 / 2 * S.m * (Time.deriv x t) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (le_of_lt S.m_pos)) (sq_nonneg _)
  have hk : 0 ≤ 1 / 2 * S.k * (x t) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (le_of_lt S.k_pos)) (sq_nonneg _)
  linarith

/-!

## F. Special points in the trajectories

-/

/-!

### F.1. Underdamped: amplitude envelope

The amplitude of the underdamped oscillation decays exponentially. The position is bounded
above by the initial amplitude envelope `A · exp(−β t)`, where
    A := √(x₀² + ((v₀ + β x₀)/ω₁)²) ≥ 0.

-/

/-- The amplitude constant for the underdamped trajectory. -/
noncomputable def underdampedAmplitude (hS : S.IsUnderdamped) : ℝ :=
  √(IC.x₀ ^ 2 + ((IC.v₀ + S.β * IC.x₀) / S.ω₁ hS) ^ 2)

/-- The amplitude constant is non-negative. -/
lemma underdampedAmplitude_nonneg (hS : S.IsUnderdamped) :
    0 ≤ IC.underdampedAmplitude S hS :=
  Real.sqrt_nonneg _

/-- The underdamped trajectory is bounded in absolute value by `A · exp(−β t)`. -/
lemma trajectoryUnderdamped_abs_le (hS : S.IsUnderdamped) (t : Time) :
    |IC.trajectoryUnderdamped S hS t| ≤
    IC.underdampedAmplitude S hS * Real.exp (- S.β * ↑t) := by
  rw [trajectoryUnderdamped_eq, underdampedAmplitude, abs_mul, Real.abs_exp]
  rw [mul_comm]  -- rearrange to |...| * exp ≤ sqrt(...) * exp
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  have hcs := sin_sq_add_cos_sq (S.ω₁ hS * ↑t)
  nlinarith [sq_nonneg (IC.x₀ * sin (S.ω₁ hS * ↑t) -
      (IC.v₀ + S.β * IC.x₀) / S.ω₁ hS * cos (S.ω₁ hS * ↑t)),
    sq_nonneg (IC.x₀ * cos (S.ω₁ hS * ↑t) +
      (IC.v₀ + S.β * IC.x₀) / S.ω₁ hS * sin (S.ω₁ hS * ↑t)),
    sq_abs IC.x₀, sq_abs ((IC.v₀ + S.β * IC.x₀) / S.ω₁ hS)]

/-!

### F.2. Critically damped: at most one positive zero

The critically damped trajectory `e^(−β t) (x₀ + c t)` with `c = v₀ + β x₀` has at most
one positive zero, since the factor `(x₀ + c t)` is linear in `t`.

-/

/-- The critically damped trajectory has at most one positive zero, provided the initial
  conditions are not both zero (in which case the trajectory is identically zero). -/
lemma trajectoryCritical_at_most_one_zero (hS : S.IsCriticallyDamped)
    (hIC : IC.x₀ ≠ 0 ∨ IC.v₀ + S.β * IC.x₀ ≠ 0)
    (t₁ t₂ : Time)
    (h₁ : IC.trajectoryCritical S hS t₁ = 0)
    (h₂ : IC.trajectoryCritical S hS t₂ = 0) : t₁ = t₂ := by
  simp only [trajectoryCritical_eq] at h₁ h₂
  -- Since exp(−β t) > 0, we must have x₀ + c t = 0
  have hexp₁ : Real.exp (- S.β * ↑t₁) ≠ 0 := Real.exp_ne_zero _
  have hexp₂ : Real.exp (- S.β * ↑t₂) ≠ 0 := Real.exp_ne_zero _
  have hlin₁ : IC.x₀ + (IC.v₀ + S.β * IC.x₀) * ↑t₁ = 0 := by
    rcases mul_eq_zero.mp h₁ with habs | h
    · exact absurd habs hexp₁
    · exact h
  have hlin₂ : IC.x₀ + (IC.v₀ + S.β * IC.x₀) * ↑t₂ = 0 := by
    rcases mul_eq_zero.mp h₂ with habs | h
    · exact absurd habs hexp₂
    · exact h
  -- Two zeros of a linear function force t₁ = t₂
  have hc : (IC.v₀ + S.β * IC.x₀) * ((↑t₁ : ℝ) - ↑t₂) = 0 := by nlinarith
  rcases mul_eq_zero.mp hc with hc0 | htdiff
  · -- c = 0: then x₀ + 0 = 0, so x₀ = 0; contradicts hIC
    have hx0 : IC.x₀ = 0 := by
      have := hlin₁; rw [hc0, zero_mul, add_zero] at this; exact this
    rcases hIC with hx | hc
    · exact absurd hx0 hx
    · exact absurd hc0 hc
  · -- t₁.val = t₂.val
    exact Time.val_injective (sub_eq_zero.mp htdiff)

/-!

### F.3. Overdamped: at most one positive zero

The overdamped trajectory can be written as `A₊ e^(r₊ t) + A₋ e^(r₋ t)` with
`r₊ = −β + β₁ > 0 ≥ r₋ = −β − β₁`. If `A₊` and `A₋` have the same sign, the solution
is monotone and has no zero. If they have opposite signs, there is exactly one zero.

-/

TODO "Prove that the overdamped trajectory has at most one positive zero.
  Hint: write x(t) = e^(-β t)(x₀ cosh(β₁ t) + c/β₁ sinh(β₁ t)) =
  A₊ e^(-β+β₁)t + A₋ e^(-β-β₁)t with A₊=(x₀+(c/β₁))/2, A₋=(x₀-(c/β₁))/2.
  Then x(t)=0 iff A₊/A₋ = -e^(-2β₁ t), which has at most one positive solution."

end InitialConditions

end DampedHarmonicOscillator

end ClassicalMechanics
