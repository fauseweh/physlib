/-
Copyright (c) 2025 Nicola Bernini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Bernini, Benedikt Fauseweh
-/
module

public import Physlib.ClassicalMechanics.EulerLagrange
public import Physlib.ClassicalMechanics.HamiltonsEquations
public import Physlib.SpaceAndTime.Time.Derivatives
public import Mathlib.Data.Real.Hom
/-!

# The Damped Harmonic Oscillator

## i. Overview

The damped harmonic oscillator is a classical mechanical system corresponding to a
mass `m` under a restoring force `- k x` and a damping force `- γ ẋ`, where `k` is the
spring constant, `γ` is the damping coefficient, `x` is the position, and `ẋ` is the velocity.

The equation of motion for the damped harmonic oscillator is:
```
m ẍ + γ ẋ + k x = 0
```

Depending on the relationship between the damping coefficient and the natural frequency,
the system exhibits three different behaviors:
- **Underdamped** (γ² < 4mk) : Oscillatory motion with exponentially decaying amplitude
- **Critically damped** (γ² = 4mk) : Fastest return to equilibrium without oscillation
- **Overdamped** (γ² > 4mk) : Slow return to equilibrium without oscillation

## ii. Key results

This module is currently a placeholder for future implementation. The following results
are planned to be formalized:

- `DampedHarmonicOscillator`: Structure containing the input data (mass, spring constant,
  damping coefficient)
- `EquationOfMotion`: The equation of motion for the damped harmonic oscillator
- Solutions for underdamped, critically damped, and overdamped cases
- Energy dissipation properties
- Quality factor and relaxation time

## iii. Table of contents

- A. The input data
- B. The damped angular frequency and decay rate
- C. The energies
- D. The equation of motion
- E. Energy dissipation

- F. Solutions (to be implemented)
  - F.1. Underdamped case
  - F.2. Critically damped case
  - F.3. Overdamped case
- G. Quality factor and decay time (to be implemented)

## iv. References

References for the damped harmonic oscillator include:
- Landau & Lifshitz, Mechanics, page 76, section 25.
- Goldstein, Classical Mechanics, Chapter 2.

-/

@[expose] public section

namespace ClassicalMechanics
open Real
open Space
open InnerProductSpace

TODO "Derive solutions for the underdamped case (oscillatory with exponential decay)."

TODO "Derive solutions for the critically damped case (fastest non-oscillatory return)."

TODO "Derive solutions for the overdamped case (slow non-oscillatory return)."

TODO "Define and prove properties of the quality factor Q."

TODO "Define and prove properties of the relaxation time τ."

TODO "Prove that the damped harmonic oscillator reduces to the undamped case when γ = 0."

/-!

## A. The input data

The input data for the damped harmonic oscillator will consist of:
- Mass `m > 0`
- Spring constant `k > 0`
- Damping coefficient `γ ≥ 0`

-/

/-- Placeholder structure for the damped harmonic oscillator.
  The damped harmonic oscillator is specified by a mass `m`, a spring constant `k`,
  and a damping coefficient `γ`. All parameters are assumed to be positive (or non-negative
  for the damping coefficient). -/
structure DampedHarmonicOscillator where
  /-- The mass of the oscillator. -/
  m : ℝ
  /-- The spring constant of the oscillator. -/
  k : ℝ
  /-- The damping coefficient of the oscillator. -/
  γ : ℝ
  m_pos : 0 < m
  k_pos : 0 < k
  γ_nonneg : 0 ≤ γ

namespace DampedHarmonicOscillator

variable (S : DampedHarmonicOscillator)

@[simp]
lemma k_ne_zero : S.k ≠ 0 := by
linarith [S.k_pos]

@[simp]
lemma m_ne_zero : S.m ≠ 0 := by
linarith [S.m_pos]

/-!

## B. The natural angular frequency and decay rate

The natural angular frequency ω₀ = √(k/m) and the decay rate β = γ/(2m) are the two
fundamental derived quantities of the damped harmonic oscillator. Together they determine
the discriminant and hence the damping regime.

-/

/-- The natural (undamped) angular frequency of the oscillator, ω₀ = √(k/m). -/
noncomputable def ω₀ : ℝ := √(S.k / S.m)

@[simp]
lemma ω₀_pos : 0 < S.ω₀ := by
  simp [ω₀]
  positivity [S.k_pos, S.m_pos]


--sqrt_pos.mpr (div_pos S.k_pos S.m_pos)

lemma ω₀_sq : S.ω₀^2 = S.k / S.m := by
  simp [ω₀]
  rw [sq_sqrt]
  positivity [S.k_pos, S.m_pos]

lemma ω₀_ne_zero : S.ω₀ ≠ 0 := by
  positivity [S.ω₀_pos]

/-- The decay rate (half-damping coefficient) β = γ/(2m). -/
noncomputable def β : ℝ := S.γ / (2 * S.m)

/-- The decay rate β is non-negative. -/
lemma β_nonneg : 0 ≤ S.β := by
  rw [β]
  positivity [S.γ_nonneg, S.m_pos]

/-- The square of β satisfies β² = γ²/(4m²). -/
lemma β_sq : S.β ^ 2 = S.γ ^ 2 / (4 * S.m ^ 2) := by
  rw [β]
  ring

/-!

## C. Energies
-/

open MeasureTheory ContDiff InnerProductSpace Time

/-- The kinetic energy of the damped harmonic oscillator is $\frac{1}{2} m ‖\dot x‖^2$. -/
noncomputable def kineticEnergy ( xₜ : Time → EuclideanSpace ℝ (Fin 1)) : Time → ℝ :=
  fun t => (1 / 2 : ℝ) * S.m * ⟪∂ₜ xₜ t, ∂ₜ xₜ t⟫_ℝ

/-- The potential energy of the damped harmonic oscillator is `1/2 k x ^ 2` -/
noncomputable def potentialEnergy (x : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  (1 / (2 : ℝ)) • S.k • ⟪x, x⟫_ℝ

/-- The energy of the damped harmonic oscillator is the kinetic energy plus the potential energy. -/
noncomputable def energy (xₜ : Time → EuclideanSpace ℝ (Fin 1)) : Time → ℝ := fun t =>
  kineticEnergy S xₜ t + potentialEnergy S (xₜ t)




lemma kineticEnergy_eq (xₜ : Time → EuclideanSpace ℝ (Fin 1)) :
    kineticEnergy S xₜ = fun t => (1 / (2 : ℝ)) * S.m * ⟪∂ₜ xₜ t, ∂ₜ xₜ t⟫_ℝ:= by rfl

lemma potentialEnergy_eq (x : EuclideanSpace ℝ (Fin 1)) :
    potentialEnergy S x = (1 / (2 : ℝ)) • S.k • ⟪x, x⟫_ℝ:= by rfl

lemma energy_eq (xₜ : Time → EuclideanSpace ℝ (Fin 1)) :
    energy S xₜ = fun t => kineticEnergy S xₜ t + potentialEnergy S (xₜ t) := by rfl
/-!


### C.3. Differentiability of the energies

On smooth trajectories the energies are differentiable.

-/
@[fun_prop]
lemma kineticEnergy_differentiable (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ xₜ) :
    Differentiable ℝ (kineticEnergy S xₜ) := by
  rw [kineticEnergy_eq]
  change Differentiable ℝ ((fun x => (1 / (2 : ℝ)) * S.m * ⟪x, x⟫_ℝ) ∘ (fun t => ∂ₜ xₜ t))
  apply Differentiable.comp
  · fun_prop
  · exact deriv_differentiable_of_contDiff xₜ hx

@[fun_prop]
lemma potentialEnergy_differentiable (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ xₜ) :
    Differentiable ℝ (fun t => potentialEnergy S (xₜ t)) := by
  simp only [potentialEnergy_eq, one_div, smul_eq_mul]
  change Differentiable ℝ ((fun x => 2⁻¹ * (S.k * ⟪x, x⟫_ℝ)) ∘ xₜ)
  apply Differentiable.comp
  · fun_prop
  · rw [contDiff_infty_iff_fderiv] at hx
    exact hx.1

@[fun_prop]
lemma energy_differentiable (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ xₜ) :
    Differentiable ℝ (energy S xₜ) := by
  rw [energy_eq]
  fun_prop

/-!

### C.4. Time derivatives of the energies

For a general smooth trajectory (which may not satisfy the equations of motion) we can compute
the time derivatives of the energies.

-/


set_option backward.isDefEq.respectTransparency false in
lemma kineticEnergy_deriv (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ xₜ) :
    ∂ₜ (kineticEnergy S xₜ) = fun t => ⟪∂ₜ xₜ t, S.m • ∂ₜ (∂ₜ xₜ) t⟫_ℝ := by
  funext t
  unfold kineticEnergy
  conv_lhs => simp only [Time.deriv, one_div, ringHom_apply]
  change (fderiv ℝ ((fun x => 2⁻¹ * S.m * ⟪x, x⟫_ℝ) ∘ (fun t => ∂ₜ xₜ t)) t) 1 = _
  rw [fderiv_comp]
  rw [fderiv_const_mul (by fun_prop)]
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_comp', Pi.smul_apply, Function.comp_apply, smul_eq_mul]
  rw [fderiv_inner_apply]
  simp only [fderiv_id', ContinuousLinearMap.coe_id', id_eq]
  rw [real_inner_comm, ← inner_add_left, ← Time.deriv, real_inner_comm, ← inner_smul_right]
  congr 1
  simp only [smul_add]
  module
  repeat fun_prop

set_option backward.isDefEq.respectTransparency false in
lemma potentialEnergy_deriv (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ xₜ) :
    ∂ₜ (fun t => potentialEnergy S (xₜ t)) = fun t => ⟪∂ₜ xₜ t, S.k • xₜ t⟫_ℝ := by
  funext t
  unfold potentialEnergy
  conv_lhs => simp only [Time.deriv, one_div, smul_eq_mul]
  change (fderiv ℝ ((fun x => 2⁻¹ * (S.k * ⟪x, x⟫_ℝ)) ∘ (fun t => xₜ t)) t) 1 = _
  rw [fderiv_comp]
  rw [fderiv_const_mul (by fun_prop), fderiv_const_mul (by fun_prop)]
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_comp', Pi.smul_apply, Function.comp_apply, smul_eq_mul]
  rw [fderiv_inner_apply]
  simp only [fderiv_id', ContinuousLinearMap.coe_id', id_eq]
  trans S.k * ⟪xₜ t, ∂ₜ xₜ t⟫_ℝ
  · rw [real_inner_comm, ← inner_add_left, ← Time.deriv, real_inner_comm, ← inner_smul_right,
      ← inner_smul_right, ← inner_smul_right]
    congr 1
    module
  rw [real_inner_comm, ← inner_smul_right]
  repeat fun_prop
  apply Differentiable.differentiableAt
  rw [contDiff_infty_iff_fderiv] at hx
  exact hx.1

set_option backward.isDefEq.respectTransparency false in
lemma energy_deriv (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (hx : ContDiff ℝ ∞ xₜ) :
    ∂ₜ (energy S xₜ) = fun t => ⟪∂ₜ xₜ t, S.m • ∂ₜ (∂ₜ xₜ) t + S.k • xₜ t⟫_ℝ := by
  unfold energy
  funext t
  rw [Time.deriv_eq]
  rw [fderiv_fun_add (by fun_prop) (by apply S.potentialEnergy_differentiable xₜ hx)]
  simp only [ContinuousLinearMap.add_apply]
  rw [← Time.deriv_eq, ← Time.deriv_eq]
  rw [potentialEnergy_deriv, kineticEnergy_deriv]
  simp only
  rw [← inner_add_right]
  fun_prop
  fun_prop




/-!

## D. Equation of motion

mx¨+γx˙+kx=0,

-/

def EquationOfMotion (xₜ : Time → EuclideanSpace ℝ (Fin 1)) : Prop :=
  ∀ t : Time, S.m • ∂ₜ (∂ₜ xₜ) t + S.γ • ∂ₜ xₜ t + S.k • xₜ t = 0



/-!

## E. Energy dissipation
-/
example (A B : ℝ) (h : A + B = 0) : A = -B := by
  suffices h' : A + B = 0 by
    linarith
  exact h

noncomputable def EnergyDissipationRate (xₜ : Time → EuclideanSpace ℝ (Fin 1)) : Time → ℝ :=
  fun t => - S.γ * ⟪∂ₜ xₜ t, ∂ₜ xₜ t⟫_ℝ

lemma energy_dissipation_rate (xₜ : Time → EuclideanSpace ℝ (Fin 1)) (h1 : S.EquationOfMotion xₜ)
    (hx : ContDiff ℝ ∞ xₜ) (t : Time) :
    ∂ₜ (energy S xₜ) t = - S.γ * ⟪∂ₜ xₜ t, ∂ₜ xₜ t⟫_ℝ := by
    rw [energy_deriv S xₜ hx]
    suffices h : ⟪∂ₜ xₜ t, S.m • ∂ₜ (∂ₜ xₜ) t + S.k • xₜ t⟫_ℝ + S.γ * ⟪∂ₜ xₜ t, ∂ₜ xₜ t⟫_ℝ = 0 by
      linarith
    rw [← real_inner_smul_right]
    rw [← inner_add_right]
    suffices h : S.m • ∂ₜ (∂ₜ xₜ) t  + S.k • xₜ t + S.γ • ∂ₜ xₜ t = 0 by
      simp [h]
    rw [add_right_comm]
    exact h1 t

lemma energy_dissipation_rate_nonpositive (xₜ : Time → EuclideanSpace ℝ (Fin 1))
    (h1 : S.EquationOfMotion xₜ) (hx : ContDiff ℝ ∞ xₜ)  (t : Time) :
    ∂ₜ (energy S xₜ) t ≤ 0 := by
    simp [energy_dissipation_rate S xₜ h1 hx t]
    positivity [S.γ_nonneg]

/-!

## E. Damping regimes (placeholder)

The three damping regimes will be defined based on the discriminant γ² - 4mk.

-/

/-- The discriminant that determines the damping regime. -/
noncomputable def discriminant : ℝ := S.γ^2 - 4 * S.m * S.k

/-- The system is underdamped when γ² < 4mk. -/
def IsUnderdamped : Prop := S.discriminant < 0

/-- The system is critically damped when γ² = 4mk. -/
def IsCriticallyDamped : Prop := S.discriminant = 0

/-- The system is overdamped when γ² > 4mk. -/
def IsOverdamped : Prop := S.discriminant > 0

/-- The discriminant equals `4 m² (β² − ω₀²)`. -/
lemma discriminant_eq : S.discriminant = 4 * S.m ^ 2 * (S.β ^ 2 - S.ω₀ ^ 2) := by
  simp only [discriminant, β_sq, ω₀_sq]
  field_simp

end DampedHarmonicOscillator

end ClassicalMechanics
