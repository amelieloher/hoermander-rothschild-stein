-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LiftedChart
public import RothschildStein.Definitions.SmoothDifferentialOperator.apply

/-!
# Singular split `K = K₀ + K₁`

For a parameter family `D^{ξ,η}` of differential operators, a pole `Γ`, a radial profile `φ` and
a gauge `ν` (in the application `ν = ‖·‖` is the standing norm of H1, and `Γ` is the fundamental
kernel), put `k^{ξ,η}(u) = (D^{ξ,η} Γ)(u) φ(ν u)` and `K(ξ, η) = k^{ξ,η}(Θ(η, ξ))`. The
part `K₀`, with parameter evaluated on the diagonal, and the remainder `K₁` of the singular split
(BB Prop 11.33, pp. 572–576, (11.52)–(11.56)) are defined verbatim, and `K = K₀ + K₁` is the
algebraic identity valid wherever
`1 + ω₋(ξ, Θ(η, ξ)) ≠ 0`, in particular on `U × U` (lifted-chart field `jacobian`).

The remainder splits as `K₁ = K₁ᵃ + E` with `K₁ᵃ = k^{ξ,ξ}(u) f(ξ, u)`, `f = ω₋/(1 + ω₋)` the
diagonal factor, and `E = [k^{ξ,η} - k^{ξ,ξ}](u)` the parameter part (BB pp. 574–576); the
size and difference estimates of the pieces are not part of this file.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1

/-- The cut-off parameter kernel `k^{ξ,η}(u) = (D^{ξ,η} Γ)(u) φ(ν u)` of the singular split
(BB p. 572). -/
def cutoffKernel {N : ℕ} (ν : (Fin N → ℝ) → ℝ)
    (D : (Fin N → ℝ) → (Fin N → ℝ) → SmoothDifferentialOperator N)
    (Γ : (Fin N → ℝ) → ℝ) (φ : ℝ → ℝ) (ξ η u : Fin N → ℝ) : ℝ :=
  (D ξ η).apply Γ u * φ (ν u)

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m) (ν : (Fin (n + m) → ℝ) → ℝ)
  (D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m))
  (Γ : (Fin (n + m) → ℝ) → ℝ) (φ : ℝ → ℝ)

/-- The truncation gauge `ρ(ξ, η) = ν(Θ(η, ξ))` of the principal value (BB p. 545). -/
def rhoGauge (ξ η : Fin (n + m) → ℝ) : ℝ := ν (C.Θ η ξ)

/-- The annulus `{η ∈ U | r < ρ(ξ, η) < t}` of the annular cancellation, inside the chart domain. -/
def rhoAnnulus (ξ : Fin (n + m) → ℝ) (r t : ℝ) : Set (Fin (n + m) → ℝ) :=
  {η | η ∈ C.U ∧ r < C.rhoGauge ν ξ η ∧ C.rhoGauge ν ξ η < t}

/-- The kernel `K(ξ, η) = k^{ξ,η}(Θ(η, ξ))` being split (BB p. 572). -/
def pairKernel (ξ η : Fin (n + m) → ℝ) : ℝ :=
  cutoffKernel ν D Γ φ ξ η (C.Θ η ξ)

/-- The singular part
`K₀(ξ, η) = k^{ξ,ξ}(Θ(η, ξ)) / (1 + ω₋(ξ, Θ(η, ξ)))` of the singular split: the input parameter set equal to
the output parameter, divided by the input density correction (BB p. 572, (11.52)). -/
def splitK0 (ξ η : Fin (n + m) → ℝ) : ℝ :=
  cutoffKernel ν D Γ φ ξ ξ (C.Θ η ξ) / (1 + C.ωm ξ (C.Θ η ξ))

/-- The first part of `K₁` in the singular split: `k^{ξ,ξ}(u) ω₋(ξ, u) / (1 + ω₋(ξ, u))` at
`u = Θ(η, ξ)` (BB p. 573, (11.53)). -/
def splitK1Diag (ξ η : Fin (n + m) → ℝ) : ℝ :=
  cutoffKernel ν D Γ φ ξ ξ (C.Θ η ξ) * C.ωm ξ (C.Θ η ξ) / (1 + C.ωm ξ (C.Θ η ξ))

/-- The second part of `K₁` in the singular split: `E = [k^{ξ,η} - k^{ξ,ξ}](Θ(η, ξ))`
(BB pp. 573, 575, (11.53)). -/
def splitK1Param (ξ η : Fin (n + m) → ℝ) : ℝ :=
  cutoffKernel ν D Γ φ ξ η (C.Θ η ξ) - cutoffKernel ν D Γ φ ξ ξ (C.Θ η ξ)

/-- The remainder `K₁` of the singular split, as displayed:
`[k^{ξ,ξ}(u) ω₋(ξ,u)/(1 + ω₋(ξ,u)) + k^{ξ,η}(u) - k^{ξ,ξ}(u)]_{u = Θ(η,ξ)}`. -/
def splitK1 (ξ η : Fin (n + m) → ℝ) : ℝ :=
  cutoffKernel ν D Γ φ ξ ξ (C.Θ η ξ) * C.ωm ξ (C.Θ η ξ) / (1 + C.ωm ξ (C.Θ η ξ)) +
    cutoffKernel ν D Γ φ ξ η (C.Θ η ξ) - cutoffKernel ν D Γ φ ξ ξ (C.Θ η ξ)

/-- The diagonal density factor `f(ξ, u) = ω₋(ξ, u) / (1 + ω₋(ξ, u))` of the first part
of `K₁` (BB p. 574). -/
def diagFactor (ξ u : Fin (n + m) → ℝ) : ℝ := C.ωm ξ u / (1 + C.ωm ξ u)

variable {C ν D Γ φ}

/-- `K₁` is the sum of its diagonal part and its parameter part (BB p. 573, (11.53)). -/
theorem splitK1_eq_diag_add_param (ξ η : Fin (n + m) → ℝ) :
    C.splitK1 ν D Γ φ ξ η = C.splitK1Diag ν D Γ φ ξ η + C.splitK1Param ν D Γ φ ξ η := by
  unfold splitK1 splitK1Diag splitK1Param
  ring

/-- The diagonal part of `K₁` is `k^{ξ,ξ}(u) f(ξ, u)` at `u = Θ(η, ξ)`. -/
theorem splitK1Diag_eq (ξ η : Fin (n + m) → ℝ) :
    C.splitK1Diag ν D Γ φ ξ η =
      cutoffKernel ν D Γ φ ξ ξ (C.Θ η ξ) * C.diagFactor ξ (C.Θ η ξ) := by
  unfold splitK1Diag diagFactor
  rw [mul_div_assoc]

/-- The algebraic identity of the singular split, `K = K₀ + K₁`, wherever the input density
correction satisfies `1 + ω₋(ξ, Θ(η, ξ)) ≠ 0` (BB p. 573, (11.52)–(11.53)). -/
theorem pairKernel_eq_splitK0_add_splitK1_of_ne {ξ η : Fin (n + m) → ℝ}
    (h : 1 + C.ωm ξ (C.Θ η ξ) ≠ 0) :
    C.pairKernel ν D Γ φ ξ η = C.splitK0 ν D Γ φ ξ η + C.splitK1 ν D Γ φ ξ η := by
  unfold pairKernel splitK0 splitK1
  field_simp
  ring

/-- `K = K₀ + K₁` on `U × U`: the input density correction is positive there, by the
lifted-chart field `jacobian` (BB p. 573, (11.52)–(11.53)). -/
theorem pairKernel_eq_splitK0_add_splitK1 {ξ η : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (hη : η ∈ C.U) :
    C.pairKernel ν D Γ φ ξ η = C.splitK0 ν D Γ φ ξ η + C.splitK1 ν D Γ φ ξ η :=
  pairKernel_eq_splitK0_add_splitK1_of_ne (C.jacobian η hη ξ hξ).2.1.ne'

/-- The diagonal factor `f(ξ, ·)` vanishes at the origin, since `ω₋(ξ, 0) = 0`
(lifted-chart field `ω_origin`; BB p. 574). -/
theorem diagFactor_zero {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) : C.diagFactor ξ 0 = 0 := by
  simp [diagFactor, (C.ω_origin ξ hξ).2]

end LiftedChart

end RothschildStein.P1
