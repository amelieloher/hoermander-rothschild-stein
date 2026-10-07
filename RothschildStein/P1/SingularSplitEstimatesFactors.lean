-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SingularSplitEstimatesProduct
public import RothschildStein.P1.SingularSplit

/-!
# Smooth factors of the singular split

The three smooth factors multiplying a homogeneous kernel in the estimates of `K₀` and `K₁`
(BB pp. 573–575) are `C¹` on `U × U`:

* the density factor `1/(1 + ω₋(ξ, Θ(η, ξ)))` of `K₀` (positive by the lifted-chart field
  `jacobian`), a smooth bounded factor whose differences are `O(d̃(ξ, ξ'))`;
* the diagonal factor `f = ω₋/(1 + ω₋)` of the first part of `K₁`, which vanishes on the diagonal
  (`ω₋(ξ, 0) = 0`), so `|f| ≤ C d̃`;
* the coordinate differences `(η - ξ)_l` of the parameter mean value in the second part of `K₁`.

Since `ω₋(ξ, u) = ω₊(ξ, -u)` (lifted-chart field `ωm_eq`) and `Θ(ξ, η) = -Θ(η, ξ)`, the composite
`(ξ, η) ↦ ω₋(ξ, Θ(η, ξ)) = ω₊(ξ, Θ(ξ, η))` is smooth on `U × U` (the point `(ξ, Θ(ξ, η))` lies in
the domain of smoothness of `ω₊`). The product lemmas of `SingularSplitEstimatesProduct` then give
the kernel bounds of the products.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The density factor `1/(1 + ω₋(ξ, Θ(η, ξ)))` of `K₀` (BB p. 572, (11.52)). -/
def densityFactor (ξ η : Fin (n + m) → ℝ) : ℝ := (1 + C.ωm ξ (C.Θ η ξ))⁻¹

/-- The composite `(ξ, η) ↦ ω₋(ξ, Θ(η, ξ))` is `C¹` on `U × U`: it equals
`ω₊(ξ, Θ(ξ, η))` there (`ωm_eq` and the antisymmetry of `Θ`), and `(ξ, Θ(ξ, η))` lies in the
domain `T` of `ω₊`. -/
theorem contDiffOn_omegaMinus_theta : ContDiffOn ℝ 1
    (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.ωm p.1 (C.Θ p.2 p.1)) (C.U ×ˢ C.U) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (p.1, C.Θ p.1 p.2)) (C.U ×ˢ C.U) :=
    contDiffOn_fst.prodMk C.theta_smooth
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.ωp p.1 (C.Θ p.1 p.2))
      (C.U ×ˢ C.U) :=
    C.ωp_smooth.comp h1 (fun p hp => C.mem_T_theta hp.1 hp.2)
  refine (h2.of_le (by simp)).congr (fun p hp => ?_)
  rw [C.ωm_eq p.1 hp.1, C.theta_antisymm p.2 hp.2 p.1 hp.1]

/-- The density factor is `C¹` on `U × U` (positivity of `1 + ω₋` from `jacobian`). -/
theorem contDiffOn_densityFactor : ContDiffOn ℝ 1
    (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.densityFactor p.1 p.2) (C.U ×ˢ C.U) :=
  (contDiffOn_const.add C.contDiffOn_omegaMinus_theta).inv
    (fun p hp => (C.jacobian p.2 hp.2 p.1 hp.1).2.1.ne')

/-- The diagonal factor `f(ξ, Θ(η, ξ))`, `f = ω₋/(1 + ω₋)`, is `C¹` on `U × U`. -/
theorem contDiffOn_diagFactor_theta : ContDiffOn ℝ 1
    (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.diagFactor p.1 (C.Θ p.2 p.1))
    (C.U ×ˢ C.U) :=
  C.contDiffOn_omegaMinus_theta.div (contDiffOn_const.add C.contDiffOn_omegaMinus_theta)
    (fun p hp => (C.jacobian p.2 hp.2 p.1 hp.1).2.1.ne')

/-- The diagonal factor vanishes on the diagonal: `Θ(ξ, ξ) = 0` and `ω₋(ξ, 0) = 0`. -/
theorem diagFactor_theta_self {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) :
    C.diagFactor ξ (C.Θ ξ ξ) = 0 := by
  rw [(C.chart ξ hξ).2.2.2.2]
  exact diagFactor_zero hξ

variable {C}
variable {L : Set (Fin (n + m) → ℝ)} {ℓ : ℕ}
  {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
variable (hL : IsCompact L) (hLU : L ⊆ C.U)
include hL hLU

/-- Multiplying a kernel with bounds of exponent `ℓ` by a factor that is `C¹` on `U × U`
preserves the exponent (the factor is bounded and `d̃`-Lipschitz on the compact patch; BB p. 573:
"product differences add `O(h r^{-Q})` to the singular `O(h r^{-Q-1})`, absorbed on the fixed
patch"). -/
theorem HasKernelBounds.mul_of_contDiffOn
    {g : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hg : ContDiffOn ℝ 1 (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => g p.1 p.2)
      (C.U ×ˢ C.U))
    (hκ : C.HasKernelBounds L ℓ κ) : C.HasKernelBounds L ℓ (fun ξ η => g ξ η * κ ξ η) := by
  obtain ⟨Gs, hGs0, hGs⟩ := C.exists_bound_prod hg hL hLU
  obtain ⟨M, hM0, hM₁, hM₂⟩ := C.exists_lipschitz hg hL hLU
  exact HasKernelBounds.mul (e := 0) hL hLU (Nat.zero_le 1) hκ hGs0 hM0
    (fun ξ hξ η hη _ => by simpa using hGs ξ hξ η hη) hM₁ hM₂

/-- Multiplying a kernel with bounds of exponent `ℓ` by a factor that is `C¹` on `U × U`
and vanishes on the diagonal raises the exponent to `ℓ + 1`: the factor is `O(d̃)` and
`d̃`-Lipschitz (BB pp. 574–575: "singular difference `O(h r^{-Q-1})` times `O(r)`, plus size
`O(r^{-Q})` times `O(h)`, gives `O(h r^{-Q})`"). -/
theorem HasKernelBounds.mul_of_contDiffOn_diag
    {g : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hg : ContDiffOn ℝ 1 (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => g p.1 p.2)
      (C.U ×ˢ C.U))
    (hdiag : ∀ ξ ∈ L, g ξ ξ = 0) (hκ : C.HasKernelBounds L ℓ κ) :
    C.HasKernelBounds L (ℓ + 1) (fun ξ η => g ξ η * κ ξ η) := by
  obtain ⟨Gs, hGs0, hGs⟩ := C.exists_size_of_diag_zero hg hL hLU hdiag
  obtain ⟨M, hM0, hM₁, hM₂⟩ := C.exists_lipschitz hg hL hLU
  exact HasKernelBounds.mul (e := 1) hL hLU le_rfl hκ hGs0 hM0
    (fun ξ hξ η hη _ => by simpa using hGs ξ hξ η hη) hM₁ hM₂

end LiftedChart
end RothschildStein.P1
