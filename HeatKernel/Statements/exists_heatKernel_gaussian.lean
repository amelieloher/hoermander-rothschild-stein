-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import RothschildStein.Definitions.HomogeneousGroup
public import RothschildStein.Definitions.HomogeneousGroup.mul
public import RothschildStein.Definitions.HomogeneousGroup.dilate
public import RothschildStein.Definitions.HomogeneousGroup.homogeneousDimension
public import RothschildStein.Definitions.HomogeneousGroup.horizontalFields
public import RothschildStein.Definitions.bracketSpansOn
public import RothschildStein.Definitions.sumSquares
public import HeatKernel.Definitions.horizontalL2Distance
public import HeatKernel.Provider.exists_heatKernel_gaussian

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal

namespace HeatKernel

open RothschildStein

/-- Heat kernel with two-sided Gaussian bounds (Saloff-Coste 1992, Theorem 4.2; upper bound:
Jerison–Sánchez-Calle 1986, Theorem 1) for the horizontal sub-Laplacian `L = ∑ᵢ Xᵢ²` of a Carnot
group: there is a kernel `p`,
smooth on `(0, ∞) × G × G`, solving the heat equation in `(t, x)`, symmetric, satisfying the
Chapman–Kolmogorov identity, of unit mass, with the delta initial condition against bounded
continuous functions, left-translation invariant, parabolically dilation covariant, and obeying
two-sided Gaussian bounds in the horizontal `ℓ²`-control distance `d = horizontalL2Distance X`,
with constants depending only on the group and its horizontal fields. The semigroup `T_t` itself
and the representation `T_t f = ∫ p(t, ·, y) f(y) dy` are not part of this statement. -/
theorem exists_heatKernel_gaussian
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq)) :
    let X := G.horizontalFields hq
    let L := sumSquares X
    let Q : ℝ := (G.homogeneousDimension : ℝ)
    let d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ :=
      fun x y => (horizontalL2Distance X x y).toReal
    ∃ p : ℝ → (Fin N → ℝ) → (Fin N → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : ℝ × (Fin N → ℝ) × (Fin N → ℝ) => p z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ univ) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : Fin N → ℝ,
        deriv (fun s => p s x y) t = L (fun w => p t w y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : Fin N → ℝ, p t x y = p t y x) ∧
      (∀ s t : ℝ, 0 < s → 0 < t → ∀ x y : Fin N → ℝ,
        Integrable (fun z => p s x z * p t z y) ∧
        p (s + t) x y = ∫ z, p s x z * p t z y) ∧
      (∀ t : ℝ, 0 < t → ∀ x : Fin N → ℝ, ∫ y, p t x y = 1) ∧
      (∀ φ : (Fin N → ℝ) → ℝ, Continuous φ → (∃ M : ℝ, ∀ y, |φ y| ≤ M) →
        ∀ x : Fin N → ℝ,
          Tendsto (fun t => ∫ y, p t x y * φ y) (𝓝[>] 0) (𝓝 (φ x))) ∧
      (∀ t : ℝ, 0 < t → ∀ g x y : Fin N → ℝ, p t (G.mul g x) (G.mul g y) = p t x y) ∧
      (∀ t r : ℝ, 0 < t → 0 < r → ∀ x y : Fin N → ℝ,
        p (r ^ 2 * t) (G.dilate r x) (G.dilate r y) = (r ^ G.homogeneousDimension)⁻¹ * p t x y) ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ t : ℝ, 0 < t → ∀ x y : Fin N → ℝ,
          c * t ^ (-Q / 2) * Real.exp (-(C * d x y ^ 2 / t)) ≤ p t x y ∧
          p t x y ≤ C * t ^ (-Q / 2) * Real.exp (-(c * d x y ^ 2 / t)) :=
  by exact HeatKernel.Provider.exists_heatKernel_gaussian G hq hqpos hw hspan

end HeatKernel
