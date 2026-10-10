-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerLocalizedEnergy
public import HeatKernel.Moser.MeanValueSobolevEnergyMoments

/-! # Uniform parabolic moments from reciprocal graph budgets -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- Scalar reciprocal budgets and graph comparisons needed for the localized
parabolic moment estimate. All time integrability and cutoff conditions are explicit. -/
def HasReciprocalLocalizedGraphBudget {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (a b ell H L : ℝ) (Y : ℝ → zeroBoundaryGraph V X)
    (θ D m : ℝ → ℝ) : Prop :=
  0 < ell ∧ 0 ≤ H ∧ 0 ≤ L ∧ MemLp Y 2 (volume.restrict (Icc a b)) ∧
  Continuous θ ∧ (∀ t ∈ Icc a b, θ t ∈ Icc (0 : ℝ) 1) ∧
  IntegrableOn D (Icc a b) ∧ IntegrableOn m (Icc a b) ∧
  (∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ D t) ∧
  (∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ m t) ∧
  (∀ᵐ t ∂volume.restrict (Icc a b),
    ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤ m t) ∧
  (∀ᵐ t ∂volume.restrict (Icc a b),
    ‖(Y t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 ≤ D t / ell + 2 * L * m t) ∧
  (∀ᵐ t ∂volume.restrict (Icc a b),
    θ t ^ 2 * ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤ H * (∫ s in Icc a b, m s)) ∧
  (∫ t in Icc a b, θ t ^ 2 * D t) ≤ H * (∫ t in Icc a b, m t)

/-- Reciprocal scalar budgets give a parabolic graph moment estimate with one
constant independent of the graph curve, time interval, and all cutoff costs. -/
theorem exists_uniform_reciprocal_graph_moment_constant {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hwG : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (V : Opens (Fin N → ℝ)),
      volume (V : Set (Fin N → ℝ)) ≠ ⊤ →
      ∀ (a b ell H L : ℝ) (Y : ℝ → zeroBoundaryGraph V (G.horizontalFields hq))
        (θ D m : ℝ → ℝ),
      HasReciprocalLocalizedGraphBudget a b ell H L Y θ D m →
      (∫⁻ t in Icc a b, ∫⁻ x,
        ‖((θ t • Y t : zeroBoundaryGraph V (G.horizontalFields hq)) :
          GradientSpace (N := N) ⊤ q).fst x‖ₑ ^ (2 + 4 / ν) ∂volume) ≤
        ENNReal.ofReal A * (ENNReal.ofReal (H + H / ell + 2 * L + 1) *
          ENNReal.ofReal (∫ t in Icc a b, m t)) ^ (1 + 2 / ν) := by
  obtain ⟨A, hA, hSob⟩ := exists_uniform_parabolic_moment_constant_of_energy_bounds
    G hq hqpos hspan hwG hν
  refine ⟨A, hA, ?_⟩
  intro V hfinite a b ell H L Y θ D m hb
  obtain ⟨hell, hH, hL, hY, hθ, hθunit, hD, hm, hD0, hm0,
    hvalue, hgradient, hslice, htotal⟩ := hb
  obtain ⟨hw, hs, he⟩ := reciprocal_localized_graph_energy_bounds
    hell hH hL hY hθ hθunit hD hm hD0 hm0 hvalue hgradient hslice htotal
  exact hSob V hfinite (volume.restrict (Icc a b)) (fun t => θ t • Y t) hw
    (H + H / ell + 2 * L + 1) (∫ t in Icc a b, m t)
    (by positivity) (integral_nonneg_of_ae hm0) hs he

end HeatKernel
