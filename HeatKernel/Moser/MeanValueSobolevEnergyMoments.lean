-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueEnergyStep
public import HeatKernel.Moser.MeanValueEnergyIntegrability
public import HeatKernel.Sobolev.GradientRepresentativeMoments
import Mathlib.Tactic

/-! # Higher moments from real quadratic Sobolev energy bounds -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- A uniform spatial Sobolev constant converts real slice and integrated energy
bounds into the parabolic higher-moment bound. The two quadratic bounds are
explicit inputs; the spatial Sobolev inequality and all extended-integral
conversions are supplied by the horizontal energy domain. -/
theorem exists_uniform_parabolic_moment_constant_of_energy_bounds {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (U : Opens (Fin N → ℝ)),
      volume (U : Set (Fin N → ℝ)) ≠ ⊤ →
      ∀ (τ : Measure ℝ) (w : ℝ → zeroBoundaryGraph U (G.horizontalFields hq)),
      MemLp w 2 τ → ∀ C M : ℝ, 0 ≤ C → 0 ≤ M →
      (∀ᵐ t ∂τ, ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤ C * M) →
      (∫ t, ‖(w t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ∂τ) ≤ C * M →
      (∫⁻ t, ∫⁻ x, ‖(w t : GradientSpace (N := N) ⊤ q).fst x‖ₑ ^
        (2 + 4 / ν) ∂volume ∂τ) ≤
          ENNReal.ofReal A * (ENNReal.ofReal C * ENNReal.ofReal M) ^ (1 + 2 / ν) := by
  obtain ⟨A₀, _, hSob⟩ :=
    exists_uniform_unnormalized_horizontal_sobolev_constant G hq hqpos hspan hw hν
  let A := max (A₀ * (volume.real
    (horizontalBall (G.horizontalFields hq) 0 1)) ^ (-2 / ν)) 1
  refine ⟨A, le_max_right _ _, ?_⟩
  intro U hfinite τ w hwmem C M hC _hM hslice henergy
  let energy := fun t => ‖(w t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
    ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2
  have hei : Integrable energy τ := by
    simpa only [one_pow, one_mul] using
      integrable_zeroBoundary_scaled_energy U (G.horizontalFields hq) τ hwmem 1
  have he0 : ∀ᵐ t ∂τ, 0 ≤ energy t := Filter.Eventually.of_forall fun _ => by
    dsimp only [energy]
    positivity
  have hquad (t : ℝ) :
      (∫⁻ x, ‖(w t : GradientSpace (N := N) ⊤ q).fst x‖ₑ ^ (2 : ℝ) ∂volume) =
        ENNReal.ofReal (‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) := by
    have hv : MemLp ((w t : GradientSpace (N := N) ⊤ q).fst) 2 volume := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        Lp.memLp ((w t : GradientSpace (N := N) ⊤ q).fst)
    have hn := (Sobolev.gradientSpace_norms_sq_eq_integrals_of_ae_eq
      (w t : GradientSpace (N := N) ⊤ q) Filter.EventuallyEq.rfl
      (fun _ => Filter.EventuallyEq.rfl)).1
    simp_rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [← ofReal_integral_eq_lintegral_ofReal hv.integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg _), ← hn]
  refine lintegral_parabolic_enorm_le_of_energy_bounds τ volume
    (lt_of_le_of_lt (le_max_left _ _) hν) ?_
      hei.aestronglyMeasurable.aemeasurable.ennreal_ofReal ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun t => by
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        (Lp.memLp ((w t : GradientSpace (N := N) ⊤ q).fst)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro t
    have hs := hSob U hfinite 1 (by norm_num) (w t)
    simp only [one_pow, one_mul] at hs
    rw [ENNReal.ofReal_mul' (show 0 ≤ energy t by positivity)] at hs
    exact hs.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl)
  · filter_upwards [hslice] with t ht
    rw [hquad t, ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal ht
  · rw [← ofReal_integral_eq_lintegral_ofReal hei he0, ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal henergy

end HeatKernel
