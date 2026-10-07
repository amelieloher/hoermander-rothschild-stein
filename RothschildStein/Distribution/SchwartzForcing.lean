-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.LocalizedForcing
public import RothschildStein.Distribution.SmoothLocalizedForcing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace SchwartzMap
namespace RothschildStein.Distribution

/-- the actual distribution equation yields its
localized Schwartz forcing identity, with the exact cutoff function. -/
theorem exists_schwartz_localized_forcing {k N : ℕ}
    (Ω : Opens (Fin N → ℝ))
    (Y : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (c : (Fin N → ℝ) → ℝ)
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) (Ω : Set (Fin N → ℝ)))
    (hcΩ : ContDiffOn ℝ (⊤ : ℕ∞) c (Ω : Set (Fin N → ℝ)))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Hormander.F.pushVectorFields Y i))
    (hXc : ∀ i, HasCompactSupport (Hormander.F.pushVectorFields Y i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) (fun y => c ((Hormander.F.coordinateEquiv N).symm y)))
    (hcc : HasCompactSupport (fun y => c ((Hormander.F.coordinateEquiv N).symm y)))
    (χ ζ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (hχ : ∀ x ∈ tsupport ζ, χ x = 1)
    (hζ : (fun y : Hormander.A.Carrier N => (ζ ((Hormander.F.coordinateEquiv N).symm y) : ℂ)).HasTemperateGrowth)
    (T : Distribution Ω ℂ (⊤ : ℕ∞)) (g : (Fin N → ℝ) → ℂ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ω : Set (Fin N → ℝ)))
    (heq : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T (adjointTest Ω Y c hY hcΩ ψ) =
      Distribution.ofFun Ω g MeasureTheory.volume (⊤ : ℕ∞) ψ) :
    ∃ f : SchwartzMap (Hormander.A.Carrier N) ℂ,
      (∀ y, f y = (ζ ((Hormander.F.coordinateEquiv N).symm y) : ℂ) *
        g ((Hormander.F.coordinateEquiv N).symm y)) ∧
      TemperedDistribution.smulLeftCLM ℂ
        (fun y : Hormander.A.Carrier N => (ζ ((Hormander.F.coordinateEquiv N).symm y) : ℂ))
        (Hormander.hormanderOp (Hormander.F.pushVectorFields Y)
          (fun y => c ((Hormander.F.coordinateEquiv N).symm y))
          (localizedTemperedEuclidean Ω χ T)) = (f : TemperedDistribution (Hormander.A.Carrier N) ℂ) := by
  obtain ⟨f, hf, hd⟩ := exists_schwartz_localized_smoothForcing Ω ζ g hg
  refine ⟨Hormander.F.schwartzToEuclideanCLM N f, ?_, ?_⟩
  · intro y
    exact hf ((Hormander.F.coordinateEquiv N).symm y)
  · rw [localized_forcing_of_distributionEquation Ω Y c hY hcΩ hX hXc hc hcc χ ζ hχ hζ T
      (Distribution.ofFun Ω g MeasureTheory.volume (⊤ : ℕ∞)) heq]
    change Hormander.F.temperedToEuclideanCLM N (localizedTempered Ω ζ
      (Distribution.ofFun Ω g MeasureTheory.volume (⊤ : ℕ∞))) = _
    rw [hd]
    exact temperedToEuclidean_coeSchwartz f

end RothschildStein.Distribution
