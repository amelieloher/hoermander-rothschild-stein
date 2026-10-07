-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.SchwartzForcing
public import RothschildStein.Distribution.LocalizedBootstrap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter SchwartzMap TopologicalSpace
open scoped Topology
namespace RothschildStein.Distribution

/-- a real-test distribution equation on a framed
compact coefficient patch gives a smooth localized representative.
Both the Sobolev start and the Schwartz forcing identity are proved
from the original distribution and equation in this theorem. -/
theorem patchedDistribution_smooth_of_equation {k N : ℕ}
    (Ω : Opens (Fin N → ℝ))
    (Y : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (c : (Fin N → ℝ) → ℝ)
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) (Ω : Set (Fin N → ℝ)))
    (hcΩ : ContDiffOn ℝ (⊤ : ℕ∞) c (Ω : Set (Fin N → ℝ)))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Hormander.F.pushVectorFields Y i))
    (hXc : ∀ i, HasCompactSupport (Hormander.F.pushVectorFields Y i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) (fun y => c ((Hormander.F.coordinateEquiv N).symm y)))
    (hcc : HasCompactSupport (fun y => c ((Hormander.F.coordinateEquiv N).symm y)))
    (χ η : TestFunction Ω ℝ (⊤ : ℕ∞)) (hχ : ∀ x ∈ tsupport η, χ x = 1)
    {K U : Set (Hormander.A.Carrier N)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (w : Fin N → Hormander.Interface.LieWord k)
    (hw : ∀ x ∈ U, LinearIndependent ℝ (fun a => Hormander.lieWordEval (Hormander.F.pushVectorFields Y) (w a) x))
    (ζ : Hormander.A.Carrier N → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζη : ∀ᶠ y in 𝓝ˢ (tsupport ζ), η ((Hormander.F.coordinateEquiv N).symm y) = 1)
    (hηK : tsupport (fun y : Hormander.A.Carrier N => η ((Hormander.F.coordinateEquiv N).symm y)) ⊆ K)
    (T : Distribution Ω ℂ (⊤ : ℕ∞)) (g : (Fin N → ℝ) → ℂ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ω : Set (Fin N → ℝ)))
    (heq : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T (adjointTest Ω Y c hY hcΩ ψ) =
      Distribution.ofFun Ω g volume (⊤ : ℕ∞) ψ) :
    ∃ F : Hormander.A.Carrier N → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ φ : SchwartzMap (Hormander.A.Carrier N) ℂ,
        Integrable (fun y => φ y * F y) ∧
        TemperedDistribution.smulLeftCLM ℂ (fun y => (ζ y : ℂ))
          (localizedTemperedEuclidean Ω χ T) φ = ∫ y, φ y * F y := by
  have hηg : (fun x : Fin N → ℝ => (η x : ℂ)).HasTemperateGrowth := by
    convert (SchwartzMap.postcompCLM Complex.ofRealCLM
      (η.hasCompactSupport.toSchwartzMap η.contDiff)).hasTemperateGrowth using 1
    funext x
    rfl
  have hηge : (fun y : Hormander.A.Carrier N => (η ((Hormander.F.coordinateEquiv N).symm y) : ℂ)).HasTemperateGrowth := by
    exact hηg.comp (Hormander.F.coordinateEquiv N).symm.toContinuousLinearMap.hasTemperateGrowth
  obtain ⟨f, _, hf⟩ := exists_schwartz_localized_forcing Ω Y c hY hcΩ hX hXc hc hcc χ η hχ hηge T g hg heq
  have hη : ContDiff ℝ (⊤ : ℕ∞) (fun y : Hormander.A.Carrier N => η ((Hormander.F.coordinateEquiv N).symm y)) :=
    η.contDiff.comp (Hormander.F.coordinateEquiv N).symm.contDiff
  exact localizedDistribution_smooth_of_forcing Ω χ T (Hormander.F.pushVectorFields Y)
    (fun y => c ((Hormander.F.coordinateEquiv N).symm y)) hX hXc hc hcc hK hU hKU w hw
    hζ hη hζη hηK (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hηg) hηge f hf

end RothschildStein.Distribution
