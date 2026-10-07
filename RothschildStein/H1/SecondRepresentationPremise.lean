-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.AssemblyInputs
public import RothschildStein.H1.FundamentalSecondDerivative
public import RothschildStein.H1.ExteriorCoefficientComparison
public import RothschildStein.H1.PrincipalValueSubstitution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter Topology
namespace RothschildStein.H1
variable {N q : ℕ} {G : HomogeneousGroup N} {H : StandingHypotheses G q}

/-- The second-derivative representation has absolute truncation
integrability, uniform convergence, and a formula for every smooth exterior
cutoff (BB pp. 281–285). -/
theorem FundamentalKernel.secondKernelRepresentation (K : FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) : Nonempty (SecondKernelRepresentation K) := by
  obtain ⟨η, R₀, hη, hsη, heη, hR₀, houtη, hbη⟩ := exists_compactGaugeCutoff G H.norm.gauge
  let α : Fin q → Fin q → ℝ := fun i j => ∫ w in {w | H.norm w ≤ R₀},
    fieldDerivative (H.fields i.succ) (fun v => fieldDerivative (H.fields j.succ) K v * (1 - η v)) w
  refine ⟨⟨α, ?_, ?_, ?_⟩⟩
  · intro φ i j x ε hε
    let ψ := sumSquaresTest ⊤ H.fields (fun k => (H.fields_smooth G k).contDiffOn) φ
    have hψ : (ψ : (Fin N → ℝ) → ℝ) = sumSquaresWithDrift H.fields φ :=
      funext (sumSquaresTest_apply ⊤ H.fields (fun k => (H.fields_smooth G k).contDiffOn) φ)
    have hF := (H.wordDerivative_smooth_off_zero G K.smooth_off_zero [i.succ, j.succ]).continuousOn
    have hi := integrableOn_principalValue_firstTruncation G H.norm.gauge hF
      ψ.contDiff.continuous ψ.hasCompactSupport hε x
    rw [hψ] at hi
    exact hi
  · intro φ i j
    have he := K.secondDerivative_representation G H hQ i j hη hsη heη hR₀ houtη hbη
      φ.contDiff φ.hasCompactSupport
    have hPV : principalValueConvolution G H.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K))
        (sumSquaresWithDrift H.fields φ) = fun x =>
          fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) φ) x -
            α i j * sumSquaresWithDrift H.fields φ x := by
      funext x
      have hx := congrFun he x
      change _ = _ + _ * α i j at hx
      linarith
    simp_rw [principalValue_firstTruncation_eq G H.norm.gauge]
    rw [← hPV]
    exact K.secondDerivative_uniformPrincipalValue G H i j φ.contDiff φ.hasCompactSupport
  · intro θ hθ hnear R hR hout i j
    obtain ⟨r, hr, honear⟩ := hnear
    have heθ : θ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0 := by
      have hzero : H.norm (0 : Fin N → ℝ) = 0 := (H.norm.gauge.2.2.1 0).mpr rfl
      filter_upwards [(isOpen_lt H.norm.gauge.1 continuous_const).mem_nhds
        (show H.norm (0 : Fin N → ℝ) < r by simpa only [hzero] using hr)] with x hx
      exact honear x hx.le
    obtain ⟨ηR, hηR, hsηR, heηR, houtηR, hbηR⟩ := exists_compactGaugeCutoff_atRadius G H.norm.gauge hR
    have heθR : (fun x => 1 - ηR x) =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0 := by
      filter_upwards [heηR] with x hx
      rw [hx, sub_self]
    have hθRout : ∀ x, R ≤ H.norm x → 1 - ηR x = 1 := by
      intro x hx
      rw [houtηR x hx, sub_zero]
    have hf := H.wordDerivative_smooth_off_zero G K.smooth_off_zero [j.succ]
    change ContDiffOn ℝ (⊤ : ℕ∞) (fieldDerivative (H.fields j.succ) K) {(0 : Fin N → ℝ)}ᶜ at hf
    have hhom := H.firstKernel_C1 G j (K.smooth_off_zero.of_le (by simp)) K.homogeneous
    have hc := H.criticalCutoffCoefficient_independent G i hhom.1 hhom.2
      hη hsη heη hR₀ houtη hbη hηR hsηR heηR hR houtηR hbηR
    have hcomp := H.exteriorCoefficient_eq_sameRadius G i hf
      hθ (contDiff_const.sub hηR) heθ heθR hout hθRout
    change α i j = _
    change α i j = _ at hc
    rw [hc, ← hcomp]
    congr 1
    funext x
    congr 1
    funext y
    exact mul_comm _ _

end RothschildStein.H1
