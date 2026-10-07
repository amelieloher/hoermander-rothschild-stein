-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RightPoleComputation
public import RothschildStein.P1.ModelHypotheses
public import RothschildStein.H1.KernelData
public import RothschildStein.H1.OperatorIntegrationByParts
public import RothschildStein.H1.TransposeLocality

/-!
# The model identity `𝓛 Γ = 0` off the origin, and the right pole formula for the fundamental kernel

The H1 fundamental kernel `K : FundamentalKernel G H` satisfies `∫ K · 𝓛*φ = φ(0)` for tests `φ`
(`FundamentalKernel.fundamental`) and is smooth off the origin. Pairing with tests supported
away from `0` and using Green's identity on the open set `{0}ᶜ`
(`StandingHypotheses.integral_operator_test_on`) gives `𝓛 K = 0` pointwise off the origin
(`sumSquaresWithDrift_kernel_eq_zero`). With the lifted chart's drift model
(`LiftedChart.driftModel`, fields `C.Y`) this turns the right pole formula into
`L̃_ξ[K(Θ(η, ξ))] = E(η, Θ(η, ξ))` for `ξ ∈ C.U`, `ξ ≠ η`
(`LiftedChart.sumSquaresWithDrift_kernel_comp_theta`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.P1

/-- The H1 fundamental kernel is annihilated by the model
operator off the origin: `𝓛 K = ∑_{i ≥ 1} Yᵢ² K + Y₀ K = 0` on `{0}ᶜ` (the pointwise form of
`𝓛 K = δ₀`; BB Thm 11.5(a), Thm 6.18, p. 264). -/
theorem sumSquaresWithDrift_kernel_eq_zero {N q : ℕ} {G : HomogeneousGroup N}
    {H : H1.StandingHypotheses G q} (K : H1.FundamentalKernel G H) {x : Fin N → ℝ}
    (hx : x ≠ 0) : sumSquaresWithDrift H.fields K x = 0 := by
  let U : Opens (Fin N → ℝ) := ⟨{(0 : Fin N → ℝ)}ᶜ, isOpen_compl_singleton⟩
  have hd0 : ContDiffOn ℝ (⊤ : ℕ∞) (fieldDerivative (H.fields 0) K) (U : Set (Fin N → ℝ)) :=
    S.contDiffOn_fieldDerivative U (H.fields 0) K (H.fields_smooth G 0).contDiffOn
      K.smooth_off_zero
  have hdd (i : Fin q) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields i.succ) K))
      (U : Set (Fin N → ℝ)) :=
    S.contDiffOn_fieldDerivative U (H.fields i.succ) _ (H.fields_smooth G i.succ).contDiffOn
      (S.contDiffOn_fieldDerivative U (H.fields i.succ) K
        (H.fields_smooth G i.succ).contDiffOn K.smooth_off_zero)
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (sumSquaresWithDrift H.fields K) (U : Set (Fin N → ℝ)) :=
    hd0.add (ContDiffOn.sum fun i _ => hdd i)
  have h0 : (0 : Fin N → ℝ) ∉ ({0}ᶜ : Set (Fin N → ℝ)) := fun h => h rfl
  have hpair : ∀ B : TestFunction U ℝ (⊤ : ℕ∞),
      (∫ y in (U : Set (Fin N → ℝ)), sumSquaresWithDrift H.fields K y * B y) = 0 := by
    intro B
    rw [H.integral_operator_test_on G U K K.smooth_off_zero B]
    have h1 : (∫ y in (U : Set (Fin N → ℝ)), K y * sumSquaresWithDriftTranspose H.fields B y) =
        ∫ y, K y * sumSquaresWithDriftTranspose H.fields B y :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
        have hp := image_eq_zero_of_notMem_tsupport (fun ht => hy
          (B.tsupport_subset (H1.tsupport_sumSquaresTranspose_subset H.fields B ht)))
        rw [hp, mul_zero])
    rw [h1, K.fundamental B B.contDiff B.hasCompactSupport]
    exact image_eq_zero_of_notMem_tsupport (fun h => h0 (B.tsupport_subset h))
  have hae := U.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := (volume : Measure (Fin N → ℝ))) (f := sumSquaresWithDrift H.fields K)
    (hg.continuousOn.locallyIntegrableOn U.isOpen.measurableSet) (fun g' hg' hcs hts => by
      have h2 := hpair ⟨g', hg', hcs, hts⟩
      calc ∫ y, g' y • sumSquaresWithDrift H.fields K y
          = ∫ y in (U : Set (Fin N → ℝ)), g' y • sumSquaresWithDrift H.fields K y :=
            (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
              simp [image_eq_zero_of_notMem_tsupport (fun h => hy (hts h))])).symm
        _ = ∫ y in (U : Set (Fin N → ℝ)), sumSquaresWithDrift H.fields K y * g' y := by
            simp_rw [smul_eq_mul, mul_comm]
        _ = 0 := h2)
  have hae' : sumSquaresWithDrift H.fields K =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
      fun _ => (0 : ℝ) :=
    (ae_restrict_iff' U.isOpen.measurableSet).mpr hae
  exact Measure.eqOn_open_of_ae_eq hae' U.isOpen hg.continuousOn continuousOn_const hx

end RothschildStein.P1
