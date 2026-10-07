-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityReducedDriftDifferentiation
public import RothschildStein.P2.BaseHolderLifted

/-!
# Local regularity with drift, Hölder: reduction of the base Hölder estimate to the P1 hypotheses

`LiftedBaseHolderAllChartsDrift` (the lifted base Hölder estimate at the smooth homogeneous norm of every
drift chart) is provable from the P1 statements through `liftedBaseHolderEstimate_of_representation`
(`BaseHolderLifted`), exactly as `LiftedBaseSobolevAllChartsDrift` is through `liftedBaseSobolevEstimate_of_representation`
(`LocalRegularityReducedDrift`). At the chart `C` with centre `ξ₀ = (x₀, 0)` that theorem needs

* a standard frame `F` of `C` whose cutoff region `V` is a neighbourhood of `ξ₀`
  (`exists_frame_cutoffs`, `stdFrame`, `isStandardFrame_stdFrame`, an H1 fundamental kernel `K` of the
  drift model at the smooth homogeneous norm `ν = G2.smoothNorm C.G`, `H1.exists_globalFundamentalKernel`);
* the Props `TypeKernelIntegrable` (a theorem on every standard frame,
  `LiftedChart.IsStandardFrame.typeKernelIntegrable`), `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer` (for the model
  bracket basis `C.B`) of that frame: the hypothesis `DifferentiationTransferAllChartsDrift`;
* the density data `c = C.c` and cutoffs `a, b ∈ C_c^∞(V)` with `a b = a` and `a = 1` near `ξ₀`;
* `SignedParametrix F C.Xl C.c a b` for every `b`, which `signedParametrix_of_errorTypes` derives from the
  hypothesis `ParametrixErrorTypesAllChartsDrift` (`ParametrixErrorTypes`).

`liftedBaseHolderAllChartsDrift_of_reducedHypotheses` derives `LiftedBaseHolderAllChartsDrift` from `DifferentiationTransferAllChartsDrift` and
`ParametrixErrorTypesAllChartsDrift`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2

/-- **The lifted base Hölder estimate from the P1 hypotheses** (BB pp. 600-602,
Thms 11.57-11.58, (11.92)-(11.93)): `LiftedBaseHolderAllChartsDrift` for every lifted drift chart over a system with
`3 ≤ n` and `0 < q`, from the type-calculus Props `DifferentiationTransferAllChartsDrift` (the row integrability is
proved on every standard frame) and the error types `ParametrixErrorTypesAllChartsDrift` (the parametrix error types). At the chart `C` with
centre `ξ₀ = (x₀, 0)`: an H1 kernel `K` of the drift model at `ν = G2.smoothNorm C.G`
(`H1.exists_globalFundamentalKernel`), the standard frame `stdFrame` on a patch `V ∋ ξ₀` with
`closure V ⊆ C.U` and cutoffs `a, b ∈ C_c^∞(V)` with `a b = a`, `a = 1` near `ξ₀`
(`exists_frame_cutoffs`), `SignedParametrix` from the error types, and
`liftedBaseHolderEstimate_of_representation`. -/
theorem liftedBaseHolderAllChartsDrift_of_reducedHypotheses (hP : DifferentiationTransferAllChartsDrift) (hE : ParametrixErrorTypesAllChartsDrift) :
    LiftedBaseHolderAllChartsDrift := by
  intro n q s m hn hq Ω hΩ X x₀ C α hα0 hα1
  have hQ := C.two_lt_homogeneousDimension hn
  obtain ⟨K⟩ := (C.driftModel hq (G2.smoothNorm C.G)).exists_globalFundamentalKernel C.G hQ
  have hprops : H1.FundamentalKernelProperties K := H1.assemble_kernel K hQ
  have hsymm : ∀ u, (C.driftModel hq (G2.smoothNorm C.G)).norm (-u) =
      (C.driftModel hq (G2.smoothNorm C.G)).norm u := fun u => by
    have hu := C.smoothNorm_symmetric u
    rwa [show C.G.inv u = -u from C.inv_eq_neg u] at hu
  have hsmooth : (C.driftModel hq (G2.smoothNorm C.G)).norm.Smooth := G2.smoothNorm_smooth C.G
  -- the patch, the cutoffs and the standard frame at the chart centre
  obtain ⟨V, a, b₀, hξV, hVcl, hab, ha1⟩ := exists_frame_cutoffs C C.center_mem
  have hVU : (V : Set (Fin (n + m) → ℝ)) ⊆ C.U := subset_closure.trans hVcl
  have hF := isStandardFrame_stdFrame K hQ V hVcl hsymm hsmooth hprops
  obtain ⟨hLeftDiff, hRightDiff, hTransfer⟩ := hP hn hq C K _ hF
  -- `SignedParametrix` for every `b`, from the error types
  have hParametrix : ∀ b : TestFunction (stdFrame C K hQ V).V ℝ (⊤ : ℕ∞),
      SignedParametrix (stdFrame C K hQ V) C.Xl C.c a b := fun b =>
    signedParametrix_of_errorTypes C rfl hVU hq (G2.smoothNorm C.G) K hQ rfl rfl a b
      (hE hn hq C K _ hF a b)
  -- the density and the cutoff near the centre
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) C.c (V : Set (Fin (n + m) → ℝ)) := C.density_smooth.mono hVU
  have hc0 : ∀ ξ ∈ (V : Set (Fin (n + m) → ℝ)), 0 < C.c ξ := fun ξ hξ => C.density_pos ξ (hVU hξ)
  have ha : ∀ᶠ x in 𝓝 (joinPoint x₀ (0 : Fin m → ℝ)),
      x ∈ ((stdFrame C K hQ V).V : Set (Fin (n + m) → ℝ)) ∧ a x = 1 := by
    filter_upwards [V.isOpen.mem_nhds hξV, ha1] with x hx hx1
    exact ⟨hx, hx1⟩
  exact liftedBaseHolderEstimate_of_representation hF C.B hF.typeKernelIntegrable hLeftDiff hRightDiff hTransfer hc hc0 a
    hParametrix (G2.smoothNorm C.G) hsmooth ha hα0 hα1

end RothschildStein.P2
