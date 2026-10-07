-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityReducedNoDrift
public import RothschildStein.P2.HigherHolderRoot
public import RothschildStein.P2.BaseHolderNoDriftLifted

/-!
# Local regularity without drift, Hölder: reduction of the higher Hölder estimate to the P1 hypotheses (the three P1 inputs)

`HigherHolderRegularityNoDrift` (higher Hölder regularity without drift) is proved by
`higherHolderRegularityNoDrift_of_hypotheses` (`HigherHolderRoot`) from the lifting theorem `LiftApproximationNoDriftStatement`, the
doubling interface `LocalDoublingAllChartsNoDrift` (the local doubling property) and three statements about the standard no-drift frames:
`HolderTypeCalculusAllChartsNoDrift` (row integrability, differentiation and transfer), `HolderSignedParametrixAllChartsNoDrift` (the signed parametrix) and
`LiftedBaseHolderAllChartsNoDrift` (the base Hölder estimate without drift). This file derives these three from the two P1 hypotheses
statements of `LocalRegularityReducedNoDrift`, quantified over the whole class of standard frames of every
no-drift chart (`3 ≤ n`, `0 < q`): `DifferentiationTransferAllChartsNoDrift` (differentiation and transfer) and `ParametrixErrorTypesAllChartsNoDrift` (parametrix error types).

* `holderTypeCalculusAllChartsNoDrift_of_differentiationTransfer`: `HolderTypeCalculusAllChartsNoDrift` from `DifferentiationTransferAllChartsNoDrift` (the row-integrability
  conjunct is `LiftedChart.IsStandardFrame.typeKernelIntegrable`);
* `holderSignedParametrixAllChartsNoDrift_of_errorTypes`: `HolderSignedParametrixAllChartsNoDrift` from `ParametrixErrorTypesAllChartsNoDrift`
  (`signedParametrixNoDrift_of_errorTypesNoDrift`);
* `liftedBaseHolderAllChartsNoDrift_of_reducedHypotheses`: `LiftedBaseHolderAllChartsNoDrift` from both
  (`liftedBaseHolderEstimate_noDrift_of_representation`, at the standard frame `stdFrameNoDrift` of a
  patch `V ∋ ξ₀`, with cutoffs `a, b` of `exists_frame_cutoffs_noDrift`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2

/-- `HolderTypeCalculusAllChartsNoDrift` (the P1 type-calculus statements `TypeKernelIntegrable`,
`LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer` for every standard no-drift frame) follows from
`DifferentiationTransferAllChartsNoDrift`: the row-integrability conjunct is `LiftedChart.IsStandardFrame.typeKernelIntegrable`. -/
theorem holderTypeCalculusAllChartsNoDrift_of_differentiationTransfer (h : DifferentiationTransferAllChartsNoDrift) : HolderTypeCalculusAllChartsNoDrift := by
  intro n q s m hn hq Ω hΩ X x₀ C K F hF
  exact ⟨hF.typeKernelIntegrable, h hn hq C K F hF⟩

/-- `HolderSignedParametrixAllChartsNoDrift` (`SignedParametrixNoDrift F C.Xl C.c a b` for every standard no-drift frame and
every pair of cutoffs) follows from the error types `ParametrixErrorTypesAllChartsNoDrift`
(`signedParametrixNoDrift_of_errorTypesNoDrift`; the frame fields of `IsStandardFrame` are `F.Θ = C.Θ`,
`closure F.V ⊆ C.U`, `F.Γ = K`, `F.Γs = K.reflection`). -/
theorem holderSignedParametrixAllChartsNoDrift_of_errorTypes (hE : ParametrixErrorTypesAllChartsNoDrift) : HolderSignedParametrixAllChartsNoDrift := by
  intro n q s m hn hq Ω hΩ X x₀ C K F hF a b
  exact signedParametrixNoDrift_of_errorTypesNoDrift C hF.lifted.Θ_eq
    (subset_closure.trans hF.lifted.closure_subset) hq (G2.smoothNorm C.G) K
    (C.two_lt_homogeneousDimension hn) hF.Γ_eq hF.Γs_eq a b (hE hn hq C K F hF a b)

/-- **The lifted base Hölder estimate without drift from the P1 hypotheses** (BB pp. 600-602,
Thms 11.57-11.58, (11.92)-(11.93)): `LiftedBaseHolderAllChartsNoDrift` for every lifted no-drift chart over a
system with `3 ≤ n` and `0 < q`, from the P1 Props `DifferentiationTransferAllChartsNoDrift` and the error types
`ParametrixErrorTypesAllChartsNoDrift`. At the chart `C` with centre `ξ₀ = (x₀, 0)`: an H1 kernel `K` of the no-drift model
at `ν = G2.smoothNorm C.G` (`H1.exists_globalFundamentalKernel`), the standard frame `stdFrameNoDrift` on a
patch `V ∋ ξ₀` with `closure V ⊆ C.U` and cutoffs `a, b ∈ C_c^∞(V)` with `a b = a`, `a = 1` near `ξ₀`
(`exists_frame_cutoffs_noDrift`), `SignedParametrixNoDrift` from the error types, `TypeKernelIntegrable` from the
standard frame, and `liftedBaseHolderEstimate_noDrift_of_representation`. -/
theorem liftedBaseHolderAllChartsNoDrift_of_reducedHypotheses (hP : DifferentiationTransferAllChartsNoDrift)
    (hE : ParametrixErrorTypesAllChartsNoDrift) : LiftedBaseHolderAllChartsNoDrift := by
  intro n q s m hn hq Ω hΩ X x₀ C α hα0 hα1
  have hQ := C.two_lt_homogeneousDimension hn
  obtain ⟨K⟩ := (C.noDriftModel hq (G2.smoothNorm C.G)).exists_globalFundamentalKernel C.G hQ
  have hprops : H1.FundamentalKernelProperties K := H1.assemble_kernel K hQ
  have hsymm : ∀ u, (C.noDriftModel hq (G2.smoothNorm C.G)).norm (-u) =
      (C.noDriftModel hq (G2.smoothNorm C.G)).norm u := fun u => by
    have hu := C.smoothNorm_symmetric u
    rwa [show C.G.inv u = -u from C.inv_eq_neg u] at hu
  have hsmooth : (C.noDriftModel hq (G2.smoothNorm C.G)).norm.Smooth := G2.smoothNorm_smooth C.G
  -- the patch, the cutoffs and the standard frame at the chart centre
  obtain ⟨V, a, b₀, hξV, hVcl, hab, ha1⟩ := exists_frame_cutoffs_noDrift C C.center_mem
  have hVU : (V : Set (Fin (n + m) → ℝ)) ⊆ C.U := subset_closure.trans hVcl
  have hF := isStandardFrame_stdFrameNoDrift K hQ V hVcl hsymm hsmooth hprops
  obtain ⟨hLeftDiff, hRightDiff, hTransfer⟩ := hP hn hq C K _ hF
  -- `SignedParametrixNoDrift` for every `b`, from the error types
  have hParametrix : ∀ b : TestFunction (stdFrameNoDrift C K hQ V).V ℝ (⊤ : ℕ∞),
      SignedParametrixNoDrift (stdFrameNoDrift C K hQ V) C.Xl C.c a b := fun b =>
    signedParametrixNoDrift_of_errorTypesNoDrift C rfl hVU hq (G2.smoothNorm C.G) K hQ rfl rfl a b
      (hE hn hq C K _ hF a b)
  -- the density and the cutoff near the centre
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) C.c (V : Set (Fin (n + m) → ℝ)) := C.density_smooth.mono hVU
  have hc0 : ∀ ξ ∈ (V : Set (Fin (n + m) → ℝ)), 0 < C.c ξ := fun ξ hξ => C.density_pos ξ (hVU hξ)
  have ha : ∀ᶠ x in 𝓝 (joinPoint x₀ (0 : Fin m → ℝ)),
      x ∈ ((stdFrameNoDrift C K hQ V).V : Set (Fin (n + m) → ℝ)) ∧ a x = 1 := by
    filter_upwards [V.isOpen.mem_nhds hξV, ha1] with x hx hx1
    exact ⟨hx, hx1⟩
  exact liftedBaseHolderEstimate_noDrift_of_representation hF C.B hF.typeKernelIntegrable hLeftDiff hRightDiff hTransfer
    hc hc0 a hParametrix (G2.smoothNorm C.G) hsmooth ha hα0 hα1

end RothschildStein.P2
