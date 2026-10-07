-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherSobolevRoot
public import RothschildStein.P2.BaseSobolevNoDriftLifted
public import RothschildStein.P2.SolvabilityFullNoDriftFrame
public import RothschildStein.P1.ParametrixStatementsNoDrift
public import RothschildStein.P1.StandardFrameIntegrability
public import RothschildStein.H1.CompleteAssembly

/-!
# Local regularity without drift, `L^p`: reduction of the higher Sobolev estimate to the P1 hypotheses

`HigherSobolevRegularityNoDrift` (higher Sobolev regularity without drift) is proved by
`higherSobolevRegularityNoDrift_of_hypotheses` (`HigherSobolevRoot`) from four operator and geometric hypotheses: the lifting theorem `LiftApproximationNoDriftStatement` (the lifted charts), `TypeCalculusAllChartsNoDrift` (row integrability, differentiation
and transfer), `SignedParametrixAllChartsNoDrift` (the signed parametrix) and `LiftedBaseSobolevAllChartsNoDrift` (the base Sobolev estimate, no drift). This file derives
the last three from two P1 hypotheses, quantified over the whole class of standard frames of
every no-drift chart (`3 ≤ n`, `0 < q`; the H1 kernel `K` of the no-drift model at
`ν = G2.smoothNorm C.G` arbitrary; the same class as `LeftDifferentiationAllChartsNoDrift`):

* `DifferentiationTransferAllChartsNoDrift` (differentiation and transfer): `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer` (for the model bracket
  basis `C.B`) for every standard frame. The remaining type-calculus Prop, `TypeKernelIntegrable`, is a theorem
  on every standard frame (`LiftedChart.IsStandardFrame.typeKernelIntegrable`).
* `ParametrixErrorTypesAllChartsNoDrift` (parametrix error types): `ParametrixErrorTypesNoDrift` (the error-type step) for every standard
  frame and every pair of cutoffs `a, b` of its region (the hypothesis `a b = a` is part of
  `ParametrixErrorTypesNoDrift`).

Derived statements:

* `typeCalculusAllChartsNoDrift_of_differentiationTransfer`: `TypeCalculusAllChartsNoDrift` from `DifferentiationTransferAllChartsNoDrift`;
* `leftDifferentiationAllChartsNoDrift_of_differentiationTransfer`: `LeftDifferentiationAllChartsNoDrift` from `DifferentiationTransferAllChartsNoDrift`;
* `signedParametrixAllChartsNoDrift_of_errorTypes`: `SignedParametrixAllChartsNoDrift` from `ParametrixErrorTypesAllChartsNoDrift`
  (`signedParametrixNoDrift_of_errorTypesNoDrift`: the frame fields of `IsStandardFrame` give
  `F.Θ = C.Θ`, `F.V ⊆ C.U`, `F.Γ = K`, `F.Γs = Γ*`);
* `liftedBaseSobolevAllChartsNoDrift_of_reducedHypotheses`: `LiftedBaseSobolevAllChartsNoDrift` from both
  (`liftedBaseSobolevEstimate_noDrift_of_representation`, at the standard frame `stdFrameNoDrift` of a
  patch `V ∋ ξ₀`, with cutoffs `a, b` of `exists_frame_cutoffs_noDrift`);
* `higherSobolevRegularityNoDrift_of_reducedHypotheses`: `HigherSobolevRegularityNoDrift` from `LiftApproximationNoDriftStatement` and both.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2

/-- The P1 type-calculus statements, without the row-integrability conjunct `TypeKernelIntegrable`
(proved on every standard frame by `LiftedChart.IsStandardFrame.typeKernelIntegrable`), for every standard
frame of every lifted no-drift chart over a system with `3 ≤ n` and `0 < q`, with every H1 fundamental
kernel `K` of the no-drift model of the chart at the smooth homogeneous norm of the chart group: left
and right differentiation of type-`λ` operators (`LeftDifferentiation`, `RightDifferentiation`, BB pp. 546-551, Thm 11.15) and
transfer to the integration variable along the model bracket basis `C.B` (`DerivativeTransfer`, BB
pp. 552-559, Thm 11.24). -/
def DifferentiationTransferAllChartsNoDrift : Prop :=
  ∀ {n q s m : ℕ} (hn : 3 ≤ n) (hq : 0 < q) {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : P1.LiftedChart noDriftWeight s Ω hΩ X x₀ m)
    (K : H1.FundamentalKernel C.G (C.noDriftModel hq (G2.smoothNorm C.G)))
    (F : KernelFrame (n + m))
    (hF : C.IsStandardFrame F (C.noDriftModel hq (G2.smoothNorm C.G)) K
      (C.two_lt_homogeneousDimension hn)),
    LeftDifferentiation F noDriftWeight C.Xl ∧
      RightDifferentiation F noDriftWeight C.Xl hF.lifted.contDiffOn_Xl ∧ DerivativeTransfer F noDriftWeight C.Xl C.B

/-- The types of the error terms of the signed parametrix without drift
(`ParametrixErrorTypesNoDrift`, BB pp. 561-563) for every standard frame of every lifted no-drift chart over
a system with `3 ≤ n` and `0 < q`, every H1 fundamental kernel `Γ` of the no-drift model of the chart
at the smooth homogeneous norm of the chart group, and all cutoffs `a, b ∈ C_c^∞(F.V)` (with
`a b = a` inside `ParametrixErrorTypesNoDrift`). By `signedParametrixNoDrift_of_errorTypesNoDrift` it is all
that the operator-level statement `SignedParametrixNoDrift` of the signed parametrix needs. -/
def ParametrixErrorTypesAllChartsNoDrift : Prop :=
  ∀ {n q s m : ℕ} (hn : 3 ≤ n) (hq : 0 < q) {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : P1.LiftedChart noDriftWeight s Ω hΩ X x₀ m)
    (Γ : H1.FundamentalKernel C.G (C.noDriftModel hq (G2.smoothNorm C.G)))
    (F : KernelFrame (n + m))
    (_hF : C.IsStandardFrame F (C.noDriftModel hq (G2.smoothNorm C.G)) Γ
      (C.two_lt_homogeneousDimension hn))
    (a b : TestFunction F.V ℝ (⊤ : ℕ∞)),
    ParametrixErrorTypesNoDrift C F hq (G2.smoothNorm C.G) Γ (C.two_lt_homogeneousDimension hn) a b

/-- The hypothesis `TypeCalculusAllChartsNoDrift` follows from
`DifferentiationTransferAllChartsNoDrift`: the row-integrability conjunct is `LiftedChart.IsStandardFrame.typeKernelIntegrable`. -/
theorem typeCalculusAllChartsNoDrift_of_differentiationTransfer (h : DifferentiationTransferAllChartsNoDrift) : TypeCalculusAllChartsNoDrift := by
  intro n q s m hn hq Ω hΩ X x₀ C K F hF
  exact ⟨hF.typeKernelIntegrable, h hn hq C K F hF⟩

/-- The hypothesis `LeftDifferentiation` for every standard frame of every lifted no-drift
chart (`LeftDifferentiationAllChartsNoDrift`) is the left-differentiation component of `DifferentiationTransferAllChartsNoDrift`. -/
theorem leftDifferentiationAllChartsNoDrift_of_differentiationTransfer (h : DifferentiationTransferAllChartsNoDrift) : LeftDifferentiationAllChartsNoDrift := by
  intro n q s m hn hq Ω hΩ X x₀ C K F hF
  exact (h hn hq C K F hF).1

/-- The hypothesis `SignedParametrixAllChartsNoDrift` (`SignedParametrixNoDrift F C.Xl C.c a b` for
every standard frame and every pair of cutoffs) follows from the error types `ParametrixErrorTypesAllChartsNoDrift`
(`signedParametrixNoDrift_of_errorTypesNoDrift`; the frame fields of `IsStandardFrame` are
`F.Θ = C.Θ`, `closure F.V ⊆ C.U`, `F.Γ = K`, `F.Γs = K.reflection`). -/
theorem signedParametrixAllChartsNoDrift_of_errorTypes (hE : ParametrixErrorTypesAllChartsNoDrift) : SignedParametrixAllChartsNoDrift := by
  intro n q s m hn hq Ω hΩ X x₀ C K F hF a b
  exact signedParametrixNoDrift_of_errorTypesNoDrift C hF.lifted.Θ_eq
    (subset_closure.trans hF.lifted.closure_subset) hq (G2.smoothNorm C.G) K
    (C.two_lt_homogeneousDimension hn) hF.Γ_eq hF.Γs_eq a b (hE hn hq C K F hF a b)

/-- **The lifted base Sobolev estimate without drift from the P1 hypotheses** (BB pp. 585-587,
Thms 11.42-11.43, (11.69)-(11.72)): `LiftedBaseSobolevAllChartsNoDrift` for every lifted no-drift chart over a
system with `3 ≤ n` and `0 < q`, from the P1 Props `DifferentiationTransferAllChartsNoDrift` and the error types
`ParametrixErrorTypesAllChartsNoDrift`. At the chart `C` with centre `ξ₀ = (x₀, 0)`: an H1 kernel `K` of the
no-drift model at `ν = G2.smoothNorm C.G` (`H1.exists_globalFundamentalKernel`), the standard frame
`stdFrameNoDrift` on a patch `V ∋ ξ₀` with `closure V ⊆ C.U` and cutoffs `a, b ∈ C_c^∞(V)` with
`a b = a`, `a = 1` near `ξ₀` (`exists_frame_cutoffs_noDrift`), `SignedParametrixNoDrift` from the error
types, `TypeKernelIntegrable` from the standard frame, and
`liftedBaseSobolevEstimate_noDrift_of_representation`. -/
theorem liftedBaseSobolevAllChartsNoDrift_of_reducedHypotheses (hP : DifferentiationTransferAllChartsNoDrift)
    (hE : ParametrixErrorTypesAllChartsNoDrift) : LiftedBaseSobolevAllChartsNoDrift := by
  intro n q s m hn hq Ω hΩ X x₀ C p hp hpt
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
  have hw : ∀ j : Fin q, ((noDriftWeight j : ℕ+) : ℕ) = 1 := fun j => rfl
  exact liftedBaseSobolevEstimate_noDrift_of_representation hF hw C.B hF.typeKernelIntegrable hLeftDiff
    hRightDiff hTransfer hc hc0 a hParametrix (G2.smoothNorm C.G) hsmooth ha hp hpt.ne

/-- **Higher Sobolev regularity without drift from the P1 hypotheses** (BB pp. 588-591,
Thm 11.45): `HigherSobolevRegularityNoDrift`, assuming the lifting theorem statement
(`LiftApproximationNoDriftStatement`) and the P1 hypotheses (`DifferentiationTransferAllChartsNoDrift`, `ParametrixErrorTypesAllChartsNoDrift`), by
`higherSobolevRegularityNoDrift_of_hypotheses` with the derived statements
`typeCalculusAllChartsNoDrift_of_differentiationTransfer`, `signedParametrixAllChartsNoDrift_of_errorTypes` and
`liftedBaseSobolevAllChartsNoDrift_of_reducedHypotheses`. -/
theorem higherSobolevRegularityNoDrift_of_reducedHypotheses (liftApproximation : LiftApproximationNoDriftStatement) (hP : DifferentiationTransferAllChartsNoDrift)
    (hE : ParametrixErrorTypesAllChartsNoDrift) : HigherSobolevRegularityNoDrift :=
  higherSobolevRegularityNoDrift_of_hypotheses liftApproximation (typeCalculusAllChartsNoDrift_of_differentiationTransfer hP)
    (signedParametrixAllChartsNoDrift_of_errorTypes hE) (liftedBaseSobolevAllChartsNoDrift_of_reducedHypotheses hP hE)

end RothschildStein.P2
