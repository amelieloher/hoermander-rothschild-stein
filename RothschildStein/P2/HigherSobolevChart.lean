-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherSobolevLocalReg
public import RothschildStein.P2.LocalRegularitySolvability
public import RothschildStein.P2.SolvabilityFullNoDriftFrame

/-!
# The chart-level regularity and estimate from the operator and geometric hypotheses

The operator and geometric hypotheses on which the higher Sobolev estimate depends for a lifted no-drift chart `C` with
`3 ≤ n` (the model has `Q ≥ n ≥ 3`, the homogeneous-dimension condition):

* `TypeCalculusAllChartsNoDrift` (row integrability, differentiation and transfer): `TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer` (for the
  basis words `C.B` of the chart) on every standard frame of every chart, with every H1 fundamental kernel `K` of
  the no-drift model at the smooth homogeneous norm of the chart group;
* `SignedParametrixAllChartsNoDrift` (the signed parametrix): `SignedParametrixNoDrift` with the chart density `C.c`, for every standard frame and every
  pair of cutoffs;
* `LiftedBaseSobolevAllChartsNoDrift` (the base Sobolev estimate): the lifted base estimate `LiftedBaseSobolevEstimate` without drift at the
  smooth homogeneous norm of every no-drift chart.

`chart_higher_of_upstream` builds, at every chart, the standard frame (`stdFrameNoDrift`, the H1 kernel, a cutoff
`a = 1` near the centre), the bundle `HigherFrame`, and concludes the lifted regularity
`LiftedHigherRegularity` and the lifted higher estimate `LiftedHigherEstimate`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2

/-- The type-calculus hypotheses `TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer`
(the last for the basis words `C.B`) for every standard frame of every lifted no-drift chart over a system with
`3 ≤ n` (`0 < q`), with every H1 fundamental kernel `K` of the no-drift model of the chart at the smooth
homogeneous norm of the chart group. -/
def TypeCalculusAllChartsNoDrift : Prop :=
  ∀ {n q s m : ℕ} (hn : 3 ≤ n) (hq : 0 < q) {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : P1.LiftedChart noDriftWeight s Ω hΩ X x₀ m)
    (K : H1.FundamentalKernel C.G (C.noDriftModel hq (G2.smoothNorm C.G)))
    (F : KernelFrame (n + m))
    (hF : C.IsStandardFrame F (C.noDriftModel hq (G2.smoothNorm C.G)) K
      (C.two_lt_homogeneousDimension hn)),
    TypeKernelIntegrable F ∧ LeftDifferentiation F noDriftWeight C.Xl ∧
      RightDifferentiation F noDriftWeight C.Xl hF.lifted.contDiffOn_Xl ∧ DerivativeTransfer F noDriftWeight C.Xl C.B

/-- The hypothesis `SignedParametrixNoDrift` (the operator-level conclusion of the signed
parametrix, BB Thm 11.25 without drift) with the chart density `C.c`, for every standard frame of every lifted
no-drift chart over a system with `3 ≤ n`, and every pair of cutoffs `a, b`. -/
def SignedParametrixAllChartsNoDrift : Prop :=
  ∀ {n q s m : ℕ} (hn : 3 ≤ n) (hq : 0 < q) {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : P1.LiftedChart noDriftWeight s Ω hΩ X x₀ m)
    (K : H1.FundamentalKernel C.G (C.noDriftModel hq (G2.smoothNorm C.G)))
    (F : KernelFrame (n + m))
    (_hF : C.IsStandardFrame F (C.noDriftModel hq (G2.smoothNorm C.G)) K
      (C.two_lt_homogeneousDimension hn))
    (a b : TestFunction F.V ℝ (⊤ : ℕ∞)), SignedParametrixNoDrift F C.Xl C.c a b

/-- The lifted base Sobolev estimate without drift (BB pp. 585-587, Thms 11.42-11.43,
(11.69)-(11.72)): for every lifted no-drift chart over a system with `3 ≤ n`, `0 < q` and every `1 < p < ∞`,
`LiftedBaseSobolevEstimate` at the smooth homogeneous norm of the chart group. -/
def LiftedBaseSobolevAllChartsNoDrift : Prop :=
  ∀ {n q s m : ℕ}, 3 ≤ n → 0 < q → ∀ {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : P1.LiftedChart noDriftWeight s Ω hΩ X x₀ m) {p : ℝ≥0∞}, 1 < p → p < ⊤ →
    LiftedBaseSobolevEstimate C (G2.smoothNorm C.G) (noDriftOpWords q) p

/-- **The chart-level conclusions**: from the upstream statements, at every lifted no-drift chart with
`3 ≤ n` and `1 < p < ∞`, the lifted regularity (`u ∈ W^{2,p}(U_R)`, `L̃ u ∈ W^{k,p}(U_R)` imply
`u ∈ W^{k+2,p}(U_{R/2^k})`) and the lifted a priori estimate
(`‖u‖_{W^{k+2,p}(U_{R/2^{k+2}})} ≤ C (‖L̃ u‖_{W^{k,p}(U_R)} + ‖u‖_{L^p(U_R)})`). -/
theorem chart_higher_of_upstream (h1 : TypeCalculusAllChartsNoDrift) (hParametrix : SignedParametrixAllChartsNoDrift)
    (hlift : LiftedBaseSobolevAllChartsNoDrift) {n q s m : ℕ} (hn : 3 ≤ n) (hq : 0 < q)
    {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} (C : P1.LiftedChart noDriftWeight s Ω hΩ X x₀ m) {p : ℝ≥0∞} (hp1 : 1 < p)
    (hp : p < ⊤) (k : ℕ) :
    LiftedHigherRegularity C (G2.smoothNorm C.G) (noDriftOpWords q) p k ∧
      LiftedHigherEstimate C (G2.smoothNorm C.G) (noDriftOpWords q) p k := by
  have hQ := C.two_lt_homogeneousDimension hn
  obtain ⟨K⟩ := (C.noDriftModel hq (G2.smoothNorm C.G)).exists_globalFundamentalKernel C.G hQ
  have hsymm : ∀ u, (C.noDriftModel hq (G2.smoothNorm C.G)).norm (-u) =
      (C.noDriftModel hq (G2.smoothNorm C.G)).norm u := by
    intro u
    have hu := C.smoothNorm_symmetric u
    rwa [show C.G.inv u = -u from C.inv_eq_neg u] at hu
  obtain ⟨V, a, b, hξV, hVcl, hab, ha1⟩ := exists_frame_cutoffs_noDrift C C.center_mem
  have hF := isStandardFrame_stdFrameNoDrift K hQ V hVcl hsymm (G2.smoothNorm_smooth C.G)
    (H1.assemble_kernel K hQ)
  obtain ⟨hRowInt, hLeftDiff, hRightDiff, hTransfer⟩ := h1 hn hq C K _ hF
  have hnear : ∀ᶠ x in 𝓝 (joinPoint x₀ (0 : Fin m → ℝ)),
      x ∈ (V : Set (Fin (n + m) → ℝ)) ∧ a x = 1 :=
    (show ∀ᶠ x in 𝓝 (joinPoint x₀ (0 : Fin m → ℝ)), x ∈ (V : Set (Fin (n + m) → ℝ)) from
      V.isOpen.mem_nhds hξV).and ha1
  have hH : HigherFrame C (C.noDriftModel hq (G2.smoothNorm C.G)) K hQ (stdFrameNoDrift C K hQ V) a :=
    ⟨hF, fun j => rfl, hRowInt, hLeftDiff, hRightDiff, hTransfer, fun b' => hParametrix hn hq C K _ hF a b', hnear⟩
  have hν : (G2.smoothNorm C.G).Smooth := G2.smoothNorm_smooth C.G
  obtain ⟨R₀, hg⟩ := exists_goodRadius hH (G2.smoothNorm C.G) hν
  have hpt : p ≠ ⊤ := hp.ne
  refine ⟨⟨R₀, hg.1, fun R hR hRR u f hu hop hf =>
    liftedRegularity hH hg hp1 hpt k hR hRR hu hop hf⟩, ?_⟩
  obtain ⟨R₁, hR₁, -, hE⟩ := liftedEstimate hH hg (hlift hn hq C hp1 hp) hp1 hpt k
  exact ⟨R₁, hR₁, hE⟩

end RothschildStein.P2
