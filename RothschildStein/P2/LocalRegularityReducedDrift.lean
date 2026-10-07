-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityHypotheses
public import RothschildStein.P2.BaseSobolevLifted
public import RothschildStein.P2.SolvabilityFullFrame
public import RothschildStein.P1.ParametrixStatementsAssembly
public import RothschildStein.H1.CompleteAssembly

/-!
# Local regularity with drift, `L^p`: reduction of the base Sobolev estimate to the P1 hypotheses

`LiftedBaseSobolevAllChartsDrift` (the lifted base Sobolev estimate at the smooth homogeneous norm of
every drift chart) is provable from the P1 statements through `liftedBaseSobolevEstimate_of_representation`
(`BaseSobolevLifted`). That theorem needs, at the chart `C` with centre `ξ₀ = (x₀, 0)`:

* a standard frame `F` of `C` (`C.IsStandardFrame F H K hQ`) whose cutoff region `V` is a
  neighbourhood of `ξ₀` (`exists_frame_cutoffs`, `stdFrame`, `isStandardFrame_stdFrame`: `H` is the
  drift model `C.driftModel hq ν` at the smooth homogeneous norm `ν = G2.smoothNorm C.G` (symmetric
  and smooth), `K` an H1 fundamental kernel (existence for `Q > 2`, which follows from
  `3 ≤ n`; `H1.exists_globalFundamentalKernel`, with the fundamental-kernel properties `H1.assemble_kernel`),
  `Γ = K`, `Γ* = K ∘ inv`, `gauge = ν`);
* the Props `TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer` of that frame (for the model
  bracket basis `C.B`, the basis of the chart; BB pp. 544-559);
* the density data `c = C.c` (smooth and positive on `C.U ⊇ V`) and cutoffs `a, b ∈ C_c^∞(V)` with
  `a b = a` and `a = 1` near `ξ₀` (`exists_frame_cutoffs`);
* `SignedParametrix F C.Xl C.c a b` for every `b`, which `signedParametrix_of_errorTypes` derives from
  `ParametrixErrorTypes C F hq ν Γ hQ a b`.

The two hypotheses below are exactly these P1 inputs, quantified over the whole class of
standard frames of every drift chart (`3 ≤ n`, `0 < q`; the H1 kernel `K` of the drift model at
`ν = G2.smoothNorm C.G` arbitrary; the same class as `LeftDifferentiationAllChartsDrift`):

* `TypeCalculusAllChartsDrift` (row integrability, differentiation and transfer): `TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer`
  (for `C.B`) for every standard frame;
* `ParametrixErrorTypesAllChartsDrift` (parametrix error types): `ParametrixErrorTypes` (the error-type step) for every standard frame
  and every pair of cutoffs `a, b` of its region (the hypothesis `a b = a` is part of
  `ParametrixErrorTypes`).

`liftedBaseSobolevAllChartsDrift_of_reducedHypotheses` derives `LiftedBaseSobolevAllChartsDrift` from them; `leftDifferentiationAllChartsDrift_of_typeCalculus`
derives `LeftDifferentiationAllChartsDrift` from `TypeCalculusAllChartsDrift`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2

/-- The P1 type-calculus statements for every standard frame of every lifted
drift chart over a system with `3 ≤ n` and `0 < q`, with every H1 fundamental kernel `K` of the
drift model of the chart at the smooth homogeneous norm of the chart group: for every standard frame
`F`, row and column integrability of positive-type kernels (`TypeKernelIntegrable`, BB p. 544, Prop 11.10),
left and right differentiation of type-`λ` operators (`LeftDifferentiation`, `RightDifferentiation`, BB pp. 546-551,
Thm 11.15) and transfer to the integration variable along the model bracket basis `C.B`
(`DerivativeTransfer`, BB pp. 552-559, Thm 11.24). -/
def TypeCalculusAllChartsDrift : Prop :=
  ∀ {n q s m : ℕ} (hn : 3 ≤ n) (hq : 0 < q) {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : P1.LiftedChart driftWeight s Ω hΩ X x₀ m)
    (K : H1.FundamentalKernel C.G (C.driftModel hq (G2.smoothNorm C.G)))
    (F : KernelFrame (n + m))
    (hF : C.IsStandardFrame F (C.driftModel hq (G2.smoothNorm C.G)) K
      (C.two_lt_homogeneousDimension hn)),
    TypeKernelIntegrable F ∧ LeftDifferentiation F driftWeight C.Xl ∧
      RightDifferentiation F driftWeight C.Xl hF.lifted.contDiffOn_Xl ∧ DerivativeTransfer F driftWeight C.Xl C.B

/-- The types of the error terms of the signed parametrix (`ParametrixErrorTypes`, BB
pp. 561-563) for every standard frame of every lifted drift chart over a system with `3 ≤ n` and
`0 < q`, every H1 fundamental kernel `Γ` of the drift model of the chart at the smooth homogeneous
norm of the chart group, and all cutoffs `a, b ∈ C_c^∞(F.V)` (with `a b = a` inside
`ParametrixErrorTypes`). By `signedParametrix_of_errorTypes` it is all that the operator-level statement
`SignedParametrix` of the signed parametrix needs. -/
def ParametrixErrorTypesAllChartsDrift : Prop :=
  ∀ {n q s m : ℕ} (hn : 3 ≤ n) (hq : 0 < q) {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : P1.LiftedChart driftWeight s Ω hΩ X x₀ m)
    (Γ : H1.FundamentalKernel C.G (C.driftModel hq (G2.smoothNorm C.G)))
    (F : KernelFrame (n + m))
    (_hF : C.IsStandardFrame F (C.driftModel hq (G2.smoothNorm C.G)) Γ
      (C.two_lt_homogeneousDimension hn))
    (a b : TestFunction F.V ℝ (⊤ : ℕ∞)),
    ParametrixErrorTypes C F hq (G2.smoothNorm C.G) Γ (C.two_lt_homogeneousDimension hn) a b

/-- The hypothesis `LeftDifferentiation` for every standard frame of every lifted drift
chart (`LeftDifferentiationAllChartsDrift`) is the left-differentiation component of `TypeCalculusAllChartsDrift`. -/
theorem leftDifferentiationAllChartsDrift_of_typeCalculus (h : TypeCalculusAllChartsDrift) : LeftDifferentiationAllChartsDrift := by
  intro n q s m hn hq Ω hΩ X x₀ C K F hF
  exact (h hn hq C K F hF).2.1

/-- **The lifted base Sobolev estimate from the P1 hypotheses** (BB pp. 585-587,
Thms 11.42-11.43, (11.69)-(11.72)): `LiftedBaseSobolevAllChartsDrift` for every lifted drift chart over a system
with `3 ≤ n` and `0 < q`, from the P1 Props `TypeCalculusAllChartsDrift` and the error types `ParametrixErrorTypesAllChartsDrift`.
At the chart `C` with centre `ξ₀ = (x₀, 0)`: an H1 kernel `K` of the drift model at
`ν = G2.smoothNorm C.G` (`H1.exists_globalFundamentalKernel`), the standard frame `stdFrame` on a patch
`V ∋ ξ₀` with `closure V ⊆ C.U` and cutoffs `a, b ∈ C_c^∞(V)` with `a b = a`, `a = 1` near `ξ₀`
(`exists_frame_cutoffs`), `SignedParametrix` from the error types, and
`liftedBaseSobolevEstimate_of_representation`. -/
theorem liftedBaseSobolevAllChartsDrift_of_reducedHypotheses (hP : TypeCalculusAllChartsDrift) (hE : ParametrixErrorTypesAllChartsDrift) :
    LiftedBaseSobolevAllChartsDrift := by
  intro n q s m hn hq Ω hΩ X x₀ C p hp hpt
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
  obtain ⟨hRowInt, hLeftDiff, hRightDiff, hTransfer⟩ := hP hn hq C K _ hF
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
  have hw : ∀ j : Fin q, ((driftWeight j.succ : ℕ+) : ℕ) = 1 := fun j => by
    simp [driftWeight]
  have hw0 : ((driftWeight (0 : Fin (q + 1)) : ℕ+) : ℕ) = 2 := by simp [driftWeight]
  exact liftedBaseSobolevEstimate_of_representation hF hw hw0 C.B hRowInt hLeftDiff hRightDiff hTransfer hc hc0 a hParametrix
    (G2.smoothNorm C.G) hsmooth ha hp hpt.ne

end RothschildStein.P2
