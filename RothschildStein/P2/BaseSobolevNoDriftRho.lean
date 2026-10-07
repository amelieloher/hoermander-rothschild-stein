-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.BaseSobolevNoDriftAbsorb
public import RothschildStein.P2.SobolevInterpolationNoDriftNhds

/-!
# No drift, on the `ρ`-balls `U_r^ρ`

The abstract absorption `seminormPhi_second_absorption_noDrift` applied to the `ρ`-balls `U_r^ρ(ξ₀)` of a
lifted no-drift chart (BB pp. 578-587), with

* the cutoff family of the radial cutoffs (`exists_cutoffFamily_noDrift`),
* the seminorm interpolation `Φ₁ ≤ δ Φ₂ + C δ^{-1} Φ₀` of the Sobolev interpolation inequality
  (`exists_seminormAbsorption_nhds_noDrift_of_representation`),
* the compact second-derivative estimate (`exists_compactSecond_noDrift_of_representation`),

under the hypotheses of `representation_secondOrder_noDrift_of` (`TypeKernelIntegrable`,
`LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer`, `SignedParametrixNoDrift`) and on a standard frame (the continuity theorem). The result
(`exists_secondAbsorption_nhds_noDrift_of_representation`) is `Φ₂ + Φ₁ ≤ K (r² ‖L̃u‖_{L^p(U_r)} + Φ₀)` for
`0 < r ≤ r₀` and `u ∈ W^{2,p}_{X̃}(U_r)` with `L̃u = f` weakly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

variable {n q s m : ℕ} {w : Fin q → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- **The absorption on the `ρ`-balls, from the representation, no drift.** Let
`C` be a lifted no-drift chart, `F` a standard frame of it, `a ∈ C_c^∞(V)` a cutoff with `a = 1` near
`ξ₀ ∈ C.U` for which the derivative representations hold (hypotheses `TypeKernelIntegrable`, `LeftDifferentiation`,
`RightDifferentiation`, `DerivativeTransfer`, `SignedParametrixNoDrift`) and `ν` a smooth homogeneous norm. There is
`r₀ ∈ (0, 1]` such that for `1 < p < ∞` there is `K ≥ 0` with: for `0 < r ≤ r₀`,
`u ∈ W^{2,p}_{X̃}(U_r^ρ)` and `f = L̃u` weakly,
`Φ₂(u) + Φ₁(u) ≤ K (r² ‖f‖_{L^p(U_r^ρ)} + Φ₀(u))`
(`Φ_j = sup_{1/2 ≤ σ < 1} ((1 - σ) r)^j ∑_{|I| = j} ‖X̃_I u‖_{L^p(U_{σ r}^ρ)}`). -/
theorem exists_secondAbsorption_nhds_noDrift_of_representation
    {q₀ : ℕ} {H : H1.StandingHypotheses C.G q₀} {K : H1.FundamentalKernel C.G H}
    {hQ : 2 < (C.G.homogeneousDimension : ℝ)} (hF : C.IsStandardFrame F H K hQ)
    (hw : ∀ j, (w j : ℕ) = 1)
    (B : Fin (n + m) → List (Fin q)) (hRowInt : TypeKernelIntegrable F) (hLeftDiff : LeftDifferentiation F w C.Xl)
    (hRightDiff : RightDifferentiation F w C.Xl hF.lifted.contDiffOn_Xl) (hTransfer : DerivativeTransfer F w C.Xl B)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl c a b)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U)
    (ha : ∀ᶠ x in 𝓝 ξ₀, x ∈ (F.V : Set (Fin (n + m) → ℝ)) ∧ a x = 1) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ ∀ p : ℝ, 1 < p → ∃ Kc : ℝ, 0 ≤ Kc ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ u f : (Fin (n + m) → ℝ) → ℝ,
        memSobolevX w C.Xl (rhoOpensNoDrift C ν hξ₀ r) 2 (ENNReal.ofReal p) u →
        HasWeakOperatorValue C.Xl (rhoOpensNoDrift C ν hξ₀ r) (noDriftOpWords q) u f →
        seminormPhi w C.Xl (rhoOpensNoDrift C ν hξ₀) (ENNReal.ofReal p) r 2 u +
            seminormPhi w C.Xl (rhoOpensNoDrift C ν hξ₀) (ENNReal.ofReal p) r 1 u ≤
          ENNReal.ofReal Kc * (ENNReal.ofReal (r ^ 2) *
            eLpNorm f (ENNReal.ofReal p)
              (volume.restrict (rhoOpensNoDrift C ν hξ₀ r : Set (Fin (n + m) → ℝ))) +
            seminormPhi w C.Xl (rhoOpensNoDrift C ν hξ₀) (ENNReal.ofReal p) r 0 u) := by
  have hXV := hF.lifted.contDiffOn_Xl
  obtain ⟨r₁, δ₀, hr₁, hr₁1, hδ₀, habs⟩ :=
    exists_seminormAbsorption_nhds_noDrift_of_representation hF hw hLeftDiff hc hc0 a hParametrix ν hν hξ₀ ha
  obtain ⟨rstar, Bc, hrs0, hrs1, hBc, hcut⟩ := exists_cutoffFamily_noDrift C hw ν hν hξ₀
  obtain ⟨r₂, hr₂, hsub⟩ := exists_rhoBall_subset_of_mem_nhds_noDrift C ν hξ₀ ha
  refine ⟨min (min r₁ (rstar / 2)) r₂, lt_min (lt_min hr₁ (by linarith)) hr₂,
    (min_le_left _ _).trans ((min_le_left _ _).trans hr₁1), fun p hp => ?_⟩
  obtain ⟨Λ, hΛ0, hCS⟩ :=
    exists_compactSecond_noDrift_of_representation hF hw B hRowInt hLeftDiff hRightDiff hTransfer hc hc0 a hParametrix p hp
  obtain ⟨Cabs, hCabs, habs'⟩ := habs p hp
  obtain ⟨Kc, hKc0, hKc⟩ := seminormPhi_second_absorption_noDrift hw hXV hp hΛ0.le hCS
    (U := rhoOpensNoDrift C ν hξ₀) (fun s t hst => rhoOpensNoDrift_mono C ν hξ₀ hst) hBc hδ₀
    hCabs.le
  refine ⟨Kc, hKc0, fun r hr0 hrr u f hu hf => ?_⟩
  have hr₁r : r ≤ r₁ := hrr.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrstar : r < rstar := by
    have : r ≤ rstar / 2 := hrr.trans ((min_le_left _ _).trans (min_le_right _ _))
    linarith
  have hr₂r : r ≤ r₂ := hrr.trans (min_le_right _ _)
  have hsub' := hsub r hr₂r
  exact hKc r hr0 (hr₁r.trans hr₁1) (fun x hx => (hsub' hx).1) (fun x hx => (hsub' hx).2)
    (hcut r hr0 hrstar) u f hu hf (fun δ hδ hδδ₀ => habs' r hr0 hr₁r u hu δ hδ hδδ₀)

end RothschildStein.P2
