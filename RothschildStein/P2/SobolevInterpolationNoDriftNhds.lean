-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationNoDriftTheorem

/-!
# Sobolev interpolation without drift: small `ρ`-balls lie in any neighbourhood

`ρ`-balls `U_r^ρ(ξ₀)` shrink to `ξ₀` (`exists_rhoBall_subset_of_mem_nhds_noDrift`: the chart `e_{ξ₀}` is
a homeomorphism onto its image with `e_{ξ₀}(ξ) = Θ(ξ₀, ξ)`). Consequently, if the cutoff `a` of the
representation is `1` on a neighbourhood of `ξ₀ ∈ V`, the radius restrictions `U_r^ρ ⊆ V`,
`a = 1` on `U_r^ρ` of `exists_seminormAbsorption_noDrift_of_representation` hold for all small `r`
(`exists_seminormAbsorption_nhds_noDrift_of_representation`).
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

/-- **`ρ`-balls shrink to the centre**: every neighbourhood `W` of `ξ₀ ∈ U` contains the
`ρ`-balls `U_r^ρ(ξ₀)` of all sufficiently small radii. -/
theorem exists_rhoBall_subset_of_mem_nhds_noDrift (C : LiftedChart w s Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U)
    {W : Set (Fin (n + m) → ℝ)} (hW : W ∈ 𝓝 ξ₀) :
    ∃ r₂ : ℝ, 0 < r₂ ∧ ∀ r : ℝ, r ≤ r₂ → rhoBall C ν ξ₀ r ⊆ W := by
  obtain ⟨hsrc, hΘ, -, -, hη0⟩ := C.chart ξ₀ hξ₀
  have hs : ξ₀ ∈ (C.e ξ₀).source := by rw [hsrc]; exact hξ₀
  have hmap : C.e ξ₀ ξ₀ ∈ (C.e ξ₀).target := (C.e ξ₀).map_source hs
  have h0 : C.e ξ₀ ξ₀ = 0 := by rw [hΘ ξ₀ hξ₀]; exact hη0
  have hcont : ContinuousAt (C.e ξ₀).symm (C.e ξ₀ ξ₀) :=
    (C.e ξ₀).continuousOn_symm.continuousAt ((C.e ξ₀).open_target.mem_nhds hmap)
  have hsymm : (C.e ξ₀).symm (C.e ξ₀ ξ₀) = ξ₀ := (C.e ξ₀).left_inv hs
  have hv : ((C.e ξ₀).symm ⁻¹' W) ∈ 𝓝 (0 : Fin (n + m) → ℝ) := by
    rw [← h0]
    exact hcont.preimage_mem_nhds (by rw [hsymm]; exact hW)
  obtain ⟨r, hr0, -, hr⟩ := exists_gauge_sublevel_subset C.G ν.gauge hv
  refine ⟨r, hr0, fun r' hr' ξ hξ => ?_⟩
  have hu : ν (C.Θ ξ₀ ξ) ≤ r := hξ.2.le.trans hr'
  have h1 : (C.e ξ₀).symm (C.Θ ξ₀ ξ) ∈ W := hr _ hu
  rw [← hΘ ξ hξ.1, (C.e ξ₀).left_inv (by rw [hsrc]; exact hξ.1)] at h1
  exact h1

/-- **Sobolev interpolation, seminorm form, no drift, with the radius conditions
discharged**: if `ξ₀ ∈ V` and the cutoff `a` is `1` near `ξ₀`, then in
`exists_seminormAbsorption_noDrift_of_representation` the conditions `U_r^ρ ⊆ V` and `a = 1` on `U_r^ρ` hold
for all small `r`. There are `r₁ ∈ (0, 1]`, `δ₀ > 0` and, for `1 < p < ∞`, `Cabs > 0` such that for
`0 < r ≤ r₁`, `u ∈ W^{2,p}_{X̃}(U_r^ρ)`, `0 < δ ≤ δ₀`:
`Φ₁(u) ≤ δ Φ₂(u) + Cabs δ^{-1} Φ₀(u)`. -/
theorem exists_seminormAbsorption_nhds_noDrift_of_representation
    {q₀ : ℕ} {H : H1.StandingHypotheses C.G q₀} {K : H1.FundamentalKernel C.G H}
    {hQ : 2 < (C.G.homogeneousDimension : ℝ)} (hF : C.IsStandardFrame F H K hQ)
    (hw : ∀ j, (w j : ℕ) = 1) (hLeftDiff : LeftDifferentiation F w C.Xl)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl c a b)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U)
    (ha : ∀ᶠ x in 𝓝 ξ₀, x ∈ (F.V : Set (Fin (n + m) → ℝ)) ∧ a x = 1) :
    ∃ r₁ δ₀ : ℝ, 0 < r₁ ∧ r₁ ≤ 1 ∧ 0 < δ₀ ∧ ∀ p : ℝ, 1 < p → ∃ Cabs : ℝ, 0 < Cabs ∧
      ∀ r : ℝ, 0 < r → r ≤ r₁ → ∀ u : (Fin (n + m) → ℝ) → ℝ,
        memSobolevX w C.Xl (rhoOpensNoDrift C ν hξ₀ r) 2 (ENNReal.ofReal p) u →
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          seminormPhi w C.Xl (rhoOpensNoDrift C ν hξ₀) (ENNReal.ofReal p) r 1 u ≤
            ENNReal.ofReal δ * seminormPhi w C.Xl (rhoOpensNoDrift C ν hξ₀) (ENNReal.ofReal p) r 2 u +
              ENNReal.ofReal (Cabs / δ) *
                seminormPhi w C.Xl (rhoOpensNoDrift C ν hξ₀) (ENNReal.ofReal p) r 0 u := by
  obtain ⟨r₁, δ₀, hr₁, hr₁1, hδ₀, hmain⟩ :=
    exists_seminormAbsorption_noDrift_of_representation hF hw hLeftDiff hc hc0 a hParametrix ν hν hξ₀
  obtain ⟨r₂, hr₂, hsub⟩ := exists_rhoBall_subset_of_mem_nhds_noDrift C ν hξ₀ ha
  refine ⟨min r₁ r₂, δ₀, lt_min hr₁ hr₂, (min_le_left _ _).trans hr₁1, hδ₀, fun p hp => ?_⟩
  obtain ⟨Cabs, hCabs, hres⟩ := hmain p hp
  refine ⟨Cabs, hCabs, fun r hr hrr u hu δ hδ hδ' => ?_⟩
  have hsub' := hsub r (hrr.trans (min_le_right _ _))
  exact hres r hr (hrr.trans (min_le_left _ _)) (fun x hx => (hsub' hx).1)
    (fun x hx => (hsub' hx).2) u hu δ hδ hδ'

end RothschildStein.P2
