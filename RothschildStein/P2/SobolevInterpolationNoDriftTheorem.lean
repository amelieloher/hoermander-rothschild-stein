-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationNoDriftRho
public import RothschildStein.P2.SobolevInterpolationNoDriftRepresentation

/-!
# Sobolev interpolation without drift (BB Prop 11.38, Thm 11.39, pp. 580-583)

The two forms of the Sobolev interpolation inequality for a lifted no-drift chart (alphabet `Fin q`, all weights one, `L̃ = sumSquares`):

* **compact form** (`exists_compactInterpolation_noDrift_of_representation`, in
  `SobolevInterpolationNoDriftRepresentation`): `∑_l ‖X̃_l v‖_p ≤ ε ‖L̃v‖_p + C(p) ε^{-1} ‖v‖_p` for
  `v ∈ C_c^∞(V)` with the cutoff `a = 1` on `supp v`, `0 < ε < ε_*`, `1 < p < ∞`;
* **seminorm form** (`exists_seminormAbsorption_noDrift_of_representation`):
  `Φ₁ ≤ δ Φ₂ + C(p) δ^{-1} Φ₀` on the `ρ`-balls `U_r^ρ` for `u ∈ W^{2,p}_{X̃}(U_r^ρ)`,
  `0 < δ ≤ δ_*`, `0 < r ≤ r₁`.

Both are conditional exactly on the hypotheses of `representation_firstOrder_noDrift_of`
(`LeftDifferentiation`, `SignedParametrixNoDrift`, density data `c`) and on a standard frame (as in the continuity theorem).
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

/-- **The absorption inequality on the `ρ`-balls, no drift**, assuming the
compact interpolation inequality `CompactInterpolationOnNoDrift` (constants `εs > 0`, `Cp ≥ 0`) and on the
cutoff family of `exists_cutoffFamily_noDrift` (constants `r_* , B`): for `0 < r ≤ r_*/2` with `U_r^ρ ⊆ V` and
`a = 1` on `U_r^ρ`, every `u ∈ W^{2,p}_{X̃}(U_r^ρ)` and `0 < δ ≤ min(1/2, εs/2)`,
`Φ₁(u) ≤ δ Φ₂(u) + ((q + 1 + 16 Cp (1 + B))/δ) Φ₀(u)`, where
`Φ_j = sup_{1/2 ≤ σ < 1} ((1 - σ) r)^j ∑_{|I| = j} ‖X̃_I u‖_{L^p(U_{σ r}^ρ)}`. -/
theorem seminormPhi_absorption_rho_noDrift (hw : ∀ j, (w j : ℕ) = 1)
    (ν : G2.HomogeneousNorm C.G)
    {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) {V : Opens (Fin (n + m) → ℝ)}
    (hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (V : Set (Fin (n + m) → ℝ)))
    {a : TestFunction V ℝ (⊤ : ℕ∞)} {p εs Cp : ℝ} (hp : 1 < p) (hCp : 0 ≤ Cp)
    (hCI : CompactInterpolationOnNoDrift C.Xl V a p εs Cp) {rstar B : ℝ} (hrs1 : rstar ≤ 1) (hB : 0 ≤ B)
    (hcut : ∀ r : ℝ, 0 < r → r < rstar → CutoffFamilyNoDrift C.Xl (rhoOpensNoDrift C ν hξ₀) r B)
    {r : ℝ} (hr : 0 < r) (hrr : r ≤ rstar / 2) (hrV : rhoBall C ν ξ₀ r ⊆ (V : Set (Fin (n + m) → ℝ)))
    (hra : ∀ x ∈ rhoBall C ν ξ₀ r, a x = 1) {u : (Fin (n + m) → ℝ) → ℝ}
    (hu : memSobolevX w C.Xl (rhoOpensNoDrift C ν hξ₀ r) 2 (ENNReal.ofReal p) u) {δ : ℝ} (hδ : 0 < δ)
    (hδ0 : δ ≤ min (1 / 2) (εs / 2)) :
    seminormPhi w C.Xl (rhoOpensNoDrift C ν hξ₀) (ENNReal.ofReal p) r 1 u ≤
      ENNReal.ofReal δ * seminormPhi w C.Xl (rhoOpensNoDrift C ν hξ₀) (ENNReal.ofReal p) r 2 u +
        ENNReal.ofReal (((q : ℝ) + 1 + 16 * Cp * (1 + B)) / δ) *
          seminormPhi w C.Xl (rhoOpensNoDrift C ν hξ₀) (ENNReal.ofReal p) r 0 u := by
  have hδ1 : δ ≤ 1 / 2 := hδ0.trans (min_le_left _ _)
  have hεs : 0 < εs := by
    by_contra hneg
    have : εs / 2 ≤ 0 := by linarith [not_lt.1 hneg]
    linarith [hδ0.trans (min_le_right _ _)]
  have hδ2 : δ < εs := lt_of_le_of_lt (hδ0.trans (min_le_right _ _)) (by linarith)
  exact seminormPhi_absorption_noDrift hw hXV hp hCp hCI (U := rhoOpensNoDrift C ν hξ₀)
    (fun s t hst => rhoOpensNoDrift_mono C ν hξ₀ hst) hr (by linarith) hrV hra hB
    (hcut r hr (by linarith)) hu hδ hδ1 hδ2

/-- **Sobolev interpolation, seminorm form, no drift** (BB Thm 11.39, p. 583), from the
first-order representation: with `a ∈ C_c^∞(V)` as in `representation_firstOrder_noDrift_of`
(hypotheses `LeftDifferentiation`, `SignedParametrixNoDrift`, the density data `c`) on a standard frame, there are `r₁ ∈ (0, 1]`
and `δ₀ > 0` such that for `1 < p < ∞` there is `Cabs > 0` with: for `0 < r ≤ r₁`, `U_r^ρ ⊆ V`,
`a = 1` on `U_r^ρ`, `u ∈ W^{2,p}_{X̃}(U_r^ρ)` and `0 < δ ≤ δ₀`,
`Φ₁(u) ≤ δ Φ₂(u) + Cabs δ^{-1} Φ₀(u)`. -/
theorem exists_seminormAbsorption_noDrift_of_representation
    {q₀ : ℕ} {H : H1.StandingHypotheses C.G q₀} {K : H1.FundamentalKernel C.G H}
    {hQ : 2 < (C.G.homogeneousDimension : ℝ)} (hF : C.IsStandardFrame F H K hQ)
    (hw : ∀ j, (w j : ℕ) = 1) (hLeftDiff : LeftDifferentiation F w C.Xl)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl c a b)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) :
    ∃ r₁ δ₀ : ℝ, 0 < r₁ ∧ r₁ ≤ 1 ∧ 0 < δ₀ ∧ ∀ p : ℝ, 1 < p → ∃ Cabs : ℝ, 0 < Cabs ∧
      ∀ r : ℝ, 0 < r → r ≤ r₁ → rhoBall C ν ξ₀ r ⊆ (F.V : Set (Fin (n + m) → ℝ)) →
      (∀ x ∈ rhoBall C ν ξ₀ r, a x = 1) →
      ∀ u : (Fin (n + m) → ℝ) → ℝ,
        memSobolevX w C.Xl (rhoOpensNoDrift C ν hξ₀ r) 2 (ENNReal.ofReal p) u →
        ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
          seminormPhi w C.Xl (rhoOpensNoDrift C ν hξ₀) (ENNReal.ofReal p) r 1 u ≤
            ENNReal.ofReal δ * seminormPhi w C.Xl (rhoOpensNoDrift C ν hξ₀) (ENNReal.ofReal p) r 2 u +
              ENNReal.ofReal (Cabs / δ) *
                seminormPhi w C.Xl (rhoOpensNoDrift C ν hξ₀) (ENNReal.ofReal p) r 0 u := by
  have hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n + m) → ℝ)) :=
    fun i => (C.contDiffOn_Xl_U i).mono hF.lifted.subset_U
  obtain ⟨εs, hεs, hmain⟩ :=
    exists_compactInterpolation_noDrift_of_representation hF hw hLeftDiff hc hc0 a hParametrix
  obtain ⟨rstar, B, hrs0, hrs1, hB, hcut⟩ := exists_cutoffFamily_noDrift C hw ν hν hξ₀
  refine ⟨rstar / 2, min (1 / 2) (εs / 2), by linarith, by linarith,
    lt_min (by norm_num) (by linarith), fun p hp => ?_⟩
  obtain ⟨Cp, hCp, hCI⟩ := hmain p hp
  refine ⟨(q : ℝ) + 1 + 16 * Cp * (1 + B), by positivity, fun r hr hrr hrV hra u hu δ hδ hδ0 => ?_⟩
  exact seminormPhi_absorption_rho_noDrift hw ν hξ₀ hXV hp hCp.le hCI hrs1 hB hcut hr hrr hrV hra hu hδ hδ0

end RothschildStein.P2
