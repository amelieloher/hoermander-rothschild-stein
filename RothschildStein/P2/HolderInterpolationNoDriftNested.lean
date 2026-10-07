-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HolderInterpolationNoDriftDerivative
public import RothschildStein.P2.HolderInterpolationNoDriftLocal
public import RothschildStein.P2.HolderInterpolationNested

/-!
# No drift: the nested interpolation inequality

The no-drift counterpart of `exists_nestedInterpolation_of_representation` (BB Thm 11.53, pp. 596-597,
(11.87); alphabet `Fin q`, all weights one, `L̃ = ∑ᵢ X̃ᵢ²`). The localization step
`nested_step_noDrift`, the derivative interpolation `exists_derivativeInterpolation_noDrift_of_representation`
and the iteration `nested_arith` (the real iteration lemma of the drift case, alphabet independent) combine
exactly as in the drift case. Conditional exactly on the hypotheses of the derivative representations on a
standard frame (`LeftDifferentiation`, `SignedParametrixNoDrift`, the density data `c`); the `(HD)` package of the lifted control
distance is `LiftedChart.distanceGeometry`, which needs no further hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart noDriftWeight st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {q₀ : ℕ} {H : H1.StandingHypotheses C.G q₀} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **The nested interpolation inequality, no drift** (BB Thm 11.53, pp. 596-597,
(11.87)). Conditional exactly on the hypotheses of the derivative representations
(`LeftDifferentiation`, `SignedParametrixNoDrift`, the density data `c`) on a standard frame. For `0 < α < 1`, a smooth gauge
`ν`, and a chart centre `ξ₀` there are a threshold `R_* ≤ 1`, `γ > 1` and `C_n` such that for `0 < R ≤ R_*` with
`U_R^ρ ⊆ V` and `a = 1` on `U_R^ρ` (`a` the cutoff of the representation), every `u ∈ C^{2,α}_{X̃}(V)` with
Hölder weak jet `D`, `0 < r < R` and `0 < δ < 1/3`:
`∑_l ‖X̃_l u‖_{C^α(U_r^ρ)} ≤ δ ‖L̃u‖_{L^∞(U_R^ρ)} + C_n δ^{-γ} (R - r)^{-γ} ‖u‖_{L^∞(U_R^ρ)}`. -/
theorem exists_nestedInterpolation_noDrift_of_representation (hF : C.IsStandardFrame F H K hQ)
    (hLeftDiff : LeftDifferentiation F noDriftWeight C.Xl)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl c a b)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ Rstar γ Cn : ℝ, 0 < Rstar ∧ Rstar ≤ 1 ∧ 1 < γ ∧ 0 < Cn ∧
      ∀ R : ℝ, 0 < R → R ≤ Rstar → rhoBall C ν ξ₀ R ⊆ (F.V : Set (Fin (n + m) → ℝ)) →
        (∀ x ∈ rhoBall C ν ξ₀ R, a x = 1) →
        ∀ (u : (Fin (n + m) → ℝ) → ℝ) (D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ),
          memHolderX noDriftWeight C.Xl C.dl F.V 2 α u →
          LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl F.V 2 α u D →
          ∀ r : ℝ, 0 < r → r < R → ∀ δ : ℝ, 0 < δ → δ < 1 / 3 →
            ∑ l : Fin q, holderENorm C.dl α (rhoBall C ν ξ₀ r) (D [l]) ≤
              ENNReal.ofReal δ * (⨆ x : rhoBall C ν ξ₀ R,
                  ENNReal.ofReal |weakSumSquares D [] x|) +
                ENNReal.ofReal (Cn * δ ^ (-γ) * (R - r) ^ (-γ)) *
                  ⨆ x : rhoBall C ν ξ₀ R, ENNReal.ofReal |u x| := by
  classical
  obtain ⟨γ₁, Cc₁, hγ₁, hCc₁, hder⟩ := exists_derivativeInterpolation_noDrift_of_representation hF
    hLeftDiff hc hc0 a hParametrix hα0 hα1
  obtain ⟨rstar, b₁, b₂, hr0, hr1, hb₁, hb₂, hqual, hζb1, hζb2⟩ :=
    exists_cutoff_data_noDrift C ν hν hξ₀
  obtain ⟨Cn, hCn, harith⟩ := nested_arith hb₁ hb₂ hCc₁.le hγ₁
  refine ⟨rstar / 2, γ₁ + 2, Cn, by linarith, by linarith, by linarith, hCn, ?_⟩
  intro R hR0 hRstar hBV ha1 u D hu hD r hr0' hrR δ hδ0 hδ3
  have hw : ∀ j : Fin q, ((noDriftWeight j : ℕ+) : ℕ) = 1 := noDriftWeight_natCast_eq_one
  have hRr : R < rstar := by linarith
  have hu' : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) u ≠ ⊤ := ne_top_of_lt hu.1
  have hLD : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (weakSumSquares D []) ≠ ⊤ :=
    hD.weakSumSquares_nil_ne_top hw hα0
  have hDfin : ∀ i : Fin q, holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (D [i]) ≠ ⊤ :=
    fun i => (hD [i] (LiftedChart.horizontal_mem_wordFamily_noDrift (w := noDriftWeight) hw i)).2
  have hfinR : ∑ l : Fin q, holderENorm C.dl α (rhoBall C ν ξ₀ R) (D [l]) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun l _ => holderENorm_ball_ne_top_noDrift ν (hDfin l) hBV
  have hfinr : ∑ l : Fin q, holderENorm C.dl α (rhoBall C ν ξ₀ r) (D [l]) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun l _ => holderENorm_ball_ne_top_noDrift ν (hDfin l)
      ((rhoBall_mono C ν ξ₀ hrR.le).trans hBV)
  have hK : ∃ K, ∀ t ∈ Icc r R, psiBallNoDrift C ν ξ₀ α D t ≤ K := by
    refine ⟨psiBallNoDrift C ν ξ₀ α D R, fun t ht => ?_⟩
    exact ENNReal.toReal_mono hfinR (Finset.sum_le_sum fun l _ =>
      S.holderENorm_mono C.dl α _ _ (rhoBall_mono C ν ξ₀ ht.2))
  have hstep : ∀ t s : ℝ, r ≤ t → t < s → s ≤ R → ∀ ε : ℝ, 0 < ε → ε < 1 →
      psiBallNoDrift C ν ξ₀ α D t ≤
        ε * (supBallNoDrift C ν ξ₀ (weakSumSquares D []) R +
            2 * b₁ * (s - t)⁻¹ * psiBallNoDrift C ν ξ₀ α D s +
              b₂ * ((s - t) ^ 2)⁻¹ * supBallNoDrift C ν ξ₀ u R) +
          Cc₁ * ε ^ (-γ₁) * supBallNoDrift C ν ξ₀ u R :=
    fun t s htr hts hsR ε hε0 hε1 => nested_step_noDrift hF.lifted ν hξ₀ hα0 hα1 hder hCc₁.le hb₁
      hb₂ hqual hζb1 hζb2 hRr hBV ha1 hu' hD (lt_of_lt_of_le hr0' htr) hts hsR hε0 hε1
  have hres := harith (psiBallNoDrift C ν ξ₀ α D) R r
    (supBallNoDrift C ν ξ₀ (weakSumSquares D []) R) (supBallNoDrift C ν ξ₀ u R) δ
    (supBallNoDrift_nonneg C ν ξ₀ _ R) (supBallNoDrift_nonneg C ν ξ₀ _ R) hr0' hrR
    (by linarith) hδ0 hδ3 hK hstep
  have hML : ENNReal.ofReal (supBallNoDrift C ν ξ₀ (weakSumSquares D []) R) =
      ⨆ x : rhoBall C ν ξ₀ R, ENNReal.ofReal |weakSumSquares D [] x| :=
    ENNReal.ofReal_toReal (supBallNoDrift_ne_top ν hLD hBV)
  have hMu : ENNReal.ofReal (supBallNoDrift C ν ξ₀ u R) =
      ⨆ x : rhoBall C ν ξ₀ R, ENNReal.ofReal |u x| :=
    ENNReal.ofReal_toReal (supBallNoDrift_ne_top ν hu' hBV)
  have hCδ0 : 0 ≤ Cn * δ ^ (-(γ₁ + 2)) * (R - r) ^ (-(γ₁ + 2)) :=
    mul_nonneg (mul_nonneg hCn.le (Real.rpow_nonneg hδ0.le _))
      (Real.rpow_nonneg (sub_pos.2 hrR).le _)
  calc ∑ l : Fin q, holderENorm C.dl α (rhoBall C ν ξ₀ r) (D [l])
      = ENNReal.ofReal (psiBallNoDrift C ν ξ₀ α D r) := (ENNReal.ofReal_toReal hfinr).symm
    _ ≤ ENNReal.ofReal (δ * supBallNoDrift C ν ξ₀ (weakSumSquares D []) R +
          Cn * δ ^ (-(γ₁ + 2)) * (R - r) ^ (-(γ₁ + 2)) * supBallNoDrift C ν ξ₀ u R) :=
        ENNReal.ofReal_le_ofReal hres
    _ = ENNReal.ofReal δ * ENNReal.ofReal (supBallNoDrift C ν ξ₀ (weakSumSquares D []) R) +
          ENNReal.ofReal (Cn * δ ^ (-(γ₁ + 2)) * (R - r) ^ (-(γ₁ + 2))) *
            ENNReal.ofReal (supBallNoDrift C ν ξ₀ u R) := by
        rw [ENNReal.ofReal_add (mul_nonneg hδ0.le (supBallNoDrift_nonneg C ν ξ₀ _ R))
          (mul_nonneg hCδ0 (supBallNoDrift_nonneg C ν ξ₀ _ R)), ENNReal.ofReal_mul hδ0.le,
          ENNReal.ofReal_mul hCδ0]
    _ = _ := by rw [hML, hMu]

end RothschildStein.P2
