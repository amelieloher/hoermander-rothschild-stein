-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingDriftTriangularAdapter
public import RothschildStein.P1.PaddingCylinderFiberSetting
public import RothschildStein.P2.SmoothingRegularity
public import RothschildStein.P2.NormTransferWords
public import RothschildStein.P1.PaddingDriftSobolevAlphabetNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.P1

/-- Quantitative forcing Sobolev lift to genuine
diffusion padding: the full norm at every order increases by at most
the exact fiber-volume factor |J|^(1/p), including infinite values. -/
theorem sobolevXENorm_paddingDrift_pullback_le {q n d k : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (hJ0 : 0 < volume (J : Set (Fin d → ℝ)))
    (hJ : volume (J : Set (Fin d → ℝ)) < ⊤)
    (w : Fin (q + 1) → ℕ+) (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (f : (Fin n → ℝ) → ℝ)
    (hf : LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume) :
    sobolevXENorm (paddingControlWeights (d := d) w) (paddingVectorFields (d := d) X)
      (P2.cylinder Ω J) k p (fun ξ => f (basePoint ξ)) ≤
      ENNReal.ofReal ((volume (J : Set (Fin d → ℝ))).toReal ^ (1 / p.toReal)) *
        sobolevXENorm w X Ω k p f := by
  let Y := paddingDriftBaseAlphabet (d := d) X
  let P := paddingDriftPolynomials q n d
  have hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) (Ω : Set (Fin n → ℝ)) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [Y, paddingDriftBaseAlphabet] using hX 0
    · refine Fin.addCases (fun a => ?_) (fun b => ?_) j
      · simpa [Y, paddingDriftBaseAlphabet] using hX a.succ
      · simp only [Y, paddingDriftBaseAlphabet, Fin.cases_succ, Fin.addCases_right]
        simpa only [Pi.zero_def] using
          (contDiff_zero_fun (𝕜 := ℝ) (n := (⊤ : ℕ∞))
            (E := Fin n → ℝ) (F := Fin n → ℝ)).contDiffOn
  have hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift Y P i)
      (P2.cylinder Ω J : Set (Fin (n + d) → ℝ)) := by
    change ∀ i, ContDiffOn ℝ (⊤ : ℕ∞)
      (triangularLift (paddingDriftBaseAlphabet (d := d) X)
        (paddingDriftPolynomials q n d) i) _
    rw [← paddingVectorFields_eq_triangularLift]
    exact contDiffOn_paddingVectorFields_projection _ _
      (padding_cylinder_subset_base Ω J) X hX
  let S := fiberSetting_padding_cylinder Ω J hJ.ne
  let K : ℝ≥0∞ := ENNReal.ofReal ((volume (J : Set (Fin d → ℝ))).toReal ^ (1 / p.toReal))
  have hK0 : K ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact Real.rpow_pos_of_pos (ENNReal.toReal_pos hJ0.ne' hJ.ne) _
  have hKt : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have h := S.sobolevXENorm_lift_le (paddingControlWeights (d := d) w) Y P hXt hY k hK0 hKt
    (fun g hgm => le_of_eq (P2.eLpNorm_comp_cylinder (A := Ω) (B := J) hp hpt hJ hgm)) f
  dsimp only [Y, P] at h
  rw [← paddingVectorFields_eq_triangularLift, sobolevXENorm_paddingDriftBaseAlphabet_eq Ω w X p f hf] at h
  exact h

end RothschildStein.P1
