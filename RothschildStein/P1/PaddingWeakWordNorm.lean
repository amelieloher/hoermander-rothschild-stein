-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingWeakWordDescent
public import RothschildStein.P2.SmoothingRegularity
public import RothschildStein.Definitions.weakWordENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.P1

/-- Quantitative descent for every original weak word, with
the exact fiber-volume factor and the infimum-based norm.
The inequality remains valid when either norm is infinite. -/
theorem paddingDistributionTensor_weakWordENorm_le {q n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (hJ : volume (J : Set (Fin d → ℝ)) < ⊤)
    (η : _root_.TestFunction J ℝ ⊤) (hη : ∫ z, η z = 1)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (v : (Fin (n + d) → ℝ) → ℝ)
    (hv : LocallyIntegrableOn v (P2.cylinder Ω J : Set (Fin (n + d) → ℝ)) volume)
    (hT : paddingDistributionTensorOneCLM Ω (P2.cylinder Ω J)
      (padding_cylinder_subset_base Ω J) T =
      Distribution.ofFun (P2.cylinder Ω J) v volume (⊤ : ℕ∞))
    (I : List (Fin (q + 1))) :
    ENNReal.ofReal ((volume (J : Set (Fin d → ℝ))).toReal ^ (1 / p.toReal)) *
      weakWordENorm X Ω I p (P2.fiberAvg v η) ≤
      weakWordENorm (paddingVectorFields (d := d) X) (P2.cylinder Ω J)
        (I.map paddingGeneratorIndex) p v := by
  unfold weakWordENorm
  apply le_sInf
  rintro r ⟨g, hg, hgm, rfl⟩
  obtain ⟨hweak, hgae⟩ := paddingDistributionTensor_weakWord_descent
    Ω J hJ.ne η hη X hX T v g hv hT I hg
  have hmeas := (P2.locallyIntegrableOn_fiberAvg hg.2.1 η).aestronglyMeasurable
  have hnorm := P2.eLpNorm_comp_cylinder (A := Ω) (B := J) hp hpt hJ hmeas
  have hle : sInf {r | ∃ g : (Fin n → ℝ) → ℝ,
      hasWeakWordDeriv X Ω I (P2.fiberAvg v η) g ∧
      AEStronglyMeasurable g (volume.restrict (Ω : Set (Fin n → ℝ))) ∧
      r = eLpNorm g p (volume.restrict (Ω : Set (Fin n → ℝ)))} ≤
      eLpNorm (P2.fiberAvg g η) p (volume.restrict (Ω : Set (Fin n → ℝ))) :=
    sInf_le ⟨P2.fiberAvg g η, hweak, hmeas, rfl⟩
  calc
    _ ≤ ENNReal.ofReal ((volume (J : Set (Fin d → ℝ))).toReal ^ (1 / p.toReal)) *
        eLpNorm (P2.fiberAvg g η) p (volume.restrict (Ω : Set (Fin n → ℝ))) :=
      mul_le_mul' le_rfl hle
    _ = eLpNorm g p (volume.restrict (P2.cylinder Ω J : Set (Fin (n + d) → ℝ))) := by
      rw [← hnorm, eLpNorm_congr_ae hgae.symm]

end RothschildStein.P1
