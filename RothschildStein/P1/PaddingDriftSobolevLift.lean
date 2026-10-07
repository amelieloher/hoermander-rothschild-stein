-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingDriftTriangularAdapter
public import RothschildStein.P1.PaddingCylinderFiberSetting
public import RothschildStein.P2.SmoothingRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.P1

/-- A forcing function in every original Sobolev
order lifts to the full genuinely padded diffusion family on a
finite positive-volume cylinder, including words with added indices. -/
theorem memSobolevX_paddingDrift_lift {q n d k : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (hJ0 : 0 < volume (J : Set (Fin d → ℝ)))
    (hJ : volume (J : Set (Fin d → ℝ)) < ⊤)
    (w : Fin (q + 1) → ℕ+) (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (f : (Fin n → ℝ) → ℝ) (hf : memSobolevX w X Ω k p f) :
    memSobolevX (paddingControlWeights (d := d) w)
      (paddingVectorFields (d := d) X) (P2.cylinder Ω J) k p
      (fun ξ => f (basePoint ξ)) := by
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
  have hbase := memSobolevX_paddingDriftBaseAlphabet (d := d) Ω w X p f hf
  rw [paddingVectorFields_eq_triangularLift]
  refine ⟨(P2.memLp_comp_cylinder_iff (A := Ω) (B := J) hp hpt hJ0 hJ
    hf.1.aestronglyMeasurable).mpr hf.1, ?_⟩
  intro I hI
  obtain ⟨g, hg, hgp⟩ := hbase.2 I hI
  exact ⟨fun ξ => g (basePoint ξ), S.hasWeakWordDeriv_lift Y P hXt hY I hg,
    (P2.memLp_comp_cylinder_iff (A := Ω) (B := J) hp hpt hJ0 hJ
      hgp.aestronglyMeasurable).mpr hgp⟩

end RothschildStein.P1
