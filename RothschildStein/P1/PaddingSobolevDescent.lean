-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingWeakWordDescent
public import RothschildStein.P1.PaddingWeightedSpan
public import RothschildStein.P2.SmoothingRegularity
public import RothschildStein.S.Sobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.P1

/-- Sobolev regularity of any order descends from the padded
representative to the original arbitrary distribution, at the same
finite exponent p. Every original weighted word is retained; added words
are unnecessary for descent (BB p. 542, dimension reduction). -/
theorem paddingDistributionTensor_sobolev_descent {q n d k : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (hJ0 : 0 < volume (J : Set (Fin d → ℝ)))
    (hJ : volume (J : Set (Fin d → ℝ)) < ⊤)
    (η : _root_.TestFunction J ℝ ⊤) (hη : ∫ z, η z = 1)
    (w : Fin (q + 1) → ℕ+)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (v : (Fin (n + d) → ℝ) → ℝ)
    (hv : LocallyIntegrableOn v (P2.cylinder Ω J : Set (Fin (n + d) → ℝ)) volume)
    (hT : paddingDistributionTensorOneCLM Ω (P2.cylinder Ω J)
      (padding_cylinder_subset_base Ω J) T =
      Distribution.ofFun (P2.cylinder Ω J) v volume (⊤ : ℕ∞))
    (hSob : memSobolevX (paddingControlWeights (d := d) w) (paddingVectorFields (d := d) X)
      (P2.cylinder Ω J) k p v) :
    representsDistribution Ω T (P2.fiberAvg v η) ∧
      memSobolevX w X Ω k p (P2.fiberAvg v η) := by
  obtain ⟨hrep, hae⟩ := paddingDistributionTensor_descent Ω J hJ.ne η hη T v hv hT
  refine ⟨hrep, P2.memLp_fiberAvg hp hpt hJ0 hJ hv hae hSob.1, ?_⟩
  intro I hI
  have hmap : I.map paddingGeneratorIndex ∈ wordFamily (paddingControlWeights (d := d) w) k := by
    apply (S.mem_wordFamily_iff _ _ _).mpr
    rw [wordWeight_padding_map]
    exact (S.mem_wordFamily_iff _ _ _).mp hI
  obtain ⟨g, hg, hgp⟩ := hSob.2 _ hmap
  obtain ⟨hweak, hgae⟩ := paddingDistributionTensor_weakWord_descent
    Ω J hJ.ne η hη X hX T v g hv hT I hg
  exact ⟨P2.fiberAvg g η, hweak, P2.memLp_fiberAvg hp hpt hJ0 hJ hg.2.1 hgae hgp⟩

end RothschildStein.P1
