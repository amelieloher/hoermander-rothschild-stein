-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingWeakWordNorm
public import RothschildStein.P1.PaddingWeightedSpan
public import RothschildStein.S.Sobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.P1

private theorem padding_index_val {q d : ℕ} (i : Fin (q + 1)) :
    (paddingGeneratorIndex (d := d) i).val = i.val := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    simp [paddingGeneratorIndex]

private theorem padding_index_injective {q d : ℕ} :
    Function.Injective (paddingGeneratorIndex (q := q) (d := d)) := by
  intro i j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  simpa only [padding_index_val] using hv

/-- Quantitative descent of the Sobolev norm at
all orders: the base norm times the fiber-volume factor is bounded
by the full padded norm, including infinite values. -/
theorem paddingDistributionTensor_sobolevXENorm_le {q n d k : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
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
 :
    ENNReal.ofReal ((volume (J : Set (Fin d → ℝ))).toReal ^ (1 / p.toReal)) *
      sobolevXENorm w X Ω k p (P2.fiberAvg v η) ≤
      sobolevXENorm (paddingControlWeights (d := d) w)
        (paddingVectorFields (d := d) X) (P2.cylinder Ω J) k p v := by
  classical
  have hword (I : List (Fin (q + 1))) :=
    paddingDistributionTensor_weakWordENorm_le Ω J hJ η hη X hX hp hpt T v hv hT I
  have hinj : Function.Injective (List.map (paddingGeneratorIndex (q := q) (d := d))) :=
    List.map_injective_iff.mpr padding_index_injective
  have hsub : (wordFamily w k).image (List.map (paddingGeneratorIndex (d := d))) ⊆
      wordFamily (paddingControlWeights (d := d) w) k := by
    intro I hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    apply (S.mem_wordFamily_iff _ _ _).mpr
    rw [wordWeight_padding_map]
    exact (S.mem_wordFamily_iff _ _ _).mp hJ
  simp only [sobolevXENorm, Finset.mul_sum]
  apply le_trans (Finset.sum_le_sum (fun I _ => hword I))
  have hsum :
      (∑ I ∈ (wordFamily w k).image (List.map (paddingGeneratorIndex (d := d))),
        weakWordENorm (paddingVectorFields (d := d) X) (P2.cylinder Ω J) I p v) =
      ∑ I ∈ wordFamily w k,
        weakWordENorm (paddingVectorFields (d := d) X) (P2.cylinder Ω J)
          (I.map paddingGeneratorIndex) p v :=
    Finset.sum_image (fun I _ J _ h => hinj h)
  rw [← hsum]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro I _ _
  exact bot_le

end RothschildStein.P1
