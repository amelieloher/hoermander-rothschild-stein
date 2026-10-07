-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingNoDriftWeakWordNorm
public import RothschildStein.P1.PaddingNoDriftWeightedSpan
public import RothschildStein.S.Sobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.P1

/-- Quantitative descent of the Sobolev norm at
all orders: the base norm times the fiber-volume factor is bounded
by the full padded norm, including infinite values. -/
theorem paddingDistributionTensor_noDrift_sobolevXENorm_le {q n d k : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (hJ : volume (J : Set (Fin d → ℝ)) < ⊤)
    (η : _root_.TestFunction J ℝ ⊤) (hη : ∫ z, η z = 1)
    (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
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
      sobolevXENorm (paddingNoDriftWeights (d := d) w)
        (paddingNoDriftVectorFields (d := d) X) (P2.cylinder Ω J) k p v := by
  classical
  have hword (I : List (Fin q)) :=
    paddingDistributionTensor_noDrift_weakWordENorm_le Ω J hJ η hη X hX hp hpt T v hv hT I
  have hinj : Function.Injective (List.map (Fin.castAdd d : Fin q → Fin (q + d))) :=
    List.map_injective_iff.mpr (Fin.castAdd_injective _ _)
  have hsub : (wordFamily w k).image (List.map (Fin.castAdd d)) ⊆
      wordFamily (paddingNoDriftWeights (d := d) w) k := by
    intro I hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    apply (S.mem_wordFamily_iff _ _ _).mpr
    rw [wordWeight_paddingNoDrift_map]
    exact (S.mem_wordFamily_iff _ _ _).mp hJ
  simp only [sobolevXENorm, Finset.mul_sum]
  apply le_trans (Finset.sum_le_sum (fun I _ => hword I))
  have hsum :
      (∑ I ∈ (wordFamily w k).image (List.map (Fin.castAdd d)),
        weakWordENorm (paddingNoDriftVectorFields (d := d) X) (P2.cylinder Ω J) I p v) =
      ∑ I ∈ wordFamily w k,
        weakWordENorm (paddingNoDriftVectorFields (d := d) X) (P2.cylinder Ω J)
          (I.map (Fin.castAdd d)) p v :=
    Finset.sum_image (fun I _ J _ h => hinj h)
  rw [← hsum]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro I _ _
  exact bot_le

end RothschildStein.P1
