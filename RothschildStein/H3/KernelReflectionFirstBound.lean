-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FirstDerivativeBudget
public import RothschildStein.H3.EuclideanReflectionBounds
public import RothschildStein.H3.KernelSphereReflection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Reflection obeys the precise shared Λ₁ estimate with
C_iota = max(1, sqrt(N) c_iota), where c_iota is the actual Euclidean
inversion differential maximum. All budget-one partials are checked
(BB Definition 8.13 and Proposition 6.25). -/
theorem kernelDerivativeBound_reflection_one
    (ν : G2.HomogeneousNorm G) (hsym : ν.Symmetric)
    {T : (Fin N → ℝ) → ℝ} (hT : ContDiffOn ℝ (⊤ : ℕ∞) T {0}ᶜ) :
    kernelDerivativeBound ν (T ∘ G.inv) 1 ≤
      max 1 (Real.sqrt N * euclideanInversionSphereBound G ν) * kernelDerivativeBound ν T 1 := by
  have hfg : ContDiffOn ℝ (⊤ : ℕ∞) (T ∘ G.inv) {0}ᶜ :=
    hT.comp (G2.contDiff_inv G).contDiffOn (inversion_maps_punctured G)
  have hΛ : 0 ≤ kernelDerivativeBound ν T 1 := (kernelDerivativeBound_properties ν.gauge hT 1).1
  have hc : 0 ≤ euclideanInversionSphereBound G ν :=
    (euclideanInversionSphereBound_properties G ν.gauge).1
  unfold kernelDerivativeBound
  apply (Finset.sup'_le_iff _ _).mpr
  intro b _
  rcases multiindex_budget_one_cases (fun j => (b.val j).val) b.property with hz | ⟨i, hi⟩
  · rw [hz, euclideanPartial_zero]
    have he := kernelSphereBound_reflection G ν hsym T
    change kernelSphereBound ν (T ∘ G.inv) = kernelSphereBound ν T at he
    rw [he]
    have hb : kernelSphereBound ν T ≤ kernelDerivativeBound ν T 1 := by
      have hh := kernelDerivativeBound_mono ν T (by norm_num : (0 : ℕ) ≤ 1)
      simpa only [kernelDerivativeBound_zero] using hh
    have hmul : kernelDerivativeBound ν T 1 ≤
        max 1 (Real.sqrt N * euclideanInversionSphereBound G ν) * kernelDerivativeBound ν T 1 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (le_max_left (1 : ℝ) (Real.sqrt N * euclideanInversionSphereBound G ν)) hΛ
    simpa only [kernelDerivativeBound] using hb.trans hmul
  · rw [hi, euclideanPartial_single_one]
    have hpartial := (euclideanPartial_punctured_smooth hfg (Pi.single i 1)).continuousOn
    rw [euclideanPartial_single_one] at hpartial
    obtain ⟨x, hx, he⟩ := (kernelSphereBound_continuous ν.gauge hpartial).2.1
    rw [← he]
    have hb := coordinateDerivative_le_euclideanDifferential (T ∘ G.inv) x i
    have hg := (euclideanGradientSphereBound_properties ν.gauge
      (hfg.of_le (by simp))).2.2 x hx
    have hr := euclideanGradientSphereBound_reflection G ν hsym (hT.of_le (by simp))
    have hgrad := euclideanGradientSphereBound_le_kernelDerivativeBound G ν.gauge hT
    calc
      _ ≤ ‖euclideanDifferential (T ∘ G.inv) x‖ := hb
      _ ≤ euclideanGradientSphereBound ν (T ∘ G.inv) := hg
      _ ≤ euclideanInversionSphereBound G ν * euclideanGradientSphereBound ν T := hr
      _ ≤ euclideanInversionSphereBound G ν * (Real.sqrt N * kernelDerivativeBound ν T 1) :=
        mul_le_mul_of_nonneg_left hgrad hc
      _ = (Real.sqrt N * euclideanInversionSphereBound G ν) * kernelDerivativeBound ν T 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) _) hΛ

end RothschildStein.H3
