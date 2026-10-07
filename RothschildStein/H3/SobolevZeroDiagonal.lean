-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SobolevApproximationTriangle
public import RothschildStein.S.TestSobolev
public import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.H3

/-- Sobolev limits of zero-boundary functions have actual diagonal
compact test approximations in the full fixed norm (BB Theorem 3.49, p. 123). -/
theorem memSobolevXZero_of_approximating_zero {N m : ℕ}
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (Ω : Opens (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) {u : (Fin N → ℝ) → ℝ}
    (hu : memSobolevX w X Ω k p u)
    (v : ℕ → (Fin N → ℝ) → ℝ)
    (hv : ∀ j, memSobolevXZero w X Ω k p (v j))
    (ht : Tendsto (fun j => sobolevXENorm w X Ω k p (fun x => u x-v j x))
      atTop (𝓝 0)) : memSobolevXZero w X Ω k p u := by
  classical
  have ha (j : ℕ) : ∃ φ : TestFunction Ω ℝ (⊤ : ℕ∞),
      sobolevXENorm w X Ω k p (fun x => v j x-φ x) <
        ENNReal.ofReal (1/((j : ℝ)+1)) := by
    obtain ⟨_,φ,hφ⟩ := hv j
    have he := hφ.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) <
      ENNReal.ofReal (1/((j : ℝ)+1)) by positivity))
    obtain ⟨n,hn⟩ := he.exists
    exact ⟨φ n,hn⟩
  choose φ hφ using ha
  refine ⟨hu,φ,?_⟩
  have he : Tendsto (fun j : ℕ => ENNReal.ofReal (1/((j : ℝ)+1))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim := ht.add he
  simp only [add_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le)
  intro j
  exact (sobolevXENorm_sub_le_sub_add_sub w X Ω hX k p hp hu (hv j).1
    (S.test_memSobolevX w Ω X hX k p (φ j))).trans (add_le_add le_rfl (hφ j).le)

end RothschildStein.H3
