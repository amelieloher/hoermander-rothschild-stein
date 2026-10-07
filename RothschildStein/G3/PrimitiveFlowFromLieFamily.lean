-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteLieEndpointTimeScaling
public import RothschildStein.G3.FiniteLieFieldWords
@[expose] public section
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.G3

def primitiveFlowFromLieFamily {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (κ : ℝ) (i : Fin a) (q : (Fin N → ℝ) × ℝ) : Fin N → ℝ :=
  Φ ((D.basis.equivFun (κ • (wordLieElement [i] : formalSpan a s p)),q.1),q.2/κ)

theorem primitiveFlowFromLieFamily_contDiffOn {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω₀ : Opens (Fin N → ℝ))
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    {σ κ : ℝ} (hκ : 0 < κ)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 σ ×ˢ (Ω₀ : Set (Fin N → ℝ))) ×ˢ Ioo (-2) 2))
    (i : Fin a) (hi : D.basis.equivFun (κ • (wordLieElement [i] : formalSpan a s p)) ∈ ball 0 σ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (primitiveFlowFromLieFamily D Φ κ i)
      ((Ω₀ : Set (Fin N → ℝ)) ×ˢ Ioo (-κ) κ) := by
  apply hΦ.comp
    (((contDiffOn_const.prodMk contDiffOn_fst).prodMk (contDiffOn_snd.div_const κ)))
  intro q hq
  refine ⟨⟨hi,hq.1⟩,?_⟩
  apply abs_lt.mp
  rw [abs_div,abs_of_pos hκ]
  exact ((div_lt_one hκ).mpr (abs_lt.mpr hq.2)).trans (by norm_num)
end RothschildStein.G3
