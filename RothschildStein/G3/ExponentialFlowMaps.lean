-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ModelProduct
public import RothschildStein.G3.ModelWords
public import RothschildStein.G3.LinearWordPolynomials
public import RothschildStein.G3.FreeModels
public import RothschildStein.G3.ModelFields
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import RothschildStein.G3.FiniteLieFields
public import RothschildStein.G4.TimeOneFlow

@[expose] public section
noncomputable section
open Set Metric
namespace RothschildStein.G3

def finiteLieTimeOneMap {m N : ℕ}
    (Φ : (((Fin m → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ)) :
    ((Fin m → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) := fun z => Φ (z, 1)

theorem finiteLieTimeOneMap_contDiffOn {m N : ℕ} {ε : ℝ} {x₀ : Fin N → ℝ}
    {Φ : (((Fin m → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ)}
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 ε ×ˢ ball x₀ ε) ×ˢ Ioo (-2) 2)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (finiteLieTimeOneMap Φ) (ball 0 ε ×ˢ ball x₀ ε) := by
  apply hΦ.comp (contDiffOn_id.prodMk contDiffOn_const)
  intro z hz
  exact ⟨hz, by norm_num⟩

end RothschildStein.G3
