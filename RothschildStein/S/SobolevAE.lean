-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Sobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.S
variable {n m : ℕ}
variable (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Opens (Fin n → ℝ))

/-- The weak derivative norm depends only on the a.e.
function class (BB Def. 2.2, p. 68). -/
theorem weakWordENorm_congr_ae (I : List (Fin m)) (p : ℝ≥0∞)
    {f g : (Fin n → ℝ) → ℝ}
    (h : f =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))] g) :
    weakWordENorm X Ω I p f = weakWordENorm X Ω I p g := by
  unfold weakWordENorm
  congr 1
  ext r
  constructor
  · rintro ⟨z,hz,hm,hr⟩
    exact ⟨z,hasWeakWordDeriv_congr_ae X Ω hz h ae_eq_rfl,hm,hr⟩
  · rintro ⟨z,hz,hm,hr⟩
    exact ⟨z,hasWeakWordDeriv_congr_ae X Ω hz h.symm ae_eq_rfl,hm,hr⟩

/-- The Sobolev norm depends only on the a.e. function class
(BB Def. 2.2, p. 68). -/
theorem sobolevXENorm_congr_ae (w : Fin m → ℕ+) (k : ℕ) (p : ℝ≥0∞)
    {f g : (Fin n → ℝ) → ℝ}
    (h : f =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))] g) :
    sobolevXENorm w X Ω k p f = sobolevXENorm w X Ω k p g := by
  unfold sobolevXENorm
  apply Finset.sum_congr rfl
  intro I _
  exact weakWordENorm_congr_ae X Ω I p h

/-- Sobolev membership is invariant under a.e. equality
(BB Def. 2.2, p. 68). -/
theorem memSobolevX_congr_ae (w : Fin m → ℕ+) (k : ℕ) (p : ℝ≥0∞)
    {f g : (Fin n → ℝ) → ℝ}
    (h : f =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))] g) :
    memSobolevX w X Ω k p f ↔ memSobolevX w X Ω k p g := by
  constructor
  · intro hf
    refine ⟨hf.1.ae_eq h, fun I hI => ?_⟩
    obtain ⟨z,hz,hm⟩ := hf.2 I hI
    exact ⟨z,hasWeakWordDeriv_congr_ae X Ω hz h ae_eq_rfl,hm⟩
  · intro hg
    refine ⟨hg.1.ae_eq h.symm, fun I hI => ?_⟩
    obtain ⟨z,hz,hm⟩ := hg.2 I hI
    exact ⟨z,hasWeakWordDeriv_congr_ae X Ω hz h.symm ae_eq_rfl,hm⟩

end RothschildStein.S
