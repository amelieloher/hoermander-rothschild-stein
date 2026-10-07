-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BracketJetBounds
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.G3

/-- A bracket loses one coefficient jet, with a quantitative
constant bilinear in the two field jet bounds (BB pp. 413–415). -/
theorem norm_bracket_jet_le {N R n : ℕ}
    (Ω : Opens (Fin N → ℝ)) (U V : (Fin N → ℝ) → (Fin N → ℝ))
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U Ω) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) (hn : n + 1 ≤ R) {B F : ℝ}
    (hUjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j U x‖ ≤ B)
    (hVjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j V x‖ ≤ F) :
    ‖iteratedFDeriv ℝ n (VectorField.lieBracket ℝ U V) x‖ ≤ 2 ^ (n + 1) * B * F := by
  have hUV := (hV.fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply hU
  have hVU := (hU.fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply hV
  have hUVn : ContDiffAt ℝ n (fun y => fderiv ℝ V y (U y)) x :=
    (hUV.contDiffAt (Ω.isOpen.mem_nhds hx)).of_le (by simp)
  have hVUn : ContDiffAt ℝ n (fun y => fderiv ℝ U y (V y)) x :=
    (hVU.contDiffAt (Ω.isOpen.mem_nhds hx)).of_le (by simp)
  change ‖iteratedFDeriv ℝ n ((fun y => fderiv ℝ V y (U y)) -
    (fun y => fderiv ℝ U y (V y))) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply hUVn hVUn]
  apply (norm_sub_le _ _).trans
  have hh := add_le_add (norm_vectorDerivative_jet_le Ω U V hU hV hx hn hUjet hVjet)
    (norm_vectorDerivative_jet_le Ω V U hV hU hx hn hVjet hUjet)
  apply hh.trans_eq
  rw [pow_succ]
  ring
end RothschildStein.G3
