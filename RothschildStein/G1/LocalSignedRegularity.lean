-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalSmoothExtension
public import RothschildStein.G1.SignedQuasiexponentialRegularity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Local smooth product factors with opposite initial coefficients
produce a signed weighted quasiexponential which is jointly C¹ at time zero.
This uses local factor data directly and requires no global flow inverse
(BB Thm 1.48, pp. 32–34). -/
theorem signedWeightedFactoredMap_contDiffAt_zero_of_local_factors {n : ℕ}
    {U : Set ((Fin n → ℝ) × E)} (hU : IsOpen U)
    (Hp Hm : (Fin n → ℝ) × E → E)
    (hHp : ContDiffOn ℝ (⊤ : ℕ∞) Hp U) (hHm : ContDiffOn ℝ (⊤ : ℕ∞) Hm U)
    (hmatch : ∀ y, (0, y) ∈ U → -Hm (0, y) = Hp (0, y))
    (α : Fin n → ℝ) (hα : ∀ i, 0 < α i) (x : E) (hx : (0, x) ∈ U) :
    ContDiffAt ℝ 1 (signedFactoredMap Hp Hm (weightedAbsolutePowers α)) (0, x) := by
  obtain ⟨Kp, Km, hKp, hKm, hmatchK, heq⟩ :=
    exists_signedFactor_localExtensions hU Hp Hm hHp hHm hmatch x hx
  have hK := (signedWeightedFactoredMap_contDiff_one Kp Km α
    (hKp.of_le (by simp)) (hKm.of_le (by simp)) hmatchK hα).contDiffAt (x := (0, x))
  apply hK.congr_of_eventuallyEq
  have hmap : Continuous (fun q : ℝ × E => (weightedAbsolutePowers α q.1, q.2)) :=
    ((weightedAbsolutePowers_continuous α hα).comp continuous_fst).prodMk continuous_snd
  have heq' : ∀ᶠ p in 𝓝 (weightedAbsolutePowers α 0, x), Kp p = Hp p ∧ Km p = Hm p := by
    rw [weightedAbsolutePowers_zero α hα]
    exact heq
  have ht := (hmap.tendsto (0, x)).eventually heq'
  filter_upwards [ht] with q hq
  simp only [signedFactoredMap, hq.1, hq.2]

end RothschildStein.G1
