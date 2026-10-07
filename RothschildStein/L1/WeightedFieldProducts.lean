-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedJetProducts
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- Scalar multiplication adds
weighted thresholds to every field coefficient. -/
theorem fieldJetClass_smul {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) {ω : Fin N → ℕ} {a b : ℝ}
    {f : (Fin N → ℝ) → ℝ} {R : (Fin N → ℝ) → (Fin N → ℝ)}
    (hf : scalarJetClass Ω ω a p f) (hR : fieldJetClass Ω ω b p R) :
    fieldJetClass Ω ω (a+b) p (fun u => f u • R u) := by
  refine ⟨hf.1.smul hR.1, ?_⟩
  intro j
  have hj := scalarJetVanishing_mul Ω h0 hf.1 (contDiffOn_pi.mp hR.1 j) hf.2 (hR.2 j)
  simpa only [smul_eq_mul, Pi.smul_apply, add_assoc] using hj

/-- A scalar factor zero at the
origin saves one ordinary order in the field factor. -/
theorem circleFieldJetClass_smul_scalar_zero {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) {ω : Fin N → ℕ} {a b : ℝ}
    {f : (Fin N → ℝ) → ℝ} {R : (Fin N → ℝ) → (Fin N → ℝ)}
    (hf : circleScalarJetClass Ω ω a (p+1) f) (hR : fieldJetClass Ω ω b p R) :
    circleFieldJetClass Ω ω (a+b) (p+1) (fun u => f u • R u) := by
  refine ⟨⟨hf.1.1.smul hR.1, ?_⟩, ?_⟩
  · intro j
    have hj := scalarJetVanishing_mul_of_zero Ω h0 hf.1.1
      (contDiffOn_pi.mp hR.1 j) hf.2 hf.1.2 (hR.2 j)
    simpa only [smul_eq_mul, Pi.smul_apply, add_assoc] using hj
  · simp only [hf.2, zero_smul]

end RothschildStein.L1
