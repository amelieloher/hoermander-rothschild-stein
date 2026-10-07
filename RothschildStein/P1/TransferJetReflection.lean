-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ErrorTypesJets

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.P1

/-- Ordered coordinate derivatives of a locally smooth reflected
function retain the exact sign for each ordinary derivative. This is
used for the full reflected chart remainder (BB Lemma 11.22, p. 553). -/
theorem rsPartial_reflection_on {N : ℕ} (U : Opens (Fin N → ℝ))
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (J : List (Fin N)) : ∀ u : Fin N → ℝ, -u ∈ U →
      rsPartial J (fun v => f (-v)) u = (-1 : ℝ)^J.length * rsPartial J f (-u) := by
  induction J with
  | nil => intro u _; simp only [rsPartial, List.length_nil, pow_zero, one_mul]
  | cons j J ih =>
    intro u hu
    have he : rsPartial J (fun v => f (-v)) =ᶠ[𝓝 u]
        (fun v => (-1 : ℝ)^J.length * rsPartial J f (-v)) := by
      filter_upwards [((continuous_neg.tendsto u).eventually (U.isOpen.mem_nhds hu))] with v hv
      exact ih v hv
    have hd := ((L1.rsPartial_contDiffOn U J f hf).contDiffAt
      (U.isOpen.mem_nhds hu)).differentiableAt (by simp)
    have hp := (hd.hasFDerivAt.comp u (hasFDerivAt_id u).neg).const_mul ((-1 : ℝ)^J.length)
    change fderiv ℝ (rsPartial J (fun v => f (-v))) u (Pi.single j 1) = _
    change HasFDerivAt (fun v => (-1 : ℝ)^J.length * rsPartial J f (-v)) _ u at hp
    rw [he.fderiv_eq, hp.fderiv]
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      neg_apply, ContinuousLinearMap.id_apply, map_neg, smul_eq_mul,
      List.length_cons, pow_succ, rsPartial]
    ring

/-- Reflection preserves every weighted vanishing-jet order,
including negative integer thresholds; only smoothness near zero is
needed (BB Lemma 11.22, p. 553). -/
theorem JetVan.reflection {N : ℕ} {ω : Fin N → ℕ} {o : ℤ}
    (U : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ U)
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hjet : JetVan ω o f) : JetVan ω o (fun u => f (-u)) := by
  intro J hJ
  rw [rsPartial_reflection_on U f hf J 0 (by simpa only [neg_zero] using h0)]
  simp only [neg_zero, hjet J hJ, mul_zero]

end RothschildStein.P1
