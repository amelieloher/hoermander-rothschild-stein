-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependenceTangent
public import RothschildStein.G1.SmoothDependenceTaylor

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace RothschildStein.G1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The joint derivative obtained from the first variation and the ODE. -/
def flowDerivative (Z : E → E) (Φ : E → ℝ → E)
    (J : (E × ℝ) → E →L[ℝ] E) (p : E × ℝ) : (E × ℝ) →L[ℝ] E :=
  (J p).coprod (ContinuousLinearMap.toSpanSingleton ℝ (Z (Φ p.1 p.2)))

set_option backward.defeqAttrib.useBackward true in
/-- Continuous initial variations and the ODE's time
partial give the joint derivative. This is an assembly lemma, with the first
variation explicitly supplied (BB Proposition 1.2, p. 3). -/
theorem flow_hasStrictFDerivAt_of_first_variation
    {Z : E → E} {Φ : E → ℝ → E} {J : (E × ℝ) → E →L[ℝ] E} {p : E × ℝ}
    (hJ : ∀ᶠ q in 𝓝 p, HasFDerivAt (fun x => Φ x q.2) (J q) q.1)
    (hODE : ∀ᶠ q in 𝓝 p, HasDerivAt (Φ q.1) (Z (Φ q.1 q.2)) q.2)
    (hcJ : ContinuousAt J p) (hcZ : ContinuousAt (fun q : E × ℝ => Z (Φ q.1 q.2)) p) :
    HasStrictFDerivAt (fun q : E × ℝ => Φ q.1 q.2) (flowDerivative Z Φ J p) p := by
  apply hasStrictFDerivAt_uncurry_coprod
    (f := Φ) (f₁ := fun x t => J (x, t))
    (f₂ := fun x t => ContinuousLinearMap.toSpanSingleton ℝ (Z (Φ x t)))
    hJ hODE hcJ
  exact (ContinuousLinearMap.toSpanSingletonLIE ℝ E).continuous.continuousAt.comp hcZ

set_option backward.defeqAttrib.useBackward true in
/-- The regularity induction step after construction and
identification of the first variation: a `C^n` first variation and a `C^n`
flow yield a `C^{n+1}` flow. Finite orders suffice; no analytic order occurs
(BB Proposition 1.2, p. 3). -/
theorem flow_contDiffOn_succ_of_first_variation
    {n : ℕ} {Ω : Set E} {D : Set (E × ℝ)} (hD : IsOpen D)
    {Z : E → E} (hZ : ContDiffOn ℝ (n : ℕ∞ω) Z Ω)
    {Φ : E → ℝ → E} {J : (E × ℝ) → E →L[ℝ] E}
    (hΦ : ContDiffOn ℝ (n : ℕ∞ω) (fun q : E × ℝ => Φ q.1 q.2) D)
    (hmem : ∀ q ∈ D, Φ q.1 q.2 ∈ Ω)
    (hJ : ContDiffOn ℝ (n : ℕ∞ω) J D)
    (hpartial : ∀ q ∈ D, HasFDerivAt (fun x => Φ x q.2) (J q) q.1)
    (hODE : ∀ q ∈ D, HasDerivAt (Φ q.1) (Z (Φ q.1 q.2)) q.2) :
    ContDiffOn ℝ ((n : ℕ∞ω) + 1) (fun q : E × ℝ => Φ q.1 q.2) D := by
  have hcomp := hZ.comp hΦ hmem
  have hder : ∀ q ∈ D,
      HasFDerivAt (fun p : E × ℝ => Φ p.1 p.2) (flowDerivative Z Φ J q) q := by
    intro q hq
    have hn := hD.mem_nhds hq
    have he : ∀ᶠ p in 𝓝 q, p ∈ D := hn
    exact (flow_hasStrictFDerivAt_of_first_variation
      (he.mono fun p hp => hpartial p hp) (he.mono fun p hp => hODE p hp)
      (hJ.continuousOn.continuousAt hn) (hcomp.continuousOn.continuousAt hn)).hasFDerivAt
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hD]
  refine ⟨fun q hq => (hder q hq).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro h
    simp at h
  · have ht : ContDiffOn ℝ (n : ℕ∞ω)
        (fun p : E × ℝ => ContinuousLinearMap.toSpanSingleton ℝ (Z (Φ p.1 p.2))) D := by
      exact (ContinuousLinearMap.toSpanSingletonLIE ℝ E).toContinuousLinearEquiv.contDiff.contDiffOn.comp
          hcomp (fun _ _ => mem_univ _)
    have hfd : ContDiffOn ℝ (n : ℕ∞ω) (flowDerivative Z Φ J) D := by
      have hh := (hJ.clm_comp (contDiffOn_const (c := ContinuousLinearMap.fst ℝ E ℝ))).add
        (ht.clm_comp (contDiffOn_const (c := ContinuousLinearMap.snd ℝ E ℝ)))
      convert hh using 1
      funext p
      apply ContinuousLinearMap.ext
      intro v
      rfl
    exact hfd.congr (fun q hq => (hder q hq).fderiv)

end RothschildStein.G1
