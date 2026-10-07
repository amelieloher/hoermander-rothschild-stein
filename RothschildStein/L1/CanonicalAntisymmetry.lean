-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalFrameOpenInverse
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace RothschildStein.L1

/-- Reversal of canonical trajectories and the actual inverse
germs imply antisymmetry near the diagonal (BB (10.39), p. 509). -/
theorem canonicalInverse_antisymmetric_eventually {N : ℕ}
    (K Θ : ((Fin N → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ)) (x : Fin N → ℝ)
    (hΘ : ContinuousAt Θ (x,x)) (hΘx : Θ (x,x) = 0)
    (hright : ∀ᶠ q in 𝓝 (x,x), K (q.1,Θ q) = q.2)
    (hleft : ∀ᶠ q in 𝓝 (x,0), Θ (q.1,K q) = q.2)
    (hreverse : ∀ᶠ q in 𝓝 (x,0), K (K q,-q.2) = q.1) :
    ∀ᶠ q in 𝓝 (x,x), Θ (q.2,q.1) = -Θ q := by
  have hG : Tendsto (fun q : (Fin N → ℝ) × (Fin N → ℝ) => (q.1,Θ q))
      (𝓝 (x,x)) (𝓝 (x,0)) := by
    simpa only [hΘx] using (continuousAt_fst.prodMk hΘ).tendsto
  have hH : Tendsto (fun q : (Fin N → ℝ) × (Fin N → ℝ) => (q.2,-Θ q))
      (𝓝 (x,x)) (𝓝 (x,0)) := by
    simpa only [Pi.neg_apply,hΘx,neg_zero] using (continuousAt_snd.prodMk hΘ.neg).tendsto
  filter_upwards [hright,hG.eventually hreverse,hH.eventually hleft] with q hq hr hl
  change K (K (q.1,Θ q),-Θ q) = q.1 at hr
  change Θ (q.2,K (q.2,-Θ q)) = -Θ q at hl
  rw [hq] at hr
  rwa [hr] at hl
end RothschildStein.L1
