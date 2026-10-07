-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.LocalIntervalIntegralJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

universe u

/-- A smooth bounded scalar weight and a smooth time change preserve
an actual integrand's uniform full parameter-jet bound on a local domain
(BB Lemma 9.48, pp. 441–443). -/
theorem norm_weighted_reparametrized_local_interval_integral_jet_le {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {S : Set (E × ℝ)} (hS : IsOpen S) (G : E × ℝ → F)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G S) (a w : ℝ → ℝ)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (x : E)
    (hsegment : ∀ r ∈ Icc (0 : ℝ) 1, (x, a r) ∈ S)
    (hwbound : ∀ r ∈ Icc (0 : ℝ) 1, ‖w r‖ ≤ 1) (n : ℕ) {M : ℝ}
    (hbound : ∀ r ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ n (fun y => G (y, a r)) x‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (fun y => ∫ r in (0 : ℝ)..1, w r • G (y, a r)) x‖ ≤ M := by
  let L : E × ℝ → E × ℝ := fun p => (p.1, a p.2)
  have hL : ContDiff ℝ (⊤ : ℕ∞) L := contDiff_fst.prodMk (ha.comp contDiff_snd)
  have hT : IsOpen (L ⁻¹' S) := hS.preimage hL.continuous
  have hK : ContDiffOn ℝ (⊤ : ℕ∞) (G ∘ L) (L ⁻¹' S) :=
    hG.comp hL.contDiffOn (fun _ hp => hp)
  have hW : ContDiff ℝ (⊤ : ℕ∞) (fun p : E × ℝ => w p.2) := hw.comp contDiff_snd
  apply norm_local_interval_integral_jet_le hT (fun p => w p.2 • G (L p))
    (hW.contDiffOn.smul hK) x hsegment n
  intro r hr
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => G (y, a r)) x :=
    (hG.contDiffAt (hS.mem_nhds (hsegment r hr))).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
  change ‖iteratedFDeriv ℝ n (w r • (fun y => G (y, a r))) x‖ ≤ M
  rw [iteratedFDeriv_const_smul_apply (hs.of_le (by simp)), norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hwbound r hr)).trans (hbound r hr)

end RothschildStein.G4
