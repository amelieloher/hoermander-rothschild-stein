-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.CompactSmoothExtension
public import RothschildStein.G4.CompactIntegralJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace RothschildStein.G4

universe u

/-- The finite-jet bound for an actual compact parameter integral
requires smoothness only near its compact integration segment. A common
open agreement buffer is derived, and derivatives of the unchanged local
integrand control derivatives of the integral (BB pp. 441–443). -/
theorem norm_local_compact_parameter_integral_jet_le {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {S : Set (E × ℝ)} (hS : IsOpen S) (G : E × ℝ → F)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G S) (x : E)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, (x, t) ∈ S) (n : ℕ) {M : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ n (fun y => G (y, t)) x‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (fun y => ∫ t in Icc (0 : ℝ) 1, G (y, t)) x‖ ≤ M := by
  have hK : IsCompact (({x} : Set E) ×ˢ Icc (0 : ℝ) 1) := isCompact_singleton.prod isCompact_Icc
  have hKS : ({x} : Set E) ×ˢ Icc (0 : ℝ) 1 ⊆ S := by
    rintro ⟨y, t⟩ ⟨hy, ht⟩
    have hy' : y = x := mem_singleton_iff.mp hy
    subst y
    exact hsegment t ht
  obtain ⟨g, hg, V, hV, hKV, heq⟩ := exists_contDiff_extension_near_compact hS hK hKS hG
  have he : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (0 : ℝ) 1, (y, t) ∈ V :=
    isCompact_Icc.eventually_forall_of_forall_eventually
      (fun t ht => hV.mem_nhds (hKV ⟨mem_singleton x, ht⟩))
  have hI : (fun y => ∫ t in Icc (0 : ℝ) 1, g (y, t)) =ᶠ[𝓝 x]
      (fun y => ∫ t in Icc (0 : ℝ) 1, G (y, t)) := by
    filter_upwards [he] with y hy
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact heq (hy t ht)
  rw [← (hI.iteratedFDeriv ℝ n).eq_of_nhds]
  apply norm_compact_parameter_integral_jet_le n g hg x
  intro t ht
  have htEq : (fun y => g (y, t)) =ᶠ[𝓝 x] (fun y => G (y, t)) :=
    he.mono (fun y hy => heq (hy t ht))
  rw [(htEq.iteratedFDeriv ℝ n).eq_of_nhds]
  exact hbound t ht

end RothschildStein.G4
