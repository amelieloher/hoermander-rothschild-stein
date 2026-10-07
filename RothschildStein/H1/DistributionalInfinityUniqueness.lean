-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.DistributionalUniqueness
public import RothschildStein.H1.NullDecay
public import RothschildStein.H1.KernelCommonBounds
public import RothschildStein.H1.GaugeDecay

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
namespace RothschildStein.H1
variable {N q : ℕ} {G : HomogeneousGroup N} {H : StandingHypotheses G q}

/-- Uniqueness for arbitrary fundamental distributions with
continuous tails tending to zero. The local weak regularity theorem smooths
the difference; compact-test pairings identify its tail, and Liouville
finishes the proof (BB p. 271). -/
theorem FundamentalKernel.distributionalKernelUniquenessAtInfinity
    (K : FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ)) :
    DistributionalKernelUniquenessAtInfinity K := by
  intro T hfund htail
  obtain ⟨R, g, hg, hgd, hgt⟩ := htail
  obtain ⟨f, hf, hrep⟩ := H.smooth_difference_fundamental G K T hfund
  let V : Set (Fin N → ℝ) := {x | max R 1 < ‖x‖}
  have hV : IsOpen V := isOpen_lt continuous_const continuous_norm
  have hVR : V ⊆ {x | R < ‖x‖} := by
    intro x hx
    change R < ‖x‖
    exact (le_max_left R 1).trans_lt hx
  have hV0 : V ⊆ {(0 : Fin N → ℝ)}ᶜ := by
    intro x hx hz
    have hn := (le_max_right R 1).trans_lt hx
    rw [mem_singleton_iff.mp hz, norm_zero] at hn
    norm_num at hn
  have hc : ContinuousOn (fun x => f x + K x - g x) V :=
    (hf.continuous.continuousOn.add (K.smooth_off_zero.continuousOn.mono hV0)).sub (hg.mono hVR)
  have hae : ∀ᵐ x ∂volume, x ∈ V → f x + K x - g x = 0 := by
    apply hV.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hc.locallyIntegrableOn hV.measurableSet)
    intro φ hφ hs hφV
    let ψ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) := ⟨φ, hφ, hs, subset_univ _⟩
    let ψV : TestFunction ⟨V, hV⟩ ℝ (⊤ : ℕ∞) := ⟨φ, hφ, hs, hφV⟩
    have hif : Integrable (fun x => φ x * f x) :=
      hf.continuous.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφ.continuous hs
    have hiK : Integrable (fun x => φ x * K x) :=
      K.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφ.continuous hs
    have hig : Integrable (fun x => φ x * g x) := by
      change Integrable (fun x => ψV x • g x)
      exact ψV.integrable_smul ((hg.mono hVR).locallyIntegrableOn hV.measurableSet)
    have he := hrep ψ
    change T ψ - K.toDistribution ψ = _ at he
    have hk : K.toDistribution ψ = ∫ x, φ x * K x := by
      rw [FundamentalKernel.toDistribution, Distribution.ofFun_apply
        (locallyIntegrableOn_univ.mpr K.locallyIntegrable)]
      rfl
    rw [hgt ψ (hφV.trans hVR), hk] at he
    change (∫ x, g x * φ x) - (∫ x, φ x * K x) = ∫ x, φ x * f x at he
    simp_rw [smul_eq_mul, mul_sub, mul_add]
    have hsub := integral_sub (hif.add hiK) hig
    have hadd := integral_add hif hiK
    simp only [Pi.add_apply] at hsub hadd
    rw [hsub, hadd]
    have hswap : (fun x => g x * φ x) = (fun x => φ x * g x) := by
      funext x; exact mul_comm _ _
    rw [hswap] at he
    linarith
  have he : EqOn (fun x => f x + K x - g x) 0 V := by
    apply Measure.eqOn_open_of_ae_eq (μ := volume) _ hV hc continuousOn_const
    change ∀ᵐ x ∂volume.restrict V, f x + K x - g x = 0
    exact (ae_restrict_iff' hV.measurableSet).mpr hae
  obtain ⟨C, _, hb⟩ := K.common_bounds
  have hKd := decay_of_gauge_power_bound G H.norm (by linarith : 2 - (G.homogeneousDimension : ℝ) < 0)
    (C := C) (A := 1) (f := K) (fun x hx => (hb x (by
      intro hz
      rw [(H.norm.gauge.2.2.1 x).mpr hz] at hx
      norm_num at hx)).1)
  have hfd : ∀ ε > 0, ∃ A : ℝ, ∀ x, A ≤ ‖x‖ → ‖f x‖ ≤ ε := by
    intro ε hε
    obtain ⟨A, hA⟩ := hgd (ε / 2) (by positivity)
    obtain ⟨B, hB⟩ := hKd (ε / 2) (by positivity)
    refine ⟨max (max A B) (max R 1 + 1), fun x hx => ?_⟩
    have hxV : x ∈ V := by dsimp [V]; linarith [le_max_right (max A B) (max R 1 + 1)]
    have heq : f x = g x - K x := by have hh := he hxV; dsimp at hh; linarith
    rw [heq]
    exact (norm_sub_le _ _).trans (by
      have ha := hA x ((le_max_left A B).trans ((le_max_left _ _).trans hx))
      have hb := hB x ((le_max_right A B).trans ((le_max_left _ _).trans hx))
      linarith)
  have hnull : ∀ φ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, f x * sumSquaresWithDriftTranspose H.fields φ x) = 0 := by
    intro φ hφ hs
    let ψ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) := ⟨φ, hφ, hs, subset_univ _⟩
    have hh := hrep (sumSquaresWithDriftTransposeTest ⊤ H.fields
      (fun i => (H.fields_smooth G i).contDiffOn) ψ)
    change T _ - K.toDistribution _ = _ at hh
    rw [(H.isFundamentalDistribution_iff G T).mp hfund,
      (H.isFundamentalDistribution_iff G K.toDistribution).mp K.distribution_fundamental] at hh
    simp only [sub_self, H.transposeTest_apply G, mul_comm] at hh
    change 0 = ∫ x, f x * sumSquaresWithDriftTranspose H.fields φ x at hh
    exact hh.symm
  have hz := H.weak_null_decay_ae_zero G hf.continuous.locallyIntegrable
    hf.continuous.continuousOn hnull hfd
  apply DFunLike.ext
  intro φ
  have hh := hrep φ
  change T φ - K.toDistribution φ = _ at hh
  have hi : (∫ x, φ x * f x) = 0 := by
    rw [← integral_zero]
    apply integral_congr_ae
    filter_upwards [hz] with x hx
    simp only [hx, Pi.zero_apply, mul_zero]
  rw [hi] at hh
  exact sub_eq_zero.mp hh

end RothschildStein.H1
