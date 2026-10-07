-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FundamentalPositiveTypes
public import RothschildStein.H3.FundamentalSecondBoundCompactPv
public import RothschildStein.H3.LocalConvolutionBound
public import RothschildStein.H3.WeakWordWeightCases
public import RothschildStein.H3.QuasiballOriginFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- Bounds for the type-two kernel and type-one first derivatives,
combined with the global second-order estimate, control every local word
through weight two. Radius-dependent constants precede all sources. -/
theorem fundamental_local_word_bounds_of_compact_principalValue_bounds {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (ρ : ℝ) (hρ : 0 < ρ) (p : ℝ≥0∞) (hp : 1 ≤ p) (M : ℝ) (hM : 0 ≤ M)
    (hLp : ∀ i j : Fin q, ∀ f : (Fin n → ℝ) → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm (H1.principalValueConvolution G H.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) f) p volume ≤
          ENNReal.ofReal M*eLpNorm f p volume) :
    ∃ C : ℝ → ℝ, ∀ R : ℝ, 0 < R → 0 < C R ∧
      ∀ f : (Fin n → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        (∀ᵐ y ∂volume, ρ ≤ ν y → f y = 0) →
        ∀ I ∈ wordFamily driftWeight 2,
          eLpNorm (wordDerivative H.fields I (G2.groupConvolution G f K)) p
            (volume.restrict (quasiballDomain G ν 0 R : Set (Fin n → ℝ))) ≤
              ENNReal.ofReal (C R)*eLpNorm f p volume := by
  classical
  have hK := fundamental_type_two G H K
  have hfirst := fun i : Fin q => fundamental_horizontal_type_one G H K i
  let lam := fun i : Fin q => kernelSphereBound ν (fieldDerivative (H.fields i.succ) K)
  have hlam : ∀ i, 0 ≤ lam i := fun i => ((hfirst i).kernelSphereBound_properties ν.gauge).1
  let L : ℝ := ∑ i : Fin q, lam i
  have hL : 0 ≤ L := Finset.sum_nonneg (fun i _ => hlam i)
  have hlamL : ∀ i, lam i ≤ L := fun i => Finset.single_le_sum (fun j _ => hlam j) (Finset.mem_univ i)
  have hzero : 0 ≤ kernelSphereBound ν K := (hK.kernelSphereBound_properties ν.gauge).1
  obtain ⟨C₉,hC₉,hsecond⟩ := fundamental_second_bound_of_compact_principalValue_bounds G H K hQ p hp M hM hLp
  let F := fun R α : ℝ => (G.homogeneousDimension : ℝ)*(volume {x | ν x < 1}).toReal*(ρ+R)^α/α
  let C := fun R : ℝ => kernelSphereBound ν K*F R 2+L*F R 1+C₉
  refine ⟨C, ?_⟩
  intro R hR
  have hF2 : 0 ≤ F R 2 := by dsimp only [F]; positivity
  have hF1 : 0 ≤ F R 1 := by dsimp only [F]; positivity
  have hC0 : kernelSphereBound ν K*F R 2 ≤ C R := by dsimp only [C]; nlinarith [mul_nonneg hL hF1]
  have hC1 : L*F R 1 ≤ C R := by dsimp only [C]; nlinarith [mul_nonneg hzero hF2]
  have hC2 : C₉ ≤ C R := by dsimp only [C]; nlinarith [mul_nonneg hzero hF2,mul_nonneg hL hF1]
  refine ⟨by dsimp only [C]; positivity, ?_⟩
  intro f hf hsf hs I hI
  have hfp : MemLp f p volume := hf.continuous.memLp_of_hasCompactSupport hsf
  have hw := (S.mem_wordFamily_iff driftWeight 2 I).mp hI
  have hc : wordWeight driftWeight I = 0 ∨ wordWeight driftWeight I = 1 ∨ wordWeight driftWeight I = 2 := by omega
  rcases hc with h0 | h1w | h2
  · rw [word_eq_nil_of_weight_zero driftWeight I h0]
    simp only [wordDerivative]
    rw [quasiballDomain_origin_set]
    exact (hK.local_convolution_bound ν h1 hsym hρ hR hp hfp hs).2.trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal hC0) le_rfl)
  · obtain ⟨i,rfl⟩ := drift_word_weight_one I h1w
    simp only [wordDerivative]
    rw [H.fieldDerivative_homogeneousPotential G i (K.smooth_off_zero.of_le (by simp))
      K.homogeneous (by linarith) hf hsf, quasiballDomain_origin_set]
    have hb := ((hfirst i).local_convolution_bound ν h1 hsym hρ hR hp hfp hs).2
    exact hb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      ((mul_le_mul_of_nonneg_right (hlamL i) hF1).trans hC1)) le_rfl)
  · exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
      ((hsecond f hf hsf I h2).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hC2) le_rfl))

end RothschildStein.H3
