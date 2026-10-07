-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.RetainedLiePositiveJets
public import RothschildStein.G3.ParameterTravelJets
public import RothschildStein.G3.DilatedCoefficientNorm
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.G3

/-- Numerical endpoint and dilation jets control all actual list prefixes. -/
theorem retainedLie_chronologicalJetBounds {a s N Q : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω) {σ C A R ρ t : ℝ}
    (hC : 0 ≤ C) (hA : 1 ≤ A) (hR : 0 ≤ R) (ht : |t| ≤ 1)
    (hsmall : |t| *R < σ)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) (finiteLieTimeOneMap Φ) (ball 0 σ ×ˢ Ω))
    (hHjet : ∀ q ∈ ball 0 σ ×ˢ Ω, ∀ j, 1 ≤ j → j ≤ Q →
      ‖iteratedFDeriv ℝ j (finiteLieTimeOneMap Φ) q‖ ≤ C)
    (htravel : ∀ q ∈ ball 0 σ ×ˢ Ω, ‖finiteLieTimeOneMap Φ q-q.2‖ ≤ C*‖q.1‖)
    (fs : List (formalSpan a s p))
    (hcoeff : ∀ f ∈ fs, ‖D.basis.equivFun f‖ ≤ R)
    (hdilation : ∀ f ∈ fs, ∀ j, 1 ≤ j → j ≤ Q →
      ‖iteratedFDeriv ℝ j (dilatedInputCoordinates D f) t‖ ≤ A)
    (x y : Fin N → ℝ) (hball : ball x ρ ⊆ Ω)
    (hbudget : ‖y-x‖ + fs.length*(C*|t| *R) < ρ) :
    ChronologicalJetBounds Q (max 1 ((Q.factorial : ℝ)*C*A^Q))
      (fs.map (retainedLieAbsoluteStateMap D Φ)) (t,y) := by
  have hinput (f : formalSpan a s p) (hf : f ∈ fs) (z : Fin N → ℝ)
      (hz : z ∈ ball x ρ) : (dilatedInputCoordinates D f t,z) ∈ ball 0 σ ×ˢ Ω := by
    refine ⟨mem_ball_zero_iff.mpr ?_,hball hz⟩
    exact ((norm_dilatedInputCoordinates_le D f ht).trans
      (mul_le_mul_of_nonneg_left (hcoeff f hf) (abs_nonneg t))).trans_lt hsmall
  apply chronologicalJetBounds_of_parameter_travel Q _ _ t x y
    (ρ := ρ) (d := C*|t| *R)
    (by positivity)
  · intro g hg z hz
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hg
    have hi : ContDiffAt ℝ Q (fun w : ℝ × (Fin N → ℝ) =>
        (dilatedInputCoordinates D f w.1,w.2)) (t,z) :=
      ((((dilatedInputCoordinates_contDiff D f).comp contDiff_fst).prodMk
        contDiff_snd).contDiffAt).of_le (by simp)
    have he := (hH.contDiffAt ((isOpen_ball.prod hΩ).mem_nhds (hinput f hf z hz))).of_le
      (show (Q : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by simp)
    have ho := he.comp (g := finiteLieTimeOneMap Φ)
      (f := fun w : ℝ × (Fin N → ℝ) => (dilatedInputCoordinates D f w.1,w.2)) (t,z) hi
    exact contDiffAt_fst.prodMk ho
  · intro g hg z hz j hj hjQ
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hg
    have he := norm_retainedLieAbsoluteStateMap_jet_le D Φ f (t,z) hj
      ((hH.contDiffAt ((isOpen_ball.prod hΩ).mem_nhds (hinput f hf z hz))).of_le (by simp))
      hC hA (fun k hk hkj => hHjet _ (hinput f hf z hz) k hk (hkj.trans hjQ))
      (fun k hk hkj => hdilation f hf k hk (hkj.trans hjQ))
    apply he.trans
    apply max_le_max le_rfl
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hjQ) hC
    · exact pow_le_pow_right₀ hA hjQ
    · positivity
    · positivity
  · intro g hg z
    obtain ⟨f,_,rfl⟩ := List.mem_map.mp hg
    rfl
  · intro g hg z hz
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hg
    exact (htravel _ (hinput f hf z hz)).trans
      ((mul_le_mul_of_nonneg_left ((norm_dilatedInputCoordinates_le D f ht).trans
        (mul_le_mul_of_nonneg_left (hcoeff f hf) (abs_nonneg t))) hC).trans_eq (by ring))
  · simpa only [List.length_map] using hbudget
end RothschildStein.G3
