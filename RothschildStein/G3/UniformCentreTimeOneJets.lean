-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.UniformBufferDomains
public import RothschildStein.G3.RescaledFiniteLieFlowBundle
@[expose] public section
noncomputable section
open Set Metric TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- A common actual time-one family on a numerical coefficient radius and
half-buffer around all centres. Its positive endpoint jets are bounded by
constants selected before the centres and the fields (BB Thm 9.23). -/
theorem exists_uniform_centre_timeOne_jet_flow {a s N R Q : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (hQR : Q+s ≤ R+1) :
    ∃ σ C : ℝ, 0 < σ ∧ 0 < C ∧
      ∀ (K : Set (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ)),
        (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (centreBuffer K r)) →
        (∀ x ∈ centreBuffer K r, ∀ i j, j ≤ R →
          ‖iteratedFDeriv ℝ j (X i) x‖ ≤ B) →
        ∃ Ψ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ),
          ContDiffOn ℝ (⊤ : ℕ∞) Ψ
            ((ball 0 σ ×ˢ (centreBuffer K (r/2) : Set (Fin N → ℝ))) ×ˢ Ioo (-2) 2) ∧
          (∀ f : formalSpan a s p, D.basis.equivFun f ∈ ball 0 σ →
            ∀ x ∈ centreBuffer K (r/2), Ψ ((D.basis.equivFun f,x),0) = x ∧
              ∀ t ∈ Ioo (-2 : ℝ) 2, Ψ ((D.basis.equivFun f,x),t) ∈ centreBuffer K r ∧
                HasDerivAt (fun v => Ψ ((D.basis.equivFun f,x),v))
                  (finiteLieField D X f (Ψ ((D.basis.equivFun f,x),t))) t) ∧
          ∀ q ∈ ball 0 σ ×ˢ (centreBuffer K (r/2) : Set (Fin N → ℝ)),
            ∀ n, 1 ≤ n → n ≤ Q → ‖iteratedFDeriv ℝ n (finiteLieTimeOneMap Ψ) q‖ ≤ C := by
  let ρ := min (1/4 : ℝ) (r/4)
  have hρ : 0 < ρ := lt_min (by norm_num) (by positivity)
  obtain ⟨ε,hε,hετ,hflow⟩ := exists_uniform_buffered_finiteLie_jet_flow
    (N := N) D ρ 1 B hρ zero_lt_one hB hQR
  let θ := ε/4
  have hθ : 0 < θ := by dsimp [θ]; positivity
  let C := (Q.factorial : ℝ) * (2*(1+ε⁻¹)^Q) * (1+|θ⁻¹|)^Q
  have hfact : 0 < (Q.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos Q
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨θ/2,C,by positivity,hC,?_⟩
  intro K X hX hXjet
  let A : Set ((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) :=
    ball 0 (1/2 : ℝ) ×ˢ (centreBuffer K (r/2) : Set (Fin N → ℝ))
  obtain ⟨U,hU,hAU,_,Φ,hΦ,hODE,hjets⟩ :=
    hflow (centreBuffer K r) X hX hXjet A
      (fun q hq => closedBall_subset_coefficient_centreBuffer K hr hq)
  have hpre : ∀ q ∈ ball (0 : Fin (freeDimension a s p) → ℝ) (θ/2) ×ˢ
      (centreBuffer K (r/2) : Set (Fin N → ℝ)), coefficientRescalingMap θ q ∈ U := by
    intro q hq
    apply hAU
    refine ⟨?_,hq.2⟩
    rw [mem_ball_zero_iff, coefficientRescalingMap_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hθ)]
    calc
      _ < θ⁻¹*(θ/2) := mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp hq.1) (inv_pos.mpr hθ)
      _ = 1/2 := by field_simp [ne_of_gt hθ]
  have hb := rescaled_finiteLie_flow_bundle D (centreBuffer K r) X hU hε hετ Φ hΦ hODE
    (fun z hz t ht j hj hjQ => (hjets z hz t ht).2 j hj hjQ |>.1) hpre
  exact ⟨Φ ∘ G4.flowScale θ, hb.1,
    fun f hf x hx => hb.2.1 f x ⟨hf,hx⟩, hb.2.2⟩
end RothschildStein.G3
