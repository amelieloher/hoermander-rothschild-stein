-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.RetainedLieChronologicalBounds
public import RothschildStein.G3.RetainedLieParameterJets
public import RothschildStein.G3.RetainedLieListSmoothAt
public import RothschildStein.G3.NumericalDilationJets
public import RothschildStein.G3.NumericalListRadius
public import RothschildStein.G3.ChronologicalBudgetMonotone
public import RothschildStein.G3.UniformCentreFlowBounds
public import RothschildStein.G3.ExponentialFlowMaps
public import RothschildStein.G3.NestedCentreBuffers
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.G3

/-- A single genuine flow family has numerical positive parameter jets for all
bounded-length lists with bounded coefficients, uniformly over all centres. -/
theorem exists_uniform_retainedLie_list_jet_bounds {a s N R Q : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) {r B T : ℝ} (hr : 0 < r) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hQR : Q+s ≤ R+1) (hQ : 1 ≤ Q) (L : ℕ) :
    ∃ η M σ : ℝ, 0 < η ∧ 0 < M ∧ 0 < σ ∧
      ∀ (K : Set (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ)),
        (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (centreBuffer K r)) →
        (∀ x ∈ centreBuffer K r, ∀ i j, j ≤ R → ‖iteratedFDeriv ℝ j (X i) x‖ ≤ B) →
        ∃ Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ),
          ContDiffOn ℝ (⊤ : ℕ∞) Φ
            ((ball 0 σ ×ˢ (centreBuffer K (r/2) : Set (Fin N → ℝ))) ×ˢ Ioo (-2) 2) ∧
          (∀ f : formalSpan a s p, D.basis.equivFun f ∈ ball 0 σ →
            ∀ x ∈ centreBuffer K (r/2), Φ ((D.basis.equivFun f,x),0) = x ∧
              ∀ t ∈ Ioo (-2 : ℝ) 2, Φ ((D.basis.equivFun f,x),t) ∈ centreBuffer K r ∧
                HasDerivAt (fun v => Φ ((D.basis.equivFun f,x),v))
                  (finiteLieField D X f (Φ ((D.basis.equivFun f,x),t))) t) ∧
          ∀ fs : List (formalSpan a s p), fs.length ≤ L →
            (∀ f ∈ fs, ‖D.basis.equivFun f‖ ≤ T) →
            ∀ x ∈ K, ∀ t : ℝ, |t| < η →
              ContDiffAt ℝ Q (fun w : ℝ × (Fin N → ℝ) =>
                runRetainedLiePointList D Φ fs w.1 w.2) (t,x) ∧
              ContDiffAt ℝ Q (fun v => runRetainedLiePointList D Φ fs v x) t ∧
              ∀ j, 1 ≤ j → j ≤ Q →
              ‖iteratedFDeriv ℝ j (fun v => runRetainedLiePointList D Φ fs v x) t‖ ≤ M := by
  obtain ⟨σ,C,hσ,hC,hflow⟩ := exists_uniform_centre_timeOne_flow_bounds
    (N := N) D hr hB hQR hQ
  obtain ⟨A,hA,hAjets⟩ := exists_numerical_dilation_jet_bound D T Q
  obtain ⟨η,hη,hηone,hsmall⟩ := exists_numerical_list_radius hσ
    (show 0 < r/4 by positivity) hC.le hT L
  let J : ℝ := max 1 ((Q.factorial : ℝ)*C*A^Q)
  have hJ : 1 ≤ J := le_max_left _ _
  let M : ℝ := (Q.factorial : ℝ)*chronologicalJetBudget Q J L
  have hM : 0 < M := mul_pos (by exact_mod_cast Nat.factorial_pos Q)
    (lt_of_lt_of_le zero_lt_one (chronologicalJetBudget_one_le Q J L))
  refine ⟨η,M,σ,hη,hM,hσ,?_⟩
  intro K X hX hXjet
  obtain ⟨Φ,hΦ,hODE,hjets⟩ := hflow K X hX hXjet
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) (finiteLieTimeOneMap Φ)
      (ball 0 σ ×ˢ (centreBuffer K (r/2) : Set (Fin N → ℝ))) := by
    apply hΦ.comp (contDiffOn_id.prodMk contDiffOn_const)
    intro z hz
    exact ⟨hz,by norm_num⟩
  refine ⟨Φ,hΦ,hODE,?_⟩
  intro fs hlen hcoeff x hx t ht
  have htone : |t| ≤ 1 := (ht.trans_le hηone).le
  have hball : ball x (r/4) ⊆ (centreBuffer K (r/2) : Set (Fin N → ℝ)) := by
    intro z hz
    exact mem_centreBuffer_iff.mpr ⟨x,hx,ball_subset_ball (by linarith) hz⟩
  have hbudget : ‖x-x‖ + fs.length*(C*|t| *T) < r/4 := by
    rw [sub_self,norm_zero,zero_add]
    have he : (fs.length : ℝ)*(C*|t| *T) ≤ (L : ℝ)*(C*|t| *T) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (by positivity)
    exact he.trans_lt (by nlinarith [(hsmall t ht).2])
  have hb := retainedLie_chronologicalJetBounds D Φ
    (centreBuffer K (r/2)).isOpen hC.le hA hT htone (hsmall t ht).1 hH
    (fun q hq j hj hjQ => (hjets q hq).1 j hj hjQ)
    (fun q hq => (hjets q hq).2) fs hcoeff
    (fun f hf j hj hjQ => hAjets f (hcoeff f hf) t htone j hj hjQ) x x hball hbudget
  refine ⟨retainedLiePointList_contDiffAt_of_bounds D Φ fs (t,x) hb,
    retainedLiePointList_parameter_contDiffAt_of_bounds D Φ fs t x hb,?_⟩
  intro j hj hjQ
  have he := norm_retainedLiePointList_parameter_jet_le D Φ fs t x hJ hb j hj hjQ
  exact he.trans (mul_le_mul_of_nonneg_left (chronologicalJetBudget_monotone Q hJ hlen)
    (by positivity))
end RothschildStein.G3
