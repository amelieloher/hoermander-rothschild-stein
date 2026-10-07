-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ShortFlowRescaling
public import RothschildStein.G1.PositiveCompositionJets
public import RothschildStein.G4.AffineJetBounds
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.G3

theorem norm_shortFlow_endpoint_linear_reparametrized_jet_le
    {E G F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {τ ε t D : ℝ}
    (hε : 0 < ε) (ht : |t| < ε) (htτ : t ∈ Ioo (-τ) τ) (hD : 1 ≤ D)
    (Φ : E × ℝ → F) (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (L : G →L[ℝ] E) (hL : ‖L‖ ≤ D) {x : G} (hx : L x ∈ U)
    {Q n : ℕ} (hn : 1 ≤ n) (hnQ : n ≤ Q)
    (hjet : ∀ q ∈ U, ∀ v, |v| < ε → ∀ j, 1 ≤ j → j ≤ Q →
      ‖iteratedFDeriv ℝ j (fun z : ℝ × E => Φ (z.2,z.1)) (v,q)‖ ≤
        2 * (1+ε⁻¹)^j) :
    ‖iteratedFDeriv ℝ n (fun y => Φ (L y,t)) x‖ ≤
      n.factorial * (2 * (1+ε⁻¹)^Q) * D^n := by
  let S : Set (ℝ × E) := Ioo (-τ) τ ×ˢ U
  let T : Set G := L ⁻¹' U
  let f := fun z : ℝ × E => Φ (z.2,z.1)
  let J := (ContinuousLinearMap.inr ℝ ℝ E).comp L
  let g := fun y : G => (t,(0 : E)) + J y
  have hgapply (y : G) : g y = (t, L y) := by
    simp [g, J, ContinuousLinearMap.comp_apply]
  have hJ : ‖J‖ ≤ D := (J.opNorm_le_bound (zero_le_one.trans hD) (by
    intro y
    change ‖((0 : ℝ),L y)‖ ≤ D * ‖y‖
    simpa using (L.le_opNorm y).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg y))))
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) f S :=
    hΦ.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun z hz => ⟨hz.2,hz.1⟩)
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g T := (contDiff_const.add J.contDiff).contDiffOn
  have hmap : MapsTo g T S := by
    intro y hy
    rw [hgapply]
    exact ⟨htτ,hy⟩
  have hb : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j f (g x)‖ ≤ 2*(1+ε⁻¹)^Q := by
    intro j hj hjn
    have he := hjet (L x) hx t ht j hj (hjn.trans hnQ)
    rw [hgapply]
    apply he.trans
    gcongr
    · have hi : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
      linarith
    · exact hjn.trans hnQ
  have hgj : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j g x‖ ≤ D := by
    intro j hj _
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [Nat.add_comm 1 k]
    change ‖iteratedFDeriv ℝ (k+1) (fun y => (t,(0 : E)) + J y) x‖ ≤ D
    rw [fun_iteratedFDeriv_add_apply contDiffAt_const (J.contDiff.contDiffAt),
      iteratedFDeriv_succ_const,Pi.zero_apply,zero_add]
    exact (G4.norm_positive_jet_clm_le J x k).trans hJ
  simpa [f, g, J, Function.comp_def, ContinuousLinearMap.comp_apply] using
    G1.norm_local_positive_composition_jet_le (isOpen_Ioo.prod hU)
    (hU.preimage L.continuous) hf hg hmap hx n hn (by positivity) hD hb hgj
end RothschildStein.G3
