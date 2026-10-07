-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.JointShortChartFamilyProperties
public import RothschildStein.G4.ActualWeightedChartVolume
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.L1.JointShortChartFamily

/-- The constructed family's zero-shift chart has actual
smoothness, injectivity, full Jacobians and both inner and outer ball
containments at every permitted application scale. Its map is fixed
throughout the rescaling (BB pp. 520–521). -/
theorem exists_zeroShift_geometry {q n s : ℕ} {w : Fin q → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    {z : Fin n → ℝ} {t : ℝ} (H : JointShortChartFamily (s := s) w Ω X z t)
    {a : ℝ} (ha : 0 < a) (haa₀ : a ≤ H.a₀) :
    ∃ b : ℝ, 0 < b ∧ b < a/4 ∧ 2*b ≤ 1 ∧
      ∀ x ∈ closedBall z (H.R/16), ∀ r : ℝ, 0 < r → r ≤ H.r₀ →
      ∀ B : Fin n → G4.ShortWord w s,
      G4.IsSuboptimal (G4.shortField w X) (G4.shortWeight w) B x t r →
      let F := fun u => H.Φ B ((Fin.append u
        (0 : Fin (Fintype.card (G4.ShortWord w s)) → ℝ),x),1)
      let Q := G4.weightedBox (G4.shortWeight w ∘ B) (a*r)
      ContDiffOn ℝ (⊤ : ℕ∞) F Q ∧ InjOn F Q ∧
      (∀ u ∈ Q, |G4.frameDet (G4.shortField w X) B x|/4 ≤ |(fderiv ℝ F u).det| ∧
        |(fderiv ℝ F u).det| ≤ 4*|G4.frameDet (G4.shortField w X) B x|) ∧
      ({y | G4.auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal (b*r)} ⊆ F '' Q) ∧
      (F '' Q ⊆ {y | G4.auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal (a*r)}) := by
  obtain ⟨b,hb,hba,hb1,hprops⟩ := H.slices a ha haa₀
  refine ⟨b,hb,hba,hb1,?_⟩
  intro x hx r hr hrr B hB F Q
  have hz : (0 : Fin (Fintype.card (G4.ShortWord w s)) → ℝ) ∈
      G4.weightedBox (fun j => G4.shortWeight w (G4.shortIndex w j)) (b*r) := by
    intro j
    simp only [Pi.zero_apply,abs_zero]
    exact pow_pos (mul_pos hb hr) _
  obtain ⟨hAB,_htraj,_hzero,hi,hj,hinner,_houter,_houterAux,hzo,_hopen,_hinv⟩ :=
    hprops x hx r hr hrr B hB 0 hz
  simp only [G4.coordinateDerivativeMatrix_det] at hj
  refine ⟨hAB.1,hi,hj,hinner,?_⟩
  intro y hy
  exact (G4.auxiliaryDistance_le_constantShortDistance (s := s) Ω w X x y).trans_lt
    (hzo rfl hy)

end RothschildStein.L1.JointShortChartFamily
