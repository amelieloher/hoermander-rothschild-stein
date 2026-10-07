-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ChartAnalyticData
public import RothschildStein.G4.UniformSelectedChartAnalyticBounds
public import RothschildStein.G4.SelectedAuxiliaryBox
public import RothschildStein.G4.SelectedAuxiliaryTrajectory
public import RothschildStein.G4.ZeroCoefficientFlow

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped BigOperators Topology

namespace RothschildStein.G4

/-- Primitive quantitative data construct analytic bounds and
actual trajectories and factor-four Jacobian bounds for the same selected chart. The full coefficient
domain is fixed before all subsequent box shrinkages (BB pp. 445–449). -/
theorem exists_uniform_selected_chart_data_with_jacobian (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q + 1 = n * s + s) (hq : q + 1 ≤ h)
    (w : Fin (k + 1) → ℕ+) (M Δ R : ℝ)
    (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR : 0 < R) :
    let m := n + Fintype.card (ShortWord w s)
    let δ := R / (64 * (1 + (m : ℝ) * wordJetBase n 0 s M ^ s))
    ∃ D : ℝ, 0 < D ∧ ∃ κ : ℝ, 0 < κ ∧ (n : ℝ) * κ ≤ 1 / 4 ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 →
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ e ≤ t ∧ e < δ ∧
      ∀ (Ω : Set (Fin n → ℝ)), IsOpen Ω →
      ∀ (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) → bracketStepOn Ω w X s →
      ∀ x₀ : Fin n → ℝ, closedBall x₀ R ⊆ Ω →
      (∀ j, HasJetBound Ω (closedBall x₀ R) (X j)
        (max (2 * (n * s) + 2 * s) (max ((q + 1) * s) (h + 1 + s))) M) →
      (∀ y ∈ closedBall x₀ R, ∃ B : Fin n → ShortWord w s,
        Δ ≤ |frameDet (shortField w X) B y|) →
      ∀ B : Fin n → ShortWord w s,
      let wf : Fin (Fintype.card (ShortWord w s)) → ℕ+ :=
        fun j => shortWeight w (shortIndex (s := s) w j)
      let Zf : Fin (Fintype.card (ShortWord w s)) → (Fin n → ℝ) → (Fin n → ℝ) :=
        fun j => shortField w X (shortIndex (s := s) w j)
      let Bf := (Fintype.equivFin (ShortWord w s)) ∘ B
      ∃ Φ : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ),
        ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 δ ×ˢ ball x₀ (R / 4)) ×ˢ Ioo (-2) 2) ∧
        (∀ p ∈ ball 0 δ, ∀ x ∈ ball x₀ (R / 4), Φ ((p, x), 0) = x ∧
          ∀ τ ∈ Ioo (-2 : ℝ) 2, Φ ((p, x), τ) ∈ ball x₀ R ∧
            HasDerivAt (fun v => Φ ((p, x), v))
              (∑ j, p j • shortField w X (selectedAuxiliaryIndex w B j) (Φ ((p, x), τ))) τ) ∧
        ∀ x ∈ ball x₀ (R / 8), ∀ r : ℝ, 0 < r → r ≤ 1 →
          IsSuboptimal (shortField w X) (shortWeight w) B x t r →
        ∀ a b : ℝ, 0 < a → a ≤ e → 0 < b → b ≤ e →
        ∀ v : Fin (Fintype.card (ShortWord w s)) → ℝ,
          v ∈ weightedBox wf (b * r) →
        let F := fun u => Φ ((Fin.append u v, x), 1)
        let Γ := fun u τ => Φ ((Fin.append u v, x), τ)
        ChartAnalyticBounds Ω wf Zf Bf F (weightedBox (shortWeight w ∘ B) (a * r))
          r κ (2 * D * t⁻¹ ^ n) ∧
        ChartTrajectories Ω Zf Bf F (weightedBox (shortWeight w ∘ B) (a * r)) x v Γ ∧
        (v = 0 → F 0 = x) ∧
        ∀ u ∈ weightedBox (shortWeight w ∘ B) (a * r),
          |frameDet (shortField w X) B x| / 4 ≤
            |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ∧
          |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ≤
            4 * |frameDet (shortField w X) B x| := by
  intro m δ
  obtain ⟨D, hD, κ, hκ, hsmall, hprovider⟩ :=
    exists_uniform_selected_chart_analytic_bounds k n s h q hn hs horder hq w M Δ R hM hΔ hR
  refine ⟨D, hD, κ, hκ, hsmall, ?_⟩
  intro t ht ht1
  obtain ⟨e, he, he1, het, heδ, hcharts⟩ := hprovider t ht ht1
  refine ⟨e, he, he1, het, heδ, ?_⟩
  intro Ω hΩ X hX hstep x₀ hRΩ hjets hmax B wf Zf Bf
  obtain ⟨Φ, hsmooth, hflow, hgeometry⟩ := hcharts Ω hΩ X hX hstep x₀ hRΩ hjets hmax B
  refine ⟨Φ, hsmooth, hflow, ?_⟩
  intro x hx r hr hr1 hB a b ha hae hb hbe v hv F Γ
  have hweights : wf ∘ Bf = shortWeight w ∘ B := by
    funext i
    simp [wf, Bf, shortIndex]
  have hxin : x ∈ ball x₀ (R / 4) := ball_subset_ball (by linarith) hx
  have hxK : x ∈ closedBall x₀ R := ball_subset_closedBall
    (ball_subset_ball (by linarith) hx)
  have hspan : ∃ C : Fin n → ShortWord w s, frameDet (shortField w X) C x ≠ 0 := by
    obtain ⟨C, hC⟩ := hmax x hxK
    exact ⟨C, abs_pos.mp (hΔ.trans_le hC)⟩
  have hBx := suboptimal_frame_ne_zero ht hr hspan hB
  have hcoeff : ∀ u ∈ weightedBox (shortWeight w ∘ B) (a * r), ∀ j,
      |Fin.append u v j| ≤ (e * r) ^ (shortWeight w (selectedAuxiliaryIndex w B j) : ℕ) :=
    fun u hu => selectedAuxiliary_coefficients_le w B ha.le hb.le hr.le hae hbe u v hu hv
  have hp : ∀ u ∈ weightedBox (shortWeight w ∘ B) (a * r), Fin.append u v ∈ ball 0 δ := by
    intro u hu
    have hnorm := weighted_coefficients_norm_le
      (fun j => shortWeight w (selectedAuxiliaryIndex w B j)) (mul_nonneg he.le hr.le)
      ((mul_le_mul_of_nonneg_right he1 hr.le).trans (by simpa using hr1)) (hcoeff u hu)
    rw [mem_ball, dist_zero_right]
    exact (hnorm.trans (mul_le_of_le_one_right he.le hr1)).trans_lt heδ
  have hgeom := fun u hu => hgeometry x hx r hr hr1 hB u v (hcoeff u hu)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨fun u hu => (hgeom u hu).1.contDiffWithinAt, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      exact hRΩ (ball_subset_closedBall ((hflow _ (hp u hu) x hxin).2 1 (by constructor <;> norm_num)).1)
    · intro u hu
      have hj := (hgeom u hu).2.2.2.2.1.1
      exact abs_pos.mp ((show 0 < |frameDet (shortField w X) B x| / 4 by positivity).trans_le hj)
    · intro u hu
      simpa only [Zf, Bf, shortIndex, frameDet_reindex] using (hgeom u hu).2.1
    · intro u hu j i
      simpa [Zf, Bf, wf, shortIndex, frameCoefficient_reindex] using (hgeom u hu).2.2.2.1 j i
    · intro u hu J j
      simpa [Zf, Bf, wf, shortIndex, frameCoefficient_reindex] using
        (hgeom u hu).2.2.1 (shortIndex w J) j
  · intro u hu
    have hsol : Φ ((Fin.append u v, x), 0) = x ∧
        ∀ τ ∈ Ioo (-2 : ℝ) 2, Φ ((Fin.append u v, x), τ) ∈ Ω ∧
          HasDerivAt (Γ u)
            (∑ j, Fin.append u v j • shortField w X (selectedAuxiliaryIndex w B j) (Γ u τ)) τ :=
      ⟨(hflow _ (hp u hu) x hxin).1, fun τ hτ =>
        ⟨hRΩ (ball_subset_closedBall ((hflow _ (hp u hu) x hxin).2 τ hτ).1),
          ((hflow _ (hp u hu) x hxin).2 τ hτ).2⟩⟩
    exact selectedAuxiliary_timeOneTrajectory w B (shortField w X) Φ hsmooth u v
      (hp u hu) hxin hsol
  · intro hv0
    subst v
    have happ : Fin.append (0 : Fin n → ℝ)
        (0 : Fin (Fintype.card (ShortWord w s)) → ℝ) = 0 := by
      ext j
      exact Fin.addCases (fun i => by simp) (fun i => by simp) j
    have hzero : (0 : Fin m → ℝ) ∈ ball 0 δ := by
      rw [mem_ball, dist_self]
      exact he.trans heδ
    have hsol : ∀ p ∈ ball 0 δ ×ˢ ball x₀ (R / 4), Φ (p, 0) = p.2 ∧
        ∀ τ ∈ Ioo (-2 : ℝ) 2, HasDerivAt (fun t => Φ (p, t))
          (∑ j, p.1 j • shortField w X (selectedAuxiliaryIndex w B j) (Φ (p, τ))) τ ∧
          Φ (p, τ) ∈ ball x₀ R := by
      intro p hp'
      exact ⟨(hflow p.1 hp'.1 p.2 hp'.2).1, fun τ hτ =>
        ⟨((hflow p.1 hp'.1 p.2 hp'.2).2 τ hτ).2,
          ((hflow p.1 hp'.1 p.2 hp'.2).2 τ hτ).1⟩⟩
    simpa only [F, happ] using linear_field_flow_zero_coefficients
      (fun j => shortField w X (selectedAuxiliaryIndex w B j)) (τ := 2) (by norm_num)
      Φ hsol hzero hxin (t := 1) (by constructor <;> norm_num)

  · intro u hu
    exact (hgeom u hu).2.2.2.2.1

end RothschildStein.G4
