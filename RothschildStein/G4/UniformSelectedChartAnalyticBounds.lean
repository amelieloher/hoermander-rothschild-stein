-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.UniformSelectedTimeOnePersistence
public import RothschildStein.G4.PersistentCoefficientBounds
public import RothschildStein.G4.ActualFrameJacobianBounds
public import RothschildStein.G4.ActualLocalInverseFrameDerivative

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped BigOperators Topology

namespace RothschildStein.G4

/-- All analytic bounds for the same constructed chart, with numerical constants chosen before fields and frames. -/
theorem exists_uniform_selected_chart_analytic_bounds (k n s h q : ℕ)
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
      ∃ Φ : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ),
        ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 δ ×ˢ ball x₀ (R / 4)) ×ˢ Ioo (-2) 2) ∧
        (∀ a ∈ ball 0 δ, ∀ x ∈ ball x₀ (R / 4), Φ ((a, x), 0) = x ∧
          ∀ τ ∈ Ioo (-2 : ℝ) 2, Φ ((a, x), τ) ∈ ball x₀ R ∧
            HasDerivAt (fun v => Φ ((a, x), v))
              (∑ j, a j • shortField w X (selectedAuxiliaryIndex w B j) (Φ ((a, x), τ))) τ) ∧
        ∀ x ∈ ball x₀ (R / 8), ∀ r : ℝ, 0 < r → r ≤ 1 →
          IsSuboptimal (shortField w X) (shortWeight w) B x t r →
        ∀ (u : Fin n → ℝ) (v : Fin (Fintype.card (ShortWord w s)) → ℝ),
          (∀ j, |Fin.append u v j| ≤
            (e * r) ^ (shortWeight w (selectedAuxiliaryIndex w B j) : ℕ)) →
        let F := fun a => Φ ((Fin.append a v, x), 1)
        let y := F u
        ContDiffAt ℝ (⊤ : ℕ∞) F u ∧
        frameDet (shortField w X) B y ≠ 0 ∧
        (∀ (J : ShortWord w s) (i : Fin n),
          |frameCoefficient (shortField w X) B (shortField w X J) i y| ≤
            (2 * D * t⁻¹ ^ n) *
              r ^ (((shortWeight w (B i) : ℕ) : ℤ) - ((shortWeight w J : ℕ) : ℤ))) ∧
        (∀ (i j : Fin n),
          |frameCoefficient (shortField w X) B (fun z =>
            fderiv ℝ F u (Pi.single j 1) - shortField w X (B j) z) i y| ≤
            κ * r ^ (((shortWeight w (B i) : ℕ) : ℤ) -
              ((shortWeight w (B j) : ℕ) : ℤ))) ∧
        (|frameDet (shortField w X) B x| / 4 ≤
          |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ∧
          |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ≤
            4 * |frameDet (shortField w X) B x|) ∧
        ∀ Ψ : (Fin n → ℝ) → (Fin n → ℝ), Ψ y = u → DifferentiableAt ℝ Ψ y →
          (fun z => F (Ψ z)) =ᶠ[𝓝 y] (fun z => z) →
          ∀ (ℓ i : Fin n), |(fderiv ℝ Ψ y (shortField w X (B ℓ) y)) i| ≤ (4 / 3 : ℝ) *
            r ^ (((shortWeight w (B i) : ℕ) : ℤ) - ((shortWeight w (B ℓ) : ℕ) : ℤ)) := by
  intro m δ
  obtain ⟨κ, hκ, hκsmall, hJacobian⟩ := exists_actual_frame_jacobian_threshold n
  obtain ⟨D, hD, hprovider⟩ := exists_uniform_selected_timeOne_persistence
    k n s h q hn hs horder hq w M Δ R κ hM hΔ hR hκ
  refine ⟨D, hD, κ, hκ, hκsmall, ?_⟩
  intro t ht ht1
  obtain ⟨e, he, he1, het, heδ, hselected⟩ := hprovider t ht ht1
  refine ⟨e, he, he1, het, heδ, ?_⟩
  intro Ω hΩ X hX hstep x₀ hRΩ hjets hmax B
  obtain ⟨Φ, hsmooth, hflow, hgeometry⟩ := hselected Ω hΩ X hX hstep x₀ hRΩ hjets hmax B
  refine ⟨Φ, hsmooth, hflow, ?_⟩
  intro x hx r hr hr1 hB u v ha F y
  obtain ⟨hpersist, hother, hcoords⟩ := hgeometry x hx r hr hr1 hB u v ha
  have hxK : x ∈ closedBall x₀ R := ball_subset_closedBall
    (ball_subset_ball (by linarith) hx)
  have hw : ∀ J : ShortWord w s, (shortWeight w J : ℕ) ≤ s := fun J =>
    ((mem_shortWordFamily_iff w J.val).mp J.property).2
  have hdet0 := suboptimal_frameDet_lower_bound (shortWeight w) s hw B ht hr hr1 hΔ.le
    (hmax x hxK) hB
  have hBx : frameDet (shortField w X) B x ≠ 0 := abs_pos.mp
    ((by positivity : 0 < t * Δ * r ^ (n * s)).trans_le hdet0)
  have htri : |frameDet (shortField w X) B x| ≤
      |frameDet (shortField w X) B y - frameDet (shortField w X) B x| +
        |frameDet (shortField w X) B y| := by
    simpa only [sub_add_cancel, abs_sub_comm] using abs_add_le
      (frameDet (shortField w X) B x - frameDet (shortField w X) B y)
      (frameDet (shortField w X) B y)
  have hhalf : |frameDet (shortField w X) B x| / 2 ≤ |frameDet (shortField w X) B y| := by
    linarith
  have hBy : frameDet (shortField w X) B y ≠ 0 := abs_pos.mp
    ((half_pos (abs_pos.mpr hBx)).trans_le hhalf)
  have hnorm := weighted_coefficients_norm_le
    (fun j => shortWeight w (selectedAuxiliaryIndex w B j)) (mul_nonneg he.le hr.le)
    ((mul_le_mul_of_nonneg_right he1 hr.le).trans (by simpa using hr1)) ha
  have hz : Fin.append u v ∈ ball 0 δ := by
    rw [mem_ball, dist_zero_right]
    exact (hnorm.trans (mul_le_of_le_one_right he.le hr1)).trans_lt heδ
  have hxin : x ∈ ball x₀ (R / 4) := ball_subset_ball (by linarith) hx
  have hFsmooth := timeOne_selected_slice_contDiffAt isOpen_ball Φ hsmooth u v hz hxin
  have hF : DifferentiableAt ℝ F u := hFsmooth.differentiableAt (by simp)
  have hall : ∀ (J : ShortWord w s) (i : Fin n),
      |frameCoefficient (shortField w X) B (shortField w X J) i y| ≤
        (2 * D * t⁻¹ ^ n) *
          r ^ (((shortWeight w (B i) : ℕ) : ℤ) - ((shortWeight w J : ℕ) : ℤ)) := by
    intro J i
    have hb := frameCoefficient_le_of_determinant_bounds (shortWeight w) B hr
      (show 0 ≤ D * t⁻¹ ^ n by positivity) hBx hhalf hother J i
    convert hb using 1; ring
  refine ⟨hFsmooth, hBy, hall, (fun i j => hcoords j i), hJacobian _ (shortField w X) (shortWeight w) B (fderiv ℝ F u)
    x y r hr hBx hpersist (fun i j => hcoords j i), ?_⟩
  intro Ψ hpoint hΨ hright
  exact local_inverse_frame_derivative_bound (shortField w X) (shortWeight w) B F Ψ
    hpoint hF hΨ hright hBy hr hκ.le hκsmall (fun i j => hcoords j i)

end RothschildStein.G4
