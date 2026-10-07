-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.GeneratorCosts
public import RothschildStein.G1.WeightedTriangle
public import RothschildStein.G1.FlowSchedules

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.G1

/-- A genuine local primitive flow arc has the prescribed
weighted control cost. Smoothness and range are checked along the
normalized actual arc (BB Remark 1.40, p. 22). -/
theorem controlDistance_local_flow_arc {m n : ℕ}
    {Ω U : Set (Fin n → ℝ)} (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (i : Fin m) {τ δ t : ℝ} (hδ : 0 < δ)
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    {x : Fin n → ℝ} (hx : x ∈ U)
    (hzero : Φ (x, 0) = x)
    (hODE : ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun z => Φ (x, z)) (X i (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    (ht : |t| < τ) (hcost : |t| ≤ δ ^ (w i : ℕ)) :
    controlDistance Ω w X x (Φ (x, t)) ≤ ENNReal.ofReal δ := by
  let γ := fun θ : ℝ => Φ (x, θ * t)
  have htime : ∀ θ ∈ Icc (0 : ℝ) 1, θ * t ∈ Ioo (-τ) τ := by
    intro θ hθ
    have hh : |θ * t| ≤ |t| := by
      rw [abs_mul, abs_of_nonneg hθ.1]
      exact mul_le_of_le_one_left (abs_nonneg _) hθ.2
    exact abs_lt.mp (hh.trans_lt ht)
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun θ : ℝ => (x, θ * t)) :=
    contDiff_const.prodMk (contDiff_id.mul contDiff_const)
  have hs : ContDiffOn ℝ 1 γ (Icc 0 1) :=
    (hΦ.of_le (by simp)).comp (hc.of_le (by simp)).contDiffOn (fun θ hθ => ⟨hx, htime θ hθ⟩)
  have hd : ∀ θ ∈ Icc (0 : ℝ) 1, HasDerivAt γ (t • X i (γ θ)) θ := by
    intro θ hθ
    have hlin : HasDerivAt (fun θ : ℝ => θ * t) t θ := by
      simpa using (hasDerivAt_id θ).mul_const t
    simpa only [γ, Function.comp_def] using ((hODE _ (htime θ hθ)).1.scomp θ hlin)
  have hγ := isControlledCurve_generatorArc hs (fun θ hθ => (hODE _ (htime θ hθ)).2)
    i hδ hd hcost
  have hh := controlDistance_le_of_curve hγ
  simpa only [γ, zero_mul, one_mul, hzero] using hh

end RothschildStein.G1
