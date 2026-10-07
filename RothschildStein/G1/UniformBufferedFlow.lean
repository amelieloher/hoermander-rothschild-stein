-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.BufferedFlowExistence
public import RothschildStein.G1.LocalFlowGluing

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace RothschildStein.G1

/-- A uniform prescribed clearance around the starting set
provides one smooth actual flow on its open neighborhood, with numerical
time radius depending only on the clearance and field-value bound.
Local flows glue by uniqueness without a cover-count constant
(BB Prop 1.2, pp. 3–4). -/
theorem exists_uniform_buffered_smooth_flow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] [ProperSpace E]
    {Ω K : Set E} (hΩ : IsOpen Ω) {Z : E → E}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hRΩ : ∀ x ∈ K, closedBall x R ⊆ Ω) (hbound : ∀ x ∈ Ω, ‖Z x‖ ≤ B) :
    let κ : ℝ := R / (16 * (1 + B))
    ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ U ⊆ Ω ∧
      ∃ Φ : E × ℝ → E, ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-(2 * κ)) (2 * κ)) ∧
        ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ t ∈ Ioo (-(2 * κ)) (2 * κ),
          Φ (x, t) ∈ Ω ∧ HasDerivAt (fun v => Φ (x, v)) (Z (Φ (x, t))) t := by
  classical
  intro κ
  have hκ : 0 < κ := by dsimp [κ]; positivity
  let V : K → Set E := fun x => ball x.val (R / 4)
  have hlocal : ∀ x : K, ∃ Ψ : E × ℝ → E,
      ContDiffOn ℝ (⊤ : ℕ∞) Ψ (V x ×ˢ Ioo (-(2 * κ)) (2 * κ)) ∧
      ∀ y ∈ V x, Ψ (y, 0) = y ∧ ∀ t ∈ Ioo (-(2 * κ)) (2 * κ),
        Ψ (y, t) ∈ closedBall x.val R ∧ HasDerivAt (fun v => Ψ (y, v)) (Z (Ψ (y, t))) t := by
    intro x
    exact exists_smooth_buffered_local_flow hΩ hZ x.val hR hB (hRΩ x.val x.property)
      (fun y hy => hbound y (hRΩ x.val x.property hy))
  choose Ψ hΨ hsol using hlocal
  have hsol' : ∀ i y, y ∈ V i → Ψ i (y, 0) = y ∧ ∀ t ∈ Ioo (-(2 * κ)) (2 * κ),
      Ψ i (y, t) ∈ Ω ∧ HasDerivAt (fun v => Ψ i (y, v)) (Z (Ψ i (y, t))) t := by
    intro i y hy
    refine ⟨(hsol i y hy).1, ?_⟩
    intro t ht
    exact ⟨hRΩ i.val i.property ((hsol i y hy).2 t ht).1, ((hsol i y hy).2 t ht).2⟩
  obtain ⟨Φ, hΦ, hΦsol, _⟩ := exists_glued_smooth_local_flow hΩ hZ
    (by positivity : 0 < 2 * κ) V (fun _ => isOpen_ball) Ψ hΨ hsol'
  refine ⟨⋃ i, V i, isOpen_iUnion (fun _ => isOpen_ball), ?_, ?_, Φ, hΦ, hΦsol⟩
  · intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (by positivity)⟩
  · intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    apply hRΩ i.val i.property
    exact (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))) hi

end RothschildStein.G1
