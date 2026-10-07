-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.GeneralFlowUniqueness

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G1

/-- Smooth actual local flows of the same field glue on their
open union when they share one time interval. Uniqueness gives equality
on each overlap, so no derivative or cover-count constant is introduced
(BB Prop 1.2, pp. 3–4). -/
theorem exists_glued_smooth_local_flow {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {Z : E → E}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) {τ : ℝ} (hτ : 0 < τ)
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i)) (Ψ : ι → E × ℝ → E)
    (hΨ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Ψ i) (U i ×ˢ Ioo (-τ) τ))
    (hsol : ∀ i x, x ∈ U i → Ψ i (x, 0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      Ψ i (x, t) ∈ Ω ∧ HasDerivAt (fun v => Ψ i (x, v)) (Z (Ψ i (x, t))) t) :
    ∃ Φ : E × ℝ → E, ContDiffOn ℝ (⊤ : ℕ∞) Φ
      ((⋃ i, U i) ×ˢ Ioo (-τ) τ) ∧
      (∀ x ∈ ⋃ i, U i, Φ (x, 0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
        Φ (x, t) ∈ Ω ∧ HasDerivAt (fun v => Φ (x, v)) (Z (Φ (x, t))) t) ∧
      ∀ i x, x ∈ U i → ∀ t ∈ Ioo (-τ) τ, Φ (x, t) = Ψ i (x, t) := by
  classical
  let V : Set E := ⋃ i, U i
  have hV : IsOpen V := isOpen_iUnion hU
  have hex : ∀ x ∈ V, ∃ i, x ∈ U i := fun x hx => mem_iUnion.mp hx
  choose pick hpick using hex
  let Φ : E × ℝ → E := fun q => if hq : q.1 ∈ V then Ψ (pick q.1 hq) q else 0
  have hzero : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
  have hagree : ∀ i j x, x ∈ U i → x ∈ U j → ∀ t ∈ Ioo (-τ) τ,
      Ψ i (x, t) = Ψ j (x, t) := by
    intro i j x hi hj t ht
    exact integralCurve_eqOn_general hΩ hZ hzero
      (fun v hv => ⟨((hsol i x hi).2 v hv).2, ((hsol i x hi).2 v hv).1⟩)
      (fun v hv => ⟨((hsol j x hj).2 v hv).2, ((hsol j x hj).2 v hv).1⟩)
      ((hsol i x hi).1.trans (hsol j x hj).1.symm) ht
  have heq : ∀ i x, x ∈ U i → ∀ t ∈ Ioo (-τ) τ, Φ (x, t) = Ψ i (x, t) := by
    intro i x hx t ht
    have hxV : x ∈ V := mem_iUnion.mpr ⟨i, hx⟩
    dsimp only [Φ]
    rw [dite_eq_left hxV]
    exact hagree _ i x (hpick x hxV) hx t ht
  refine ⟨Φ, ?_, ?_, heq⟩
  · apply (hV.prod isOpen_Ioo).contDiffOn_iff.mpr
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have he : Φ =ᶠ[𝓝 (x, t)] Ψ i := by
      filter_upwards [((hU i).prod isOpen_Ioo).mem_nhds ⟨hi, ht⟩] with q hq
      exact heq i q.1 hq.1 q.2 hq.2
    exact ((hΨ i).contDiffAt (((hU i).prod isOpen_Ioo).mem_nhds ⟨hi, ht⟩)).congr_of_eventuallyEq he
  · intro x hx
    have hi := hpick x hx
    have he : (fun t => Φ (x, t)) = (fun t => Ψ (pick x hx) (x, t)) := by
      funext t
      dsimp only [Φ]
      rw [dite_eq_left hx]
    have hs := hsol (pick x hx) x hi
    refine ⟨(congrFun he 0).trans hs.1, ?_⟩
    intro t ht
    have hst := hs.2 t ht
    rw [← congrFun he t] at hst
    exact ⟨hst.1, by simpa only [he] using hst.2⟩

end RothschildStein.G1
