-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.FlowUniqueness

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G1

/-- Composition of actual local flows on the overlap of their time
intervals. Both initial points must belong to the flow domain (BB Prop 1.2, p. 3). -/
theorem localFlow_composition {N : ℕ} {Ω U : Set (Fin N → ℝ)}
    (hΩ : IsOpen Ω) {Z : (Fin N → ℝ) → (Fin N → ℝ)}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) {τ : ℝ} (hτ : 0 < τ)
    (Φ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U) {s t : ℝ}
    (hs : s ∈ Ioo (-τ) τ) (ht : t ∈ Ioo (-τ) τ)
    (hst : t + s ∈ Ioo (-τ) τ) (hsx : Φ (x, s) ∈ U) :
    Φ (Φ (x, s), t) = Φ (x, t + s) := by
  let a := max (-τ) (-τ - s)
  let b := min τ (τ - s)
  have hzero : (0 : ℝ) ∈ Ioo a b := by
    dsimp [a, b]
    constructor
    · exact max_lt (by linarith) (by linarith [hs.1])
    · exact lt_min hτ (by linarith [hs.2])
  have htime : t ∈ Ioo a b := by
    dsimp [a, b]
    exact ⟨max_lt ht.1 (by linarith [hst.1]), lt_min ht.2 (by linarith [hst.2])⟩
  have hsub : ∀ v ∈ Ioo a b, v ∈ Ioo (-τ) τ ∧ v + s ∈ Ioo (-τ) τ := by
    intro v hv
    have ha := (max_lt_iff.mp hv.1)
    have hb := (lt_min_iff.mp hv.2)
    exact ⟨⟨ha.1, hb.1⟩, ⟨by linarith [ha.2], by linarith [hb.2]⟩⟩
  have heq := integralCurve_eqOn hΩ hZ hzero
    (α := fun v => Φ (Φ (x, s), v)) (β := fun v => Φ (x, v + s))
    (fun v hv => (hΦ _ hsx).2 v (hsub v hv).1)
    (fun v hv => ⟨by
      simpa only [Function.comp_def, one_smul] using (((hΦ x hx).2 (v + s) (hsub v hv).2).1.scomp v
        (show HasDerivAt (fun w : ℝ => w + s) 1 v from (hasDerivAt_id v).add_const s)), ((hΦ x hx).2 (v + s) (hsub v hv).2).2⟩)
    (by simp only [(hΦ _ hsx).1, zero_add])
  exact heq htime

/-- The opposite time map is an inverse whenever the trajectory's
endpoint remains in the initial-point domain (BB Prop 1.2, p. 3). -/
theorem localFlow_inverse {N : ℕ} {Ω U : Set (Fin N → ℝ)}
    (hΩ : IsOpen Ω) {Z : (Fin N → ℝ) → (Fin N → ℝ)}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) {τ : ℝ} (hτ : 0 < τ)
    (Φ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (htx : Φ (x, t) ∈ U) : Φ (Φ (x, t), -t) = x := by
  have hneg : -t ∈ Ioo (-τ) τ := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hsum : -t + t ∈ Ioo (-τ) τ := by constructor <;> linarith
  simpa only [neg_add_cancel, (hΦ x hx).1] using
    localFlow_composition hΩ hZ hτ Φ hΦ hx ht hneg hsum htx

end RothschildStein.G1
