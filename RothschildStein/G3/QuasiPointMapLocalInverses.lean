-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ActualQuasiExponentialPoints
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.G3

theorem quasiPointMaps_smooth_and_inverse_of_admissible {a N : ℕ}
    (p : Fin a → ℕ+) {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (U : Fin a → Set (Fin N → ℝ)) (hU : ∀ i, IsOpen (U i))
    (τ : Fin a → ℝ) (hτ : ∀ i, 0 < τ i)
    (Φ : Fin a → ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hΦ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Φ i) (U i ×ˢ Ioo (-τ i) (τ i)))
    (hODE : ∀ i x, x ∈ U i → Φ i (x,0) = x ∧ ∀ v ∈ Ioo (-τ i) (τ i),
      HasDerivAt (fun w => Φ i (x,w)) (X i (Φ i (x,v))) v ∧ Φ i (x,v) ∈ Ω)
    (I : List (Fin a)) (t : ℝ) (x : Fin N → ℝ)
    (hf : G1.FlowScheduleAdmissible Φ (fun i t => t^(p i : ℕ)) U τ t (G1.commutatorSchedule I) x)
    (hg : G1.FlowScheduleAdmissible Φ (fun i t => t^(p i : ℕ)) U τ t
      (G1.inverseSchedule (G1.commutatorSchedule I)) x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × (Fin N → ℝ) => quasiExponentialPointMap p Φ I q.1 q.2) (t,x) ∧
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × (Fin N → ℝ) => inverseQuasiExponentialPointMap p Φ I q.1 q.2) (t,x) ∧
    inverseQuasiExponentialPointMap p Φ I t (quasiExponentialPointMap p Φ I t x) = x ∧
    quasiExponentialPointMap p Φ I t (inverseQuasiExponentialPointMap p Φ I t x) = x := by
  refine ⟨quasiExponentialPointMap_contDiffAt_of_admissible p U hU τ Φ hΦ I t x hf,?_,
    inverseQuasiExponentialPointMap_apply_of_ode p hΩ X hX U τ hτ Φ hODE I t x hf,?_⟩
  · exact G1.flowSchedule_contDiffAt_of_joint_contDiff U hU τ Φ hΦ
      (fun i t => t^(p i : ℕ)) t (fun i => contDiffAt_id.pow (p i : ℕ)) _ x hg
  · have he := G1.runSchedule_inverse_of_reversible _ _ _
      (G1.flowSchedule_reversible hΩ X hX U τ hτ Φ hODE (fun i t => t^(p i : ℕ)) t _ x hg)
    simpa only [G1.inverseSchedule_inverse,quasiExponentialPointMap,
      inverseQuasiExponentialPointMap,weightedPrimitiveArc] using he
end RothschildStein.G3
