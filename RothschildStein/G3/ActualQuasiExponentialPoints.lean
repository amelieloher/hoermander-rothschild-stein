-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G1.FlowSchedules
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.G3

/-- Actual weighted primitive arcs, in application order. -/
def weightedPrimitiveArc {a N : ℕ} (p : Fin a → ℕ+)
    (Φ : Fin a → ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (b : Fin a × Bool) (q : ℝ × (Fin N → ℝ)) : Fin N → ℝ :=
  G1.flowArc Φ (fun i t => t ^ (p i : ℕ)) b q

/-- The point map Q_I is the actual finite signed primitive-flow schedule,
with the corrected positive nested-bracket convention (BB Lemma 9.26). -/
def quasiExponentialPointMap {a N : ℕ} (p : Fin a → ℕ+)
    (Φ : Fin a → ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (I : List (Fin a)) (t : ℝ) (x : Fin N → ℝ) : Fin N → ℝ :=
  G1.runSchedule (fun b y => weightedPrimitiveArc p Φ b (t,y))
    (G1.commutatorSchedule I) x

/-- The actual inverse schedule reverses the primitive arcs and their signs. -/
def inverseQuasiExponentialPointMap {a N : ℕ} (p : Fin a → ℕ+)
    (Φ : Fin a → ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (I : List (Fin a)) (t : ℝ) (x : Fin N → ℝ) : Fin N → ℝ :=
  G1.runSchedule (fun b y => weightedPrimitiveArc p Φ b (t,y))
    (G1.inverseSchedule (G1.commutatorSchedule I)) x

/-- Genuine local flow inverses cancel along every admissible weighted schedule. -/
theorem inverseQuasiExponentialPointMap_apply_of_ode {a N : ℕ}
    (p : Fin a → ℕ+) {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (U : Fin a → Set (Fin N → ℝ)) (τ : Fin a → ℝ) (hτ : ∀ i, 0 < τ i)
    (Φ : Fin a → ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hΦ : ∀ i x, x ∈ U i → Φ i (x,0) = x ∧ ∀ v ∈ Ioo (-τ i) (τ i),
      HasDerivAt (fun w => Φ i (x,w)) (X i (Φ i (x,v))) v ∧ Φ i (x,v) ∈ Ω)
    (I : List (Fin a)) (t : ℝ) (x : Fin N → ℝ)
    (h : G1.FlowScheduleAdmissible Φ (fun i t => t ^ (p i : ℕ)) U τ t
      (G1.commutatorSchedule I) x) :
    inverseQuasiExponentialPointMap p Φ I t (quasiExponentialPointMap p Φ I t x) = x :=
  G1.runSchedule_inverse_of_reversible _ _ _
    (G1.flowSchedule_reversible hΩ X hX U τ hτ Φ hΦ _ t _ x h)

/-- Smoothness is in the actual scalar dilation and the initial point,
including when a drift letter has weight two. -/
theorem quasiExponentialPointMap_contDiffAt_of_admissible {a N : ℕ}
    (p : Fin a → ℕ+) (U : Fin a → Set (Fin N → ℝ)) (hU : ∀ i, IsOpen (U i))
    (τ : Fin a → ℝ) (Φ : Fin a → ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hΦ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Φ i) (U i ×ˢ Ioo (-τ i) (τ i)))
    (I : List (Fin a)) (t : ℝ) (x : Fin N → ℝ)
    (h : G1.FlowScheduleAdmissible Φ (fun i t => t ^ (p i : ℕ)) U τ t
      (G1.commutatorSchedule I) x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × (Fin N → ℝ) =>
      quasiExponentialPointMap p Φ I q.1 q.2) (t,x) :=
  G1.flowSchedule_contDiffAt_of_joint_contDiff U hU τ Φ hΦ
    (fun i t => t ^ (p i : ℕ)) t (fun i => contDiffAt_id.pow (p i : ℕ)) _ x h
end RothschildStein.G3
