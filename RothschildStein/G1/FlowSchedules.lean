-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ScheduleSmoothness
public import RothschildStein.G1.FlowComposition

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G1

variable {ι P : Type*} {N : ℕ} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Signed generator arcs of a local flow family, with independent
parameter functions attached to labels (BB eq. (1.32), pp. 29–30). -/
def flowArc (Φ : ι → ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (T : ι → P → ℝ) (a : ι × Bool) (q : P × (Fin N → ℝ)) : Fin N → ℝ :=
  Φ a.1 (q.2, if a.2 then T a.1 q.1 else -T a.1 q.1)

/-- Every local arc must begin and end in its own initial-point
domain and have an allowed time. This records the finite trajectory rather
than a global invariant domain (BB Lemma 1.52, pp. 30–31). -/
def FlowScheduleAdmissible (Φ : ι → ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (T : ι → P → ℝ) (U : ι → Set (Fin N → ℝ)) (τ : ι → ℝ) (p : P) :
    List (ι × Bool) → (Fin N → ℝ) → Prop
  | [], _ => True
  | a :: S, x => x ∈ U a.1 ∧ T a.1 p ∈ Ioo (-τ a.1) (τ a.1) ∧
      flowArc Φ T a (p, x) ∈ U a.1 ∧
      FlowScheduleAdmissible Φ T U τ p S (flowArc Φ T a (p, x))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- Actual local flow arcs cancel in reverse order along every
admissible schedule (BB Lemma 1.52, pp. 30–31). -/
theorem flowSchedule_reversible
    {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    (Z : ι → (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω)
    (U : ι → Set (Fin N → ℝ)) (τ : ι → ℝ) (hτ : ∀ i, 0 < τ i)
    (Φ : ι → ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hΦ : ∀ i x, x ∈ U i → Φ i (x, 0) = x ∧ ∀ v ∈ Ioo (-τ i) (τ i),
      HasDerivAt (fun w => Φ i (x, w)) (Z i (Φ i (x, v))) v ∧ Φ i (x, v) ∈ Ω)
    (T : ι → P → ℝ) (p : P) (S : List (ι × Bool)) (x : Fin N → ℝ)
    (h : FlowScheduleAdmissible Φ T U τ p S x) :
    ScheduleReversible (fun a y => flowArc Φ T a (p, y)) S x := by
  induction S generalizing x with
  | nil => trivial
  | cons a S ih =>
    obtain ⟨hx, ht, hend, htail⟩ := h
    refine ⟨?_, ih _ htail⟩
    have hneg : -T a.1 p ∈ Ioo (-τ a.1) (τ a.1) :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    cases ha : a.2 <;> simp only [flowArc, ha, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true] at hend ⊢
    · simpa only [neg_neg] using localFlow_inverse hΩ (hZ a.1) (hτ a.1)
        (Φ a.1) (hΦ a.1) hx hneg hend
    · exact localFlow_inverse hΩ (hZ a.1) (hτ a.1) (Φ a.1) (hΦ a.1) hx ht hend

/-- Joint smoothness of each actual local flow supplies smoothness
of an admissible schedule in parameters and initial points. Conditional
only on joint smoothness of the local flow (BB Lemma 1.52, pp. 30–31). -/
theorem flowSchedule_contDiffAt_of_joint_contDiff
    (U : ι → Set (Fin N → ℝ)) (hU : ∀ i, IsOpen (U i)) (τ : ι → ℝ)
    (Φ : ι → ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hjoint : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Φ i) (U i ×ˢ Ioo (-τ i) (τ i)))
    (T : ι → P → ℝ) (p : P)
    (hT : ∀ i, ContDiffAt ℝ (⊤ : ℕ∞) (T i) p)
    (S : List (ι × Bool)) (x : Fin N → ℝ)
    (h : FlowScheduleAdmissible Φ T U τ p S x) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : P × (Fin N → ℝ) =>
        runSchedule (fun a y => flowArc Φ T a (q.1, y)) S q.2) (p, x) := by
  apply runSchedule_contDiffAt_of_arc_smoothness
  induction S generalizing x with
  | nil => trivial
  | cons a S ih =>
    obtain ⟨hx, ht, _, htail⟩ := h
    refine ⟨?_, ih _ htail⟩
    have hneg : -T a.1 p ∈ Ioo (-τ a.1) (τ a.1) :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hp : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : P × (Fin N → ℝ) => T a.1 q.1)
        (p, x) := (hT a.1).comp (p, x) contDiffAt_fst
    change ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : P × (Fin N → ℝ) => Φ a.1 (q.2, if a.2 then T a.1 q.1 else -T a.1 q.1)) (p, x)
    cases ha : a.2
    · simpa only [ha, Bool.false_eq_true, ite_false, Function.comp_def] using ((hjoint a.1).contDiffAt
        ((hU a.1).prod isOpen_Ioo |>.mem_nhds ⟨hx, hneg⟩)).comp (p, x)
        (contDiffAt_snd.prodMk hp.neg)
    · simpa only [ha, ite_true, Function.comp_def] using ((hjoint a.1).contDiffAt
        ((hU a.1).prod isOpen_Ioo |>.mem_nhds ⟨hx, ht⟩)).comp (p, x)
        (contDiffAt_snd.prodMk hp)

end RothschildStein.G1
