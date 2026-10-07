-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.UniformPrimitiveScheduleError
public import RothschildStein.G3.WeightedCommutatorScheduleBound
public import RothschildStein.G3.AdmissibleWeightedPaths
public import RothschildStein.G3.QuasiPointMapLocalInverses
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.G3

/-- The actual weighted Q_I and inverse have uniform numerical
approximations by the retained logarithm exponentials (BB Lemma 9.26). -/
theorem exists_uniform_quasiExponentialPoint_error {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (hs : 1 ≤ s) (hp : ∀ i, (p i : ℕ) ≤ s)
    {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B) :
    ∃ η M κ σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < M ∧ 0 < κ ∧ 0 < σ ∧
      ∀ (K : Set (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ)),
        (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (centreBuffer K r)) →
        (∀ x ∈ centreBuffer K r, ∀ i j, j ≤ 3*s+2 → ‖iteratedFDeriv ℝ j (X i) x‖ ≤ B) →
        ∃ Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ),
          ContDiffOn ℝ (⊤ : ℕ∞) Φ
            ((ball 0 σ ×ˢ (centreBuffer K (r/2) : Set (Fin N → ℝ))) ×ˢ Ioo (-2) 2) ∧
          (∀ f : formalSpan a s p, D.basis.equivFun f ∈ ball 0 σ →
            ∀ x ∈ centreBuffer K (r/2), Φ ((D.basis.equivFun f,x),0) = x ∧
              ∀ t ∈ Ioo (-2 : ℝ) 2, Φ ((D.basis.equivFun f,x),t) ∈ centreBuffer K r ∧
                HasDerivAt (fun v => Φ ((D.basis.equivFun f,x),v))
                  (finiteLieField D X f (Φ ((D.basis.equivFun f,x),t))) t) ∧
          (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (primitiveFlowFromLieFamily D Φ κ i)
            ((centreBuffer K (r/2) : Set (Fin N → ℝ)) ×ˢ Ioo (-κ) κ)) ∧
          (∀ i x, x ∈ centreBuffer K (r/2) → primitiveFlowFromLieFamily D Φ κ i (x,0) = x ∧
            ∀ v ∈ Ioo (-κ) κ, primitiveFlowFromLieFamily D Φ κ i (x,v) ∈ centreBuffer K r ∧
              HasDerivAt (fun w => primitiveFlowFromLieFamily D Φ κ i (x,w))
                (X i (primitiveFlowFromLieFamily D Φ κ i (x,v))) v) ∧
          ∀ I : List (Fin a), I ≠ [] → wordWeight p I ≤ s → ∀ x ∈ K,
            ∀ t : ℝ, |t| < η →
              G1.FlowScheduleAdmissible (primitiveFlowFromLieFamily D Φ κ)
                (fun i t => t^(p i : ℕ)) (fun _ => (centreBuffer K (r/2) : Set (Fin N → ℝ)))
                (fun _ => κ) t (G1.commutatorSchedule I) x ∧
              G1.FlowScheduleAdmissible (primitiveFlowFromLieFamily D Φ κ)
                (fun i t => t^(p i : ℕ)) (fun _ => (centreBuffer K (r/2) : Set (Fin N → ℝ)))
                (fun _ => κ) t (G1.inverseSchedule (G1.commutatorSchedule I)) x ∧
              ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × (Fin N → ℝ) =>
                quasiExponentialPointMap p (primitiveFlowFromLieFamily D Φ κ) I q.1 q.2) (t,x) ∧
              ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × (Fin N → ℝ) =>
                inverseQuasiExponentialPointMap p (primitiveFlowFromLieFamily D Φ κ) I q.1 q.2) (t,x) ∧
              inverseQuasiExponentialPointMap p (primitiveFlowFromLieFamily D Φ κ) I t
                (quasiExponentialPointMap p (primitiveFlowFromLieFamily D Φ κ) I t x) = x ∧
              quasiExponentialPointMap p (primitiveFlowFromLieFamily D Φ κ) I t
                (inverseQuasiExponentialPointMap p (primitiveFlowFromLieFamily D Φ κ) I t x) = x ∧
              TimedScheduleInside (primitiveFlowFromLieFamily D Φ κ) (centreBuffer K r)
                ((G1.commutatorSchedule I).map (fun b => (b.1,signedPrimitiveTime p b t))) x ∧
              TimedScheduleInside (primitiveFlowFromLieFamily D Φ κ) (centreBuffer K r)
                ((G1.inverseSchedule (G1.commutatorSchedule I)).map
                  (fun b => (b.1,signedPrimitiveTime p b t))) x ∧
              ‖quasiExponentialPointMap p (primitiveFlowFromLieFamily D Φ κ) I t x -
                finiteLieTimeOneMap Φ (dilatedInputCoordinates D (quasiExponentialLog I) t,x)‖ ≤ M*|t| ^(s+1) ∧
              ‖inverseQuasiExponentialPointMap p (primitiveFlowFromLieFamily D Φ κ) I t x -
                finiteLieTimeOneMap Φ (dilatedInputCoordinates D (-(quasiExponentialLog I : formalSpan a s p)) t,x)‖ ≤
                  M*|t| ^(s+1) := by
  obtain ⟨η,M,κ,σ,hη,hη1,hM,hκ,hσ,hflow⟩ :=
    exists_uniform_primitiveSchedule_BCH_error (N := N) D hs hp hr hB (3*2^s)
  refine ⟨η,M,κ,σ,hη,hη1,hM,hκ,hσ,?_⟩
  intro K X hX hXjet
  obtain ⟨Φ,hΦ,hODE,hΨ,hsol,herror⟩ := hflow K X hX hXjet
  refine ⟨Φ,hΦ,hODE,hΨ,hsol,?_⟩
  intro I hI hw x hx t ht
  have hlen := weighted_commutatorSchedule_length_le p I hI hw
  have hforward := herror (G1.commutatorSchedule I) hlen x hx t ht
  have hinverse := herror (G1.inverseSchedule (G1.commutatorSchedule I))
    (by simpa only [G1.inverseSchedule_length] using hlen) x hx t ht
  have hmaps := quasiPointMaps_smooth_and_inverse_of_admissible p
    (centreBuffer K r).isOpen X hX (fun _ => (centreBuffer K (r/2) : Set (Fin N → ℝ)))
    (fun _ => (centreBuffer K (r/2)).isOpen) (fun _ => κ) (fun _ => hκ)
    (primitiveFlowFromLieFamily D Φ κ) hΨ
    (fun i y hy => ⟨(hsol i y hy).1,
      fun v hv => ⟨((hsol i y hy).2 v hv).2,((hsol i y hy).2 v hv).1⟩⟩)
    I t x hforward.1 hinverse.1
  have hrange := fun i y hy v hv => ((hsol i y hy).2 v hv).1
  have hfpath := timedScheduleInside_of_weighted_admissible p
    (primitiveFlowFromLieFamily D Φ κ) (centreBuffer K (r/2)) (centreBuffer K r)
    hrange (G1.commutatorSchedule I) x hforward.1
  have hipath := timedScheduleInside_of_weighted_admissible p
    (primitiveFlowFromLieFamily D Φ κ) (centreBuffer K (r/2)) (centreBuffer K r)
    hrange (G1.inverseSchedule (G1.commutatorSchedule I)) x hinverse.1
  refine ⟨hforward.1,hinverse.1,hmaps.1,hmaps.2.1,hmaps.2.2.1,hmaps.2.2.2,
    hfpath,hipath,?_,?_⟩
  · have hprod := commutatorSchedule_retainedLieListProduct (s := s) (p := p) I
    have he := hforward.2
    rw [hprod] at he
    exact he
  · have hprod : retainedLieListProduct
        ((G1.inverseSchedule (G1.commutatorSchedule I)).map
          (primitiveScheduleLieInput (s := s) (p := p))) =
        -(quasiExponentialLog I : formalSpan a s p) := by
      rw [primitiveScheduleLieInput_inverse,retainedLieListProduct_inverse]
      exact congrArg (fun f : formalSpan a s p => -f)
        (commutatorSchedule_retainedLieListProduct (s := s) (p := p) I)
    have he := hinverse.2
    rw [hprod] at he
    exact he
end RothschildStein.G3
