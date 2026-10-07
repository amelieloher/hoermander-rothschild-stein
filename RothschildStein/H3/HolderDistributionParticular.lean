-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SmoothRelCompactHolder
public import RothschildStein.H3.FrozenHolderAddition
public import RothschildStein.H1.StandingDistributionRegularity
public import RothschildStein.S.WeakDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- An actual Holder particular solution and equal forcing
produce a fixed Holder representative of an arbitrary distribution.
Hypoellipticity is applied to the homogeneous remainder distribution. -/
theorem distribution_representative_of_particular_solution_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (Ω U : Opens (Fin N → ℝ))
    (hK : IsCompact (closure (U : Set (Fin N → ℝ))))
    (hKΩ : closure (U : Set (Fin N → ℝ)) ⊆ Ω)
    {a : ℝ≥0} (ha : 0 < a) (ha1 : a ≤ 1)
    (T : Distribution Ω ℝ (⊤ : ℕ∞)) (v : (Fin N → ℝ) → ℝ)
    (hv : LocallyIntegrableOn v (Ω : Set (Fin N → ℝ)) volume)
    (hvs : memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields) U 2 a v)
    (heq : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞),
      T (sumSquaresWithDriftTransposeTest Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) ψ) =
      Distribution.ofFun Ω v volume (⊤ : ℕ∞)
        (sumSquaresWithDriftTransposeTest Ω H.fields
          (fun i => (H.fields_smooth G i).contDiffOn) ψ)) :
    ∃ w : (Fin N → ℝ) → ℝ,
      memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields) U 2 a w ∧
      ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T ψ = ∫ x, ψ x * w x := by
  have hd : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞),
      (T - Distribution.ofFun Ω v volume (⊤ : ℕ∞))
        (sumSquaresWithDriftTransposeTest Ω H.fields
          (fun i => (H.fields_smooth G i).contDiffOn) ψ) =
      Distribution.ofFun Ω (fun _ => 0) volume (⊤ : ℕ∞) ψ := by
    intro ψ
    simp only [sub_apply, heq ψ, sub_self]
    simp only [show (fun _ : Fin N → ℝ => (0 : ℝ)) = 0 from rfl,
      Distribution.ofFun_zero, zero_apply]
  obtain ⟨f, hf, hrep⟩ := H.exists_smooth_distributionRepresentative G Ω
    (T - Distribution.ofFun Ω v volume (⊤ : ℕ∞)) (fun _ => 0) (by fun_prop) hd
  have hfs := memHolderX_of_contDiffOn_relCompact_of_controlNorm G H C Ω U hK hKΩ 2 ha ha1 f hf
  refine ⟨fun x => v x + f x, memHolderX_add_of_controlNorm G H C U 2 ha hvs hfs, ?_⟩
  intro ψ
  have hh := hrep ψ
  rw [sub_apply, Distribution.ofFun_apply hv] at hh
  simp only [smul_eq_mul] at hh
  have hvψ : Integrable (fun x => ψ x * v x) volume := by
    simpa only [mul_comm] using RothschildStein.S.integrable_mul_test Ω hv ψ
  have hfψ : Integrable (fun x => ψ x * f x) volume := by
    simpa only [mul_comm] using RothschildStein.S.integrable_mul_test Ω
      (hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet) ψ
  simp_rw [mul_add]
  rw [integral_add hvψ hfψ]
  linarith

end RothschildStein.H3
