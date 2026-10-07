-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeakParticular
public import RothschildStein.H3.PatchRepresentativeEquation
public import RothschildStein.H3.WeakOperatorDistributionUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- the local Sobolev representative has an actual certified
weak operator equal almost everywhere to the original forcing. -/
theorem patch_certified_of_weak_particular_solution {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (Ω V U : Opens (Fin n → ℝ)) (hV : V ≤ Ω)
    (hK : IsCompact (closure (U : Set (Fin n → ℝ))))
    (hKV : closure (U : Set (Fin n → ℝ)) ⊆ V)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (F v : (Fin n → ℝ) → ℝ)
    (hv : memSobolevX driftWeight H.fields V 2 p v)
    (D : WeakDriftOperatorData H.fields V p v)
    (hD : D.operator =ᵐ[volume.restrict (V : Set (Fin n → ℝ))] F)
    (hT : ∀ ψ : TestFunction V ℝ (⊤ : ℕ∞),
      T (TestFunction.monoCLM ℝ
        (Distribution.adjointTest V H.fields (fun _ => 0)
          (fun i => (H.fields_smooth G i).contDiffOn) (by fun_prop) ψ)) =
        Distribution.ofFun V F volume (⊤ : ℕ∞) ψ) :
    ∃ w : (Fin n → ℝ) → ℝ, memSobolevX driftWeight H.fields U 2 p w ∧
      ∃ E : WeakDriftOperatorData H.fields U p w,
        E.operator =ᵐ[volume.restrict (U : Set (Fin n → ℝ))] F ∧
        ∀ ψ : TestFunction U ℝ (⊤ : ℕ∞),
          T (TestFunction.monoCLM ℝ ψ) = ∫ x, ψ x*w x := by
  obtain ⟨w,hw,hrep⟩ := patch_regular_of_weak_particular_solution G H Ω V U
    hV hK hKV p hp T F v hv D hD hT
  obtain ⟨E⟩ := exists_weakDriftOperatorData H.fields U p w hw
  have hU : U ≤ V := subset_closure.trans hKV
  have hF := locallyIntegrableOn_of_locallyIntegrable_restrict
    ((D.operator_memLp.ae_eq hD).locallyIntegrable hp)
  have heq := distribution_equation_of_patch_representative G H Ω V U hV hU
    T F w hF (E.first_weak 0).1 hrep hT
  exact ⟨w,hw,E,E.operator_ae_eq_of_distribution_equation hp
    (fun i => (H.fields_smooth G i).contDiffOn) F (hF.mono_set hU) heq,hrep⟩

end RothschildStein.H3
