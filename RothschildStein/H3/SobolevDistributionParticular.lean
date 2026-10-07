-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DistributionRemainder
public import RothschildStein.H1.Standing

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- equal forcing for the actual distribution and its
particular solution yields a local Sobolev representative. The standing
group hypotheses discharge the complete bracket and smoothness inputs. -/
theorem local_regular_of_particular_solution {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (Ω U : Opens (Fin n → ℝ))
    (hK : IsCompact (closure (U : Set (Fin n → ℝ))))
    (hKΩ : closure (U : Set (Fin n → ℝ)) ⊆ Ω)
    (p : ℝ≥0∞) (T F : Distribution Ω ℝ (⊤ : ℕ∞)) (v : (Fin n → ℝ) → ℝ)
    (hv : LocallyIntegrableOn v (Ω : Set (Fin n → ℝ)) volume)
    (hvs : memSobolevX driftWeight H.fields U 2 p v)
    (hT : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞),
      T (Distribution.adjointTest Ω H.fields (fun _ => 0)
        (fun i => (H.fields_smooth G i).contDiffOn) (by fun_prop) ψ) = F ψ)
    (hV : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞),
      Distribution.ofFun Ω v volume (⊤ : ℕ∞)
        (Distribution.adjointTest Ω H.fields (fun _ => 0)
          (fun i => (H.fields_smooth G i).contDiffOn) (by fun_prop) ψ) = F ψ) :
    ∃ w : (Fin n → ℝ) → ℝ, memSobolevX driftWeight H.fields U 2 p w ∧
      ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T ψ = ∫ x, ψ x*w x := by
  apply distribution_representative_of_particular_solution G.dimension_pos Ω U hK hKΩ
    H.fields (fun i => (H.fields_smooth G i).contDiffOn) (H.spansOn G _) p T v hv hvs
  intro ψ
  exact (hT ψ).trans (hV ψ).symm

end RothschildStein.H3
