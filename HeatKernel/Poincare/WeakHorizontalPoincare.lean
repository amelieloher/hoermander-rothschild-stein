-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WeakInvariantPoincare
public import HeatKernel.Poincare.SmoothPoincareNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal BigOperators
namespace HeatKernel

/-- The uniform same-ball horizontal Poincaré bound holds for Lp functions with weak
horizontal derivatives on a neighborhood of the closed ball. -/
theorem exists_uniform_weak_horizontalPoincare_neighborhood_constant
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {κ p : ℝ} (hκ : 240 < κ) (k : ℕ) (hk : 0 < k)
    (hscale : 2 * κ + 22 ≤ (k : ℝ)) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : Fin N → ℝ) (r : ℝ), 0 < r →
      ∀ Ω : Opens (Fin N → ℝ), closure (horizontalBall (G.horizontalFields hq) x r) ⊆ Ω →
      ∀ (f : (Fin N → ℝ) → ℝ) (g : Fin q → (Fin N → ℝ) → ℝ),
        MemLp f (ENNReal.ofReal p) (volume.restrict (Ω : Set (Fin N → ℝ))) →
        (∀ i, MemLp (g i) (ENNReal.ofReal p) (volume.restrict (Ω : Set (Fin N → ℝ)))) →
        (∀ i, hasWeakWordDeriv (G.horizontalFields hq) Ω [i] f (g i)) →
        eLpNorm (fun y => f y - ⨍ z in horizontalBall (G.horizontalFields hq) x r, f z)
          (ENNReal.ofReal p) (volume.restrict (horizontalBall (G.horizontalFields hq) x r)) ≤
          ENNReal.ofReal (C * r) * eLpNorm (fun y => Real.sqrt (∑ i, g i y ^ 2))
            (ENNReal.ofReal p) (volume.restrict (horizontalBall (G.horizontalFields hq) x r)) := by
  obtain ⟨C, hC, hPI⟩ := exists_uniform_horizontalPoincare_seminorm_constant
    G hq hqpos hspan hw hκ k hk hscale hp
  refine ⟨C, hC, ?_⟩
  intro x r hr Ω hΩ f g hf hg hfg
  let B := horizontalBall (G.horizontalFields hq) x r
  have hK : IsCompact (closure B) := isCompact_closure_horizontalBall G hq hqpos hspan hw x hr.le
  let v := fun i : Fin q => Hormander.Interface.basisVec (Fin.castLE hq i)
  have hweak : ∀ i, hasWeakWordDeriv (fun _ : Fin 1 => G2.leftField G (v i)) Ω [0] f (g i) := by
    intro i
    refine ⟨(hfg i).1, (hfg i).2.1, ?_⟩
    intro φ
    simpa only [wordTranspose, HomogeneousGroup.horizontalFields, G2.canonicalField_eq_leftField]
      using (hfg i).2.2 φ
  apply weak_invariant_poincare_of_smooth_bound G Ω hK
    subset_closure hΩ v hp ENNReal.ofReal_ne_top ?_ hf hg hweak
  intro u hu
  have hui : IntegrableOn u B :=
    (hu.continuous.continuousOn.integrableOn_compact hK).mono_set subset_closure
  have hh := hPI x r hr u ((hu.of_le (by simp)).contDiffOn) hui
  have hgrad : horizontalGradientNorm (G.horizontalFields hq) u =
      (fun y => Real.sqrt (∑ j, fieldDerivative (G2.leftField G (v j)) u y ^ 2)) := by
    funext y
    rfl
  rw [hgrad] at hh
  exact hh

end HeatKernel
