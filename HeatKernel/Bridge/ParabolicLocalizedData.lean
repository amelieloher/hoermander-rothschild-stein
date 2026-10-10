-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.LocalizedFormData
public import HeatKernel.Bridge.ParabolicValueIntegrability
import Mathlib.Tactic.Linter

/-! # Localized form-test data for the literal parabolic weak predicate -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- The value of a weak solution and a supplied L² gradient on a compact cylinder
produce localized form-test data for a smooth temporal test under explicit measurable coefficient bounds. -/
theorem IsLocalWeakSolution.exists_localized_form_data {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u)
    {J : Set ℝ} {K : Set (Fin N → ℝ)}
    (hJ : IsCompact J) (hJI : J ⊆ (I : Set ℝ))
    (hK : IsCompact K) (hKU : K ⊆ (U : Set (Fin N → ℝ)))
    (g : Fin q → ℝ → (Fin N → ℝ) → ℝ)
    (hg : ∀ j, MemLp (fun z : ℝ × (Fin N → ℝ) => g j z.1 z.2) 2 (volume.restrict (J ×ˢ K)))
    (ha : ∀ i j, AEStronglyMeasurable (fun z : ℝ × (Fin N → ℝ) => a z.1 z.2 i j)
      (volume.restrict (J ×ˢ K)))
    {C : ℝ} (hbound : ∀ i j, ∀ᵐ z : ℝ × (Fin N → ℝ) ∂(volume.restrict (J ×ˢ K)),
      ‖a z.1 z.2 i j‖ ≤ C)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ) :
    ∃ (T : Lp ℝ 2 ((volume.restrict J).prod (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ)))))
      (F : Fin q → Lp ℝ 2 ((volume.restrict J).prod (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))))),
      (T : ℝ × (Fin N → ℝ) → ℝ) =ᵐ[(volume.restrict J).prod volume]
        (fun z => K.indicator (fun x => -(deriv ψ z.1) * u z.1 x) z.2) ∧
      ∀ i, (F i : ℝ × (Fin N → ℝ) → ℝ) =ᵐ[(volume.restrict J).prod volume]
        (fun z => K.indicator (fun x => ψ z.1 * ∑ j, a z.1 x i j * g j z.1 x) z.2) := by
  have hup := hu.memLp_two_on_compact_cylinder G hq hqpos hw hspan a I U hJ hJI hK hKU
  have hup' : MemLp (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) 2
      ((volume.restrict J).prod (volume.restrict K)) := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hup
  have hgp' (j : Fin q) : MemLp (fun z : ℝ × (Fin N → ℝ) => g j z.1 z.2) 2
      ((volume.restrict J).prod (volume.restrict K)) := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hg j
  have hap' (i j : Fin q) : AEStronglyMeasurable (fun z : ℝ × (Fin N → ℝ) => a z.1 z.2 i j)
      ((volume.restrict J).prod (volume.restrict K)) := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using ha i j
  have hbp' (i j : Fin q) : ∀ᵐ z : ℝ × (Fin N → ℝ)
      ∂((volume.restrict J).prod (volume.restrict K)), ‖a z.1 z.2 i j‖ ≤ C := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hbound i j
  have htop : (volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))).restrict K =
      (volume : Measure (Fin N → ℝ)).restrict K := by
    rw [Opens.coe_top, Measure.restrict_univ]
  have huptop : MemLp (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) 2
      ((volume.restrict J).prod
        ((volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))).restrict K)) := by
    rw [htop]
    exact hup'
  have hgptop (j : Fin q) : MemLp (fun z : ℝ × (Fin N → ℝ) => g j z.1 z.2) 2
      ((volume.restrict J).prod
        ((volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))).restrict K)) := by
    rw [htop]
    exact hgp' j
  have haptop (i j : Fin q) : AEStronglyMeasurable (fun z : ℝ × (Fin N → ℝ) => a z.1 z.2 i j)
      ((volume.restrict J).prod
        ((volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))).restrict K)) := by
    rw [htop]
    exact hap' i j
  have hbptop (i j : Fin q) : ∀ᵐ z : ℝ × (Fin N → ℝ)
      ∂((volume.restrict J).prod
        ((volume.restrict ((⊤ : Opens (Fin N → ℝ)) : Set (Fin N → ℝ))).restrict K)),
      ‖a z.1 z.2 i j‖ ≤ C := by
    rw [htop]
    exact hbp' i j
  have H := exists_localized_square_integrable_form_data hK.measurableSet
    (fun z => u z.1 z.2) (fun j z => g j z.1 z.2) (fun i j z => a z.1 z.2 i j)
    huptop hgptop haptop hbptop (hψ.continuous_deriv (by simp)).neg hcψ.deriv.neg hψ.continuous hcψ
  simpa only [Opens.coe_top, Measure.restrict_univ, Pi.neg_apply] using H

end HeatKernel
