-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalCutoffKernel
public import RothschildStein.P1.KernelEstimatesChart
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory

namespace RothschildStein.P1

/-- The canonical representative obtained by assigning zero on the diagonal. -/
def zeroDiagonal {N : ℕ} (kern : (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (ξ η : Fin N → ℝ) : ℝ := by
  classical
  exact if ξ = η then 0 else kern ξ η

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The principal kernel with zero diagonal is jointly Borel
measurable. Smoothness is used only inside the actual chart and off its pole;
the cutoffs remove all points outside the chart. -/
theorem LiftedChart.measurable_principal_zeroDiagonal
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (t : PrincipalTerm F)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n + m) → ℝ)}ᶜ) :
    Measurable (Function.uncurry (zeroDiagonal t.kernel)) := by
  classical
  let E : Set ((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) :=
    ((F.V : Set _) ×ˢ (F.V : Set _)) ∩ {p | p.1 ≠ p.2}
  have hE : MeasurableSet E :=
    (F.V.isOpen.prod F.V.isOpen).measurableSet.inter
      (isClosed_eq continuous_fst continuous_snd).measurableSet.compl
  have hEU : E ⊆ C.U ×ˢ C.U := fun _ hp => ⟨hVU hp.1.1, hVU hp.1.2⟩
  have hθ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.Θ p.2 p.1) E :=
    (C.theta_smooth.comp (contDiffOn_snd.prodMk contDiffOn_fst)
      (fun _ hp => ⟨hp.2, hp.1⟩)).mono hEU
  have hmap : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (p.1, p.2, C.Θ p.2 p.1)) E :=
    contDiffOn_fst.prodMk (contDiffOn_snd.prodMk hθ)
  have hc : ContinuousOn (Function.uncurry t.kernel) E := by
    have h := (t.cutoffModelKernel_contDiffOn hΓ).comp hmap
      (fun p hp => (C.theta_eq_zero_iff (hVU hp.1.2) (hVU hp.1.1)).not.mpr hp.2)
    have he : (kernelUncurry t.cutoffModelKernel ∘
        (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (p.1, p.2, C.Θ p.2 p.1))) =
        Function.uncurry t.kernel := by
      funext p
      change t.cutoffModelKernel p.1 p.2 (C.Θ p.2 p.1) = t.kernel p.1 p.2
      rw [t.kernel_eq_cutoffModelKernel, hΘ]
    rw [he] at h
    exact h.continuousOn
  have hm := hc.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) hE
  have he : E.piecewise (Function.uncurry t.kernel) (fun _ => (0 : ℝ)) =
      Function.uncurry (zeroDiagonal t.kernel) := by
    funext p
    by_cases hp : p ∈ E
    · rw [Set.piecewise_eq_of_mem E _ _ hp]
      change t.kernel p.1 p.2 = if p.1 = p.2 then 0 else t.kernel p.1 p.2
      rw [ite_eq_right hp.2]
    · rw [Set.piecewise_eq_of_notMem E _ _ hp]
      change 0 = if p.1 = p.2 then 0 else t.kernel p.1 p.2
      split_ifs with heq
      · rfl
      · have hnot : p.1 ∉ F.V ∨ p.2 ∉ F.V := by
          by_contra h
          push Not at h
          exact hp ⟨h, heq⟩
        rcases hnot with hleft | hright
        · have hz : t.a p.1 = 0 := image_eq_zero_of_notMem_tsupport
            (fun h => hleft (t.a.tsupport_subset h))
          simp only [PrincipalTerm.kernel, hz, zero_mul]
        · have hz : t.b p.2 = 0 := image_eq_zero_of_notMem_tsupport
            (fun h => hright (t.b.tsupport_subset h))
          simp only [PrincipalTerm.kernel, hz, mul_zero, zero_mul]
  rw [he] at hm
  exact hm

end RothschildStein.P1
