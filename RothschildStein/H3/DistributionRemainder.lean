-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SmoothRelCompactSobolev
public import RothschildStein.Definitions.driftWeight
public import RothschildStein.Distribution.RealHypoellipticity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- an actual particular solution and the homogeneous
remainder equation give a local Sobolev representative of an arbitrary
distribution. Hypoellipticity is invoked on the difference distribution. -/
theorem distribution_representative_of_particular_solution {n q : ℕ}
    (hn : 0 < n) (Ω U : Opens (Fin n → ℝ))
    (hK : IsCompact (closure (U : Set (Fin n → ℝ))))
    (hKΩ : closure (U : Set (Fin n → ℝ)) ⊆ Ω)
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : Hormander.Interface.LieAlgebraSpansOn (Ω : Set (Fin n → ℝ)) X)
    (p : ℝ≥0∞) (T : Distribution Ω ℝ (⊤ : ℕ∞)) (v : (Fin n → ℝ) → ℝ)
    (hv : LocallyIntegrableOn v (Ω : Set (Fin n → ℝ)) volume)
    (hvs : memSobolevX driftWeight X U 2 p v)
    (heq : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞),
      T (Distribution.adjointTest Ω X (fun _ => 0) hX (by fun_prop) ψ) =
      Distribution.ofFun Ω v volume (⊤ : ℕ∞)
        (Distribution.adjointTest Ω X (fun _ => 0) hX (by fun_prop) ψ)) :
    ∃ w : (Fin n → ℝ) → ℝ, memSobolevX driftWeight X U 2 p w ∧
      ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), T ψ = ∫ x, ψ x*w x := by
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : Fin n → ℝ => (0 : ℝ))
      (Ω : Set (Fin n → ℝ)) := by fun_prop
  have hd : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞),
      (T-Distribution.ofFun Ω v volume (⊤ : ℕ∞))
        (Distribution.adjointTest Ω X (fun _ => 0) hX hc ψ) =
      Distribution.ofFun Ω (fun _ => 0) volume (⊤ : ℕ∞) ψ := by
    intro ψ
    simp only [sub_apply, heq ψ, sub_self]
    simp only [show (fun _ : Fin n → ℝ => (0 : ℝ)) = 0 from rfl,
      Distribution.ofFun_zero, zero_apply]
  obtain ⟨f,hf,hrep⟩ := Distribution.exists_real_smooth_representative_of_distribution_equation
    hn Ω X (fun _ => 0) hX hspan hc
    (T-Distribution.ofFun Ω v volume (⊤ : ℕ∞)) (fun _ => 0) (by fun_prop) hd
  have hfs := memSobolevX_of_contDiffOn_relCompact Ω U hK hKΩ driftWeight X hX 2 p f hf
  have hUΩ : (U : Set (Fin n → ℝ)) ⊆ Ω := subset_closure.trans hKΩ
  refine ⟨fun x => v x+f x, ⟨hvs.1.add hfs.1,?_⟩,?_⟩
  · intro I hI
    obtain ⟨a,ha,hal⟩ := hvs.2 I hI
    obtain ⟨b,hb,hbl⟩ := hfs.2 I hI
    exact ⟨fun x => a x+b x,
      S.hasWeakWordDeriv_add X U (fun i => (hX i).mono hUΩ) ha hb, hal.add hbl⟩
  · intro ψ
    have hh := hrep ψ
    rw [sub_apply, Distribution.ofFun_apply hv] at hh
    simp only [smul_eq_mul] at hh
    have hvψ : Integrable (fun x => ψ x*v x) volume := by
      simpa only [mul_comm] using S.integrable_mul_test Ω hv ψ
    have hfψ : Integrable (fun x => ψ x*f x) volume := by
      simpa only [mul_comm] using S.integrable_mul_test Ω
        (hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet) ψ
    simp_rw [mul_add]
    rw [integral_add hvψ hfψ]
    linarith

end RothschildStein.H3
