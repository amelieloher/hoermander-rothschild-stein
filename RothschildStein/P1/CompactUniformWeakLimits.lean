-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.UniformTestConvergence
public import RothschildStein.S.DistributionWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology Distributions
namespace RothschildStein.P1
open RothschildStein.S
variable {n m : ℕ} {ι : Type*}

/-- Weak word identities pass to compact uniform limits on
an open domain when both limits are locally integrable (BB Prop 2.15,
p. 82 and Thm 2.17, p. 83; test-pairing gap fill). -/
theorem hasWeakWordDeriv_of_compactUniformLimits
    {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i,ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin m)) (F H : ι → (Fin n → ℝ) → ℝ)
    (f g : (Fin n → ℝ) → ℝ)
    (h : ∀ j,hasWeakWordDeriv X Ω I (F j) (H j))
    (hf : LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume)
    (hg : LocallyIntegrableOn g (Ω : Set (Fin n → ℝ)) volume)
    (htF : ∀ K : Set (Fin n → ℝ), IsCompact K → K ⊆ (Ω : Set (Fin n → ℝ)) →
      TendstoUniformlyOn F f l K)
    (htH : ∀ K : Set (Fin n → ℝ), IsCompact K → K ⊆ (Ω : Set (Fin n → ℝ)) →
      TendstoUniformlyOn H g l K) :
    hasWeakWordDeriv X Ω I f g := by
  refine ⟨hf,hg,fun φ => ?_⟩
  let ψ := wordTransposeTest Ω X hX I φ
  have hL := tendsto_testIntegral_of_uniformOnSupport Ω φ H g
    (fun j => (h j).2.1) hg (htH _ φ.hasCompactSupport.isCompact φ.tsupport_subset)
  have hR := tendsto_testIntegral_of_uniformOnSupport Ω ψ F f
    (fun j => (h j).1) hf (htF _ ψ.hasCompactSupport.isCompact ψ.tsupport_subset)
  have he : (fun j => Distribution.ofFun Ω (H j) volume (⊤ : ℕ∞) φ) =
      (fun j => Distribution.ofFun Ω (F j) volume (⊤ : ℕ∞) ψ) := by
    funext j
    have hh := congrArg (fun T => T φ) (distributionWord_ofFun_eq Ω X hX I (F j) (H j) (h j))
    simpa only [distributionWordCLM_apply,ψ] using hh.symm
  rw [he] at hL
  have hh := tendsto_nhds_unique hL hR
  rw [Distribution.ofFun_apply hg,Distribution.ofFun_apply hf] at hh
  simp only [smul_eq_mul] at hh
  have hzG : ∀ x,x ∉ (Ω : Set (Fin n → ℝ)) → φ x*g x = 0 := by
    intro x hx
    simp [φ.zero_on_compl hx]
  have hzF : ∀ x,x ∉ (Ω : Set (Fin n → ℝ)) → ψ x*f x = 0 := by
    intro x hx
    simp [ψ.zero_on_compl hx]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzG,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hzF] at hh
  simpa only [ψ,wordTransposeTest_apply,mul_comm] using hh

end RothschildStein.P1
