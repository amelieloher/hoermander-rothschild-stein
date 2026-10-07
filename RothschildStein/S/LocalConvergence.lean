-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.TestPairing
public import RothschildStein.S.Conjugate

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal Distributions
namespace RothschildStein.S
variable {n : ℕ}

/-- Lp convergence on every relatively compact open subset implies
convergence against each test (BB pp. 68–69). -/
theorem tendsto_testIntegral_of_localLp {α : Type*} {l : Filter α}
    (Ω : Opens (Fin n → ℝ)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (F : α → (Fin n → ℝ) → ℝ) (f : (Fin n → ℝ) → ℝ)
    (hF : ∀ (U : Opens (Fin n → ℝ)), IsCompact (closure (U : Set (Fin n → ℝ))) →
      closure (U : Set (Fin n → ℝ)) ⊆ Ω →
      ∀ j, MemLp (F j) p (volume.restrict (U : Set (Fin n → ℝ))))
    (hf : ∀ (U : Opens (Fin n → ℝ)), IsCompact (closure (U : Set (Fin n → ℝ))) →
      closure (U : Set (Fin n → ℝ)) ⊆ Ω →
      MemLp f p (volume.restrict (U : Set (Fin n → ℝ))))
    (ht : ∀ (U : Opens (Fin n → ℝ)), IsCompact (closure (U : Set (Fin n → ℝ))) →
      closure (U : Set (Fin n → ℝ)) ⊆ Ω →
      Tendsto (fun j => eLpNorm (fun x => F j x-f x) p
        (volume.restrict (U : Set (Fin n → ℝ)))) l (𝓝 0))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    Tendsto (fun j => ∫ x in (Ω : Set (Fin n → ℝ)), F j x * φ x) l
      (𝓝 (∫ x in (Ω : Set (Fin n → ℝ)), f x * φ x)) := by
  obtain ⟨W,hW,hKW,hclW,hcW⟩ := exists_open_between_and_isCompact_closure
    φ.hasCompactSupport Ω.isOpen φ.tsupport_subset
  let U : Opens (Fin n → ℝ) := ⟨W,hW⟩
  let ψ : TestFunction U ℝ (⊤ : ℕ∞) := ⟨φ,φ.contDiff,φ.hasCompactSupport,hKW⟩
  let r := (1-p⁻¹)⁻¹
  let : ENNReal.HolderConjugate p r := holderConjugate_complement p Fact.out
  let : Fact (1 ≤ r) := ⟨ENNReal.HolderConjugate.one_le r p⟩
  have he : ∀ g : (Fin n → ℝ) → ℝ,
      (∫ x in (U : Set (Fin n → ℝ)), g x * ψ x) =
      ∫ x in (Ω : Set (Fin n → ℝ)), g x * φ x := by
    intro g
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by simp [ψ.zero_on_compl hx]),
      setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by simp [φ.zero_on_compl hx])]
    rfl
  have hh := tendsto_testIntegral_of_tendsto_eLpNorm U p r ψ F f
    (hF U hcW hclW) (hf U hcW hclW) (ht U hcW hclW)
  rw [he f] at hh
  exact hh.congr (fun j => he (F j))

end RothschildStein.S
