-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakDeriv
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
variable {n m : ℕ}

/-- Compatible weak identities on patches containing every compact
set give the global identity, once the two representatives are in Lp. -/
theorem hasWeakWordDeriv_global_of_compact_patches
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (I : List (Fin m))
    {f g : (Fin n → ℝ) → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : MemLp f p (volume : Measure (Fin n → ℝ)))
    (hg : MemLp g p (volume : Measure (Fin n → ℝ)))
    (hpatch : ∀ K : Set (Fin n → ℝ), IsCompact K →
      ∃ U : Opens (Fin n → ℝ), K ⊆ (U : Set (Fin n → ℝ)) ∧
        hasWeakWordDeriv X U I f g) : hasWeakWordDeriv X ⊤ I f g := by
  refine ⟨(hf.locallyIntegrable hp).locallyIntegrableOn _,
    (hg.locallyIntegrable hp).locallyIntegrableOn _, ?_⟩
  intro φ
  obtain ⟨U, hU, hw⟩ := hpatch (tsupport φ) φ.hasCompactSupport
  let ψ : TestFunction U ℝ (⊤ : ℕ∞) :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, hU⟩
  have he := hw.2.2 ψ
  change (∫ x in (U : Set (Fin n → ℝ)), g x * φ x) =
    ∫ x in (U : Set (Fin n → ℝ)), f x * wordTranspose X I φ x at he
  have hgz : ∀ x, x ∉ (U : Set (Fin n → ℝ)) → g x * φ x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hU ht)), mul_zero]
  have hfz : ∀ x, x ∉ (U : Set (Fin n → ℝ)) → f x * wordTranspose X I φ x = 0 := by
    intro x hx
    have hz : wordTranspose X I φ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hx (hU (S.tsupport_wordTranspose_subset X I φ ht)))
    rw [hz, mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hgz,
    setIntegral_eq_integral_of_forall_compl_eq_zero hfz] at he
  simpa only [Opens.coe_top, Measure.restrict_univ] using he

end RothschildStein.H3
