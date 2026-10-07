-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeKernel
public import RothschildStein.S.FieldGermExtension
public import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.P1
variable {N : ℕ} {F : KernelFrame N}

/-- Differentiating the output of a regular kernel consumes one
regularity order and preserves its compact interior support (BB p. 550). -/
theorem IsRegularKernel.outputDerivative {b : ℕ}
    {r : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (hr : IsRegularKernel F (b + 1) r)
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (F.V : Set (Fin N → ℝ))) :
    IsRegularKernel F b (fun ξ η =>
      fderiv ℝ (fun z : (Fin N → ℝ) × (Fin N → ℝ) => r z.1 z.2)
        (ξ, η) (Y ξ, 0)) := by
  let f := fun z : (Fin N → ℝ) × (Fin N → ℝ) => r z.1 z.2
  let K : Compacts (Fin N → ℝ) :=
    ⟨Prod.fst '' tsupport f, hr.2.1.isCompact.image continuous_fst⟩
  have hK : (K : Set (Fin N → ℝ)) ⊆ (F.V : Set (Fin N → ℝ)) := by
    rintro x ⟨z, hz, rfl⟩
    exact (hr.2.2 hz).1
  obtain ⟨B, hB, hg⟩ := S.exists_global_field_germ_extension F.V K hK Y hY
  let d := fun z : (Fin N → ℝ) × (Fin N → ℝ) =>
    fderiv ℝ f z (B z.1, 0)
  have hd : ContDiff ℝ b d :=
    (hr.1.fderiv_right (by simp)).clm_apply
      (((hB.of_le (by simp)).comp contDiff_fst).prodMk contDiff_const)
  have hs : tsupport d ⊆ tsupport f := by
    apply closure_minimal
    · intro z hz
      by_contra hn
      have he : d z = 0 := by
        dsimp [d]
        rw [fderiv_of_notMem_tsupport ℝ hn]
        simp
      exact hz he
    · exact isClosed_tsupport f
  have he : (fun z : (Fin N → ℝ) × (Fin N → ℝ) =>
      fderiv ℝ f z (Y z.1, 0)) = d := by
    funext z
    by_cases hz : z ∈ tsupport f
    · have hgz := (hg z.1 ⟨z, hz, rfl⟩).eq_of_nhds
      dsimp [d]
      rw [hgz]
    · dsimp [d]
      rw [fderiv_of_notMem_tsupport ℝ hz]
      simp
  change ContDiff ℝ b _ ∧ HasCompactSupport _ ∧ tsupport _ ⊆ _
  rw [he]
  exact ⟨hd, hr.2.1.of_isClosed_subset (isClosed_tsupport d) hs, hs.trans hr.2.2⟩

end RothschildStein.P1
