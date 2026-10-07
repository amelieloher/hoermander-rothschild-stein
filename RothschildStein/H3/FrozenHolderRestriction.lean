-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalFirstHolderMonotonicity
public import RothschildStein.S.IntrinsicWeakHolderExport
public import RothschildStein.S.WeakHolderToIntrinsic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- Fixed intrinsic Hölder membership restricts on the fixed
ambient distance. Both bridges use the same complete weighted word data. -/
theorem frozen_holderX_restrict {N m : ℕ}
    (Ω U V : Opens (Fin N → ℝ)) (G : S.DistanceGeometry Ω)
    (hU : (U : Set (Fin N → ℝ)) ⊆ Ω) (hVU : (V : Set (Fin N → ℝ)) ⊆ U)
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    (k : ℕ) {α : ℝ} (hα : 0 < α) {u : (Fin N → ℝ) → ℝ}
    (hu : memHolderX w X G.d U k α u) : memHolderX w X G.d V k α u := by
  have hw := S.memWeakHolderX_of_memHolderX Ω U G hU w X hX k hα hu
  exact S.memHolderX_of_memWeakHolderX Ω V G (hVU.trans hU) w X
    (fun i => (hX i).mono hVU) k hα
    (S.memWeakHolderX_restrict w X G.d U V hVU k α hw)

/-- Every first-order norm on a smaller domain is bounded by
one finite outer first-order norm of the original fixed input. -/
theorem frozen_first_holderNorm_restrict_bound {N q : ℕ}
    (Ω U V : Opens (Fin N → ℝ)) (G : S.DistanceGeometry Ω)
    (hU : (U : Set (Fin N → ℝ)) ⊆ Ω) (hVU : (V : Set (Fin N → ℝ)) ⊆ U)
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    {α : ℝ} (hα : 0 < α) {u : (Fin N → ℝ) → ℝ}
    (hu : memHolderX driftWeight X G.d U 2 α u) :
    holderXENorm driftWeight X G.d V 1 α u ≤ holderXENorm driftWeight X G.d U 1 α u ∧
      holderXENorm driftWeight X G.d U 1 α u < ⊤ := by
  have hw := S.memWeakHolderX_of_memHolderX Ω U G hU driftWeight X hX 2 hα hu
  obtain ⟨jet, hzero, hj⟩ := S.exists_weakHolder_representatives driftWeight X G.d U 2 α hw
  exact local_first_holderNorm_mono_of_weak_jets Ω U V G hU hVU X hX hα u jet hzero
    (fun I hI => hj I ((S.mem_wordFamily_iff driftWeight 2 I).mpr hI))

end RothschildStein.H3
