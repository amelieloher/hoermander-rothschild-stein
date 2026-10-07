-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CompactKernelLocalData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Filter Metric TopologicalSpace
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ}

/-- A base-point directional derivative of a smooth kernel is
itself a test function in the integration variable when nearby sections
have one common interior compact support (BB p. 78; support). -/
def compactKernelDirectionalTest
    (Ω : Opens (Fin n → ℝ)) (K : Compacts (Fin n → ℝ))
    (hK : (K : Set (Fin n → ℝ)) ⊆ Ω)
    {k : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hk : ContDiff ℝ (⊤ : ℕ∞) (uncurry k))
    (x v : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (hks : ∀ a z, a ∈ ball x r → z ∉ K → k a z = 0) :
    TestFunction Ω ℝ (⊤ : ℕ∞) := by
  let d := fun z => fderiv ℝ (uncurry k) (x,z) (v,0)
  have hs : ContDiff ℝ (⊤ : ℕ∞) d :=
    ((hk.fderiv_right (m := ((⊤ : ℕ∞) : ℕ∞ω)) (by simp)).clm_apply
      contDiff_const).comp (contDiff_const.prodMk contDiff_id)
  have hz : ∀ z, z ∉ (K : Set (Fin n → ℝ)) → d z = 0 := by
    intro z hz
    have he : (fun a => k a z) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [ball_mem_nhds x hr] with a ha
      exact hks a z ha hz
    dsimp [d]
    rw [← fderiv_productSection_first_apply hk x z v]
    change fderiv ℝ (fun a => k a z) x v = 0
    rw [he.fderiv_eq,fderiv_const_apply,zero_apply]
  have ht : tsupport d ⊆ K := by
    apply closure_minimal _ K.isCompact.isClosed
    intro z hz'
    by_contra hn
    exact hz' (hz z hn)
  exact ⟨d,hs,K.isCompact.of_isClosed_subset isClosed_closure ht,ht.trans hK⟩

end RothschildStein.S
