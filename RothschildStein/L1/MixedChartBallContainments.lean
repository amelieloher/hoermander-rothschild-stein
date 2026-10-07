-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.MixedWeightedBoxes
public import RothschildStein.G4.AuxiliaryControl
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.L1

/-- The same lifted chart at a smaller application scale
places its inner ball inside a mixed box. At the original application
scale the mixed box lies in the full lifted box. No frame or chart
is selected again during this rescaling (BB pp. 520–521). -/
theorem mixed_chart_image_ball_containments {q n m s : ℕ}
    (Ω : Set (Fin (n+m) → ℝ)) (w : Fin q → ℕ+)
    (X : Fin q → (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ))
    (ξ : Fin (n+m) → ℝ) (wu : Fin n → ℕ+) (wv : Fin m → ℕ+)
    (F : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ))
    {a b au av c r₀ δ : ℝ} (ha : 0 < a) (hau : 0 ≤ au) (hav : 0 ≤ av)
    (hc : 0 < c) (hcau : c ≤ au) (hcav : c ≤ av)
    (haua : au ≤ a) (hava : av ≤ a) (hδ : 0 < δ) (hδr : δ ≤ r₀)
    (hinner : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      {η | G4.auxiliaryDistance (s := s) Ω w X ξ η < ENNReal.ofReal (b*r)} ⊆
        F '' G4.weightedBox (Fin.addCases wu wv) (a*r))
    (houter : F '' G4.weightedBox (Fin.addCases wu wv) (a*δ) ⊆
      {η | G4.auxiliaryDistance (s := s) Ω w X ξ η < ENNReal.ofReal (a*δ)}) :
    let Q := G4.weightedBox wu (au*δ) ×ˢ G4.weightedBox wv (av*δ)
    {η | G4.auxiliaryDistance (s := s) Ω w X ξ η < ENNReal.ofReal ((b*c/a)*δ)} ⊆
      (fun p => F (joinPoint p.1 p.2)) '' Q ∧
    (fun p => F (joinPoint p.1 p.2)) '' Q ⊆
      {η | G4.auxiliaryDistance (s := s) Ω w X ξ η < ENNReal.ofReal (a*δ)} := by
  intro Q
  have hca : c ≤ a := hcau.trans haua
  have hscale : c/a*δ ≤ r₀ := by
    apply le_trans _ hδr
    exact (mul_le_mul_of_nonneg_right ((div_le_one ha).mpr hca) hδ.le).trans_eq (one_mul δ)
  have har : a*(c/a*δ) = c*δ := by field_simp [ha.ne']
  have hbr : b*(c/a*δ) = (b*c/a)*δ := by ring
  constructor
  · intro η hη
    obtain ⟨z,hz,heq⟩ := hinner (c/a*δ) (mul_pos (div_pos hc ha) hδ) hscale
      (by simpa only [hbr] using hη)
    rw [har] at hz
    have hm := full_weightedBox_subset_mixed wu wv hc.le hδ.le hcau hcav
      (Set.mem_image_of_mem (P1.paddingCoordinates n m) hz)
    refine ⟨P1.paddingCoordinates n m z,hm,?_⟩
    change F (joinPoint (P1.paddingBaseCLM n m z) (P1.paddingFiberCLM n m z)) = η
    rw [← P1.paddingJoinCLM_apply,P1.paddingJoinCLM_projections]
    exact heq
  · rintro η ⟨p,hp,rfl⟩
    apply houter
    refine ⟨joinPoint p.1 p.2,?_,rfl⟩
    exact joinPoint_mixed_weightedBox_subset wu wv hau hav hδ.le haua hava
      (Set.mem_image_of_mem (fun p => joinPoint p.1 p.2) hp)

end RothschildStein.L1
