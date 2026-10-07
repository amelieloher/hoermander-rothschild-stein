-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.CoordinatePowerBallVolumes
public import RothschildStein.L1.CoordinateBallFacts

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.L1.CoordinateApproximationData

/-- The complete non-fiber prefix of GaugeFiberData.ball_bounds
for the fixed coordinate data: containment, measurability, finite
positive volumes, the chosen model power law and ambient projection.
Only the upper/lower fiber clauses remain for the chart assembly
(BB pp. 515–522, Cor. 10.37, Prop. 10.39 and Thm. 10.40). -/
theorem compact_ball_density_facts {n k s m : ℕ} {w : Fin (k+1) → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} {L : FixedLiftData w s Ω X x₀ m}
    {M : ModelData (k+1) s (n+m) w} (A : CoordinateApproximationData L M)
    (hΩ : IsOpen Ω) (hs : 1 ≤ s) (hw : ∀ i, (w i : ℕ) ≤ s)
    {K : Set (Fin (n+m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ A.U) :
    ∃ rstar cv Cv : ℝ, 0 < rstar ∧ 0 < cv ∧ 0 < Cv ∧
      ∀ η ∈ K, ∀ r : ℝ, 0 < r → r < rstar →
        let Ul := rsBall (basePoint ⁻¹' Ω) w (triangularLift X L.P) η r
        let Vb := rsBall Ω w X (basePoint η) r
        Ul ⊆ A.U ∧ MeasurableSet Ul ∧ MeasurableSet Vb ∧
        volume Ul ≠ ⊤ ∧ volume Vb ≠ ⊤ ∧
        0 < (volume Ul).toReal ∧ 0 < (volume Vb).toReal ∧
        cv*r^M.G.homogeneousDimension ≤ (volume Ul).toReal ∧
        (volume Ul).toReal ≤ Cv*r^M.G.homogeneousDimension ∧
        (∀ ξ ∈ Ul, controlDistance Ω w X (basePoint η) (basePoint ξ) ≤
          controlDistance (basePoint ⁻¹' Ω) w (triangularLift X L.P) η ξ) := by
  obtain ⟨ρ,hρ,hfacts⟩ := A.compact_ball_facts hΩ hs hw hK hKU
  obtain ⟨rstar,cv,Cv,hrstar,hcv,hCv,hpower⟩ :=
    A.compact_real_power_ball_volumes hs hw hK hKU
  refine ⟨min ρ rstar,cv,Cv,lt_min hρ hrstar,hcv,hCv,?_⟩
  intro η hη r hr hrr Ul Vb
  obtain ⟨hsub,_ho,_hVo,hmu,hmv,hfu,hfv,hpu,hpv,hproj⟩ :=
    hfacts η hη r hr (hrr.trans_le (min_le_left _ _))
  obtain ⟨_hf,_hp,hlo,hhi⟩ :=
    hpower η hη r hr (hrr.trans_le (min_le_right _ _))
  exact ⟨hsub,hmu,hmv,hfu,hfv,hpu,hpv,hlo,hhi,hproj⟩

end RothschildStein.L1.CoordinateApproximationData
