-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RescaledChartParameters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MvPolynomial Metric
open scoped BigOperators Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- Compact rescaled input endpoint ranges
lie inside the actual chart neighborhood. This permits uniform Taylor
bounds for the complete transfer remainder (BB p. 557). -/
theorem exists_transferInput_parameter_range
    {K S : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U)
    (hS : IsCompact S) :
    ∃ L : Set (Fin (n + m) → ℝ), IsCompact L ∧ L ⊆ C.U ∧
      (∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ ξ ∈ K,
        ContinuousOn (fun u => (ξ, (C.e ξ).symm (-C.G.dilate ε u))) S ∧
        ∀ u ∈ S, ξ ∈ L ∧ (C.e ξ).symm (-C.G.dilate ε u) ∈ L) ∧
      ∀ ξ ∈ K, ∀ u : Fin (n + m) → ℝ,
        Tendsto (fun ε : ℝ => (ξ, (C.e ξ).symm (-C.G.dilate ε u)))
          (𝓝[>] (0 : ℝ)) (𝓝 (ξ, ξ)) := by
  obtain ⟨ρ, M, hρ, _, hI⟩ := C.exists_inverse_zero_bound hK hKU
  let A := K ×ˢ closedBall (0 : Fin (n + m) → ℝ) ρ
  let I := fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (C.e p.1).symm p.2
  have hAT : A ⊆ C.T := by
    intro p hp
    exact ⟨hKU hp.1, (hI p.1 hp.1 p.2 (by simpa using hp.2)).1⟩
  have hIC : IsCompact (I '' A) :=
    (hK.prod (isCompact_closedBall (0 : Fin (n + m) → ℝ) ρ)).image_of_continuousOn
      (C.inverse_joint_contDiffOn.continuousOn.mono hAT)
  obtain ⟨B, hb⟩ := hS.exists_bound_of_continuousOn continuousOn_id
  let H := max B 0 + 1
  have hH : 0 < H := by dsimp [H]; linarith [le_max_right B 0]
  have huB (u : Fin (n + m) → ℝ) (hu : u ∈ S) : ‖u‖ ≤ H :=
    (hb u hu).trans (by dsimp [H]; linarith [le_max_left B 0])
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < min 1 (ρ / H) :=
    (eventually_lt_nhds (lt_min zero_lt_one (div_pos hρ hH))).filter_mono nhdsWithin_le_nhds
  have hLU : K ∪ I '' A ⊆ C.U := by
    intro ζ hζ
    rcases hζ with hζ | ⟨p, hp, rfl⟩
    · exact hKU hζ
    · rw [← (C.chart p.1 (hKU hp.1)).1]
      exact (C.e p.1).mapsTo_symm (hAT hp).2
  refine ⟨K ∪ I '' A, hK.union hIC, hLU, ?_, ?_⟩
  · filter_upwards [hsmall, self_mem_nhdsWithin] with ε he hε
    intro ξ hξ
    have hnorm (u : Fin (n + m) → ℝ) (hu : u ∈ S) : ‖-C.G.dilate ε u‖ ≤ ρ := by
      rw [norm_neg]
      have he1 : ε ≤ 1 := (he.trans_le (min_le_left _ _)).le
      have heρ : ε * H < ρ := (lt_div_iff₀ hH).mp (he.trans_le (min_le_right _ _))
      exact ((norm_dilate_le_parameter_mul C.G hε.le he1 u).trans
        (mul_le_mul_of_nonneg_left (huB u hu) hε.le)).trans heρ.le
    have hmap : MapsTo (fun u => -C.G.dilate ε u) S (C.e ξ).target :=
      fun u hu => (hI ξ hξ _ (hnorm u hu)).1
    have hc := ((C.chart ξ (hKU hξ)).2.2.2.1.continuousOn).comp
      (G2.continuous_dilate C.G ε).neg.continuousOn hmap
    refine ⟨continuousOn_const.prodMk hc, ?_⟩
    intro u hu
    exact ⟨Or.inl hξ, Or.inr ⟨(ξ, -C.G.dilate ε u),
      ⟨hξ, by simpa using hnorm u hu⟩, rfl⟩⟩
  · intro ξ hξ u
    have hδ := (G2.continuousAt_dilate_parameter_zero C.G u).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [G2.zero_dilate] at hδ
    have hc : ContinuousAt ((C.e ξ).symm) 0 :=
      ((C.chart ξ (hKU hξ)).2.2.2.1.continuousOn).continuousAt
        ((C.e ξ).open_target.mem_nhds (C.zero_mem_target (hKU hξ)))
    have hn := hδ.neg
    rw [neg_zero] at hn
    have hi := hc.tendsto.comp hn
    rw [C.symm_zero (hKU hξ)] at hi
    exact tendsto_const_nhds.prodMk_nhds hi


end RothschildStein.P1.LiftedChart
