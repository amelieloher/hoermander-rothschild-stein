-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.InverseCoordinateNeighborhood
public import RothschildStein.G4.WeightedLiftDisplacement
public import RothschildStein.G4.LocalCoordinateVariation
public import Mathlib.Analysis.Normed.Module.Convex

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology

namespace RothschildStein.G4

/-- Every actual continuous partial lift in the coefficient box
has the uniform weighted variation bound. Actual local inverse branches
identify the lift nearby; their AC estimates glue over the whole time
interval (BB Prop 9.52, (9.51) and continuation, pp. 448–449). -/
theorem continuous_partialLift_weighted_variation {m n : ℕ}
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (w : Fin m → ℕ+) (B : Fin n → Fin m)
    {Q : Set (Fin n → ℝ)} (hQ : IsOpen Q)
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F Q)
    (hjac : ∀ u ∈ Q, Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u)) ≠ 0)
    (hdet : ∀ u ∈ Q, frameDet Z B (F u) ≠ 0)
    {r κ b D : ℝ} (hr : 0 < r) (hκ : 0 ≤ κ) (hsmall : (n : ℝ) * κ ≤ 1 / 4)
    (hb : 0 ≤ b) (hb1 : 2 * b ≤ 1) (hD : 0 ≤ D)
    (herror : ∀ u ∈ Q, ∀ i j, |frameCoefficient Z B
      (fun z => fderiv ℝ F u (Pi.single j 1) - Z (B j) z) i (F u)| ≤
        κ * r ^ (((w (B i) : ℕ) : ℤ) - ((w (B j) : ℕ) : ℤ)))
    (hframe : ∀ u ∈ Q, ∀ J j, |frameCoefficient Z B (Z J) j (F u)| ≤
      D * r ^ (((w (B j) : ℕ) : ℤ) - ((w J : ℕ) : ℤ)))
    {Ω : Set (Fin n → ℝ)} {γ : ℝ → (Fin n → ℝ)}
    (hγ : isControlledCurve Ω w Z (2 * b * r) γ)
    {T : ℝ} (hT1 : T ≤ 1) (θ : ℝ → (Fin n → ℝ))
    (hθ : ContinuousOn θ (Icc (0 : ℝ) T)) (hθQ : MapsTo θ (Icc (0 : ℝ) T) Q)
    (hlift : EqOn (F ∘ θ) γ (Icc (0 : ℝ) T)) :
    ∀ σ ∈ Icc (0 : ℝ) T, ∀ τ ∈ Icc (0 : ℝ) T, ∀ i,
      |θ τ i - θ σ i| ≤ (2 * (m : ℝ) * n * D * (4 / 3 : ℝ)) * b *
        r ^ (w (B i) : ℕ) * |τ - σ| := by
  have hγcont : ContinuousOn γ (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hγ.2.1.continuousOn
  have hforward : ∀ σ ∈ Icc (0 : ℝ) T, ∀ τ ∈ Icc (0 : ℝ) T, σ ≤ τ → ∀ i,
      |θ τ i - θ σ i| ≤ (2 * (m : ℝ) * n * D * (4 / 3 : ℝ)) * b *
        r ^ (w (B i) : ℕ) * (τ - σ) := by
    intro σ hσ τ hτ hστ i
    apply coordinate_variation_of_local_bound hστ (fun t => θ t i)
    intro t ht
    have htT : t ∈ Icc (0 : ℝ) T := ⟨hσ.1.trans ht.1, ht.2.trans hτ.2⟩
    obtain ⟨Ψ, V, hV, hmem, hΨ, _hpoint, hmap, hright, hleft, hinv⟩ :=
      exists_inverse_coordinate_neighborhood Z w B hQ F hF hjac hdet hr hκ hsmall
        herror (hθQ htT)
    have hbase : F (θ t) = γ t := hlift htT
    have hγt : γ t ∈ V := by rwa [hbase] at hmem
    have hpre : γ ⁻¹' V ∈ 𝓝[Icc (0 : ℝ) T] t :=
      ((hγcont.mono (Icc_subset_Icc le_rfl hT1)) t htT).preimage_mem_nhdsWithin
        (hV.mem_nhds hγt)
    have heq : ∀ᶠ s in 𝓝[Icc (0 : ℝ) T] t, Ψ (γ s) = θ s := by
      filter_upwards [hleft.comp_tendsto (hθ t htT), self_mem_nhdsWithin] with s hs hsT
      change Ψ (F (θ s)) = θ s at hs
      have hh : F (θ s) = γ s := hlift hsT
      rwa [hh] at hs
    have hboth : {s | γ s ∈ V ∧ Ψ (γ s) = θ s} ∈ 𝓝[Icc (0 : ℝ) T] t := by
      filter_upwards [hpre, heq] with s hs he
      exact ⟨hs, he⟩
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhdsWithin_iff.mp hboth
    refine ⟨ball t ε, isOpen_ball, mem_ball_self hε, ?_⟩
    intro u hu v hv
    have huT : u ∈ Icc (0 : ℝ) T := ⟨hσ.1.trans hu.1.1, hu.1.2.trans hτ.2⟩
    have hvT : v ∈ Icc (0 : ℝ) T := ⟨hσ.1.trans hv.1.1, hv.1.2.trans hτ.2⟩
    have hsegment : ∀ z ∈ uIcc u v, γ z ∈ V := by
      intro z hz
      have hzball := (convex_ball t ε).ordConnected.uIcc_subset hu.2 hv.2 hz
      have hzT := ordConnected_Icc.uIcc_subset huT hvT hz
      exact (hεsub ⟨hzball, hzT⟩).1
    have hdetV : ∀ z ∈ Icc (0 : ℝ) 1, γ z ∈ V → frameDet Z B (γ z) ≠ 0 := by
      intro z _ hzV
      have hz : F (Ψ (γ z)) = γ z := hright hzV
      simpa only [hz] using hdet (Ψ (γ z)) (hmap hzV)
    have hframeV : ∀ z ∈ Icc (0 : ℝ) 1, γ z ∈ V → ∀ J j,
        |frameCoefficient Z B (Z J) j (γ z)| ≤
          D * r ^ (((w (B j) : ℕ) : ℤ) - ((w J : ℕ) : ℤ)) := by
      intro z _ hzV
      have hz : F (Ψ (γ z)) = γ z := hright hzV
      simpa only [hz] using hframe (Ψ (γ z)) (hmap hzV)
    have hm := lifted_controlledCurve_coordinate_variation_on_interval hV Z w B Ψ hΨ hr
      hb hb1 hD (by norm_num : (0 : ℝ) ≤ 4 / 3) hγ hdetV hframeV
      (fun z _ hzV => hinv (γ z) hzV) u ⟨huT.1, huT.2.trans hT1⟩
      v ⟨hvT.1, hvT.2.trans hT1⟩ hsegment i
    rw [(hεsub ⟨hu.2, huT⟩).2, (hεsub ⟨hv.2, hvT⟩).2] at hm
    exact hm
  intro σ hσ τ hτ i
  rcases le_total σ τ with hle | hle
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hle)] using hforward σ hσ τ hτ hle i
  · rw [abs_sub_comm (θ τ i) (θ σ i), abs_sub_comm τ σ,
      abs_of_nonneg (sub_nonneg.mpr hle)]
    exact hforward τ hτ σ hσ hle i

end RothschildStein.G4
