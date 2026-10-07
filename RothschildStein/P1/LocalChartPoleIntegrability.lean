-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.GaugeChartIntegrability
public import RothschildStein.P1.RightParametrixTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- A continuous punctured row with a locally
integrable gauge-power bound near its pole is integrable on compact
input patches. No global chart regularity is required. -/
theorem integrableOn_of_local_gauge_power_bound
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U)
    (f : (Fin (n + m) → ℝ) → ℝ) (hf : ContinuousOn f (K \ {ξ}))
    (d : ℤ) (hd : -(C.G.homogeneousDimension : ℤ) < d)
    {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (hb : ∀ η ∈ K, η ≠ ξ → kgauge C.G (C.Θ η ξ) < ε →
      ‖f η‖ ≤ M * kgauge C.G (C.Θ η ξ) ^ d) :
    IntegrableOn f K volume := by
  let rsLocalPoleFinNonempty : Nonempty (Fin (n + m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  let E := K \ {ξ}
  let L := K ∩ (fun η => kgauge C.G (C.Θ η ξ)) ⁻¹' Ici ε
  have hcρ : ContinuousOn (fun η => kgauge C.G (C.Θ η ξ)) K :=
    (G2.continuous_gauge C.G).continuousOn.comp
      ((C.contDiffOn_Θ_fst hξ).continuousOn.mono hKU) (fun _ _ => mem_univ _)
  have hLc : IsClosed L := hcρ.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici
  have hL : IsCompact L := hK.of_isClosed_subset hLc inter_subset_left
  have hLE : L ⊆ E := by
    intro η hη
    refine ⟨hη.1, ?_⟩
    intro he
    have heq : η = ξ := he
    have hz : C.Θ ξ ξ = 0 := theta_self hξ
    have hh : ε ≤ kgauge C.G (C.Θ η ξ) := hη.2
    rw [heq, hz, (kgauge_eq_zero_iff C.G 0).mpr rfl] at hh
    linarith
  have hiL : IntegrableOn f L volume :=
    (hf.mono hLE).integrableOn_compact hL
  have hEm : MeasurableSet E := hK.measurableSet.diff (measurableSet_singleton ξ)
  have hNm : MeasurableSet (E \ L) := hEm.diff hLc.measurableSet
  have hiN : IntegrableOn f (E \ L) volume := by
    have hm : IntegrableOn (fun η => M * kgauge C.G (C.Θ η ξ) ^ d) K volume :=
      (C.integrableOn_gauge_power_theta d hd ξ hξ K hK hKU).const_mul M
    have hmajor : IntegrableOn (fun η => M * kgauge C.G (C.Θ η ξ) ^ d) (E \ L) volume :=
      hm.mono_set (fun η (hη : η ∈ E \ L) => hη.1.1)
    apply MeasureTheory.Integrable.mono hmajor
      ((hf.mono (sdiff_subset : E \ L ⊆ E)).aestronglyMeasurable hNm)
    apply ae_restrict_of_forall_mem hNm
    intro η hη
    have hne : η ≠ ξ := fun he => hη.1.2 (mem_singleton_iff.mpr he)
    have hsmall : kgauge C.G (C.Θ η ξ) < ε := by
      by_contra hn
      exact hη.2 ⟨hη.1.1, not_lt.mp hn⟩
    have hh := hb η hη.1.1 hne hsmall
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hM (zpow_nonneg (kgauge_nonneg C.G _) _))]
    simpa only [Real.norm_eq_abs] using hh
  have heU : (E \ L) ∪ L = E := by
    ext η
    constructor
    · intro h
      exact h.elim (fun hn => hn.1) (fun hl => hLE hl)
    · intro h
      by_cases hl : η ∈ L
      · exact Or.inr hl
      · exact Or.inl ⟨h, hl⟩
  have hiE : IntegrableOn f E volume := by
    rw [← heU]
    exact hiN.union hiL
  have he : E =ᵐ[volume] K := by
    filter_upwards [volume.ae_ne ξ] with η hη
    simp [E, hη]
  exact (integrableOn_congr_set_ae he).mp hiE

end RothschildStein.P1.LiftedChart
