-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.AwayKernelL2
public import RothschildStein.H2.SupportedHolderSequence
public import RothschildStein.H2.OffDiagonalL2

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- Any continuous extension of the fixed-gauge PV on the dense
Hölder class has the absolutely convergent off-diagonal representation.
Buffered support approximation and L² pairings justify the passage to general inputs. -/
theorem LocalKernelData.offDiagonal_of_holder_formula (Q : LocalKernelData D d)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (S : Lp ℝ 2 (D.μ.restrict (ball Q.z Q.R)) →L[ℝ] Lp ℝ 2 (D.μ.restrict (ball Q.z Q.R)))
    (hS : ∀ f : holderFunctions δ (ball Q.z Q.R),
      (S (holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet Q.measure_ball_lt_top f) : X → ℝ)
        =ᵐ[D.μ.restrict (ball Q.z Q.R)] Q.principalValue f) :
    OffDiagonalL2 D (ball Q.z Q.R) Q.cutoffKernel S := by
  intro z _hz r hr hrκ v hv
  obtain ⟨f, hs, ht⟩ := Q.exists_supported_holder_sequence hδ hδ₁ z hr v hv
  let e := holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet Q.measure_ball_lt_top
  have hSt : Tendsto (fun n => S (e (f n))) atTop (𝓝 (S v)) := S.continuous.continuousAt.tendsto.comp ht
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hSt).exists_seq_tendsto_ae
  have hformula : ∀ᵐ y ∂D.μ.restrict (ball Q.z Q.R), ∀ n, (S (e (f n))) y = Q.principalValue (f n) y :=
    ae_all_iff.mpr (fun n => hS (f n))
  have hv₂ : ∀ᵐ x ∂D.μ.restrict (ball Q.z Q.R), x ∉ ball z (2 * r) → v x = 0 := by
    filter_upwards [hv] with x hx
    exact fun hn => hx (fun hb => hn (ball_subset_ball (by linarith) hb))
  filter_upwards [hae, hformula, ae_restrict_mem isOpen_ball.measurableSet] with y hy hfy hyU
  intro hyfar
  have hp := Q.away_integral_pairing z hr hrκ hyU hyfar (Lp.memLp v) hv₂
  refine ⟨hp.1, ?_⟩
  let k := Q.awayKernel z r y
  have hk := Q.awayKernel_memLp z hr hrκ hyU hyfar
  have hn : ∀ n, (∫ x in ball Q.z Q.R, Q.cutoffKernel y x * (f n : X → ℝ) x ∂D.μ) =
      inner ℝ (hk.toLp k) (e (f n)) := by
    intro n
    exact (Q.away_integral_pairing z hr hrκ hyU hyfar
      ((f n).property.1.memLp_two hδ isOpen_ball.measurableSet Q.measure_ball_lt_top)
      (ae_of_all _ (hs n))).2
  have hvinner : (∫ x in ball Q.z Q.R, Q.cutoffKernel y x * v x ∂D.μ) = inner ℝ (hk.toLp k) v := by
    have he : (Lp.memLp v).toLp (v : X → ℝ) = v := Lp.toLp_coeFn v (Lp.memLp v)
    simpa only [he] using hp.2
  have hint : Tendsto (fun n => ∫ x in ball Q.z Q.R, Q.cutoffKernel y x * (f (ns n) : X → ℝ) x ∂D.μ)
      atTop (𝓝 (∫ x in ball Q.z Q.R, Q.cutoffKernel y x * v x ∂D.μ)) := by
    rw [hvinner]
    have hi : Tendsto (fun n => inner ℝ (hk.toLp k) (e (f (ns n)))) atTop
        (𝓝 (inner ℝ (hk.toLp k) v)) :=
      (continuous_const.inner continuous_id).continuousAt.tendsto.comp (ht.comp hns.tendsto_atTop)
    exact hi.congr' (Eventually.of_forall (fun n => (hn (ns n)).symm))
  have heq : (fun n => (S (e (f (ns n)))) y) =ᶠ[atTop]
      (fun n => ∫ x in ball Q.z Q.R, Q.cutoffKernel y x * (f (ns n) : X → ℝ) x ∂D.μ) :=
    Eventually.of_forall (fun n => (hfy (ns n)).trans
      (Q.principalValue_away hδ (f (ns n)).property.1 z hr (hs (ns n)) hyU hyfar).2)
  exact tendsto_nhds_unique hy (hint.congr' heq.symm)

end RothschildStein.H2
