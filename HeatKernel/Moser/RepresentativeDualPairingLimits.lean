-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.DualPairingLimits
public import HeatKernel.Form.BochnerRepresentativeCompositionLimits

/-! # Integrated dual pairings of literal L² representatives -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace HeatKernel

/-- Strong L² limits of literal dual and test representatives preserve their integrated pairing. -/
theorem tendsto_integral_dual_apply_of_eLpNorm {α ι E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter ι} {F : ι → α → (E →L[ℝ] ℝ)} {v : ι → α → E}
    {F₀ : α → (E →L[ℝ] ℝ)} {v₀ : α → E}
    (hF : ∀ i, MemLp (F i) 2 μ) (hv : ∀ i, MemLp (v i) 2 μ)
    (hF₀ : MemLp F₀ 2 μ) (hv₀ : MemLp v₀ 2 μ)
    (hFlim : Tendsto (fun i => eLpNorm (F i - F₀) 2 μ) l (𝓝 0))
    (hvlim : Tendsto (fun i => eLpNorm (v i - v₀) 2 μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, F i x (v i x) ∂μ) l (𝓝 (∫ x, F₀ x (v₀ x) ∂μ)) := by
  have h := tendsto_integral_dual_apply_of_tendsto_L2
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF F₀ hF₀).mpr hFlim)
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v hv v₀ hv₀).mpr hvlim)
  have he : ∀ i, (∫ x, (hF i).toLp (F i) x ((hv i).toLp (v i) x) ∂μ) =
      ∫ x, F i x (v i x) ∂μ := by
    intro i
    apply integral_congr_ae
    filter_upwards [(hF i).coeFn_toLp, (hv i).coeFn_toLp] with x hx hy
    rw [hx, hy]
  have he₀ : (∫ x, hF₀.toLp F₀ x (hv₀.toLp v₀ x) ∂μ) = ∫ x, F₀ x (v₀ x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hF₀.coeFn_toLp, hv₀.coeFn_toLp] with x hx hy
    rw [hx, hy]
  simpa only [he, he₀] using h

/-- Eventual square integrability suffices for convergence of integrated dual pairings. -/
theorem tendsto_integral_dual_apply_of_eventually_memLp {α ι E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter ι} {F : ι → α → (E →L[ℝ] ℝ)} {v : ι → α → E}
    {F₀ : α → (E →L[ℝ] ℝ)} {v₀ : α → E}
    (hF : ∀ᶠ i in l, MemLp (F i) 2 μ) (hv : ∀ᶠ i in l, MemLp (v i) 2 μ)
    (hF₀ : MemLp F₀ 2 μ) (hv₀ : MemLp v₀ 2 μ)
    (hFlim : Tendsto (fun i => eLpNorm (F i - F₀) 2 μ) l (𝓝 0))
    (hvlim : Tendsto (fun i => eLpNorm (v i - v₀) 2 μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, F i x (v i x) ∂μ) l (𝓝 (∫ x, F₀ x (v₀ x) ∂μ)) := by
  classical
  let F' := fun i => if MemLp (F i) 2 μ then F i else F₀
  let v' := fun i => if MemLp (v i) 2 μ then v i else v₀
  have hF' : ∀ i, MemLp (F' i) 2 μ := by
    intro i
    by_cases hi : MemLp (F i) 2 μ
    · simp only [F', hi, ↓reduceIte]
    · simpa only [F', hi, ↓reduceIte] using hF₀
  have hv' : ∀ i, MemLp (v' i) 2 μ := by
    intro i
    by_cases hi : MemLp (v i) 2 μ
    · simp only [v', hi, ↓reduceIte]
    · simpa only [v', hi, ↓reduceIte] using hv₀
  have heF : F' =ᶠ[l] F := hF.mono fun i hi => by simp only [F', hi, ↓reduceIte]
  have hev : v' =ᶠ[l] v := hv.mono fun i hi => by simp only [v', hi, ↓reduceIte]
  have hFlim' : Tendsto (fun i => eLpNorm (F' i - F₀) 2 μ) l (𝓝 0) :=
    hFlim.congr' (heF.symm.mono fun i hi => congrArg (fun f => eLpNorm (f - F₀) 2 μ) hi)
  have hvlim' : Tendsto (fun i => eLpNorm (v' i - v₀) 2 μ) l (𝓝 0) :=
    hvlim.congr' (hev.symm.mono fun i hi => congrArg (fun f => eLpNorm (f - v₀) 2 μ) hi)
  apply (tendsto_integral_dual_apply_of_eLpNorm hF' hv' hF₀ hv₀ hFlim' hvlim').congr'
  filter_upwards [heF, hev] with i hi hj
  rw [hi, hj]

end HeatKernel
