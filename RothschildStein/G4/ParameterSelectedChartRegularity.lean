-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ContinuousSelectedChartDerivative

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G4

/-- Pull back the actual full state derivative to selected
coefficients and continuous external/initial-point parameters. Openness
supplies local differentiability near zero (BB p. 452). -/
theorem parameter_selected_chart_local_regularity {Sg P E : Type*} {n m : ℕ}
    [TopologicalSpace Sg] [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set Sg} {V : Set ((Fin (n + m) → ℝ) × E)} (hU : IsOpen U) (hV : IsOpen V)
    (F : Sg → ((Fin (n + m) → ℝ) × E) → E)
    (hF : ∀ σ ∈ U, ∀ z ∈ V, DifferentiableAt ℝ (F σ) z)
    (hD : ContinuousOn (fun q : Sg × ((Fin (n + m) → ℝ) × E) =>
      fderiv ℝ (F q.1) q.2) (U ×ˢ V))
    (σ : P → Sg) (x : P → E) (hσ : Continuous σ) (hx : Continuous x)
    (p : P) (hpσ : σ p ∈ U) (hpx : (Fin.append (0 : Fin n → ℝ) (0 : Fin m → ℝ), x p) ∈ V) :
    (∀ᶠ q : (Fin n → ℝ) × P in 𝓝 (0, p),
      DifferentiableAt ℝ (fun u => F (σ q.2) (Fin.append u 0, x q.2)) q.1) ∧
    ContinuousAt (fun q : (Fin n → ℝ) × P =>
      fderiv ℝ (fun u => F (σ q.2) (Fin.append u 0, x q.2)) q.1) (0, p) := by
  let T : Set (Sg × (((Fin n → ℝ) × (Fin m → ℝ)) × E)) :=
    {q | q.1 ∈ U ∧ (Fin.append q.2.1.1 q.2.1.2, q.2.2) ∈ V}
  have hi : Continuous
      (fun q : Sg × (((Fin n → ℝ) × (Fin m → ℝ)) × E) =>
        (q.1, (Fin.append q.2.1.1 q.2.1.2, q.2.2))) :=
    continuous_fst.prodMk (((Fin.continuous_append n m).comp continuous_snd.fst).prodMk
      continuous_snd.snd)
  have hT : IsOpen T := (hU.prod hV).preimage hi
  have hselected := selected_chart_fderiv_joint_continuousOn (T := T) F hD
    (fun q hq => hF q.1 hq.1 q.2 hq.2) (fun q hq => hq)
  have hpoint : (σ p, (((0 : Fin n → ℝ), (0 : Fin m → ℝ)), x p)) ∈ T := ⟨hpσ, hpx⟩
  have hinput : Continuous
      (fun q : (Fin n → ℝ) × P => (σ q.2, ((q.1, (0 : Fin m → ℝ)), x q.2))) :=
    (hσ.comp continuous_snd).prodMk
      ((continuous_fst.prodMk continuous_const).prodMk (hx.comp continuous_snd))
  have hnear : ∀ᶠ q : (Fin n → ℝ) × P in 𝓝 (0, p),
      (σ q.2, ((q.1, (0 : Fin m → ℝ)), x q.2)) ∈ T :=
    hinput.continuousAt.eventually (hT.mem_nhds hpoint)
  refine ⟨?_, ?_⟩
  · filter_upwards [hnear] with q hq
    have hfull := hF (σ q.2) hq.1 (Fin.append q.1 0, x q.2) hq.2
    have hcoef : DifferentiableAt ℝ
        (fun a : Fin (n + m) → ℝ => F (σ q.2) (a, x q.2)) (Fin.append q.1 0) :=
      (hfull.hasFDerivAt.comp (Fin.append q.1 0)
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) (Fin.append q.1 (0 : Fin m → ℝ)) (x q.2))).differentiableAt
    have happend : DifferentiableAt ℝ (fun u : Fin n → ℝ => Fin.append u (0 : Fin m → ℝ)) q.1 := by
      have hh : DifferentiableAt ℝ (fun u : Fin n → ℝ =>
          selectedCoefficientInclusion n m u + Fin.append (0 : Fin n → ℝ) (0 : Fin m → ℝ)) q.1 :=
        (selectedCoefficientInclusion n m).differentiableAt.add_const _
      simpa only [← selectedCoefficient_append_affine] using hh
    exact hcoef.comp q.1 (g := fun a : Fin (n + m) → ℝ => F (σ q.2) (a, x q.2))
      (f := fun u : Fin n → ℝ => Fin.append u (0 : Fin m → ℝ)) happend
  · have hd := hselected.continuousAt (hT.mem_nhds hpoint)
    exact hd.comp (f := fun q : (Fin n → ℝ) × P =>
      (σ q.2, ((q.1, (0 : Fin m → ℝ)), x q.2))) (x := (0, p)) hinput.continuousAt

end RothschildStein.G4
