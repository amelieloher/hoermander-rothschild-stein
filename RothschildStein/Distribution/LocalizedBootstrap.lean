-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.LocalizedMultiplier
public import Hormander.Statements.LocalRegularity
public import Hormander.Statements.ExistsContDiffOfMemSobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter SchwartzMap
open scoped Topology
namespace RothschildStein.Distribution

/-- A localized distribution satisfying the forcing identity has a
finite Sobolev starting order, and the local bootstrap yields smoothness. -/
theorem localizedDistribution_smooth_of_forcing {k N : ℕ}
    (Ω : TopologicalSpace.Opens (Fin N → ℝ))
    (χ : TestFunction Ω ℝ (⊤ : ℕ∞)) (T : Distribution Ω ℂ (⊤ : ℕ∞))
    (X : Fin (k + 1) → Hormander.A.Carrier N → Hormander.A.Carrier N)
    (c : Hormander.A.Carrier N → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c)
    {K U : Set (Hormander.A.Carrier N)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (w : Fin N → Hormander.Interface.LieWord k)
    (hw : ∀ x ∈ U, LinearIndependent ℝ (fun a => Hormander.lieWordEval X (w a) x))
    {ζ ζ' : Hormander.A.Carrier N → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζ' : ContDiff ℝ (⊤ : ℕ∞) ζ')
    (hζζ' : ∀ᶠ x in 𝓝ˢ (tsupport ζ), ζ' x = 1) (hζ'K : tsupport ζ' ⊆ K)
    (hg : (fun x : Fin N → ℝ => (ζ' (Hormander.F.coordinateEquiv N x) : ℂ)).HasTemperateGrowth)
    (hge : (fun x : Hormander.A.Carrier N => (ζ' x : ℂ)).HasTemperateGrowth)
    (f : SchwartzMap (Hormander.A.Carrier N) ℂ)
    (hf : TemperedDistribution.smulLeftCLM ℂ (fun x => (ζ' x : ℂ))
      (Hormander.hormanderOp X c (localizedTemperedEuclidean Ω χ T)) =
      (f : TemperedDistribution (Hormander.A.Carrier N) ℂ)) :
    ∃ F : Hormander.A.Carrier N → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ φ : SchwartzMap (Hormander.A.Carrier N) ℂ,
        Integrable (fun x => φ x * F x) ∧
        TemperedDistribution.smulLeftCLM ℂ (fun x => (ζ x : ℂ))
          (localizedTemperedEuclidean Ω χ T) φ = ∫ x, φ x * F x := by
  let a : (Fin N → ℝ) → ℝ := ζ' ∘ Hormander.F.coordinateEquiv N
  have ha : ContDiff ℝ (⊤ : ℕ∞) a := hζ'.comp (Hormander.F.coordinateEquiv N).contDiff
  have hmul := localizedTemperedEuclidean_mul Ω χ T a ha hg
    (by simpa only [a, Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using hge)
  have he : TemperedDistribution.smulLeftCLM ℂ (fun x => (ζ' x : ℂ))
      (localizedTemperedEuclidean Ω χ T) =
      localizedTemperedEuclidean Ω (testMultiplierOn Ω a ha.contDiffOn χ) T := by
    simpa only [a, Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using hmul
  obtain ⟨m, hm⟩ := localizedTemperedEuclidean_memSobolev_neg Ω
    (testMultiplierOn Ω a ha.contDiffOn χ) T
  have hs : (N : ℝ) < 2 * ((N : ℝ) + 1) := by linarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]
  have hstart := hm ((N : ℝ) + 1) hs
  rw [← he] at hstart
  have hall := Hormander.forall_memSobolev_of_localized X c hX hXc hc hcc hK hU hKU w hw
    hζ hζ' hζζ' hζ'K (localizedTemperedEuclidean Ω χ T) f hf hstart
  exact Hormander.exists_contDiff_of_forall_memSobolev hall

end RothschildStein.Distribution
