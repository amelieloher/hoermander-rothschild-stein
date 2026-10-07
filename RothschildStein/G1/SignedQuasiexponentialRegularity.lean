-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SignedQuasiexponentialZero
public import RothschildStein.G1.FlatParameterRegularity
public import RothschildStein.G1.TimePiecewiseC1
public import RothschildStein.G1.WeightedAbsolutePowers

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.G1

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Matching signed factors yield joint C¹ regularity when the
normalized root derivative extends continuously to zero
(BB Thm 1.48, pp. 32–34). -/
theorem signedFactoredMap_contDiff_one
    (Hp Hm : P × E → E) (τ ρ dτ : ℝ → P)
    (hHp : ContDiff ℝ 1 Hp) (hHm : ContDiff ℝ 1 Hm)
    (hmatch : ∀ x, -Hm (0, x) = Hp (0, x))
    (hτ : Continuous τ) (hρ : Continuous ρ) (hτ0 : τ 0 = 0) (hρ0 : ρ 0 = 0)
    (hdτ : ∀ h : ℝ, h ≠ 0 → HasDerivAt τ (dτ h) h)
    (hnorm : ∀ h : ℝ, h ≠ 0 → h • dτ h = ρ h) :
    ContDiff ℝ 1 (signedFactoredMap Hp Hm τ) := by
  let Fp : ℝ × E → E := fun q => q.2 + q.1 • Hp (τ q.1, q.2)
  let Fn : ℝ × E → E := fun q => q.2 + q.1 • -Hm (τ q.1, q.2)
  have hFp : ContDiff ℝ 1 Fp :=
    factoredParameter_contDiff_one Hp τ ρ dτ hHp hτ hρ hτ0 hρ0 hdτ hnorm
  have hFn : ContDiff ℝ 1 Fn :=
    factoredParameter_contDiff_one (fun z => -Hm z) τ ρ dτ hHm.neg hτ hρ hτ0 hρ0 hdτ hnorm
  have hval : ∀ x, Fp (0, x) = Fn (0, x) := fun x => by simp [Fp, Fn]
  have hderiv : ∀ x, fderiv ℝ Fp (0, x) = fderiv ℝ Fn (0, x) := by
    intro x
    have hp := (factoredParameter_hasFDerivAt_zero
      (fun q : ℝ × E => Hp (τ q.1, q.2)) x
      ((hHp.continuous.comp ((hτ.comp continuous_fst).prodMk continuous_snd)).continuousAt)).fderiv
    have hm := (factoredParameter_hasFDerivAt_zero
      (fun q : ℝ × E => -Hm (τ q.1, q.2)) x
      ((hHm.continuous.comp ((hτ.comp continuous_fst).prodMk continuous_snd)).neg.continuousAt)).fderiv
    simp only [hτ0, hmatch x] at hp hm
    exact hp.trans hm.symm
  have hh := timePiecewise_contDiff_one Fp Fn hFp hFn hval hderiv
  have heq : signedFactoredMap Hp Hm τ =
      (fun q : ℝ × E => if 0 ≤ q.1 then Fp q else Fn q) := by
    funext q
    dsimp [signedFactoredMap, Fp, Fn]
    split_ifs with hq
    · rfl
    · rw [abs_of_neg (lt_of_not_ge hq), neg_smul, smul_neg]
  rwa [heq]

/-- The actual weighted absolute root powers give jointly C¹ signed
quasiexponentials from C¹ product factors with opposite initial coefficients
(BB Thm 1.48, pp. 32–34). -/
theorem signedWeightedFactoredMap_contDiff_one {n : ℕ}
    (Hp Hm : (Fin n → ℝ) × E → E) (α : Fin n → ℝ)
    (hHp : ContDiff ℝ 1 Hp) (hHm : ContDiff ℝ 1 Hm)
    (hmatch : ∀ x, -Hm (0, x) = Hp (0, x)) (hα : ∀ i, 0 < α i) :
    ContDiff ℝ 1 (signedFactoredMap Hp Hm (weightedAbsolutePowers α)) :=
  signedFactoredMap_contDiff_one Hp Hm _ _ _ hHp hHm hmatch
    (weightedAbsolutePowers_continuous α hα) (weightedPowerRate_continuous α hα)
    (weightedAbsolutePowers_zero α hα) (weightedPowerRate_zero α hα)
    (fun _ hh => weightedAbsolutePowers_hasDerivAt α hh)
    (fun _ hh => weightedPowerDerivative_normalized α hh)

end RothschildStein.G1
