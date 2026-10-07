-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.ZeroExtendedCommutatorRepresentation
public import RothschildStein.S.KernelLpLocal
public import RothschildStein.S.MollifierLocalConvergence
public import RothschildStein.S.LpListSums

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Filter Metric TopologicalSpace
open scoped ENNReal Topology ContDiff
namespace RothschildStein.S
variable {n q : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Each classical word of the zero-extended mollifier converges
in local finite Lp to its weak word derivative. Only weak subwords and
local Lp input hypotheses enter; coefficient germs are fixed independently
of the input (BB Thm 2.9, p. 73; (2.9)–(2.12), pp. 77–79). -/
theorem tendsto_weakWord_mollifier_error_of_coefficient_germs
    (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) (Ω : Set (Fin n → ℝ)))
    (B : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hB : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (B j))
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hc : IsCompact (closure U))
    {δ : ℝ} (hd : 0 < δ) (hδ : cthickening δ (closure U) ⊆ Ω)
    (hG : ∀ j z, z ∈ cthickening δ (closure U) → B j =ᶠ[𝓝 z] X j)
    (hpt : p ≠ ⊤) (I : List (Fin q)) (f : (Fin n → ℝ) → ℝ)
    (jet : List (Fin q) → (Fin n → ℝ) → ℝ) (hzero : jet [] = f)
    (hw : ∀ J, J.Sublist I → hasWeakWordDeriv X Ω J f (jet J))
    (hLp : ∀ J, J.Sublist I → MemLp (jet J) p (volume.restrict (Ω : Set (Fin n → ℝ)))) :
    Tendsto (fun ε : ℝ => eLpNorm
      (fun x => wordDerivative X I (euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator f) ε) x-jet I x)
      p (volume.restrict U)) (𝓝[>] 0) (𝓝 0) := by
  let pairs := smoothFriedrichsCommutatorPairs B hB I
  let err := fun ε x => (pairs.map (fun r => friedrichsKernelOp r.1.family (jet r.2) ε x)).sum
  let base := fun ε x => euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator (jet I)) ε x-jet I x
  have ht : ∀ r ∈ pairs, Tendsto
      (fun ε : ℝ => eLpNorm (friedrichsKernelOp r.1.family (jet r.2) ε) p (volume.restrict U))
      (𝓝[>] 0) (𝓝 0) := by
    intro r hr
    have hs := (friedrichsCommutatorPairs_subword _ _ I hr).1
    exact tendsto_eLpNorm_smoothFriedrichsKernelOp_zero_local Ω r.1 hU hc hd hδ
      (smoothFriedrichsCommutatorPairs_hasVanishingMean B hB I hr U hc δ) hpt (hLp r.2 hs)
  have hterr : Tendsto (fun ε : ℝ => eLpNorm (err ε) p (volume.restrict U))
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_eLpNorm_listSum_zero Fact.out pairs
      (fun r ε => friedrichsKernelOp r.1.family (jet r.2) ε) ht
  have hUΩ : U ⊆ Ω := by
    intro x hx
    exact hδ (mem_cthickening_of_dist_le x x δ (closure U) (subset_closure hx)
      (by simpa only [dist_self] using hd.le))
  have htbase : Tendsto (fun ε : ℝ => eLpNorm (base ε) p (volume.restrict U))
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_regularize_zeroExtension_local Ω hU.measurableSet hUΩ Fact.out hpt
      (hLp I (List.Sublist.refl I))
  have H : Tendsto (fun ε : ℝ => eLpNorm (err ε) p (volume.restrict U) +
      eLpNorm (base ε) p (volume.restrict U)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_add] using hterr.add htbase
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds H
  · exact Eventually.of_forall (fun _ => zero_le)
  · filter_upwards [Ioo_mem_nhdsGT hd] with ε hε
    have he : eLpNorm
        (fun x => wordDerivative X I (euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator f) ε) x-jet I x)
        p (volume.restrict U) = eLpNorm (err ε+base ε) p (volume.restrict U) := by
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      have hr := zeroExtended_commutator_representation Ω X hX B hB hU hc hε hδ hG I f jet hzero hw hx
      change _ = err ε x + base ε x
      dsimp [err,base,pairs]
      linarith
    rw [he]
    exact eLpNorm_add_le Fact.out

end RothschildStein.S
