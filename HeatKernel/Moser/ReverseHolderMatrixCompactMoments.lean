-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderSmoothCutoffBudgets
public import HeatKernel.Moser.ReverseHolderPowerMomentRepresentatives
public import HeatKernel.Moser.ReverseHolderParabolicMoment
public import HeatKernel.Moser.MeanValueMatrixCutoffPair
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic

/-! Uniform backward small-power moments of matrix weak solutions. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- Nonnegative matrix weak solutions satisfy the backward parabolic moment
estimate on compact interior cylinders. The same Sobolev constant works for
every small positive power. Smooth nested spatial cutoffs, a compact outer
region, and a top-vanishing time cutoff are the explicit geometric inputs. -/
theorem exists_uniform_matrix_reverse_holder_compact_moment_constant {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (ell upper : ℝ), 0 < ell → 0 ≤ upper →
      ∀ (I : Opens ℝ) (U V : Opens (Fin N → ℝ)),
      volume (V : Set (Fin N → ℝ)) ≠ ⊤ →
      ∀ (u : ℝ → (Fin N → ℝ) → ℝ)
        (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ),
      IsLocalWeakSolution G hq hqpos hw hspan coeff I U u →
      (∀ᵐ z : ℝ × (Fin N → ℝ)
        ∂volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))), 0 ≤ u z.1 z.2) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      ∀ A B a b : ℝ, Icc A B ⊆ (I : Set ℝ) → a < b → A < a → b < B →
      ∀ K : Set (Fin N → ℝ), IsCompact K → K ⊆ (U : Set (Fin N → ℝ)) →
      ∀ φ η : (Fin N → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → (∀ x, φ x ∈ Icc (0 : ℝ) 1) →
      HasCompactSupport φ → tsupport φ ⊆ K → tsupport φ ⊆ (V : Set (Fin N → ℝ)) →
      ContDiff ℝ (⊤ : ℕ∞) η → (∀ x, η x ∈ Icc (0 : ℝ) 1) →
      HasCompactSupport η → tsupport η ⊆ (V : Set (Fin N → ℝ)) →
      (∀ x ∈ tsupport η, φ x = 1 ∧
        ∀ i, fieldDerivative (G.horizontalFields hq i) φ x = 0) →
      ∀ L : ℝ, 0 ≤ L →
      (∀ x, coordinateNormSq (fun i => fieldDerivative (G.horizontalFields hq i) η x) ≤ L) →
      ∀ θ : ℝ → ℝ, ContDiff ℝ 1 θ → θ b = 0 →
      (∀ t ∈ Icc a b, θ t ∈ Icc (0 : ℝ) 1) →
      ∀ H : ℝ, 0 ≤ H → (∀ t ∈ Icc a b, -(deriv (fun s => θ s ^ 2) t) ≤ H) →
      ∀ p c : ℝ, 0 < p → p ≤ 1 / 2 → 0 < c →
      (∫⁻ t in Icc a b, ∫⁻ x,
        ‖θ t * η x * (u t x + c) ^ (p / 2)‖ₑ ^ (2 + 4 / ν) ∂volume) ≤
          ENNReal.ofReal C *
            (ENNReal.ofReal ((H + 2 * (upper * L)) + (H + 2 * (upper * L)) / ell + 2 * L + 1) *
              ENNReal.ofReal (∫ t in Icc a b, ∫ x in K, (u t x + c) ^ p)) ^ (1 + 2 / ν) := by
  obtain ⟨C, hC, hSob⟩ := exists_uniform_reverse_holder_parabolic_moment_constant
    G hq hqpos hspan hw hν
  refine ⟨C, hC, ?_⟩
  intro ell upper hell hupper I U V hfinite u coeff hu hu0 ha hbound A B a b hJI hab hAa hbB
    K hK hKU φ η hφ hφunit hcφ hφK hφV hη hηunit hcη hηV hplateau
    L hL hdL θ hθ hθb hθunit H hH hθd p c hp hp2 hc
  have hX := G.horizontalFields_contDiff hq
  obtain ⟨g, v, F, hinterface, hpair, _⟩ := hu.exists_smooth_cutoff_energy_pair
    G hq hqpos hw hspan coeff I U V ha hell.le hbound hu0 hJI
    hφ hφunit hcφ (hφK.trans hKU) hφV
  have hbound' : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
      (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
        ell * coordinateNormSq ξ ≤ matrixEnergy (coeff z.1 z.2) ξ ∧
        matrixEnergy (coeff z.1 z.2) ξ ≤ upper * coordinateNormSq ξ := by
    filter_upwards [hbound] with z hz
    refine ⟨hz.1, fun ξ => ?_⟩
    simpa only [matrixEnergy, coordinateNormSq, mul_assoc, mul_left_comm, mul_comm] using hz.2 ξ
  obtain ⟨Y, e, D, R, hbudget, hrep⟩ :=
    hinterface.exists_reverse_holder_smooth_cutoff_budgets hX
      hu.1 hu0 ha hell hupper hc hp hp2 hbound' hJI hab hAa hbB
      hK hKU hφK hφunit hη hcη hηV hηunit hplateau hL hdL hpair
      hθ hθb hθunit hH hθd
  have hmoment := hSob hfinite Y θ e D R
    (fun t => ∫ x in K, (u t x + c) ^ p) hbudget
  dsimp only at hmoment
  have heq := lintegral_smul_graph_value_rpow_eq θ (2 + 4 / ν) hrep
  rw [heq] at hmoment
  simpa only [mul_assoc] using hmoment

end HeatKernel
