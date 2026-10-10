-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.FlowTestLimit
public import HeatKernel.Geometry.BoundedWeakLimits
public import RothschildStein.G2.InvariantDivergence
public import RothschildStein.S.WeakDeriv
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Bounded local weak derivatives of horizontally Lipschitz functions. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein Filter TopologicalSpace
open scoped NNReal ENNReal Topology BigOperators
namespace HeatKernel

/-- L² inner products can be computed using any almost-everywhere equal scalar representatives. -/
theorem inner_L2_eq_integral_mul_of_ae_eq {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (u v : Lp ℝ 2 μ) {f g : A → ℝ} (hu : u =ᵐ[μ] f) (hv : v =ᵐ[μ] g) :
    inner ℝ u v = ∫ x, g x * f x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu, hv] with x hx hy
  rw [hx, hy]
  rfl

/-- On every finite-volume open set a horizontal Lipschitz function has a weak derivative
in each constant horizontal direction, bounded by the Lipschitz constant times control norm. -/
theorem exists_bounded_local_weak_horizontal_derivative {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (b : Fin q → ℝ) (L : ℝ≥0) {f : (Fin N → ℝ) → ℝ}
    (hf : Continuous f)
    (hLip : ∀ x y, edist (f x) (f y) ≤ (L : ℝ≥0∞) * horizontalL2Distance (G.horizontalFields hq) x y)
    (U : Opens (Fin N → ℝ)) (hU : volume (U : Set (Fin N → ℝ)) ≠ ⊤) :
    ∃ g : (Fin N → ℝ) → ℝ,
      hasWeakWordDeriv (fun _ : Fin 1 => G2.leftField G (horizontalTangent hq b)) U [0] f g ∧
      ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), |g x| ≤ L * Real.sqrt (∑ i, b i ^ 2) := by
  let μ := volume.restrict (U : Set (Fin N → ℝ))
  let _ : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hU
  let _ : IsSeparable μ := isSeparable_of_sigmaFinite μ
  let _ : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let C : ℝ := L * Real.sqrt (∑ i, b i ^ 2)
  have hC : 0 ≤ C := mul_nonneg L.coe_nonneg (Real.sqrt_nonneg _)
  let τ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hτpos : ∀ n, 0 < τ n := fun n => by dsimp [τ]; positivity
  have hτ : Tendsto τ atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => (hτpos n).ne'⟩
  let F : ℕ → (Fin N → ℝ) → ℝ := fun n x =>
    (f (horizontalFlow G hq b x (-τ n)) - f x) / (-τ n)
  have hFbound : ∀ n x, |F n x| ≤ C := fun n x =>
    abs_horizontalFlow_differenceQuotient_le G hq b L f hLip x (neg_ne_zero.mpr (hτpos n).ne')
  have hFcont : ∀ n, Continuous (F n) := by
    intro n
    have hc : Continuous (fun x => horizontalFlow G hq b x (-τ n)) := by
      change Continuous (fun x => G.mul x (G2.leftExponential G (horizontalTangent hq b) (-τ n)))
      exact (G2.contDiff_rightTranslation G _).continuous
    exact ((hf.comp hc).sub hf).div_const _
  have hFp : ∀ n, MemLp (F n) 2 μ := fun n =>
    (memLp_const C).mono' (hFcont n).aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hFbound n x)
  let u : ℕ → Lp ℝ 2 μ := fun n => (hFp n).toLp (F n)
  have hu : ∀ n, u n =ᵐ[μ] F n := fun n => (hFp n).coeFn_toLp
  have hub : ∀ n, ∀ᵐ x ∂μ, |u n x| ≤ C := by
    intro n
    filter_upwards [hu n] with x hx
    rw [hx]
    exact hFbound n x
  have hψp : ∀ ψ : TestFunction U ℝ (⊤ : ℕ∞), MemLp (ψ : (Fin N → ℝ) → ℝ) 2 μ :=
    fun ψ => ψ.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport
  let v : TestFunction U ℝ (⊤ : ℕ∞) → Lp ℝ 2 μ := fun ψ => (hψp ψ).toLp ψ
  let ℓ : TestFunction U ℝ (⊤ : ℕ∞) → ℝ := fun ψ =>
    -(∫ x, f x * fieldDerivative (G2.leftField G (horizontalTangent hq b)) ψ x)
  have hpair : ∀ ψ, Tendsto (fun n => inner ℝ (v ψ) (u n)) atTop (𝓝 (ℓ ψ)) := by
    intro ψ
    have ht := (tendsto_integral_horizontalFlow_differenceQuotient_test G hq b hf
      ψ.contDiff ψ.hasCompactSupport).comp hτ
    apply ht.congr
    intro n
    have he := inner_L2_eq_integral_mul_of_ae_eq (v ψ) (u n) (hψp ψ).coeFn_toLp (hu n)
    rw [he]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := (U : Set (Fin N → ℝ)))
      (fun x hx => by simp [ψ.zero_on_compl hx])).symm
  obtain ⟨g, hg, hgp⟩ := exists_bounded_weak_limit_with_pairings u hC hub v ℓ hpair
  refine ⟨g, ⟨hf.continuousOn.locallyIntegrableOn U.isOpen.measurableSet,
    locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp g).locallyIntegrable (by norm_num)), ?_⟩, hg⟩
  intro ψ
  have he := inner_L2_eq_integral_mul_of_ae_eq (v ψ) g (hψp ψ).coeFn_toLp EventuallyEq.rfl
  have hp := hgp ψ
  rw [he] at hp
  change (∫ x, g x * ψ x ∂μ) =
    ∫ x, f x * wordTranspose (fun _ : Fin 1 => G2.leftField G (horizontalTangent hq b)) [0] ψ x ∂μ
  rw [hp]
  simp only [wordTranspose, G2.leftField_transpose G _ ψ ψ.contDiff, mul_neg, integral_neg]
  dsimp only [ℓ, μ]
  congr 1
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : fieldDerivative (G2.leftField G (horizontalTangent hq b)) ψ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hx (ψ.tsupport_subset
      (S.tsupport_fieldDerivative_subset _ _ ht)))
  rw [hz, mul_zero]

end HeatKernel
