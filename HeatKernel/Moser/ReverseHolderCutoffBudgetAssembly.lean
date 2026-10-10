-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderPlateauEnergyBudget
public import HeatKernel.Moser.ReverseHolderSobolevCurve
public import HeatKernel.Moser.ReverseHolderLocalizedEnergy
public import HeatKernel.Moser.ReverseHolderSpacetimeMoments
public import HeatKernel.Moser.ReverseHolderDiffusionMeasurability
public import HeatKernel.Bridge.SquareIntegrableSlices
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic

/-! Backward graph budgets from the weak time equation and spatial cutoff data. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

private theorem ae_affine_graph_energy_bounds {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {τ : Measure ℝ} {u : ℝ → (Fin N → ℝ) → ℝ}
    {g : Fin q → ℝ → (Fin N → ℝ) → ℝ} {φ : (Fin N → ℝ) → ℝ}
    {k : Fin q → (Fin N → ℝ) → ℝ} {v : ℝ → zeroBoundaryGraph V X}
    {c p ell L Kd : ℝ} (hc : 0 < c) (hp : 0 < p) (hp2 : p ≤ 1 / 2) (hell : 0 < ell)
    (w : zeroBoundaryGraph V X)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (hdw : ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i)
    (hplateau : ∀ x, W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0) →
      φ x = 1 ∧ ∀ i, k i x = 0)
    (hWb : ∀ᵐ x ∂volume, ‖W.toFun x‖ ≤ 1)
    (hd : ∀ i, MemLp (W.gradient i) 2 volume)
    (hdbound : ∀ i, ∀ᵐ x ∂volume, ‖W.gradient i x‖ ≤ Kd)
    (hvalue : ∀ᵐ t ∂τ, (v t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => u t x * φ x)
    (hgradient : ∀ᵐ t ∂τ, ∀ i, (v t : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => g i t x * φ x + u t x * k i x)
    (hdata : ∀ᵐ t ∂τ, (∀ᵐ x ∂volume, 0 ≤ (v t : GradientSpace (N := N) ⊤ q).fst x) ∧
      MemLp (u t) 2 volume ∧ (∀ᵐ x ∂volume, 0 ≤ u t x) ∧ ∀ i, MemLp (g i t) 2 volume)
    {m : ℝ → ℝ} (hcutMoment : ∀ᵐ t ∂τ,
      (∫ x, (u t x + c) ^ p * coordinateNormSq (fun i => W.gradient i x)) ≤ L * m t) :
    ∀ᵐ t ∂τ,
      let Y := W.affineEnergyMap hX
        (shiftedRpowWeakSolutionTest hc (p := p / 2) (by linarith)) w (c ^ (p / 2)) (v t)
      ‖(Y : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 =
          (∫ x, W.toFun x ^ 2 * (u t x + c) ^ p) ∧
      ‖(Y : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 ≤
        (∫ x, 2 * ell * (p / 2) ^ 2 * coordinateNormSq
          (fun i => W.toFun x * ((u t x + c) ^ (p / 2 - 1) * g i t x))) / ell +
            2 * L * m t := by
  filter_upwards [hdata, hvalue, hgradient, hcutMoment] with t ht hvt hgt hmt
  exact W.reverse_holder_affine_graph_energy_bounds hX hc hp2 hell (v t) w ht.1
    hw hdw hvt hgt hplateau ht.2.1.aestronglyMeasurable ht.2.2.1 hWb ht.2.2.2
    (fun i => memLp_shifted_small_power_mul hc (by positivity : 0 ≤ p / 2)
      (by linarith : p / 2 ≤ 1) ht.2.1 ht.2.2.1 (hd i) (hdbound i)) hmt

/-- Spatial localization and linear energy data for a backward small-power test.
The fields list the geometric and form inputs explicitly; none assumes a
nonlinear diffusion budget or a higher-moment estimate. -/
structure HasReverseHolderCutoffAssemblyData {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (u : ℝ → (Fin N → ℝ) → ℝ) (g : Fin q → ℝ → (Fin N → ℝ) → ℝ)
    (φ : (Fin N → ℝ) → ℝ) (k : Fin q → (Fin N → ℝ) → ℝ)
    (v : ℝ → zeroBoundaryGraph V X) (F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ))
    (W S : WeakSolutionSpatialWeight V X) (w ws : zeroBoundaryGraph V X)
    (Ω : Set (Fin N → ℝ)) (θ : ℝ → ℝ) (A B a b c C Kd ell upper p H L : ℝ) : Prop where
  weak_pair : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F
  shift_pos : 0 < c
  ellipticity_pos : 0 < ell
  upper_nonneg : 0 ≤ upper
  power_pos : 0 < p
  power_le_half : p ≤ 1 / 2
  interval_lt : a < b
  earlier_lt : A < a
  later_lt : b < B
  value_rep : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun
  gradient_rep : ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i
  square_value_rep : (ws : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] S.toFun
  square_gradient_rep : ∀ i, (ws : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] S.gradient i
  square_weight_value : ∀ x, S.toFun x = W.toFun x ^ 2
  square_weight_gradient : ∀ i x, S.gradient i x = 2 * W.toFun x * W.gradient i x
  square_weight_integrable : Integrable S.toFun volume
  plateau : ∀ x, W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0) →
    φ x = 1 ∧ ∀ i, k i x = 0
  region_measurable : MeasurableSet Ω
  region_finite : volume Ω ≠ ⊤
  cutoff_unit : ∀ x, W.toFun x ∈ Icc (0 : ℝ) 1
  value_support : ∀ x ∉ Ω, W.toFun x = 0
  cutoff_gradient_memLp : ∀ i, MemLp (W.gradient i) 2 volume
  gradient_support : ∀ i x, x ∉ Ω → W.gradient i x = 0
  gradient_bound : ∀ i, ∀ᵐ x ∂volume, ‖W.gradient i x‖ ≤ Kd
  gradient_cost_nonneg : 0 ≤ L
  gradient_normSq_le : ∀ᵐ x ∂volume, coordinateNormSq (fun i => W.gradient i x) ≤ L
  value_memLp : MemLp (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) 2
    ((volume.restrict (Icc a b)).prod volume)
  gradient_memLp : ∀ i, MemLp (fun z : ℝ × (Fin N → ℝ) => g i z.1 z.2) 2
    ((volume.restrict (Icc a b)).prod volume)
  value_nonneg : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂(volume.restrict (Icc a b)).prod volume, 0 ≤ u z.1 z.2
  curve_nonneg : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ᵐ x ∂volume,
    0 ≤ (v t : GradientSpace (N := N) ⊤ q).fst x
  coefficient_slices : ∀ᵐ t ∂volume.restrict (Icc a b),
    (∀ i j, AEStronglyMeasurable (fun x => coeff t x i j) volume) ∧
    (∀ i j, ∀ᵐ x ∂volume, ‖coeff t x i j‖ ≤ C) ∧
    (∀ᵐ x ∂volume, (∀ i j, coeff t x i j = coeff t x j i) ∧ ∀ ξ : Fin q → ℝ,
      ell * coordinateNormSq ξ ≤ matrixEnergy (coeff t x) ξ ∧
      matrixEnergy (coeff t x) ξ ≤ upper * coordinateNormSq ξ)
  time_cutoff_contDiff : ContDiff ℝ 1 θ
  time_cutoff_top : θ b = 0
  time_cutoff_unit : ∀ t ∈ Icc a b, θ t ∈ Icc (0 : ℝ) 1
  time_cost_nonneg : 0 ≤ H
  neg_deriv_sq_le : ∀ t ∈ Icc a b, -(deriv (fun s => θ s ^ 2) t) ≤ H

private theorem backward_initial_budgets_of_assembly_data {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X} {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)}
    {A B a b c C Kd ell upper p H L : ℝ}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (W S : WeakSolutionSpatialWeight V X) (w ws : zeroBoundaryGraph V X)
    {Ω : Set (Fin N → ℝ)} {θ : ℝ → ℝ}
    (h : HasReverseHolderCutoffAssemblyData coeff u g φ k v F W S w ws Ω θ
      A B a b c C Kd ell upper p H L)
    (hR : IntegrableOn (fun t => ∫ x, 2 * upper * (u t x + c) ^ p *
      coordinateNormSq (fun i => W.gradient i x)) (Icc a b)) :
    let D := fun t => ∫ x, 2 * ell * (p / 2) ^ 2 * coordinateNormSq
      (fun i => W.toFun x * ((u t x + c) ^ (p / 2 - 1) * g i t x))
    let R := fun t => ∫ x, 2 * upper * (u t x + c) ^ p *
      coordinateNormSq (fun i => W.gradient i x)
    IntegrableOn D (Icc a b) ∧ ∃ e : ℝ → ℝ,
      e =ᵐ[volume.restrict (Icc a b)] (fun t => ∫ x, W.toFun x ^ 2 * (u t x + c) ^ p) ∧
      ∀ s ∈ Icc a b, θ s ^ 2 * e s + (∫ t in s..b, θ t ^ 2 * D t) ≤
        (∫ t in s..b, -(deriv (fun s => θ s ^ 2) t) * e t) + ∫ t in s..b, θ t ^ 2 * R t := by
  rcases h with ⟨hpair, hc, hell, hupper, hp, hp2, hab, hAa, hbB,
    hw, hdw, hws, hdws, hS, hSd, hSint, hplateau, hΩ, hΩfinite, hWunit, hWsupport,
    hd, hdsupport, hdbound, hL, hdL, hu, hg, hu0, hz, hcoeff, hθ, hθb, hθunit, hH, hθd⟩
  let : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hΩfinite.lt_top⟩
  dsimp only
  have hWb : ∀ᵐ x ∂volume, ‖W.toFun x‖ ≤ 1 := Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_of_nonneg (hWunit x).1] using (hWunit x).2
  have huSlices := ae_memLp_two_slice hu
  have hgSlices := ae_all_iff.mpr (fun i => ae_memLp_two_slice (hg i))
  have huPos := Measure.ae_ae_of_ae_prod hu0
  have hdata : ∀ᵐ t ∂volume.restrict (Icc a b),
      (∀ᵐ x ∂volume, 0 ≤ (v t : GradientSpace (N := N) ⊤ q).fst x) ∧
      AEStronglyMeasurable (u t) volume ∧ (∀ᵐ x ∂volume, 0 ≤ u t x) ∧
      (∀ i j, AEStronglyMeasurable (fun x => coeff t x i j) volume) ∧
      (∀ i j, ∀ᵐ x ∂volume, ‖coeff t x i j‖ ≤ C) ∧
      (∀ i, MemLp (g i t) 2 volume) ∧
      (∀ᵐ x ∂volume, (∀ i j, coeff t x i j = coeff t x j i) ∧ ∀ ξ : Fin q → ℝ,
        ell * coordinateNormSq ξ ≤ matrixEnergy (coeff t x) ξ ∧
        matrixEnergy (coeff t x) ξ ≤ upper * coordinateNormSq ξ) := by
    filter_upwards [hz, huSlices, huPos, hgSlices, hcoeff] with t hzt hut hupt hgt hct
    exact ⟨hzt, hut.aestronglyMeasurable, hupt, hct.1, hct.2.1, hgt, hct.2.2⟩
  have hSp : ∀ x, S.toFun x ≠ 0 ∨ (∃ i, S.gradient i x ≠ 0) →
      φ x = 1 ∧ ∀ i, k i x = 0 := by
    intro x hx
    apply hplateau x
    left
    intro hzero
    rcases hx with hx | ⟨i, hi⟩
    · exact hx (by rw [hS, hzero, zero_pow (by decide : 2 ≠ 0)])
    · exact hi (by rw [hSd, hzero, mul_zero, zero_mul])
  have hDmeas : AEStronglyMeasurable
      (fun t => ∫ x, 2 * ell * (p / 2) ^ 2 * coordinateNormSq
        (fun i => W.toFun x * ((u t x + c) ^ (p / 2 - 1) * g i t x)))
      (volume.restrict (Icc a b)) :=
    aestronglyMeasurable_reverse_holder_diffusion
      (T := ℝ) (α := Fin N → ℝ) (ι := Fin q)
      (τ := volume.restrict (Icc a b)) (μ := volume)
      (u := fun z => u z.1 z.2) (g := fun i z => g i z.1 z.2) (η := W.toFun)
      c p ell hu.aestronglyMeasurable
      (fun i => (hg i).aestronglyMeasurable) W.aestronglyMeasurable
  have hχ : ContDiff ℝ 1 (fun t => θ t ^ 2) := hθ.pow 2
  have hχb : (fun t => θ t ^ 2) b = 0 := by
    simp only [hθb, zero_pow (by decide : 2 ≠ 0)]
  have hχpos : ∀ᵐ t ∂volume, 0 ≤ θ t ^ 2 :=
    Filter.Eventually.of_forall fun t => sq_nonneg (θ t)
  obtain ⟨hD, e, _, heq, hbudget⟩ := exists_reverse_holder_initial_energy_budgets_of_plateau
    (N := N) (q := q) (V := V) (X := X) (coeff := coeff) (u := u) (g := g)
    (φ := φ) (η := W.toFun) (k := k) (d := W.gradient) (v := v) (F := F)
    (A := A) (B := B) (a := a) (b := b) (c := c) (C := C) (K := 1) (Kd := Kd)
    (ell := ell) (upper := upper) (p := p) (χ := fun t => θ t ^ 2)
    hpair hX S hc hell hp hp2 ws hSint hab.le hAa hbB hws hdws hSp hS hSd
    W.aestronglyMeasurable hWb hd hdbound
    (fun i x hx => (hplateau x (Or.inr ⟨i, hx⟩)).1) hdata
    hDmeas hR hχ hχb hχpos
  exact ⟨hD, e, heq, hbudget⟩

/-- The actual weak cutoff equation supplies the complete backward graph budget.
Spatial support, square-weight representatives, coefficient slices and local
square-integrable extensions are explicit inputs. No nonlinear moment or
diffusion integrability is assumed, and the costs are uniform in the small power. -/
theorem exists_backward_cutoff_energy_budgets_of_weak_pair {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X} {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)}
    {A B a b c C Kd ell upper p H L : ℝ}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (W S : WeakSolutionSpatialWeight V X) (w ws : zeroBoundaryGraph V X)
    {Ω : Set (Fin N → ℝ)} {θ : ℝ → ℝ}
    (h : HasReverseHolderCutoffAssemblyData coeff u g φ k v F W S w ws Ω θ
      A B a b c C Kd ell upper p H L) :
    let Y := fun t => W.affineEnergyMap hX
      (shiftedRpowWeakSolutionTest h.shift_pos (p := p / 2) (by have := h.power_le_half; linarith)) w (c ^ (p / 2)) (v t)
    let D := fun t => ∫ x, 2 * ell * (p / 2) ^ 2 * coordinateNormSq
      (fun i => W.toFun x * ((u t x + c) ^ (p / 2 - 1) * g i t x))
    let R := fun t => ∫ x, 2 * upper * (u t x + c) ^ p *
      coordinateNormSq (fun i => W.gradient i x)
    let m := fun t => ∫ x in Ω, (u t x + c) ^ p
    ∃ e, HasBackwardCutoffEnergyBudgets a b ell H (upper * L) L Y θ e D R m := by
  have hraw := h
  rcases h with ⟨hpair, hc, hell, hupper, hp, hp2, hab, hAa, hbB,
    hw, hdw, hws, hdws, hS, hSd, hSint, hplateau, hΩ, hΩfinite, hWunit, hWsupport,
    hd, hdsupport, hdbound, hL, hdL, hu, hg, hu0, hz, hcoeff, hθ, hθb, hθunit, hH, hθd⟩
  let : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hΩfinite.lt_top⟩
  dsimp only
  let τ := volume.restrict (Icc a b)
  have hsub : Icc a b ⊆ Icc A B := fun t ht => ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩
  have hmeasure : τ.prod (volume.restrict Ω) ≤ τ.prod volume :=
    Measure.prod_mono le_rfl Measure.restrict_le_self
  have huΩ := hu.mono_measure hmeasure
  have huΩ0 := hu0.filter_mono (ae_mono hmeasure)
  obtain ⟨hm, _, hK, hmoment⟩ := integrable_reverse_holder_spacetime_cutoff_moments
    τ volume hΩ hc hp.le (by linarith : p ≤ 1) huΩ huΩ0
    W.aestronglyMeasurable hWunit hWsupport hd hdsupport hdL
  have hWb : ∀ᵐ x ∂volume, ‖W.toFun x‖ ≤ 1 := Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_of_nonneg (hWunit x).1] using (hWunit x).2
  have huSlices := ae_memLp_two_slice hu
  have hgSlices := ae_all_iff.mpr (fun i => ae_memLp_two_slice (hg i))
  have huPos := Measure.ae_ae_of_ae_prod hu0
  have hR : IntegrableOn (fun t => ∫ x, 2 * upper * (u t x + c) ^ p *
      coordinateNormSq (fun i => W.gradient i x)) (Icc a b) := by
    change Integrable _ τ
    simpa only [integral_const_mul, mul_assoc] using hK.const_mul (2 * upper)
  obtain ⟨hD, e, heq, hbudget⟩ :=
    backward_initial_budgets_of_assembly_data hX W S w ws hraw hR
  have hvalue := hpair.2.2.1.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hgradient := (ae_all_iff.mpr hpair.2.2.2.1).filter_mono
    (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hgraph := ae_affine_graph_energy_bounds W hX hc hp hp2 hell w hw hdw
    hplateau hWb hd hdbound hvalue hgradient
    (by filter_upwards [hz, huSlices, huPos, hgSlices] with t hzt hut hupt hgt
        exact ⟨hzt, hut, hupt, hgt⟩)
    (hmoment.mono fun _ ht => ht.2.2.2)
  refine ⟨e, ⟨hab, hell, hH, mul_nonneg hupper hL, hL,
    W.memLp_affineEnergyMap hX _ w _ (hpair.1.mono_measure (Measure.restrict_mono hsub le_rfl)),
    hθ, hθunit, hθd, hD, hR, hm, ?_, hmoment.mono fun _ ht => ht.1, ?_, ?_, ?_, ?_, hbudget⟩⟩
  · exact Filter.Eventually.of_forall fun t => integral_nonneg fun x =>
      mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · filter_upwards [hmoment] with t ht
    simp only [integral_const_mul, mul_assoc]
    have hb := mul_le_mul_of_nonneg_left ht.2.2.2 (show 0 ≤ 2 * upper by positivity)
    simpa only [mul_assoc] using hb
  · filter_upwards [hgraph, hmoment] with t hgt hmt
    exact hgt.1.trans_le hmt.2.2.1
  · exact hgraph.mono fun _ ht => ht.2
  · filter_upwards [heq, hgraph] with t het hgt
    exact het.trans hgt.1.symm

end HeatKernel
