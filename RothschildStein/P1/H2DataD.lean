-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.H2DataDShell
public import RothschildStein.P1.H2DataDClass
public import RothschildStein.P1.H2DataDCutoff
public import RothschildStein.H2.LocalKernelData
public import RothschildStein.H2.TransposeData
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Data D1-D3 on the doubled ball and the separate transpose certificate

For one fixed principal term `a(x) K(x, y) b(y)`, i.e. a `SplitFamily` `D` of degree 2, the pole
`Γ` (with its shell cancellation, BB Thm 11.5(d)), a radial profile `φ` equal to `1` near `0` and
vanishing on `[R', ∞)`, a truncation distance `d' = ρ` near the diagonal and an admissible radius
`R'`, this module builds, on a doubled ball `U_j^{(2)} = B(z_j, 2r)` of the carrier of the lifted
chart, the premises of H2's Hölder continuity of `T(1)`, its singular integral bound on `C^δ` and its
`L^p` bound for singular integrals:

* `exists_localKernelData` (**Data D1-D3**): an `H2.LocalKernelData` whose
  pieces are `K₀ = splitK0` (singular, exponents `(β, ν) = (1, 0)`) and `K₁ = splitK1`
  (fractional, `(β, ν) = (1, 1)`) restricted to the doubled ball (value `0` on the diagonal and
  outside the chart support, since the carrier is the chart domain), with
  * D1: `K₀ = K₁ = 0` where `d' ≥ R'`, separately, and `R' ≤ θ₁ r`;
  * D2: the kernel classes with volume denominators `μ(B(x, d(x, y)))`, converted from the powers
    of `d̃` by the uniform volume bound of the metric-measure certificate (`H2DataDClass`), constants `(A₀, S₀, A₁, S₁)`;
  * D3: the shell cancellation of `K₀` (`H2DataDShell`), for *every* `0 < t₁ < t₂ < ∞`
    (`integral_carrierKernel_splitK0_shell`), in particular for the shells `t₂ ≤ R'` demanded by
    H2's field `vanishing`;
  * measurability (`H2DataDMeasurable`), the cutoffs `χ_j, ψ_j` of the localization with their
    Lipschitz constants (`H2DataDCutoff`);
* `exists_localKernelData_transpose` (**separate transpose Data D**):
  the same for the transposed splitting `Kᵗ = K'₀ + K'₁` of the
  exchanged-and-reflected data `(transposeFamily D, Γ*)`, with its own constants
  `(A'₀, S'₀, A'₁, S'₁)`; no cancellation of the raw `K₀ᵗ` is claimed;
* `exists_dataD_pair`: the pair `(Q, P : H2.TransposeData Q)` consumed by H2's `L²` and `L^p` bounds for singular integrals, with the
  cutoffs exchanged and `Q.sumKernel(y, x) = P.data.sumKernel(x, y)` on the doubled ball;
* `exists_dataD`: the full certificate together with the geometric data from
  `LiftedChart.exists_h2Certificate`.

The finite reconstruction formula and the domain extensions are not part of this module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric MeasureTheory
open scoped NNReal
namespace RothschildStein.P1

/-- A smooth radial profile equal to `1` on `(-∞, R'/2]` and
vanishing on `[R', ∞)`. -/
theorem exists_radial_profile {R' : ℝ} (hR' : 0 < R') :
    ∃ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ (∀ t, t ≤ R' / 2 → φ t = 1) ∧
      (∀ t, R' ≤ t → φ t = 0) := by
  refine ⟨fun t => Real.smoothTransition ((R' - t) / (R' / 2)), ?_, ?_, ?_⟩
  · exact Real.smoothTransition.contDiff.comp
      ((contDiff_const.sub contDiff_id).div_const _)
  · intro t ht
    apply Real.smoothTransition.one_of_one_le
    rw [one_le_div (by positivity)]
    linarith
  · intro t ht
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- `Q` is the Data D instance of the pair of kernels `(κ₀, κ₁)` on the doubled
ball `B(z, 2r)` with cutoffs `(a, b)`: centre `z`, radius `r`, support radius `R'`, kernel
exponents `β₀ = β = ν = 1` (so `K₀` singular `(1, 0)` and `K₁` fractional `(1, 1)`), and the kernels
are `κ₀`, `κ₁` on the carrier (value `0` on the diagonal). -/
structure IsSplitData {S : H2.LocDoubling C.Carrier} {T : H2.TruncDist S}
    (Q : H2.LocalKernelData S T) (z : C.Carrier) (r R' : ℝ) (a b : C.Carrier → ℝ)
    (κ₀ κ₁ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ) : Prop where
  z_eq : Q.z = z
  R_eq : Q.R = r
  R'_eq : Q.R' = R'
  a_eq : Q.a = a
  b_eq : Q.b = b
  β₀_eq : Q.β₀ = 1
  β_eq : Q.β = 1
  ν_eq : Q.ν = 1
  K₀_eq : Q.K₀ = C.carrierKernel κ₀
  K₁_eq : Q.K₁ = C.carrierKernel κ₁

variable {C}

/-- **Data D1-D3 on the doubled ball** (BB Prop 7.17 and Prop 11.33,
pp. 306–308, 572–576). For the split `K = K₀ + K₁` of the principal term of the
`SplitFamily` `D` with pole `Γ` (with the shell cancellation of BB Thm 11.5(d)), a `C¹` radial profile `φ`
equal to `1` near `0` and vanishing on `[R', ∞)`, a truncation `d' = ρ` and an admissible radius
`R'`, and H2 kernel cutoffs `a, b` supported in `B(z, r)`, there is an `H2.LocalKernelData` on
`U^{(2)} = B(z, 2r)` whose `K₀ = splitK0` is a singular kernel of exponents `(1, 0)`, whose
`K₁ = splitK1` has fractional exponents `(1, 1)`, both with volume denominators and vanishing for
`d' ≥ R'`, `R' ≤ θ₁ r`, and whose `K₀` has the shell cancellation D3. -/
theorem exists_localKernelData {q : ℕ} {H : H1.StandingHypotheses C.G q}
    (hνs : H.norm.Smooth) (Γ : H1.FundamentalKernel C.G H) (hΓ : H1.KernelShellCancellation Γ)
    {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
    (F : SplitFamily C.G D)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {ε : ℝ} (hε : 0 < ε)
    (hφ1 : ∀ t : ℝ, 0 ≤ t → t < ε → φ t = 1) {R' : ℝ} (hφ0 : ∀ t, R' ≤ t → φ t = 0)
    {S : H2.LocDoubling C.Carrier} {vLo vHi : ℝ} (hS : C.IsMetricMeasureCertificate S vLo vHi)
    {τ : ℝ} {T : H2.TruncDist S} (hT : C.IsRhoTruncation S H.norm τ T) {r : ℝ}
    (hR : C.IsAdmissibleRadius S T H.norm τ r R') (hr : 0 < r) (hrκ : r < S.κ)
    {z : C.Carrier} (hz : z ∈ S.Ω₀) {a b : C.Carrier → ℝ} {Lₐ Lᵦ : ℝ≥0}
    (ha : H2.KernelCutoff (ball z r) Lₐ a) (hb : H2.KernelCutoff (ball z r) Lᵦ b) :
    ∃ Q : H2.LocalKernelData S T,
      C.IsSplitData Q z r R' a b (C.splitK0 H.norm D Γ φ) (C.splitK1 H.norm D Γ φ) := by
  have hEΩ : ball z (2 * r) ⊆ S.Ω₁ :=
    ball_subset_closedBall.trans (C.ball_two_mul_subset_Ω₁ S hz hrκ.le)
  have hEd : ∀ x ∈ ball z (2 * r), ∀ y ∈ ball z (2 * r), dist x y ≤ 6 * S.κ := by
    intro x hx y hy
    have h1 := mem_ball.mp hx
    have h2 := mem_ball.mp hy
    have h3 := dist_triangle_right x y z
    linarith [S.κ_pos]
  obtain ⟨hLc, hLU⟩ := Carrier.isCompact_image_closure S.cpt
  have hχ : ContDiff ℝ 1 (fun u => φ (H.norm u)) := contDiff_radial_cutoff H.norm hνs hφ hε hφ1
  have hχc : Continuous (fun u => φ (H.norm u)) := hχ.continuous
  have hb0 := hasKernelBounds_splitK0 F Γ.smooth_off_zero Γ.homogeneous hχ hLc hLU
  have hb1 := hasKernelBounds_splitK1 F Γ.smooth_off_zero Γ.homogeneous hχ hLc hLU
  have hsub : Measurable (fun p : ball z (2 * r) × ball z (2 * r) =>
      ((p.1.1, p.2.1) : C.Carrier × C.Carrier)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_subtype_coe.comp measurable_snd)
  have hm0 := (measurable_carrierKernel_splitK0 (C := C) F Γ.smooth_off_zero hχc).comp hsub
  have hm1 := (measurable_carrierKernel_splitK1 (C := C) F Γ.smooth_off_zero hχc).comp hsub
  obtain ⟨A₀, S₀, hK0⟩ := kernelClass_of_hasKernelBounds hS isOpen_ball.measurableSet hEΩ hEd
    (ℓ := 0) (e := 0) (by simp) hb0 hm0
  obtain ⟨A₁, S₁, hK1⟩ := kernelClass_of_hasKernelBounds hS isOpen_ball.measurableSet hEΩ hEd
    (ℓ := 1) (e := 1) (by simp) hb1 hm1
  have hκ0 : ∀ ξ η, φ (H.norm (C.Θ η ξ)) = 0 → C.splitK0 H.norm D Γ φ ξ η = 0 :=
    fun _ _ h => splitK0_eq_zero_of_cutoff_eq_zero h
  have hκ1 : ∀ ξ η, φ (H.norm (C.Θ η ξ)) = 0 → C.splitK1 H.norm D Γ φ ξ η = 0 :=
    fun _ _ h => splitK1_eq_zero_of_cutoff_eq_zero h
  refine ⟨{
      z := z
      center := hz
      R := r
      radius_pos := hr
      radius_lt := hrκ
      R' := R'
      support_radius_pos := hR.pos
      support_radius_le := hR.le_θ₁_mul hr
      a := a
      b := b
      Lₐ := Lₐ
      Lᵦ := Lᵦ
      cutoff_a := ha
      cutoff_b := hb
      β₀ := 1
      β := 1
      ν := 1
      ν_pos := one_pos
      A₀ := A₀
      S₀ := S₀
      A₁ := A₁
      S₁ := S₁
      K₀ := C.carrierKernel (C.splitK0 H.norm D Γ φ)
      K₁ := C.carrierKernel (C.splitK1 H.norm D Γ φ)
      singular := hK0
      fractional := hK1
      support₀ := fun x _ y _ h => carrierKernel_eq_zero_of_le_d' hκ0 hφ0 hT hR h
      support₁ := fun x _ y _ h => carrierKernel_eq_zero_of_le_d' hκ1 hφ0 hT hR h
      vanishing := ?_ }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  intro x hx r₁ r₂ hr₁ hr₁₂ _
  rw [hS.μ_eq]
  exact integral_carrierKernel_splitK0_shell Γ hΓ (fun ξ _ => F.homogeneous ξ ξ) hφ.continuous
    hφ0 hT hR hr hx (subset_closure (S.sub₁₂ (hEΩ (ball_subset_ball (by linarith) hx)))) hr₁ hr₁₂

/-- **The separate transpose Data D.** The transposed splitting
`Kᵗ = K'₀ + K'₁` of the exchanged-and-reflected data `(transposeFamily D, Γ*)` (`Γ*` the reflected
fundamental kernel, BB Thm 11.5(e)) satisfies D1-D3 on the same doubled ball, with the same symmetric
`d'`, radial profile and support radius, with its own constants (the reflected pole jets and the
exchanged coefficient jets enter `(A'₀, S'₀, A'₁, S'₁)`). Here `a, b` are the cutoffs of the
H2 datum of the transpose (in `exists_dataD_pair`, the original `b, a`). The raw `K₀ᵗ` is not
claimed to cancel. -/
theorem exists_localKernelData_transpose {q : ℕ} {H : H1.StandingHypotheses C.G q}
    (hQ : 2 < (C.G.homogeneousDimension : ℝ)) (hsym : ∀ u, H.norm (-u) = H.norm u)
    (hνs : H.norm.Smooth) (Γ : H1.FundamentalKernel C.G H) (hΓ : H1.KernelShellCancellation Γ)
    {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
    (F : SplitFamily C.G D)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {ε : ℝ} (hε : 0 < ε)
    (hφ1 : ∀ t : ℝ, 0 ≤ t → t < ε → φ t = 1) {R' : ℝ} (hφ0 : ∀ t, R' ≤ t → φ t = 0)
    {S : H2.LocDoubling C.Carrier} {vLo vHi : ℝ} (hS : C.IsMetricMeasureCertificate S vLo vHi)
    {τ : ℝ} {T : H2.TruncDist S} (hT : C.IsRhoTruncation S H.norm τ T) {r : ℝ}
    (hR : C.IsAdmissibleRadius S T H.norm τ r R') (hr : 0 < r) (hrκ : r < S.κ)
    {z : C.Carrier} (hz : z ∈ S.Ω₀) {a b : C.Carrier → ℝ} {Lₐ Lᵦ : ℝ≥0}
    (ha : H2.KernelCutoff (ball z r) Lₐ a) (hb : H2.KernelCutoff (ball z r) Lᵦ b) :
    ∃ Q : H2.LocalKernelData S T,
      C.IsSplitData Q z r R' a b (C.splitK0 H.norm (transposeFamily D) (Γ.reflection hQ) φ)
        (C.splitK1 H.norm (transposeFamily D) (Γ.reflection hQ) φ) :=
  exists_localKernelData (H := H.reverseDrift C.G) (Γ := Γ.reflection hQ)
    hνs (kernelShellCancellation_reflection Γ hQ C.G_inv_eq_neg hsym hΓ) F.transpose hφ hε hφ1
    hφ0 hS hT hR hr hrκ hz ha hb

/-- **Both Data D certificates, with the H2 pairing.**
The original Data D `Q` (cutoffs `a, b`; pieces `K₀, K₁`) and the transposed Data D `P.data`
(cutoffs `b, a` exchanged; pieces `K'₀, K'₁`) with the H2 two-sided datum
`P : H2.TransposeData Q` of H2's `L²` and `L^p` bounds: same centre, radii, support radius and symmetric `d'`, and
`P.data.sumKernel(x, y) = Q.sumKernel(y, x)` on the doubled ball (including the diagonal, where all
kernels are `0` by convention). -/
theorem exists_dataD_pair {q : ℕ} {H : H1.StandingHypotheses C.G q}
    (hQ : 2 < (C.G.homogeneousDimension : ℝ)) (hsym : ∀ u, H.norm (-u) = H.norm u)
    (hνs : H.norm.Smooth) (Γ : H1.FundamentalKernel C.G H) (hΓ : H1.KernelShellCancellation Γ)
    {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
    (F : SplitFamily C.G D)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {ε : ℝ} (hε : 0 < ε)
    (hφ1 : ∀ t : ℝ, 0 ≤ t → t < ε → φ t = 1) {R' : ℝ} (hφ0 : ∀ t, R' ≤ t → φ t = 0)
    {S : H2.LocDoubling C.Carrier} {vLo vHi : ℝ} (hS : C.IsMetricMeasureCertificate S vLo vHi)
    {τ : ℝ} {T : H2.TruncDist S} (hT : C.IsRhoTruncation S H.norm τ T) {r : ℝ}
    (hR : C.IsAdmissibleRadius S T H.norm τ r R') (hr : 0 < r) (hrκ : r < S.κ)
    {z : C.Carrier} (hz : z ∈ S.Ω₀) {a b : C.Carrier → ℝ} {Lₐ Lᵦ : ℝ≥0}
    (ha : H2.KernelCutoff (ball z r) Lₐ a) (hb : H2.KernelCutoff (ball z r) Lᵦ b) :
    ∃ (Q : H2.LocalKernelData S T) (P : H2.TransposeData Q),
      C.IsSplitData Q z r R' a b (C.splitK0 H.norm D Γ φ) (C.splitK1 H.norm D Γ φ) ∧
      C.IsSplitData P.data z r R' b a (C.splitK0 H.norm (transposeFamily D) (Γ.reflection hQ) φ)
        (C.splitK1 H.norm (transposeFamily D) (Γ.reflection hQ) φ) := by
  obtain ⟨Q, hQs⟩ := exists_localKernelData hνs Γ hΓ F hφ hε hφ1 hφ0 hS hT hR hr hrκ hz ha hb
  obtain ⟨Q', hQ's⟩ := exists_localKernelData_transpose hQ hsym hνs Γ hΓ F hφ hε hφ1 hφ0 hS hT
    hR hr hrκ hz hb ha
  refine ⟨Q, ⟨Q', hQ's.z_eq.trans hQs.z_eq.symm, hQ's.R_eq.trans hQs.R_eq.symm,
    hQ's.R'_eq.trans hQs.R'_eq.symm, hQ's.a_eq.trans hQs.b_eq.symm,
    hQ's.b_eq.trans hQs.a_eq.symm, ?_⟩, hQs, hQ's⟩
  intro x _ y _
  unfold H2.LocalKernelData.sumKernel
  rw [hQ's.K₀_eq, hQ's.K₁_eq, hQs.K₀_eq, hQs.K₁_eq]
  by_cases hxy : x = y
  · subst hxy
    simp [carrierKernel_self]
  · have hne : y ≠ x := Ne.symm hxy
    rw [carrierKernel_of_ne hxy, carrierKernel_of_ne hxy, carrierKernel_of_ne hne,
      carrierKernel_of_ne hne]
    have h1 := C.pairKernel_transpose_eq_split_reflection Γ hQ hsym D φ x.val_mem y.val_mem
      (fun h => hxy (Carrier.val_injective h).symm)
    have h2 : C.pairKernel H.norm D Γ φ y.val x.val =
        C.splitK0 H.norm D Γ φ y.val x.val + C.splitK1 H.norm D Γ φ y.val x.val :=
      pairKernel_eq_splitK0_add_splitK1 y.val_mem x.val_mem
    rw [← h2]
    exact h1.symm

/-- **Data D from the finite localization.** Given
the finite localization `(t, χ, ψ)` (`IsLocalization`) and a centre
`z ∈ t`, the H2 cutoffs are `a = χ_z ∘ val`, `b = ψ_z ∘ val` (with their Lipschitz constants for
the lifted control distance), and the original and transposed certificates exist on `B(z, 2r)`. -/
theorem exists_dataD_of_localization {q : ℕ} {H : H1.StandingHypotheses C.G q}
    (hQ : 2 < (C.G.homogeneousDimension : ℝ)) (hsym : ∀ u, H.norm (-u) = H.norm u)
    (hνs : H.norm.Smooth) (Γ : H1.FundamentalKernel C.G H) (hΓ : H1.KernelShellCancellation Γ)
    {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
    (F : SplitFamily C.G D)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {ε : ℝ} (hε : 0 < ε)
    (hφ1 : ∀ t : ℝ, 0 ≤ t → t < ε → φ t = 1) {R' : ℝ} (hφ0 : ∀ t, R' ≤ t → φ t = 0)
    {S : H2.LocDoubling C.Carrier} {vLo vHi : ℝ} (hS : C.IsMetricMeasureCertificate S vLo vHi)
    {τ : ℝ} {T : H2.TruncDist S} (hT : C.IsRhoTruncation S H.norm τ T) {r : ℝ}
    (hR : C.IsAdmissibleRadius S T H.norm τ r R') (hr : 0 < r) (hrκ : r < S.κ)
    {Fs : Set (Fin (n + m) → ℝ)} {t : Finset C.Carrier}
    {χ ψ : C.Carrier → (Fin (n + m) → ℝ) → ℝ} (hloc : C.IsLocalization S Fs r t χ ψ)
    {z : C.Carrier} (hzt : z ∈ t) :
    ∃ (Q : H2.LocalKernelData S T) (P : H2.TransposeData Q),
      C.IsSplitData Q z r R' (fun x : C.Carrier => χ z x.val) (fun x : C.Carrier => ψ z x.val)
        (C.splitK0 H.norm D Γ φ) (C.splitK1 H.norm D Γ φ) ∧
      C.IsSplitData P.data z r R' (fun x : C.Carrier => ψ z x.val) (fun x : C.Carrier => χ z x.val)
        (C.splitK0 H.norm (transposeFamily D) (Γ.reflection hQ) φ)
        (C.splitK1 H.norm (transposeFamily D) (Γ.reflection hQ) φ) := by
  obtain ⟨Lₐ, ha⟩ := hloc.exists_kernelCutoff_χ hr hzt
  obtain ⟨Lᵦ, hb⟩ := hloc.exists_kernelCutoff_ψ hzt
  exact exists_dataD_pair hQ hsym hνs Γ hΓ F hφ hε hφ1 hφ0 hS hT hR hr hrκ
    (hloc.centers_mem z hzt) ha hb

end LiftedChart
end RothschildStein.P1
