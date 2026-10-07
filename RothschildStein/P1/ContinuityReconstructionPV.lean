-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityReconstruction
public import RothschildStein.H2.DataDLpPrincipalValue
public import RothschildStein.H2.PrincipalValueHolder

/-!
# Reconstruction: the truncated integrals and the principal value of the near part

The finite reconstruction formula `T_near f = a ∑_j T_j (b f)`, at the level of the `ρ`-truncated
integrals of a type operator (`truncated`) and of the principal value:

* `rhoTruncated`, `HasRhoPV`: the `ρ`-truncated integral of a kernel against `f` and the statement
  that the truncations are integrable and converge as `ε ↓ 0` (this is `TypeOperator.HasValue`
  without the multiplier, `hasValue_iff_hasRhoPV`);
* `localKernelData_truncation`, `localKernelData_principalValue_limit`: the truncated integrals of
  the localized H2 operators `T_j` over the whole carrier, and their principal values;
* `rhoTruncated_near_eq` (**the finite reconstruction formula for the truncations**): for `0 < ε` and `x` in the
  output support, the `ρ`-truncated integral of `a(ξ) K^φ(ξ, η) b(η)` against `f` is
  `a(ξ) ∑_j ∫_{d'(x, y) > ε} χ_j(x) K(x, y) ψ_j(y) (b f)(y) dy`: the `ρ`- and `d'`-truncations
  agree on the support of the radial profile, and `∑_j χ_j K ψ_j = K`;
* `hasRhoPV_near`: the principal value of the near part exists at every `ξ`, for every `f` such
  that `b f`, extended by zero into the carrier, is Hölder on the doubled balls, and equals
  `a(ξ) ∑_j (T_j (b f))(ξ)` (`nearOutput`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology
namespace RothschildStein.P1

section Defs

variable {N : ℕ}

/-- The `ρ`-truncated integral `∫_{ρ(ξ,η) > ε} κ(ξ, η) f(η) dη` of a kernel (the
truncation of a type operator, `TypeOperator.truncated`). -/
def rhoTruncated (ρ κ : (Fin N → ℝ) → (Fin N → ℝ) → ℝ) (f : (Fin N → ℝ) → ℝ) (ε : ℝ)
    (ξ : Fin N → ℝ) : ℝ :=
  ∫ η in {η | ε < ρ ξ η}, κ ξ η * f η

/-- The `ρ`-principal value of `κ` against `f` at `ξ` exists and equals `v`: all positive
truncations are integrable and converge to `v` as `ε ↓ 0` (the clause of `TypeOperator.HasValue`
without the multiplier). -/
def HasRhoPV (ρ κ : (Fin N → ℝ) → (Fin N → ℝ) → ℝ) (f : (Fin N → ℝ) → ℝ) (ξ : Fin N → ℝ)
    (v : ℝ) : Prop :=
  (∀ ε : ℝ, 0 < ε → IntegrableOn (fun η => κ ξ η * f η) {η | ε < ρ ξ η} volume) ∧
    Tendsto (fun ε => rhoTruncated ρ κ f ε ξ) (𝓝[>] (0 : ℝ)) (𝓝 v)

/-- `TypeOperator.HasValue` is `HasRhoPV` of the kernel for the truncation distance `ρ` of
the frame, with the value shifted by the multiplier. -/
theorem hasValue_iff_hasRhoPV {F : KernelFrame N} {lam : ℕ} (T : TypeOperator F lam)
    (f : (Fin N → ℝ) → ℝ) (ξ : Fin N → ℝ) (v : ℝ) :
    T.HasValue f ξ v ↔ HasRhoPV F.rho T.kernel f ξ (v - T.mult ξ * f ξ) :=
  Iff.rfl

end Defs

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

namespace Carrier

/-- Integrability on the image of a measurable carrier set is integrability on the set of
the pullback. -/
theorem integrableOn_image_val_iff {B : Set C.Carrier} (hB : MeasurableSet B)
    (F : (Fin (n + m) → ℝ) → ℝ) :
    IntegrableOn F (val '' B) volume ↔
      IntegrableOn (fun y : C.Carrier => F y.val) B volume := by
  have hemb := Carrier.measurableEmbedding_val (C := C)
  have h1 : (volume : Measure (Fin (n + m) → ℝ)).restrict (val '' B) =
      Measure.map val ((volume : Measure C.Carrier).restrict B) := by
    have h := hemb.restrict_map (volume : Measure C.Carrier) (val '' B)
    rw [map_val_volume, preimage_image_eq _ val_injective] at h
    rw [← h, Measure.restrict_restrict (hemb.measurableSet_image.mpr hB),
      inter_eq_left.mpr (by rw [← range_val]; exact image_subset_range _ _)]
  unfold IntegrableOn
  rw [h1, hemb.integrable_map_iff]
  rfl

/-- A set integral of an ambient function vanishing outside `U` over a set `S` with
`U ∩ S = val '' B` is the set integral of the pullback over `B` (and the integrability agrees). -/
theorem setIntegral_eq_carrier_of_inter (S : Set (Fin (n + m) → ℝ))
    (F : (Fin (n + m) → ℝ) → ℝ) (hF : ∀ η, η ∉ C.U → F η = 0) {B : Set C.Carrier}
    (hB : MeasurableSet B) (hSB : C.U ∩ S = val '' B) :
    (∫ η in S, F η) = ∫ y in B, F y.val ∂(volume : Measure C.Carrier) ∧
      (IntegrableOn F S volume ↔ IntegrableOn (fun y : C.Carrier => F y.val) B volume) := by
  have hU : MeasurableSet C.U := C.isOpen_U.measurableSet
  have hFi : C.U.indicator F = F := by
    funext η
    by_cases hη : η ∈ C.U
    · simp [hη]
    · simp [hη, hF η hη]
  have h1 : ((volume : Measure (Fin (n + m) → ℝ)).restrict S).restrict C.U =
      volume.restrict (C.U ∩ S) := Measure.restrict_restrict hU
  refine ⟨?_, ?_⟩
  · calc (∫ η in S, F η) = ∫ η, C.U.indicator F η ∂(volume.restrict S) := by rw [hFi]
      _ = ∫ η in C.U, F η ∂(volume.restrict S) := integral_indicator hU
      _ = ∫ η in C.U ∩ S, F η := by rw [h1]
      _ = ∫ η in val '' B, F η := by rw [hSB]
      _ = ∫ y in B, F y.val ∂(volume : Measure C.Carrier) :=
          (setIntegral_carrier_eq_image F hB).symm
  · calc IntegrableOn F S volume ↔ Integrable (C.U.indicator F) (volume.restrict S) := by
          rw [hFi]; rfl
      _ ↔ IntegrableOn F C.U (volume.restrict S) := integrable_indicator_iff hU
      _ ↔ IntegrableOn F (C.U ∩ S) volume := by
          unfold IntegrableOn; rw [h1]
      _ ↔ IntegrableOn F (val '' B) volume := by rw [hSB]
      _ ↔ _ := integrableOn_image_val_iff hB F

end Carrier

section Pieces

variable {S : H2.LocDoubling C.Carrier} {T : H2.TruncDist S}

/-- **The truncated integral of a localized H2 operator over the whole
carrier.** For `ε > 0`, `x` in the carrier and `g` bounded Hölder on the ball of the datum, the
localized kernel `cutoffKernel(x, ·) g` is integrable on `{y | d'(x, y) > ε}` and its integral is
H2's truncated integral over the ball (the added part has pointwise zero integrand). -/
theorem localKernelData_truncation (Q : H2.LocalKernelData S T) {δ : ℝ≥0} (hδ : 0 < δ)
    {g : C.Carrier → ℝ} (hg : H2.BoundedHolder δ (ball Q.z Q.R) g) {ε : ℝ} (hε : 0 < ε)
    (x : C.Carrier) :
    IntegrableOn (fun y => Q.cutoffKernel x y * g y) {y | ε < T.d' x y} S.μ ∧
      (∫ y in {y | ε < T.d' x y}, Q.cutoffKernel x y * g y ∂S.μ) =
        H2.truncatedIntegral S.μ (ball Q.z Q.R) T.d' Q.cutoffKernel ε g x := by
  classical
  have hE : MeasurableSet {y : C.Carrier | ε < T.d' x y} :=
    measurableSet_lt measurable_const (T.meas.comp (measurable_const.prodMk measurable_id))
  have hB : MeasurableSet (ball Q.z Q.R ∩ {y : C.Carrier | ε < T.d' x y}) :=
    isOpen_ball.measurableSet.inter hE
  have hsubE : ball Q.z Q.R ∩ {y : C.Carrier | ε < T.d' x y} ⊆ {y | ε < T.d' x y} :=
    inter_subset_right
  have hzero : ∀ y ∈ {y : C.Carrier | ε < T.d' x y} \
      (ball Q.z Q.R ∩ {y : C.Carrier | ε < T.d' x y}), Q.cutoffKernel x y * g y = 0 := by
    intro y hy
    have hyB : y ∉ ball Q.z Q.R := fun h => hy.2 ⟨h, hy.1⟩
    rw [Q.cutoffKernel_outside x y (Or.inr hyB), zero_mul]
  have hi : IntegrableOn (fun y => Q.cutoffKernel x y * g y)
      (ball Q.z Q.R ∩ {y : C.Carrier | ε < T.d' x y}) S.μ := by
    by_cases hx : x ∈ ball Q.z Q.R
    · exact (Q.supported_localized_singular.truncated_absolute T hε
        (hg.aestronglyMeasurable_restrict hδ isOpen_ball.measurableSet)
        (M := (H2.holderSup (ball Q.z Q.R) g).toReal) ENNReal.toReal_nonneg
        (ae_restrict_of_forall_mem isOpen_ball.measurableSet
          (fun y hy => H2.abs_le_holderSup hg.parts.1 hy)) hx).1
    · have he : (fun y => Q.cutoffKernel x y * g y) = fun _ => 0 :=
        funext fun y => by rw [Q.cutoffKernel_outside x y (Or.inl hx), zero_mul]
      rw [he]
      exact integrable_zero _ _ _
  refine ⟨H2.integrableOn_enlarge_zero hB hE hsubE hi hzero, ?_⟩
  exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hE hsubE hzero

/-- **The principal value of a localized H2 operator at every point of
the carrier**: the truncated integrals over the ball converge to `Q.principalValue g x`, also
outside the ball (the output cutoff vanishes there). -/
theorem localKernelData_principalValue_limit (Q : H2.LocalKernelData S T) {δ : ℝ≥0}
    (hδ : 0 < δ) {g : C.Carrier → ℝ} (hg : H2.BoundedHolder δ (ball Q.z Q.R) g)
    (x : C.Carrier) :
    Tendsto (fun ε => H2.truncatedIntegral S.μ (ball Q.z Q.R) T.d' Q.cutoffKernel ε g x)
      (𝓝[>] 0) (𝓝 (Q.principalValue g x)) := by
  by_cases hx : x ∈ ball Q.z Q.R
  · exact Q.principalValue_limit hδ hg hx
  · have ha : Q.a x = 0 := Q.cutoff_a.outside x hx
    have he : (fun ε => H2.truncatedIntegral S.μ (ball Q.z Q.R) T.d' Q.cutoffKernel ε g x) =
        fun _ => 0 := funext fun ε => Q.truncated_zero_of_cutoff g ε ha
    rw [he, Q.principalValue_zero_of_cutoff g ha]
    exact tendsto_const_nhds

/-- **Zero extension of the local output preserves the
Hölder bound.** If the output cutoff of the datum is supported in `B(z, R/4)` and `g` is bounded
Hölder on `B(z, R)` (`R = r`), the principal value, extended by zero to the whole carrier, has
`‖T_j g‖_{C^δ(carrier)} ≤ (1 + (4/(3R))^δ) N ‖g‖_{C^δ(B(z,R))}`: crossing pairs use the margin
`3R/4` and the sup bound (BB pp. 306-309, Cor 7.19). -/
theorem localKernelData_principalValue_holder (Q : H2.LocalKernelData S T) {δ : ℝ≥0}
    (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hs : ∀ x, x ∉ ball Q.z (Q.R / 4) → Q.a x = 0) {g : C.Carrier → ℝ}
    (hg : H2.BoundedHolder δ (ball Q.z Q.R) g) :
    H2.boundedHolderNorm δ univ (Q.principalValue g) ≤
      ENNReal.ofReal ((1 + (4 / (3 * Q.R)) ^ (δ : ℝ)) * Q.operatorHolderConstant δ) *
        H2.boundedHolderNorm δ (ball Q.z Q.R) g := by
  have hlocal := Q.principalValue_holder_bound hδ hδ₀ hδβ hδν hg
  have hmem := Q.principalValue_boundedHolder hδ hδ₀ hδβ hδν hg
  have hext := H2.boundedHolderNorm_ball_extension Q.radius_pos hmem
    (fun x hx => Q.principalValue_zero_of_cutoff g (hs x hx))
  have hn : 0 ≤ (4 / (3 * Q.R)) ^ (δ : ℝ) :=
    Real.rpow_nonneg (by have := Q.radius_pos; positivity) _
  calc H2.boundedHolderNorm δ univ (Q.principalValue g)
      ≤ (1 + ENNReal.ofReal ((4 / (3 * Q.R)) ^ (δ : ℝ))) *
        H2.boundedHolderNorm δ (ball Q.z Q.R) (Q.principalValue g) := hext
    _ ≤ (1 + ENNReal.ofReal ((4 / (3 * Q.R)) ^ (δ : ℝ))) *
        (ENNReal.ofReal (Q.operatorHolderConstant δ) *
          H2.boundedHolderNorm δ (ball Q.z Q.R) g) := mul_le_mul_right hlocal _
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) hn,
        ← ENNReal.ofReal_mul (by positivity)]

end Pieces

end LiftedChart

end RothschildStein.P1
