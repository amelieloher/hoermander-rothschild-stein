-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityCharts
public import RothschildStein.P1.PaddingNoDriftSobolevDescent
public import RothschildStein.P1.PaddingNoDriftSobolevNorm
public import RothschildStein.P1.PaddingNoDriftSobolevLift
public import RothschildStein.P1.PaddingNoDriftSobolevPullbackNorm
public import RothschildStein.P1.PaddingNoDriftEquation
public import RothschildStein.P1.PaddingNoDriftSmoothness
public import RothschildStein.P1.PaddingNoDriftWeightedSpan
public import RothschildStein.P1.PaddingSobolevDescent
public import RothschildStein.P1.PaddingSobolevNorm
public import RothschildStein.P1.PaddingDriftSobolevLift
public import RothschildStein.P1.PaddingDriftSobolevPullbackNorm
public import RothschildStein.P1.PaddingDistributionEquation
public import RothschildStein.P1.PaddingDomainSmoothness
public import RothschildStein.P1.PaddingWeightedSpan
public import RothschildStein.P1.PaddingModelDimension
public import RothschildStein.P1.PaddingTensorRestriction
public import RothschildStein.P1.PaddingFunctionTensor
public import RothschildStein.P1.PaddingCylinderFiberSetting
public import RothschildStein.S.MollifierKernel
public import RothschildStein.P1.PaddingDistributionDescent

/-!
# Local regularity assembly: the padding setup (the reduction to dimension at least three)

The low-`Q` reduction pads the original system by three diffusion coordinates `z ∈ ℝ³`
(`paddingVectorFields`, `paddingNoDriftVectorFields`, the padding construction): the padded system on the product
cylinder `Ω × B₃(0)` has `n + 3 ≥ 3` coordinates, so every lifted chart has `Q ≥ n + 3 ≥ 3`
(`LiftedChart.three_le_homogeneousDimension`, the homogeneous-dimension condition). This file fixes the three
nested fiber balls `B₁ ⋐ B₂ ⋐ B₃` of radii `1, 2, 3`, the normalized fiber test function `η`
(the mollifier `euclideanJ`, supported in `B_{1/2}`), and proves the elementary facts on cylinders,
weights, the rank condition of the padded system and the restriction of the tensor distribution.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace Metric
open scoped ENNReal NNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2

/-! ### The fiber balls and the fiber test function -/

/-- The open fiber ball of radius `r` in `ℝ³`. -/
def fiberBall (r : ℝ) : Opens (Fin 3 → ℝ) := ⟨ball 0 r, isOpen_ball⟩

theorem volume_fiberBall_lt_top (r : ℝ) : volume (fiberBall r : Set (Fin 3 → ℝ)) < ⊤ :=
  isBounded_ball.measure_lt_top

theorem volume_fiberBall_pos {r : ℝ} (hr : 0 < r) : 0 < volume (fiberBall r : Set (Fin 3 → ℝ)) :=
  measure_ball_pos volume 0 hr

theorem closure_fiberBall_subset {r r' : ℝ} (h : r < r') :
    closure (fiberBall r : Set (Fin 3 → ℝ)) ⊆ (fiberBall r' : Set (Fin 3 → ℝ)) :=
  closure_ball_subset_closedBall.trans (closedBall_subset_ball h)

theorem isCompact_closure_fiberBall (r : ℝ) :
    IsCompact (closure (fiberBall r : Set (Fin 3 → ℝ))) :=
  (isCompact_closedBall (0 : Fin 3 → ℝ) r).of_isClosed_subset isClosed_closure
    closure_ball_subset_closedBall

theorem fiberBall_mono {r r' : ℝ} (h : r ≤ r') : fiberBall r ≤ fiberBall r' :=
  ball_subset_ball h

theorem zero_mem_fiberBall {r : ℝ} (hr : 0 < r) : (0 : Fin 3 → ℝ) ∈ (fiberBall r : Set (Fin 3 → ℝ)) :=
  mem_ball_self hr

/-- The fixed normalized fiber test function (the mollifier `euclideanJ`, supported in the ball of
radius `1/2`) as a test function on the fiber ball of radius `r > 1/2`. Its underlying function does
not depend on `r`. -/
def fiberBump (r : ℝ) (hr : 1 / 2 < r) : TestFunction (fiberBall r) ℝ (⊤ : ℕ∞) where
  toFun := RothschildStein.S.euclideanJ 3
  contDiff' := (RothschildStein.S.euclideanJ_smooth_compact 3).1
  hasCompactSupport' := (RothschildStein.S.euclideanJ_smooth_compact 3).2
  tsupport_subset' := by
    rw [RothschildStein.S.euclideanJ, ContDiffBump.tsupport_normed_eq]
    change closedBall (0 : Fin 3 → ℝ) (1 / 2 : ℝ) ⊆ ball 0 r
    exact closedBall_subset_ball hr

theorem fiberBump_integral (r : ℝ) (hr : 1 / 2 < r) : ∫ z, fiberBump r hr z = 1 :=
  (RothschildStein.S.euclideanJ_normalized 3).2

/-! ### Cylinders -/

section Cylinders

variable {n d : ℕ}

/-- The closure of a cylinder lies in the cylinder of larger sets containing the closures. -/
theorem closure_cylinder_subset {A A' : Opens (Fin n → ℝ)} {B B' : Opens (Fin d → ℝ)}
    (hA : closure (A : Set (Fin n → ℝ)) ⊆ (A' : Set (Fin n → ℝ)))
    (hB : closure (B : Set (Fin d → ℝ)) ⊆ (B' : Set (Fin d → ℝ))) :
    closure (cylinder A B : Set (Fin (n + d) → ℝ)) ⊆ (cylinder A' B' : Set (Fin (n + d) → ℝ)) := by
  have hclosed : IsClosed {ξ : Fin (n + d) → ℝ |
      basePoint ξ ∈ closure (A : Set (Fin n → ℝ)) ∧ tailPoint ξ ∈ closure (B : Set (Fin d → ℝ))} :=
    (isClosed_closure.preimage continuous_basePoint).inter
      (isClosed_closure.preimage continuous_tailPoint)
  have hsub : closure (cylinder A B : Set (Fin (n + d) → ℝ)) ⊆ {ξ : Fin (n + d) → ℝ |
      basePoint ξ ∈ closure (A : Set (Fin n → ℝ)) ∧
        tailPoint ξ ∈ closure (B : Set (Fin d → ℝ))} :=
    closure_minimal (fun ξ hξ => ⟨subset_closure hξ.1, subset_closure hξ.2⟩) hclosed
  exact hsub.trans fun ξ hξ => ⟨hA hξ.1, hB hξ.2⟩

/-- The closure of a cylinder over compact-closure bases is compact. -/
theorem isCompact_closure_cylinder {A : Opens (Fin n → ℝ)} {B : Opens (Fin d → ℝ)}
    (hA : IsCompact (closure (A : Set (Fin n → ℝ))))
    (hB : IsCompact (closure (B : Set (Fin d → ℝ)))) :
    IsCompact (closure (cylinder A B : Set (Fin (n + d) → ℝ))) := by
  have himg : IsCompact ((fun p : (Fin n → ℝ) × (Fin d → ℝ) => joinPoint p.1 p.2) ''
      (closure (A : Set (Fin n → ℝ)) ×ˢ closure (B : Set (Fin d → ℝ)))) :=
    (hA.prod hB).image continuous_joinPoint
  refine himg.of_isClosed_subset isClosed_closure ?_
  have hclosed : IsClosed {ξ : Fin (n + d) → ℝ |
      basePoint ξ ∈ closure (A : Set (Fin n → ℝ)) ∧ tailPoint ξ ∈ closure (B : Set (Fin d → ℝ))} :=
    (isClosed_closure.preimage continuous_basePoint).inter
      (isClosed_closure.preimage continuous_tailPoint)
  have hsub : closure (cylinder A B : Set (Fin (n + d) → ℝ)) ⊆ {ξ : Fin (n + d) → ℝ |
      basePoint ξ ∈ closure (A : Set (Fin n → ℝ)) ∧
        tailPoint ξ ∈ closure (B : Set (Fin d → ℝ))} :=
    closure_minimal (fun ξ hξ => ⟨subset_closure hξ.1, subset_closure hξ.2⟩) hclosed
  refine hsub.trans ?_
  intro ξ hξ
  exact ⟨(basePoint ξ, tailPoint ξ), ⟨hξ.1, hξ.2⟩, joinPoint_basePoint_tailPoint ξ⟩

theorem cylinder_mono {A A' : Opens (Fin n → ℝ)} {B B' : Opens (Fin d → ℝ)} (hA : A ≤ A')
    (hB : B ≤ B') : cylinder A B ≤ cylinder A' B' := fun _ hξ => ⟨hA hξ.1, hB hξ.2⟩

theorem cylinder_subset {A A' : Opens (Fin n → ℝ)} {B B' : Opens (Fin d → ℝ)} (hA : A ≤ A')
    (hB : B ≤ B') : (cylinder A B : Set (Fin (n + d) → ℝ)) ⊆ (cylinder A' B' : Set (Fin (n + d) → ℝ)) :=
  fun _ hξ => ⟨hA hξ.1, hB hξ.2⟩

/-- The restriction of the padded tensor to a smaller cylinder is the tensor of the restriction,
and it is represented by the same function. -/
theorem paddingTensor_restrict_ofFun (Ω V : Opens (Fin n → ℝ)) (hV : V ≤ Ω)
    (J J' : Opens (Fin d → ℝ)) (hJ' : J' ≤ J) (T : Distribution Ω ℝ (⊤ : ℕ∞))
    {v : (Fin (n + d) → ℝ) → ℝ}
    (hv : LocallyIntegrableOn v (cylinder Ω J : Set (Fin (n + d) → ℝ)) volume)
    (hT : paddingDistributionTensorOneCLM Ω (cylinder Ω J) (padding_cylinder_subset_base Ω J) T =
      Distribution.ofFun (cylinder Ω J) v volume (⊤ : ℕ∞)) :
    paddingDistributionTensorOneCLM V (cylinder V J') (padding_cylinder_subset_base V J')
        (RothschildStein.S.distributionRestrictionCLM Ω V T) =
      Distribution.ofFun (cylinder V J') v volume (⊤ : ℕ∞) := by
  have hle : cylinder V J' ≤ cylinder Ω J := cylinder_mono hV hJ'
  rw [← paddingDistributionTensorOneCLM_restriction Ω V hV (cylinder Ω J) (cylinder V J') hle
    (padding_cylinder_subset_base Ω J) (padding_cylinder_subset_base V J') T, hT,
    distributionRestrictionCLM_ofFun _ _ hle hv]

end Cylinders

/-! ### Weights -/

theorem paddingNoDriftWeights_noDriftWeight {q d : ℕ} :
    paddingNoDriftWeights (d := d) (noDriftWeight : Fin q → ℕ+) =
      (noDriftWeight : Fin (q + d) → ℕ+) :=
  paddingNoDriftWeights_one

theorem paddingControlWeights_driftWeight {q d : ℕ} :
    paddingControlWeights (d := d) (driftWeight : Fin (q + 1) → ℕ+) =
      (driftWeight : Fin (q + d + 1) → ℕ+) :=
  paddingControlWeights_canonical

/-! ### The rank condition of the padded system -/

section Rank

variable {n q d : ℕ}

/-- The padded no-drift system satisfies the rank condition on the product cylinder. -/
theorem bracketSpansOn_paddingNoDrift (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X) :
    bracketSpansOn (cylinder Ω J : Set (Fin (n + d) → ℝ))
      (paddingNoDriftVectorFields (d := d) X) := by
  intro ξ hξ
  have hb : basePoint ξ ∈ (Ω : Set (Fin n → ℝ)) := hξ.1
  obtain ⟨s, -, hst⟩ := exists_stepSpansAt_of_compact Ω.isOpen isCompact_singleton
    (singleton_subset_iff.2 hb) noDriftWeight X hX hspan
  have h := stepSpansAt_paddingNoDriftVectorFields (d := d) (Ω : Set (Fin n → ℝ)) Ω.isOpen
    noDriftWeight X hX ξ hb (by simpa [paddingBaseCLM_apply] using hst (basePoint ξ) rfl)
  rw [paddingNoDriftWeights_noDriftWeight] at h
  exact (bracketSpansOn_of_stepSpansAt (S := {ξ}) (fun x hx => by rw [hx]; exact h)) ξ rfl

/-- The padded drift system satisfies the rank condition on the product cylinder. -/
theorem bracketSpansOn_paddingDrift (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X) :
    bracketSpansOn (cylinder Ω J : Set (Fin (n + d) → ℝ)) (paddingVectorFields (d := d) X) := by
  intro ξ hξ
  have hb : basePoint ξ ∈ (Ω : Set (Fin n → ℝ)) := hξ.1
  obtain ⟨s, -, hst⟩ := exists_stepSpansAt_of_compact Ω.isOpen isCompact_singleton
    (singleton_subset_iff.2 hb) driftWeight X hX hspan
  have h := stepSpansAt_paddingVectorFields (d := d) (Ω : Set (Fin n → ℝ)) Ω.isOpen
    driftWeight X hX ξ hb (by simpa [paddingBaseCLM_apply] using hst (basePoint ξ) rfl)
  rw [paddingControlWeights_driftWeight] at h
  exact (bracketSpansOn_of_stepSpansAt (S := {ξ}) (fun x hx => by rw [hx]; exact h)) ξ rfl

end Rank

/-! ### Arithmetic of the descent of the Sobolev estimates -/

/-- The constants of the Sobolev descent: from `a N ≤ c (b A + b B)` with `a, b, c > 0` follows
`N ≤ (c b / a) (A + B)`. -/
theorem descent_arith {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {N A B : ℝ≥0∞}
    (h : ENNReal.ofReal a * N ≤
      ENNReal.ofReal c * (ENNReal.ofReal b * A + ENNReal.ofReal b * B)) :
    N ≤ ENNReal.ofReal (c * b / a) * (A + B) := by
  have hinv : ENNReal.ofReal a⁻¹ * ENNReal.ofReal a = 1 := by
    rw [← ENNReal.ofReal_mul (inv_pos.2 ha).le, inv_mul_cancel₀ ha.ne', ENNReal.ofReal_one]
  calc N = ENNReal.ofReal a⁻¹ * (ENNReal.ofReal a * N) := by rw [← mul_assoc, hinv, one_mul]
    _ ≤ ENNReal.ofReal a⁻¹ *
        (ENNReal.ofReal c * (ENNReal.ofReal b * A + ENNReal.ofReal b * B)) := by gcongr
    _ = ENNReal.ofReal (c * b / a) * (A + B) := by
      rw [← mul_add, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.2 ha).le,
        ← ENNReal.ofReal_mul (mul_pos (inv_pos.2 ha) hc).le]
      congr 2
      field_simp

end RothschildStein.P2
