-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ContinuousParameterLinearField
public import RothschildStein.G4.ParameterLinearFieldLipschitz
public import RothschildStein.G1.SourceParameterSignedContinuity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped Topology BigOperators NNReal

namespace RothschildStein.G4

/-- Actual coefficient-linear flows are jointly continuous in
external parameters, coefficients, initial points and signed time.
Only joint continuity of the fields and uniform spatial budgets are
used; external parameters are never differentiated (BB p. 452). -/
theorem parameter_linear_flow_joint_continuousOn {P : Type*} {m n : ℕ}
    [UniformSpace P] [LocallyCompactSpace P]
    {U : Set P} (hU : IsOpen U) {Ω K : Set (Fin n → ℝ)}
    {C : Set (Fin m → ℝ)} {V : Set ((Fin m → ℝ) × (Fin n → ℝ))}
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) (hV : IsOpen V)
    (hCc : IsCompact C) (hKc : IsCompact K) (hC : Convex ℝ C) (hK : Convex ℝ K)
    (hVC : ∀ p ∈ V, p.1 ∈ C)
    (Y : P → Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hY : ∀ σ ∈ U, ∀ J, ContDiffOn ℝ (⊤ : ℕ∞) (Y σ J) Ω)
    (hYjoint : ∀ J, ContinuousOn (fun q : P × (Fin n → ℝ) => Y q.1 J q.2) (U ×ˢ Ω))
    {A D M T : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hcoef : ∀ a ∈ C, ‖a‖ ≤ A)
    (hvalue : ∀ σ ∈ U, ∀ y ∈ K, ∀ J, ‖Y σ J y‖ ≤ M)
    (hder : ∀ σ ∈ U, ∀ y ∈ K, ∀ J, ‖fderiv ℝ (Y σ J) y‖ ≤ D)
    (Φ : P → (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hinit : ∀ σ ∈ U, ∀ p ∈ V, Φ σ (p, 0) = p.2)
    (hrange : ∀ σ ∈ U, ∀ p ∈ V, ∀ t ∈ Icc (-T) T, Φ σ (p, t) ∈ K)
    (hode : ∀ σ ∈ U, ∀ p ∈ V, ∀ t ∈ Icc (-T) T,
      HasDerivAt (fun v => Φ σ (p, v)) (∑ J, p.1 J • Y σ J (Φ σ (p, t))) t) :
    ContinuousOn
      (fun q : (P × ((Fin m → ℝ) × (Fin n → ℝ))) × ℝ => Φ q.1.1 (q.1.2, q.2))
      ((U ×ˢ V) ×ˢ Icc (-T) T) := by
  let L : ℝ≥0 := ⟨(m : ℝ) * (A * D + M), by positivity⟩
  let B : ℝ≥0 := ⟨(m : ℝ) * A * M, by positivity⟩
  let Z : (P × ((Fin m → ℝ) × (Fin n → ℝ))) × ((Fin m → ℝ) × (Fin n → ℝ)) →
      (Fin m → ℝ) × (Fin n → ℝ) := fun q => (0, ∑ J, q.2.1 J • Y q.1.1 J q.2.2)
  let Ψ : P × ((Fin m → ℝ) × (Fin n → ℝ)) → ℝ → (Fin m → ℝ) × (Fin n → ℝ) :=
    fun q t => (q.2.1, Φ q.1 (q.2, t))
  have hmap : MapsTo
      (fun q : (P × ((Fin m → ℝ) × (Fin n → ℝ))) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
        (q.1.1, q.2)) ((U ×ˢ V) ×ˢ (C ×ˢ K)) (U ×ˢ (univ ×ˢ Ω)) :=
    fun q hq => ⟨hq.1.1, mem_univ _, hKΩ hq.2.2⟩
  have hfield := (parameter_linear_field_joint_continuousOn Y hYjoint).comp
    (continuous_fst.fst.prodMk continuous_snd).continuousOn hmap
  have hZ : ContinuousOn Z ((U ×ˢ V) ×ˢ (C ×ˢ K)) := continuousOn_const.prodMk hfield
  have hLip : ∀ q ∈ U ×ˢ V, LipschitzOnWith L (fun y => Z (q, y)) (C ×ˢ K) := by
    intro q hq
    have hl := parameter_linear_field_lipschitzOnWith hΩ hKΩ hC hK (Y q.1) (hY q.1 hq.1)
      hA hD hM hcoef (hvalue q.1 hq.1) (hder q.1 hq.1)
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    simpa only [Z, Prod.dist_eq, dist_self, max_eq_right (dist_nonneg :
      0 ≤ dist (∑ J, y.1 J • Y q.1 J y.2) (∑ J, z.1 J • Y q.1 J z.2))] using
      hl.dist_le_mul y hy z hz
  have hbound : ∀ q ∈ U ×ˢ V, ∀ y ∈ C ×ˢ K, ‖Z (q, y)‖ ≤ B := by
    intro q hq y hy
    change ‖((0 : Fin m → ℝ), ∑ J, y.1 J • Y q.1 J y.2)‖ ≤ (m : ℝ) * A * M
    rw [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]
    exact norm_parameter_linear_field_le (Y q.1) y hA (hcoef y.1 hy.1) (hvalue q.1 hq.1 y.2 hy.2)
  have hΨrange : ∀ q ∈ U ×ˢ V, ∀ t ∈ Icc (-T) T, Ψ q t ∈ C ×ˢ K :=
    fun q hq t ht => ⟨hVC q.2 hq.2, hrange q.1 hq.1 q.2 hq.2 t ht⟩
  have hΨode : ∀ q ∈ U ×ˢ V, ∀ t ∈ Icc (-T) T,
      HasDerivAt (Ψ q) (Z (q, Ψ q t)) t :=
    fun q hq t ht => (hasDerivAt_const t q.2.1).prodMk (hode q.1 hq.1 q.2 hq.2 t ht)
  have hΨinit : ContinuousOn (fun q => Ψ q 0) (U ×ˢ V) := by
    apply continuous_snd.continuousOn.congr
    intro q hq
    exact Prod.ext rfl (hinit q.1 hq.1 q.2 hq.2)
  exact (RothschildStein.G1.flow_solutions_signed_joint_continuousOn (hU.prod hV)
    (hCc.prod hKc) Z hZ Ψ hT hLip hbound hΨrange hΨode hΨinit).snd

end RothschildStein.G4
