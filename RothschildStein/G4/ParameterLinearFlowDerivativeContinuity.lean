-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ParameterLinearFlowContinuity
public import RothschildStein.G1.SourceParameterAugmentedFlow

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Topology BigOperators

namespace RothschildStein.G4

/-- The actual coefficient/initial-state derivative of a finite
parameter-linear flow is jointly continuous at the source parameter
regularity. Flow continuity is proved by compact-carrier Grönwall;
spatial smoothness and the variational equation are then derived.
No external-parameter derivative or flow-smoothness premise is assumed
(BB Props 9.53–9.54, p. 452). -/
theorem parameter_linear_flow_state_derivative_joint_continuousOn {P : Type*} {m n : ℕ}
    [UniformSpace P] [LocallyCompactSpace P]
    {U : Set P} (hU : IsOpen U) {Ω K : Set (Fin n → ℝ)}
    {C : Set (Fin m → ℝ)} {V : Set ((Fin m → ℝ) × (Fin n → ℝ))}
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) (hV : IsOpen V)
    (hCc : IsCompact C) (hKc : IsCompact K) (hC : Convex ℝ C) (hK : Convex ℝ K)
    (hVC : ∀ p ∈ V, p.1 ∈ C)
    (Y : P → Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hY : ∀ σ ∈ U, ∀ J, ContDiffOn ℝ (⊤ : ℕ∞) (Y σ J) Ω)
    (hYjoint : ∀ J, ContinuousOn (fun q : P × (Fin n → ℝ) => Y q.1 J q.2) (U ×ˢ Ω))
    (hDYjoint : ∀ J, ContinuousOn (fun q : P × (Fin n → ℝ) => fderiv ℝ (Y q.1 J) q.2) (U ×ˢ Ω))
    {A D M T τ₀ : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hT : 0 < T) (hTτ₀ : T < τ₀)
    (hcoef : ∀ a ∈ C, ‖a‖ ≤ A)
    (hvalue : ∀ σ ∈ U, ∀ y ∈ K, ∀ J, ‖Y σ J y‖ ≤ M)
    (hder : ∀ σ ∈ U, ∀ y ∈ K, ∀ J, ‖fderiv ℝ (Y σ J) y‖ ≤ D)
    (Φ : P → (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hinit : ∀ σ ∈ U, ∀ p ∈ V, Φ σ (p, 0) = p.2)
    (hrange : ∀ σ ∈ U, ∀ p ∈ V, ∀ t ∈ Ioo (-τ₀) τ₀, Φ σ (p, t) ∈ K)
    (hode : ∀ σ ∈ U, ∀ p ∈ V, ∀ t ∈ Ioo (-τ₀) τ₀,
      HasDerivAt (fun v => Φ σ (p, v)) (∑ J, p.1 J • Y σ J (Φ σ (p, t))) t) :
    ContinuousOn
      (fun q : (P × ((Fin m → ℝ) × (Fin n → ℝ))) × ℝ =>
        fderiv ℝ (fun p => Φ q.1.1 (p, q.2)) q.1.2)
      ((U ×ˢ V) ×ˢ Ioo (-T) T) := by
  let τ := (T + τ₀) / 2
  have hTτ : T < τ := by dsimp [τ]; linarith
  have hττ₀ : τ < τ₀ := by dsimp [τ]; linarith
  have hτ : 0 < τ := hT.trans hTτ
  have hclosed : Icc (-τ) τ ⊆ Ioo (-τ₀) τ₀ := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hclosedT : Icc (-T) T ⊆ Icc (-τ) τ := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hΦjoint := parameter_linear_flow_joint_continuousOn hU hΩ hKΩ hV hCc hKc hC hK hVC
    Y hY hYjoint hA hD hM hτ.le hcoef hvalue hder Φ hinit
    (fun σ hσ p hp t ht => hrange σ hσ p hp t (hclosed ht))
    (fun σ hσ p hp t ht => hode σ hσ p hp t (hclosed ht))
  have hc : ∀ σ ∈ U, ContinuousOn (Φ σ) (V ×ˢ Ioo (-τ) τ) := by
    intro σ hσ
    have hmap : MapsTo
        (fun q : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ => ((σ, q.1), q.2))
        (V ×ˢ Ioo (-τ) τ) ((U ×ˢ V) ×ˢ Icc (-τ) τ) :=
      fun q hq => ⟨⟨hσ, hq.1⟩, Ioo_subset_Icc_self hq.2⟩
    exact hΦjoint.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd).continuousOn hmap
  let W : P → (Fin m → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) :=
    fun σ p => ∑ J, p.1 J • Y σ J p.2
  let S : Set ((Fin m → ℝ) × (Fin n → ℝ)) := univ ×ˢ Ω
  have hS : IsOpen S := isOpen_univ.prod hΩ
  have hW : ∀ σ ∈ U, ContDiffOn ℝ (⊤ : ℕ∞) (W σ) S :=
    fun σ hσ => linear_field_family_contDiffOn (Y σ) (hY σ hσ) univ
  have hDjoint : ContinuousOn (fun q : P × ((Fin m → ℝ) × (Fin n → ℝ)) =>
      fderiv ℝ (W q.1) q.2) (U ×ˢ S) :=
    parameter_linear_field_state_derivative_joint_continuousOn Y hYjoint hDYjoint
      (fun σ hσ y hy J => ((hY σ hσ J).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
  have hΦode : ∀ σ ∈ U, ∀ p ∈ V, ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ σ (p, v)) (W σ (p.1, Φ σ (p, t))) t ∧
        (p.1, Φ σ (p, t)) ∈ S := by
    intro σ hσ p hp t ht
    have ht' := hclosed (Ioo_subset_Icc_self ht)
    exact ⟨hode σ hσ p hp t ht', mem_univ _, hKΩ (hrange σ hσ p hp t ht')⟩
  have hbound : ∀ σ ∈ U, ∀ p ∈ V, ∀ t ∈ Icc (-T) T,
      ‖fderiv ℝ (W σ) (p.1, Φ σ (p, t))‖ ≤ (m : ℝ) * (A * D + M) := by
    intro σ hσ p hp t ht
    have hyrange := hrange σ hσ p hp t (hclosed (hclosedT ht))
    exact norm_parameter_linear_field_state_fderiv_le (Y σ) (p.1, Φ σ (p, t)) hA hD hM
      (hcoef p.1 (hVC p hp)) (hvalue σ hσ _ hyrange) (hder σ hσ _ hyrange)
      (fun J => ((hY σ hσ J).contDiffAt (hΩ.mem_nhds (hKΩ hyrange))).differentiableAt (by simp))
  exact RothschildStein.G1.parameterFlow_actual_state_derivative_joint_continuousOn hU hV hS
    W Φ hτ hT hTτ (by positivity) hW hc
    (hΦjoint.mono (fun q hq => ⟨hq.1, hclosedT hq.2⟩)) hinit hΦode hDjoint hbound

end RothschildStein.G4
