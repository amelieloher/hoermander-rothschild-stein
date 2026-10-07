-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependenceLocalBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace RothschildStein.G1

universe u

/-- The finite-order regularity statement used in the variational induction.
Its hypotheses are the proposed flow API, without an initial-data derivative. -/
def FlowRegularity (n : ℕ) : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {Ω U : Set E} {τ : ℝ} (_hΩ : IsOpen Ω) (_hU : IsOpen U) (_hτ : 0 < τ)
    {Z : E → E} (_hZ : ContDiffOn ℝ (n : ℕ∞ω) Z Ω)
    {Φ : (E × ℝ) → E} (_hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (_hinit : ∀ x ∈ U, Φ (x, 0) = x)
    (_hsol : ∀ x ∈ U, ∀ t ∈ Ioo (-τ) τ,
      Φ (x, t) ∈ Ω ∧ HasDerivAt (fun v => Φ (x, v)) (Z (Φ (x, t))) t),
    ContDiffOn ℝ (n : ℕ∞ω) Φ (U ×ˢ Ioo (-τ) τ)

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

/-- The flow extended by arbitrary initial linear maps in the first
variational equation. -/
def variationalFlow (Φ : (E × ℝ) → E) (J : (E × ℝ) → E →L[ℝ] E)
    (p : ((E × (E →L[ℝ] E)) × ℝ)) : E × (E →L[ℝ] E) :=
  (Φ (p.1.1, p.2), (J (p.1.1, p.2)).comp p.1.2)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- Joint continuity of the augmented variational flow
(BB Proposition 1.2, p. 3). -/
theorem variationalFlow_continuousOn
    {U : Set E} {T : ℝ} {Φ : (E × ℝ) → E} {J : (E × ℝ) → E →L[ℝ] E}
    (hc : ContinuousOn Φ (U ×ˢ Ioo (-T) T))
    (hJ : ContinuousOn J (U ×ˢ Ioo (-T) T)) :
    ContinuousOn (variationalFlow Φ J) ((U ×ˢ univ) ×ˢ Ioo (-T) T) := by
  have hp : Continuous (fun p : ((E × (E →L[ℝ] E)) × ℝ) => (p.1.1, p.2)) := by fun_prop
  have hm : MapsTo (fun p : ((E × (E →L[ℝ] E)) × ℝ) => (p.1.1, p.2))
      ((U ×ˢ univ) ×ˢ Ioo (-T) T) (U ×ˢ Ioo (-T) T) := fun p hp => ⟨hp.1.1, hp.2⟩
  exact (hc.comp hp.continuousOn hm).prodMk
    ((hJ.comp hp.continuousOn hm).clm_comp (by fun_prop))

/-- The lower-order flow theorem applied to the variational
field gives lower-order regularity of the first variation. This is the exact
induction hypothesis, not a premise that the sought variation is smooth
(BB Proposition 1.2, p. 3). -/
theorem initial_variation_contDiffOn_of_lower_order
    {n : ℕ} (ih : FlowRegularity.{u} n)
    {Ω U : Set E} (hΩ : IsOpen Ω) (hU : IsOpen U)
    {Z : E → E} (hZ : ContDiffOn ℝ ((n : ℕ∞ω) + 1) Z Ω)
    {Φ : (E × ℝ) → E} {T : ℝ} (hT : 0 < T)
    (hc : ContinuousOn Φ (U ×ˢ Ioo (-T) T))
    (hinit : ∀ x ∈ U, Φ (x, 0) = x)
    (hsol : ∀ x ∈ U, ∀ t ∈ Ioo (-T) T,
      Φ (x, t) ∈ Ω ∧ HasDerivAt (fun v => Φ (x, v)) (Z (Φ (x, t))) t)
    {J : (E × ℝ) → E →L[ℝ] E}
    (hcJ : ContinuousOn J (U ×ˢ Ioo (-T) T))
    (hJ0 : ∀ x ∈ U, J (x, 0) = ContinuousLinearMap.id ℝ E)
    (hJd : ∀ x ∈ U, ∀ t ∈ Ioo (-T) T, HasDerivAt (fun s => J (x, s))
      ((fderiv ℝ Z (Φ (x, t))).comp (J (x, t))) t) :
    ContDiffOn ℝ (n : ℕ∞ω) J (U ×ˢ Ioo (-T) T) := by
  have hfield := tangentVectorField_contDiffOn hΩ hZ le_rfl
  have hvar : ContDiffOn ℝ (n : ℕ∞ω) (variationalFlow Φ J)
      ((U ×ˢ univ) ×ˢ Ioo (-T) T) := by
    apply ih (hΩ.prod isOpen_univ) (hU.prod isOpen_univ) hT hfield
      (variationalFlow_continuousOn hc hcJ)
    · intro p hp
      simp [variationalFlow, hinit p.1 hp.1, hJ0 p.1 hp.1]
    · intro p hp t ht
      refine ⟨⟨(hsol p.1 hp.1 t ht).1, mem_univ _⟩, ?_⟩
      have hd := (hJd p.1 hp.1 t ht).clm_comp (hasDerivAt_const t p.2)
      simp only [ContinuousLinearMap.comp_zero, add_zero, ContinuousLinearMap.comp_assoc] at hd
      exact (hsol p.1 hp.1 t ht).2.prodMk hd
  have hi : ContDiff ℝ (n : ℕ∞ω)
      (fun p : E × ℝ => ((p.1, ContinuousLinearMap.id ℝ E), p.2)) := by fun_prop
  have hm : MapsTo (fun p : E × ℝ => ((p.1, ContinuousLinearMap.id ℝ E), p.2))
      (U ×ˢ Ioo (-T) T) ((U ×ˢ univ) ×ˢ Ioo (-T) T) :=
    fun p hp => ⟨⟨hp.1, mem_univ _⟩, hp.2⟩
  have he := (hvar.comp hi.contDiffOn hm).snd
  exact he.congr (fun _ _ => (ContinuousLinearMap.comp_id _).symm)

end RothschildStein.G1
