-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.IteratedGeneratorDifferentiation
public import RothschildStein.G4.DeterminantMultiplier

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G4

/-- Recurrence for derivatives relative to a selected frame determinant (BB Lemma 9.37, pp. 428–430). -/
def relativeDerivatives {k n s : ℕ} (w : Fin (k + 1) → ℕ+)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ShortWord w s) :
    List (ShortWord w s) → ((Fin n → ℝ) → ℝ) → ((Fin n → ℝ) → ℝ)
  | [], F => F
  | L :: M, F => fun x =>
      fieldDerivative (shortField w X L) (relativeDerivatives w X B M F) x +
        relativeDerivatives w X B M F x * determinantMultiplier w X B L x

/-- The relative recurrence increases the generator count by the
number of derivatives and loses their precise total weight
(BB Lemma 9.37, pp. 428–430). -/
theorem relativeDerivatives_expansion {k n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {w : Fin (k + 1) → ℕ+}
    {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (B : Fin n → ShortWord w s)
    {a : ℕ} {p : ℤ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasGeneratorExpansion Ω (shortField w X) (shortWeight w) B a p F)
    (M : List (ShortWord w s)) :
    HasGeneratorExpansion Ω (shortField w X) (shortWeight w) B (a + M.length)
      (p - derivativeWeight (shortWeight w) M) (relativeDerivatives w X B M F) := by
  induction M with
  | nil => simpa only [relativeDerivatives, derivativeWeight, List.map_nil, List.sum_nil,
      List.length_nil, add_zero, sub_zero] using hF
  | cons L M ih =>
    have hd := generatorExpansion_derivative hΩ hX hstep B L ih
    have hm := generatorExpansion_mul ih (determinantMultiplier_expansion hΩ hX hstep B L)
    have hm' : HasGeneratorExpansion Ω (shortField w X) (shortWeight w) B (a + M.length + 1)
        (p - derivativeWeight (shortWeight w) M - ((shortWeight w L : ℕ) : ℤ))
        (fun x => relativeDerivatives w X B M F x * determinantMultiplier w X B L x) := by
      convert hm using 1
      omega
    have hh := HasGeneratorExpansion.add hd hm'
    convert hh using 1
    · simp only [derivativeWeight, List.map_cons, List.sum_cons]
      omega
    · rfl

/-- The recurrence gives actual iterated derivatives of a scalar
function represented relative to the frame determinant, pointwise on its
open nondegenerate domain (BB Lemma 9.37, pp. 428–430). -/
theorem shortDerivatives_eq_relative_mul {k n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {w : Fin (k + 1) → ℕ+}
    {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (B : Fin n → ShortWord w s)
    {a : ℕ} {p : ℤ} {F f : (Fin n → ℝ) → ℝ}
    (hF : HasGeneratorExpansion Ω (shortField w X) (shortWeight w) B a p F)
    (heq : EqOn f (fun x => F x * frameDet (shortField w X) B x)
      (Ω ∩ {x | frameDet (shortField w X) B x ≠ 0}))
    (M : List (ShortWord w s)) :
    EqOn (shortDerivatives (shortField w X) M f)
      (fun x => relativeDerivatives w X B M F x * frameDet (shortField w X) B x)
      (Ω ∩ {x | frameDet (shortField w X) B x ≠ 0}) := by
  let Z := shortField (s := s) w X
  have hZ : ∀ J : ShortWord w s, ContDiffOn ℝ (⊤ : ℕ∞) (Z J) Ω := shortField_contDiffOn hΩ hX
  induction M with
  | nil => exact heq
  | cons L M ih =>
    intro x hx
    have hnear : Ω ∩ {y | frameDet Z B y ≠ 0} ∈ 𝓝 x := by
      apply inter_mem (hΩ.mem_nhds hx.1)
      exact ((frameDet_contDiffOn hZ B).contDiffAt (hΩ.mem_nhds hx.1)).continuousAt.preimage_mem_nhds
        (isOpen_compl_singleton.mem_nhds hx.2)
    have hev : shortDerivatives Z M f =ᶠ[𝓝 x]
        (fun y => relativeDerivatives w X B M F y * frameDet Z B y) := by
      filter_upwards [hnear] with y hy
      exact ih hy
    have hFm := generatorExpansion_contDiffOn hZ (relativeDerivatives_expansion hΩ hX hstep B hF M)
    have hdet := frameDet_contDiffOn hZ B
    change fieldDerivative (Z L) (shortDerivatives Z M f) x = _
    rw [fieldDerivative, hev.fderiv_eq (𝕜 := ℝ)]
    change fieldDerivative (Z L) (fun y => relativeDerivatives w X B M F y * frameDet Z B y) x = _
    rw [S.fieldDerivative_mul (Z L) _ _ x
      ((hFm.contDiffAt hnear).differentiableAt (by simp))
      ((hdet.contDiffAt (hΩ.mem_nhds hx.1)).differentiableAt (by simp)),
      fieldDerivative_frameDet_eq_multiplier hΩ hX hstep B L hx.1 hx.2]
    change _ = (fieldDerivative (Z L) (relativeDerivatives w X B M F) x +
      relativeDerivatives w X B M F x * determinantMultiplier w X B L x) * frameDet Z B x
    ring

end RothschildStein.G4
