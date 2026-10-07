-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.GeneratorDifferentiation

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G4

/-- Actual differentiation preserves finite smooth-coefficient
expansions with the exact change of factor count and signed deficit
(BB Proposition 9.36, pp. 427–428). -/
theorem generatorExpansion_derivative {k n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {w : Fin (k + 1) → ℕ+}
    {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (B : Fin n → ShortWord w s)
    (L : ShortWord w s) {a : ℕ} {p : ℤ} {f : (Fin n → ℝ) → ℝ}
    (hf : HasGeneratorExpansion Ω (shortField w X) (shortWeight w) B a p f) :
    HasGeneratorExpansion Ω (shortField w X) (shortWeight w) B (a + 1)
      (p - ((shortWeight w L : ℕ) : ℤ)) (fieldDerivative (shortField w X L) f) := by
  let Z := shortField (s := s) w X
  let v := shortWeight (s := s) w
  have hZ : ∀ J : ShortWord w s, ContDiffOn ℝ (⊤ : ℕ∞) (Z J) Ω :=
    shortField_contDiffOn hΩ hX
  have hnear : ∀ x ∈ Ω ∩ {x | frameDet Z B x ≠ 0},
      Ω ∩ {y | frameDet Z B y ≠ 0} ∈ 𝓝 x := by
    intro x hx
    apply inter_mem (hΩ.mem_nhds hx.1)
    exact ((frameDet_contDiffOn hZ B).contDiffAt (hΩ.mem_nhds hx.1)).continuousAt.preimage_mem_nhds
      (isOpen_compl_singleton.mem_nhds hx.2)
  induction hf with
  | zero =>
    exact HasGeneratorExpansion.zero.congr (fun x _ => by simp [fieldDerivative])
  | term d g hd hg =>
    have hd' : ContDiffOn ℝ (⊤ : ℕ∞) (fieldDerivative (Z L) d) Ω :=
      (hd.fderiv_of_isOpen hΩ (by simp)).clm_apply (hZ L)
    have hweight : p - ((v L : ℕ) : ℤ) ≤ p := by
      have hv : 0 ≤ ((v L : ℕ) : ℤ) := by positivity
      omega
    have hfirst := generatorExpansion_mono (Nat.le_succ a) hweight
      (generatorExpansion_smooth_mul hd' (generator_expansion (Ω := Ω) hg))
    have hsecond := generatorExpansion_smooth_mul hd
      (generator_derivative_expansion hΩ hX hstep B L hg)
    have hgs := generatorExpansion_contDiffOn hZ (generator_expansion (Ω := Ω) hg)
    exact (HasGeneratorExpansion.add hfirst hsecond).congr (fun x hx =>
      S.fieldDerivative_mul (Z L) d g x
        ((hd.contDiffAt (hΩ.mem_nhds hx.1)).differentiableAt (by simp))
        ((hgs.contDiffAt (hnear x hx)).differentiableAt (by simp)))
  | add hf hg ihf ihg =>
    have hfs := generatorExpansion_contDiffOn hZ hf
    have hgs := generatorExpansion_contDiffOn hZ hg
    exact (HasGeneratorExpansion.add ihf ihg).congr (fun x hx => by
      simp only [fieldDerivative, fderiv_fun_add
        ((hfs.contDiffAt (hnear x hx)).differentiableAt (by simp))
        ((hgs.contDiffAt (hnear x hx)).differentiableAt (by simp)),
        add_apply])
  | @congr f₁ g₁ hf heq ih =>
    exact ih.congr (fun x hx => by
      have he : g₁ =ᶠ[𝓝 x] f₁ := by
        filter_upwards [hnear x hx] with y hy
        exact heq hy
      exact congrArg (fun D => D (Z L x)) (he.fderiv_eq (𝕜 := ℝ)))

end RothschildStein.G4
