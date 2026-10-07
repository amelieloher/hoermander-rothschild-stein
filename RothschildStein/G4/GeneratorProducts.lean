-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.GeneratorExpansion

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Multiplication by a generator adds its factor count and
signed deficit (BB Proposition 9.34, p. 425). -/
theorem generatorExpansion_mul_generator {ι : Type*} {n : ℕ} {Ω : Set (Fin n → ℝ)}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} {w : ι → ℕ+} {B : Fin n → ι}
    {a b : ℕ} {p q : ℤ} {g f : (Fin n → ℝ) → ℝ}
    (hg : IsGenerator Z w B a p g) (hf : HasGeneratorExpansion Ω Z w B b q f) :
    HasGeneratorExpansion Ω Z w B (a + b) (p + q) (fun x => g x * f x) := by
  induction hf with
  | zero => exact HasGeneratorExpansion.zero.congr (fun x _ => mul_zero _)
  | term d h hd hh =>
    exact (HasGeneratorExpansion.term d (fun x => g x * h x) hd (generator_mul hg hh)).congr
      (fun x _ => by ring)
  | add hf hh ihf ihh => exact (HasGeneratorExpansion.add ihf ihh).congr (fun x _ => mul_add _ _ _)
  | congr hf heq ih => exact ih.congr (fun x hx => congrArg (fun v => g x * v) (heq hx))

/-- Finite smooth-coefficient expansions multiply by adding the
allowed factor count and signed deficit (BB Proposition 9.34, p. 425). -/
theorem generatorExpansion_mul {ι : Type*} {n : ℕ} {Ω : Set (Fin n → ℝ)}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} {w : ι → ℕ+} {B : Fin n → ι}
    {a b : ℕ} {p q : ℤ} {f g : (Fin n → ℝ) → ℝ}
    (hf : HasGeneratorExpansion Ω Z w B a p f) (hg : HasGeneratorExpansion Ω Z w B b q g) :
    HasGeneratorExpansion Ω Z w B (a + b) (p + q) (fun x => f x * g x) := by
  induction hf with
  | zero => exact HasGeneratorExpansion.zero.congr (fun x _ => zero_mul _)
  | term d h hd hh =>
    exact (generatorExpansion_smooth_mul hd (generatorExpansion_mul_generator hh hg)).congr
      (fun x _ => mul_assoc _ _ _)
  | add hf hh ihf ihh => exact (HasGeneratorExpansion.add ihf ihh).congr (fun x _ => add_mul _ _ _)
  | congr hf heq ih => exact ih.congr (fun x hx => congrArg (fun v => v * g x) (heq hx))

/-- Negation preserves a smooth-coefficient expansion. -/
theorem generatorExpansion_neg {ι : Type*} {n : ℕ} {Ω : Set (Fin n → ℝ)}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} {w : ι → ℕ+} {B : Fin n → ι}
    {a : ℕ} {p : ℤ} {f : (Fin n → ℝ) → ℝ} (hf : HasGeneratorExpansion Ω Z w B a p f) :
    HasGeneratorExpansion Ω Z w B a p (fun x => -f x) :=
  (generatorExpansion_smooth_mul (d := fun _ => -1) contDiffOn_const hf).congr
    (fun _x _ => (neg_one_mul _).symm)

/-- Subtraction preserves a smooth-coefficient expansion. -/
theorem generatorExpansion_sub {ι : Type*} {n : ℕ} {Ω : Set (Fin n → ℝ)}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} {w : ι → ℕ+} {B : Fin n → ι}
    {a : ℕ} {p : ℤ} {f g : (Fin n → ℝ) → ℝ}
    (hf : HasGeneratorExpansion Ω Z w B a p f) (hg : HasGeneratorExpansion Ω Z w B a p g) :
    HasGeneratorExpansion Ω Z w B a p (fun x => f x - g x) :=
  (HasGeneratorExpansion.add hf (generatorExpansion_neg hg)).congr (fun _x _ => sub_eq_add_neg _ _)

/-- A single frame coefficient is the one-factor generator with
its exact signed deficit. -/
theorem frameCoefficient_isGenerator {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+) (B : Fin n → ι)
    (i : Fin n) (J : ι) :
    IsGenerator Z w B 1 (((w (B i) : ℕ) : ℤ) - ((w J : ℕ) : ℤ))
      (frameCoefficient Z B (Z J) i) := by
  refine ⟨[(i, J)], le_rfl, ?_, ?_⟩
  · simp [generatorDeficit]
  · funext x
    simp [generatorValue]

end RothschildStein.G4
