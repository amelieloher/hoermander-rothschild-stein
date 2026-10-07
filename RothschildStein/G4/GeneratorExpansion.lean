-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.GeneratorCalculus

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Finite sums of generators with globally smooth coefficient
functions, interpreted on the original nondegenerate-frame domain
(BB Proposition 9.36, pp. 427–428). -/
inductive HasGeneratorExpansion {ι : Type*} {n : ℕ} (Ω : Set (Fin n → ℝ))
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+) (B : Fin n → ι)
    (a : ℕ) (p : ℤ) : ((Fin n → ℝ) → ℝ) → Prop
  | zero : HasGeneratorExpansion Ω Z w B a p (fun _ => 0)
  | term (d g : (Fin n → ℝ) → ℝ)
      (hd : ContDiffOn ℝ (⊤ : ℕ∞) d Ω) (hg : IsGenerator Z w B a p g) :
      HasGeneratorExpansion Ω Z w B a p (fun x => d x * g x)
  | add {f g : (Fin n → ℝ) → ℝ}
      (hf : HasGeneratorExpansion Ω Z w B a p f)
      (hg : HasGeneratorExpansion Ω Z w B a p g) :
      HasGeneratorExpansion Ω Z w B a p (fun x => f x + g x)
  | congr {f g : (Fin n → ℝ) → ℝ}
      (hf : HasGeneratorExpansion Ω Z w B a p f)
      (heq : EqOn g f (Ω ∩ {x | frameDet Z B x ≠ 0})) :
      HasGeneratorExpansion Ω Z w B a p g

/-- The expansion class contains each generator itself. -/
theorem generator_expansion {ι : Type*} {n : ℕ} {Ω : Set (Fin n → ℝ)}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} {w : ι → ℕ+} {B : Fin n → ι}
    {a : ℕ} {p : ℤ} {f : (Fin n → ℝ) → ℝ} (hf : IsGenerator Z w B a p f) :
    HasGeneratorExpansion Ω Z w B a p f :=
  (HasGeneratorExpansion.term (fun _ => 1) f contDiffOn_const hf).congr
    (fun x _ => (one_mul (f x)).symm)

/-- Increasing the factor allowance and lowering the deficit
preserves finite smooth-coefficient expansions. -/
theorem generatorExpansion_mono {ι : Type*} {n : ℕ} {Ω : Set (Fin n → ℝ)}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} {w : ι → ℕ+} {B : Fin n → ι}
    {a b : ℕ} {p q : ℤ} {f : (Fin n → ℝ) → ℝ}
    (hab : a ≤ b) (hqp : q ≤ p) (hf : HasGeneratorExpansion Ω Z w B a p f) :
    HasGeneratorExpansion Ω Z w B b q f := by
  induction hf with
  | zero => exact .zero
  | term d g hd hg => exact .term d g hd (generator_mono hab hqp hg)
  | add hf hg ihf ihg => exact .add ihf ihg
  | congr hf heq ih => exact .congr ih heq

/-- Smooth multiplication preserves the generator type. -/
theorem generatorExpansion_smooth_mul {ι : Type*} {n : ℕ} {Ω : Set (Fin n → ℝ)}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} {w : ι → ℕ+} {B : Fin n → ι}
    {a : ℕ} {p : ℤ} {f d : (Fin n → ℝ) → ℝ}
    (hd : ContDiffOn ℝ (⊤ : ℕ∞) d Ω) (hf : HasGeneratorExpansion Ω Z w B a p f) :
    HasGeneratorExpansion Ω Z w B a p (fun x => d x * f x) := by
  induction hf with
  | zero => exact HasGeneratorExpansion.zero.congr (fun x _ => mul_zero _)
  | term e g he hg =>
    exact (HasGeneratorExpansion.term (fun x => d x * e x) g (hd.mul he) hg).congr
      (fun x _ => (mul_assoc _ _ _).symm)
  | add hf hg ihf ihg =>
    exact (HasGeneratorExpansion.add ihf ihg).congr (fun x _ => mul_add _ _ _)
  | congr hf heq ih =>
    exact ih.congr (fun x hx => congrArg (fun v => d x * v) (heq hx))

/-- Finite sums preserve the same generator type. -/
theorem generatorExpansion_sum {ι : Type*} {n : ℕ} {κ : Type*}
    {Ω : Set (Fin n → ℝ)} {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    {w : ι → ℕ+} {B : Fin n → ι} {a : ℕ} {p : ℤ}
    (S : Finset κ) (f : κ → (Fin n → ℝ) → ℝ)
    (hf : ∀ j ∈ S, HasGeneratorExpansion Ω Z w B a p (f j)) :
    HasGeneratorExpansion Ω Z w B a p (fun x => ∑ j ∈ S, f j x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (HasGeneratorExpansion.zero (Ω := Ω) (Z := Z) (w := w) (B := B) (a := a) (p := p))
  | @insert j S hj ih =>
    have h := HasGeneratorExpansion.add (hf j (Finset.mem_insert_self _ _))
      (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))
    exact h.congr (fun x _ => Finset.sum_insert hj)

/-- Every finite smooth-coefficient expansion is smooth on the
nondegenerate-frame domain. -/
theorem generatorExpansion_contDiffOn {ι : Type*} {n : ℕ} {Ω : Set (Fin n → ℝ)}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Z j) Ω)
    {w : ι → ℕ+} {B : Fin n → ι} {a : ℕ} {p : ℤ}
    {f : (Fin n → ℝ) → ℝ} (hf : HasGeneratorExpansion Ω Z w B a p f) :
    ContDiffOn ℝ (⊤ : ℕ∞) f (Ω ∩ {x | frameDet Z B x ≠ 0}) := by
  induction hf with
  | zero => exact contDiffOn_const
  | term d g hd hg =>
    obtain ⟨L, hL, hp, rfl⟩ := hg
    exact (hd.mono inter_subset_left).mul (generatorValue_contDiffOn hZ B L)
  | add hf hg ihf ihg => exact ihf.add ihg
  | congr hf heq ih => exact ih.congr heq

end RothschildStein.G4
