-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.Suboptimality

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

variable {ι : Type*} {n : ℕ}

/-- The signed weight deficit of a list of frame coefficients. -/
def generatorDeficit (w : ι → ℕ+) (B : Fin n → ι) (L : List (Fin n × ι)) : ℤ :=
  (L.map (fun z => ((w (B z.1) : ℕ) : ℤ) - ((w z.2 : ℕ) : ℤ))).sum

/-- Products include the empty product, which has value one. -/
def generatorValue (Z : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (B : Fin n → ι) (L : List (Fin n × ι)) (x : Fin n → ℝ) : ℝ :=
  (L.map (fun z => frameCoefficient Z B (Z z.2) z.1 x)).prod

/-- A generator of type `G_a^p`, with the empty product included
exactly when the deficit condition permits it. -/
def IsGenerator (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+)
    (B : Fin n → ι) (a : ℕ) (p : ℤ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ L : List (Fin n × ι), L.length ≤ a ∧ p ≤ generatorDeficit w B L ∧
    f = generatorValue Z B L

/-- Products add the deficit and factor count
(BB Proposition 9.34, p. 425). -/
theorem generator_mul {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} {w : ι → ℕ+}
    {B : Fin n → ι} {a b : ℕ} {p q : ℤ} {f g : (Fin n → ℝ) → ℝ}
    (hf : IsGenerator Z w B a p f) (hg : IsGenerator Z w B b q g) :
    IsGenerator Z w B (a + b) (p + q) (fun x => f x * g x) := by
  obtain ⟨L, hL, hp, rfl⟩ := hf
  obtain ⟨M, hM, hq, rfl⟩ := hg
  refine ⟨L ++ M, by simpa using Nat.add_le_add hL hM, ?_, ?_⟩
  · simpa [generatorDeficit] using add_le_add hp hq
  · funext x
    simp [generatorValue]

/-- Increasing the allowed factor count and lowering the required
deficit enlarges the generator class (BB Proposition 9.34, p. 425). -/
theorem generator_mono {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} {w : ι → ℕ+}
    {B : Fin n → ι} {a b : ℕ} {p q : ℤ} {f : (Fin n → ℝ) → ℝ}
    (hab : a ≤ b) (hqp : q ≤ p) (hf : IsGenerator Z w B a p f) :
    IsGenerator Z w B b q f := by
  obtain ⟨L, hL, hp, heq⟩ := hf
  exact ⟨L, hL.trans hab, hqp.trans hp, heq⟩

/-- The empty product has type `G_a^p` whenever `p ≤ 0`
(BB Definition 9.33, p. 425). -/
theorem generator_one (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+)
    (B : Fin n → ι) (a : ℕ) {p : ℤ} (hp : p ≤ 0) :
    IsGenerator Z w B a p (fun _ => 1) := by
  exact ⟨[], Nat.zero_le _, hp, rfl⟩


/-- Multiply the sharp single-factor estimates without losing
any signed deficit (BB Proposition 9.35, p. 426). -/
theorem generatorValue_le_of_suboptimal
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} {w : ι → ℕ+}
    {B : Fin n → ι} {x : Fin n → ℝ} {t r : ℝ} (ht : 0 < t) (hr : 0 < r)
    (hspan : ∃ C : Fin n → ι, frameDet Z C x ≠ 0) (hB : IsSuboptimal Z w B x t r)
    (L : List (Fin n × ι)) :
    |generatorValue Z B L x| ≤ t⁻¹ ^ L.length * r ^ generatorDeficit w B L := by
  induction L with
  | nil => simp [generatorValue, generatorDeficit]
  | cons z L ih =>
    simp only [generatorValue, generatorDeficit, List.map_cons, List.prod_cons,
      List.sum_cons, List.length_cons, abs_mul] at *
    calc
      _ ≤ (t⁻¹ * r ^ (((w (B z.1) : ℕ) : ℤ) - ((w z.2 : ℕ) : ℤ))) *
          (t⁻¹ ^ L.length * r ^ (L.map (fun z =>
            ((w (B z.1) : ℕ) : ℤ) - ((w z.2 : ℕ) : ℤ))).sum) :=
        mul_le_mul (frameCoefficient_le_of_suboptimal ht hr hspan hB z.2 z.1) ih
          (abs_nonneg _) (mul_nonneg (inv_nonneg.mpr ht.le) (zpow_nonneg hr.le _))
      _ = _ := by rw [zpow_add₀ (ne_of_gt hr), pow_succ]; ring

/-- A generator of type `G_a^p` has the stated suboptimal-scale
bound, including empty products and negative deficits
(BB Proposition 9.35, p. 426). -/
theorem generator_le_of_suboptimal
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} {w : ι → ℕ+}
    {B : Fin n → ι} {x : Fin n → ℝ} {t r : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hspan : ∃ C : Fin n → ι, frameDet Z C x ≠ 0) (hB : IsSuboptimal Z w B x t r)
    {a : ℕ} {p : ℤ} {f : (Fin n → ℝ) → ℝ} (hf : IsGenerator Z w B a p f) :
    |f x| ≤ t⁻¹ ^ a * r ^ p := by
  obtain ⟨L, hL, hp, rfl⟩ := hf
  apply (generatorValue_le_of_suboptimal ht hr hspan hB L).trans
  apply mul_le_mul
  · apply pow_le_pow_right₀
    · exact (one_le_inv₀ ht).mpr ht1
    · exact hL
  · exact zpow_le_zpow_right_of_le_one₀ hr hr1 hp
  · exact zpow_nonneg hr.le _
  · positivity

end RothschildStein.G4
