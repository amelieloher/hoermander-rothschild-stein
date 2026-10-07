-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FiniteWeightedPatchExpansion
public import RothschildStein.P1.WeightedTaylorRegularTerm

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace RothschildStein.P1

/-- A weighted coefficient with vanishing lower
jets times a punctured homogeneous pole has an actual finite polynomial
part with the sharp lower weight and a globally C^m remainder.
Equality is asserted on the endpoint patch where the jets vanish. -/
theorem exists_finite_patch_weighted_pole_expansion {N : ℕ} {P : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [LocallyCompactSpace P]
    (G : HomogeneousGroup N) (K : Set P) (W m b low : ℕ) (hW : ∀ i, G.weight i ≤ W) (hb : 0 < b)
    (g : (Fin N → ℝ) → ℝ) (d : ℤ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin N → ℝ, u ≠ 0 →
      g (G.dilate r u) = r ^ d * g u)
    (hd : (((m + 1) * W : ℕ) : ℤ) < (b : ℤ) + d)
    (F : P × (Fin N → ℝ) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hjet : ∀ p ∈ K, ∀ I : List (Fin N), (I.map G.weight).sum < low →
      rsPartial I (fun u => F (p, u)) 0 = 0) :
    ∃ poly : List (List (Fin N) × (P → ℝ)),
    ∃ R : P × (Fin N → ℝ) → ℝ,
      (∀ q ∈ poly, low ≤ (q.1.map G.weight).sum ∧
        (q.1.map G.weight).sum < b ∧ ContDiff ℝ (⊤ : ℕ∞) q.2) ∧
      ContDiff ℝ m R ∧ ∀ p ∈ K, ∀ u,
        F (p, u) * g u =
          (poly.map (fun q => taylorWordMonomial q.1 u * q.2 p * g u)).sum + R (p, u) := by
  obtain ⟨poly, rem, hp, hr, he⟩ := exists_finite_weighted_expansion_patch_lower_weight G K b low F hF hjet
  have hreg : ∀ q ∈ rem, ContDiff ℝ m
      (fun z : P × (Fin N → ℝ) => q.2 z * (taylorWordMonomial q.1 z.2 * g z.2)) := by
    intro q hq
    have hword : q.1 ≠ [] := by
      intro heq
      have hw := (hr q hq).1
      rw [heq] at hw
      simp only [List.map_nil, List.sum_nil] at hw
      omega
    have hweight : (b : ℤ) ≤ ((q.1.map G.weight).sum : ℤ) := by exact_mod_cast (hr q hq).1
    exact contDiff_weightedTaylor_remainder_term G W m hW g d hg hhom q.1 hword
      (by omega) q.2 (hr q hq).2
  let R : P × (Fin N → ℝ) → ℝ := fun z =>
    (rem.map (fun q => q.2 z * (taylorWordMonomial q.1 z.2 * g z.2))).sum
  have hR : ContDiff ℝ m R := by
    have hs : ∀ l : List (List (Fin N) × (P × (Fin N → ℝ) → ℝ)),
        (∀ q ∈ l, ContDiff ℝ m (fun z => q.2 z * (taylorWordMonomial q.1 z.2 * g z.2))) →
        ContDiff ℝ m (fun z => (l.map (fun q => q.2 z * (taylorWordMonomial q.1 z.2 * g z.2))).sum) := by
      intro l hl
      induction l with
      | nil => exact contDiff_const
      | cons q l ih =>
        simp only [List.map_cons, List.sum_cons]
        exact (hl q (by simp)).add (ih (fun a ha => hl a (List.mem_cons_of_mem _ ha)))
    exact hs rem hreg
  refine ⟨poly, R, hp, hR, ?_⟩
  intro p hpK u
  rw [he p hpK u, add_mul]
  have hpSum : (poly.map (fun q => taylorWordMonomial q.1 u * q.2 p)).sum * g u =
      (poly.map (fun q => taylorWordMonomial q.1 u * q.2 p * g u)).sum :=
    (List.sum_map_mul_right poly _ _).symm
  have hrSum : (rem.map (fun q => taylorWordMonomial q.1 u * q.2 (p, u))).sum * g u = R (p, u) := by
    rw [← List.sum_map_mul_right]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q hq
    dsimp only
    ring
  rw [hpSum, hrSum]

end RothschildStein.P1
