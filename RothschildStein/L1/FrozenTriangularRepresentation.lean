-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.TriangularRepresentationStep
public import RothschildStein.Definitions.triangularLift
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- The coordinate representation assembles into the exact
triangularLift coefficient carrier, with its variable-support condition. -/
theorem exists_frozen_triangular_representation {a n m : ℕ}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (Y : Fin a → (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ))
    (h : TriangularPolynomialRepresentation X Y) :
    ∃ P : Fin a → Fin m → MvPolynomial (Fin (n+m)) ℝ,
      Y = triangularLift X P ∧
      ∀ i l, ∀ j ∈ (P i l).vars, j.val < n+l.val := by
  classical
  obtain ⟨hn,hbase,hpoly⟩ := h
  have he : ∀ i (l : Fin m), ∃ P : MvPolynomial (Fin (n+m)) ℝ,
      (∀ ξ, Y i ξ (Fin.natAdd n l) = MvPolynomial.eval ξ P) ∧
      ∀ j ∈ P.vars, j.val < n+l.val := by
    intro i l
    simpa only [Fin.val_natAdd] using hpoly i (Fin.natAdd n l) (by simp)
  choose P hP hvars using he
  refine ⟨P,?_,hvars⟩
  funext i ξ j
  refine Fin.addCases ?_ ?_ j
  · intro k
    have hk : Fin.castLE hn k = Fin.castAdd m k := by apply Fin.ext; rfl
    have hb := hbase i ξ k
    rw [hk] at hb
    have he : prefixPoint hn ξ = basePoint ξ := by
      funext l
      change ξ (Fin.castLE hn l) = ξ (Fin.castAdd m l)
      congr 1
    rw [he] at hb
    simpa only [triangularLift,Fin.addCases_left] using hb
  · intro l
    simpa only [triangularLift,Fin.addCases_right] using hP i l ξ
end RothschildStein.L1
