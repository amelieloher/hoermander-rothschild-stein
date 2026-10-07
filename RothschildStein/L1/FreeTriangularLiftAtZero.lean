-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FiniteFreeLiftChain
public import RothschildStein.L1.FrozenTriangularRepresentation
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- The finite lifting construction gives a free spanning lift at
zero in the polynomial triangular carrier; its number of
added variables is the formal rank minus the original dimension
(BB Theorem 10.19, pp. 493–494). -/
theorem exists_free_triangular_lift_at_zero {a s n : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hzero : (0 : Fin n → ℝ) ∈ Ω)
    (hspan : Submodule.span ℝ (range (fun I : BoundedWord a s p =>
      wordBracket X (boundedWordList I) 0)) = ⊤) :
    ∃ m : ℕ, ∃ V : Opens (Fin (n+m) → ℝ),
      ∃ P : Fin a → Fin m → MvPolynomial (Fin (n+m)) ℝ,
        n+m = freeDimension a s p ∧ m = freeDimension a s p - n ∧
        (0 : Fin (n+m) → ℝ) ∈ V ∧
        (∀ i l, ∀ j ∈ (P i l).vars, j.val < n+l.val) ∧
        (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) V) ∧
        FreeAt p s (triangularLift X P) 0 ∧
        Submodule.span ℝ (range (fun I : BoundedWord a s p =>
          wordBracket (triangularLift X P) (boundedWordList I) 0)) = ⊤ := by
  classical
  obtain ⟨N,V,Y,hN,hzeroY,hY,hfree,hspanY,hchain⟩ :=
    exists_finite_free_polynomial_lift_chain Ω X hX hzero hspan
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hchain.dimension_le
  have hm' : N = n+m := by omega
  have hd : n+m = freeDimension a s p := hm'.symm.trans hN
  clear hm hN
  subst N
  obtain ⟨P,hP,hvars⟩ := exists_frozen_triangular_representation (m := m) X Y hchain.triangularRepresentation
  subst Y
  exact ⟨m,V,P,hd,by omega,hzeroY,hvars,hY,hfree,hspanY⟩
end RothschildStein.L1
