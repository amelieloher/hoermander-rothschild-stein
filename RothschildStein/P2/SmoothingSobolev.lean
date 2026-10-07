-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SmoothingFree
public import RothschildStein.Definitions.memSobolevX
public import RothschildStein.S.Sobolev

/-!
# Distributional smoothing, descent: the Sobolev branch

The `L^p` branch of the descent in the language `memSobolevX`: if the representative `w` of
the lift `T̃ = T ∘ J` on the cylinder `A × B` lies in the weighted Sobolev class `W_{X̃}^{k,p}(A × B)`
of the lifted fields, then the vertical average `ū` represents `T|_A` and lies in
`W_X^{k,p}(A)` with weak derivatives `X_I ū = ḡ_I`, and `w = ū ∘ π` a.e. (BB p. 609: "averaging its
`L^p` representative against `η` shows `X_I T ∈ L^p_loc(A)` by Hölder/Fubini").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2
variable {n m : ℕ} {A : Opens (Fin n → ℝ)} {B : Opens (Fin m → ℝ)}

/-- Sobolev descent on a cylinder: the vertical average of a lifted `W^{k,p}`
representative is a `W^{k,p}` representative of the base distribution (`1 ≤ p < ∞`,
`0 < |B| < ∞`). -/
theorem memSobolevX_descent {k₀ : ℕ} (wt : Fin k₀ → ℕ+)
    (X : Fin k₀ → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin k₀ → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i)
      (cylinder A B : Set (Fin (n + m) → ℝ)))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (A : Set (Fin n → ℝ)))
    (S : FiberSetting (cylinder A B) A) {η : TestFunction B ℝ (⊤ : ℕ∞)}
    (hη : ∫ t : Fin m → ℝ, η t = 1) (T : Distribution A ℝ (⊤ : ℕ∞))
    {w : (Fin (n + m) → ℝ) → ℝ}
    (hT : ∀ ψ : TestFunction (cylinder A B) ℝ (⊤ : ℕ∞),
      T (S.test ψ) = Distribution.ofFun (cylinder A B) w volume (⊤ : ℕ∞) ψ)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (hB0 : 0 < volume (B : Set (Fin m → ℝ))) (hB : volume (B : Set (Fin m → ℝ)) < ⊤)
    (hS : memSobolevX wt (triangularLift X P) (cylinder A B) k p w) :
    representsDistribution A T (fiberAvg w η) ∧
      w =ᵐ[volume.restrict (cylinder A B : Set (Fin (n + m) → ℝ))]
        (fun ξ => fiberAvg w η (basePoint ξ)) ∧
      memSobolevX wt X A k p (fiberAvg w η) := by
  have hwloc : LocallyIntegrableOn w (cylinder A B : Set (Fin (n + m) → ℝ)) volume := by
    have h1 := (hS.2 [] ((RothschildStein.S.mem_wordFamily_iff wt k []).2 (by simp [wordWeight]))).choose_spec.1
    exact h1.1
  obtain ⟨hrep, hwae⟩ := descent_of_lift S hη T hwloc hT
  refine ⟨hrep, hwae, ?_, ?_⟩
  · exact memLp_fiberAvg hp hpt hB0 hB hwloc hwae hS.1
  · intro I hI
    obtain ⟨g, hg, hgL⟩ := hS.2 I hI
    obtain ⟨hwd, hgae⟩ := hasWeakWordDeriv_descent X P hXt hX S hη T hwloc hT I hg
    exact ⟨fiberAvg g η, hwd, memLp_fiberAvg hp hpt hB0 hB hg.2.1 hgae hgL⟩

end RothschildStein.P2
