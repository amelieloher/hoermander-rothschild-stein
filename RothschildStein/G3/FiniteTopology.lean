-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteAlgebra
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Analysis.Calculus.ContDiff.Operations
@[expose] public section
noncomputable section
namespace RothschildStein.G3

instance finiteWordNormedAddCommGroup {a s : ℕ} {p : Fin a → ℕ+} : NormedAddCommGroup (FiniteWordAlgebra a s p) :=
  inferInstanceAs (NormedAddCommGroup (WordCoefficients a s p))
instance finiteWordRealNormedSpace {a s : ℕ} {p : Fin a → ℕ+} : NormedSpace ℝ (FiniteWordAlgebra a s p) :=
  inferInstanceAs (NormedSpace ℝ (WordCoefficients a s p))
instance finiteWordRealFiniteDimensional {a s : ℕ} {p : Fin a → ℕ+} : FiniteDimensional ℝ (FiniteWordAlgebra a s p) :=
  inferInstanceAs (FiniteDimensional ℝ (WordCoefficients a s p))

/-- Associative multiplication as a continuous bilinear map on the
finite coefficient carrier (BB pp. 528–531). -/
def finiteMulCL {a s : ℕ} {p : Fin a → ℕ+} :
    FiniteWordAlgebra a s p →L[ℝ] FiniteWordAlgebra a s p →L[ℝ] FiniteWordAlgebra a s p :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ)).toLinearMap.comp
      (LinearMap.mul ℝ (FiniteWordAlgebra a s p)))

/-- The continuous bilinear map is actual associative multiplication
(BB pp. 528–531). -/
theorem finiteMulCL_apply {a s : ℕ} {p : Fin a → ℕ+}
    (f g : FiniteWordAlgebra a s p) : finiteMulCL f g = f * g := rfl

/-- Smoothness of finite associative multiplication
(BB pp. 528–531). -/
theorem contDiff_finite_mul {a s : ℕ} {p : Fin a → ℕ+} :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : FiniteWordAlgebra a s p × FiniteWordAlgebra a s p => z.1 * z.2) :=
  (finiteMulCL.contDiff.comp contDiff_fst).clm_apply contDiff_snd
end RothschildStein.G3
