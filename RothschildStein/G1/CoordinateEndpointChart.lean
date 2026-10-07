-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Linear

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace RothschildStein.G1

/-- Finite actual endpoints, one signed parameter per slot. -/
def coordinateEndpointChart {m n : ℕ}
    (H : Fin m → ℝ × (Fin n → ℝ) → (Fin n → ℝ)) :
    List (Fin m) → ((Fin m → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ)
  | [], q => q.2
  | i :: S, q => H i (q.1 i, coordinateEndpointChart H S q)

/-- Every zero-parameter coordinate chart fixes its base point. -/
theorem coordinateEndpointChart_zero {m n : ℕ}
    (H : Fin m → ℝ × (Fin n → ℝ) → (Fin n → ℝ))
    (hz : ∀ i x, H i (0, x) = x) (S : List (Fin m)) (x : Fin n → ℝ) :
    coordinateEndpointChart H S (0, x) = x := by
  induction S with
  | nil => rfl
  | cons i S ih => simpa only [coordinateEndpointChart, Pi.zero_apply, ih] using hz i x

/-- Joint C¹ regularity of the signed endpoints passes to the
actual finite coordinate chart (BB proof of Theorem 1.53, p. 35). -/
theorem coordinateEndpointChart_contDiffAt_zero {m n : ℕ}
    (H : Fin m → ℝ × (Fin n → ℝ) → (Fin n → ℝ))
    (hz : ∀ i x, H i (0, x) = x) (S : List (Fin m)) (x : Fin n → ℝ)
    (hH : ∀ i, ContDiffAt ℝ 1 (H i) (0, x)) :
    ContDiffAt ℝ 1 (coordinateEndpointChart H S) (0, x) := by
  induction S with
  | nil => exact contDiffAt_snd
  | cons i S ih =>
    have hp : ContDiffAt ℝ 1
        (fun q : (Fin m → ℝ) × (Fin n → ℝ) => (q.1 i, coordinateEndpointChart H S q)) (0, x) :=
      ((contDiffAt_apply ℝ ℝ i 0).comp (f := Prod.fst) (0, x) contDiffAt_fst).prodMk ih
    have hh : ContDiffAt ℝ 1 (H i)
        ((fun q : (Fin m → ℝ) × (Fin n → ℝ) => (q.1 i, coordinateEndpointChart H S q)) (0, x)) := by
      simpa only [Pi.zero_apply, coordinateEndpointChart_zero H hz] using hH i
    exact hh.comp (0, x) hp

/-- The coordinate chart's actual joint derivative is identity
in its base point plus the sum of its selected bracket columns. -/
theorem coordinateEndpointChart_hasFDerivAt_zero {m n : ℕ}
    (H : Fin m → ℝ × (Fin n → ℝ) → (Fin n → ℝ))
    (hz : ∀ i x, H i (0, x) = x) (V : Fin m → (Fin n → ℝ))
    (S : List (Fin m)) (x : Fin n → ℝ)
    (hH : ∀ i, HasFDerivAt (H i)
      ((ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)) +
        (ContinuousLinearMap.toSpanSingleton ℝ (V i)).comp
          (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ))) (0, x)) :
    HasFDerivAt (coordinateEndpointChart H S)
      ((ContinuousLinearMap.snd ℝ (Fin m → ℝ) (Fin n → ℝ)) +
        (S.map (fun i => (ContinuousLinearMap.toSpanSingleton ℝ (V i)).comp
          ((ContinuousLinearMap.proj i).comp
            (ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ))))).sum) (0, x) := by
  induction S with
  | nil => simpa only [coordinateEndpointChart, List.map_nil, List.sum_nil, add_zero] using
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (0, x)))
  | cons i S ih =>
    have hp := ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ))).hasFDerivAt.prodMk ih
    have hh : HasFDerivAt (H i)
        ((ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)) +
          (ContinuousLinearMap.toSpanSingleton ℝ (V i)).comp
            (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)))
        ((fun q : (Fin m → ℝ) × (Fin n → ℝ) => (q.1 i, coordinateEndpointChart H S q)) (0, x)) := by
      simpa only [Pi.zero_apply, coordinateEndpointChart_zero H hz] using hH i
    convert hh.comp (0, x) hp using 1 <;> try rfl
    apply ContinuousLinearMap.ext
    intro q
    ext j
    simp only [List.map_cons, List.sum_cons, ContinuousLinearMap.comp_apply,
      add_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Pi.add_apply]
    abel

end RothschildStein.G1
