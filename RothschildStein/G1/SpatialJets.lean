-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.MixedPartial
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G1

/-- Spatial derivative tensors of a family (BB p. 3). -/
def spatialJet {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ) (G : E × ℝ → F)
    (p : E × ℝ) : E [×n]→L[ℝ] F :=
  iteratedFDeriv ℝ n (fun y => G (y, p.2)) p.1

/-- Every spatial jet of a jointly smooth family is jointly smooth
(BB Prop 1.2, pp. 3–4). -/
theorem spatialJet_contDiffOn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {a b : ℝ} {G : E × ℝ → F}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G (U ×ˢ Ioo a b)) (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (spatialJet n G) (U ×ˢ Ioo a b) := by
  induction n with
  | zero =>
    exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn hG)
  | succ n ih =>
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn
      (spatial_derivative_contDiffOn hU ih)

/-- Time differentiation commutes with every spatial derivative tensor
for the specified actual time derivative (BB Prop 1.2, pp. 3–4). -/
theorem spatialJet_hasDerivAt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {a b : ℝ} {G H : E × ℝ → F}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G (U ×ˢ Ioo a b))
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H (U ×ˢ Ioo a b))
    (hd : ∀ x ∈ U, ∀ t ∈ Ioo a b,
      HasDerivAt (fun v => G (x, v)) (H (x, t)) t)
    (n : ℕ) {x : E} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun v => spatialJet n G (x, v)) (spatialJet n H (x, t)) t := by
  induction n generalizing x t with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hd x hx t ht)
  | succ n ih =>
    have hh := spatial_derivative_hasDerivAt hU (spatialJet_contDiffOn hU hG n)
      (spatialJet_contDiffOn hU hH n) (fun y hy v hv => ih hy hv) hx ht
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hh

/-- The complete spatial jet hierarchy satisfies the differentiated
actual flow equation, assuming joint smoothness (BB p. 3). -/
theorem localFlow_spatialJet_hasDerivAt_of_joint_contDiff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {U Ω : Set E}
    (hU : IsOpen U) {a b : ℝ} {Z : E → E}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) (Φ : E × ℝ → E)
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo a b))
    (hΦ : ∀ x ∈ U, ∀ t ∈ Ioo a b,
      HasDerivAt (fun v => Φ (x, v)) (Z (Φ (x, t))) t ∧ Φ (x, t) ∈ Ω)
    (n : ℕ) {x : E} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun v => spatialJet n Φ (x, v))
      (iteratedFDeriv ℝ n (fun y => Z (Φ (y, t))) x) t :=
  spatialJet_hasDerivAt hU hjoint
    (hZ.comp hjoint (fun p hp => (hΦ p.1 hp.1 p.2 hp.2).2))
    (fun y hy v hv => (hΦ y hy v hv).1) n hx ht

end RothschildStein.G1
