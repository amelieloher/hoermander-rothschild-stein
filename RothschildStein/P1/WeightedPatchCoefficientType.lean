-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeightedPatchChartRemainder
public import RothschildStein.P1.TaylorMonomialOperator
public import RothschildStein.P1.PrincipalModelKernel
public import RothschildStein.H1.FiniteCoordinateHomogeneity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.P1

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The actual cutoff coefficient-times-pole
partial is a type-λ kernel when its lower weighted coefficient jets
vanish to the required order on the compact cutoff supports. For every regularity budget the finite
Taylor construction supplies principal operators of degree ≤2-λ and
an actual compact C^budget remainder; no decomposition is a premise. -/
theorem LiftedChart.isTypeKernel_patch_weighted_coefficient_partial
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (star : Bool) (α : Fin (n + m) → ℕ) (low lam : ℕ)
    (hdegree : ((∑ j, F.G.weight j * α j : ℕ) : ℤ) - (low : ℤ) ≤ 2 - (lam : ℤ))
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole star (F.G.dilate r u) =
        r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole star u)
    (a b : TestFunction F.V ℝ (⊤ : ℕ∞))
    (A : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) → ℝ)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hjet : ∀ ξ ∈ tsupport a, ∀ η ∈ tsupport b, ∀ I : List (Fin (n + m)), (I.map F.G.weight).sum < low →
      rsPartial I (fun u => A (ξ, η, u)) 0 = 0) :
    IsTypeKernel F lam (fun ξ η => a ξ * b η *
      (A (ξ, η, F.Θ η ξ) * euclideanPartial α (F.pole star) (F.Θ η ξ))) := by
  classical
  let wα : ℕ := ∑ j, F.G.weight j * α j
  let d : ℤ := 2 - F.G.homogeneousDimension - wα
  let g := euclideanPartial α (F.pole star)
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g {(0 : Fin (n + m) → ℝ)}ᶜ := by
    apply contDiffOn_iff_forall_nat_le.mpr
    intro j hj
    exact H1.contDiffOn_euclideanPartial_finite
      ⟨{(0 : Fin (n + m) → ℝ)}ᶜ, isOpen_compl_singleton⟩ α j (F.pole star)
      (hΓ.of_le (by simp))
  have hdeg : (d : ℝ) = (2 : ℝ) - F.G.homogeneousDimension - wα := by
    dsimp only [d]
    simp only [Int.cast_sub, Int.cast_natCast, Int.cast_ofNat]
  have hh : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      g (F.G.dilate r u) = r ^ d * g u := by
    intro r hr u hu
    have h := H1.euclideanPartial_punctured_homogeneity_finite F.G α
      (hΓ.of_le (by simp)) hhom hr hu
    rw [← hdeg, Real.rpow_intCast] at h
    exact h
  let W : ℕ := ∑ j, F.G.weight j
  have hW : ∀ i, F.G.weight i ≤ W := fun i =>
    Finset.single_le_sum (fun j _ => Nat.zero_le (F.G.weight j)) (Finset.mem_univ i)
  intro budget
  let B : ℕ := (budget + 1) * W + F.G.homogeneousDimension + wα + low + 1
  have hB : 0 < B := by dsimp only [B]; omega
  have hd : (((budget + 1) * W : ℕ) : ℤ) < (B : ℤ) + d := by
    dsimp only [B, d]
    push_cast
    omega
  obtain ⟨poly, r, hp, hr, he⟩ := C.exists_patch_weightedTaylor_chart_remainder F hΘ hVU
    W budget B low hW hB g d hg hh hd a b A hA hjet
  let terms : List (PrincipalTerm F) := poly.attach.map (fun q =>
    PrincipalTerm.ofTaylorWord F a b α q.1.1 q.1.2 (hp q.1 q.2).2.2 star)
  refine ⟨{
    principal := terms
    principal_degree := ?_
    regular := r
    regular_isRegular := hr
    eq_off_diagonal := ?_ }⟩
  · intro t ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
    have hw : (low : ℤ) ≤ ((q.1.1.map F.G.weight).sum : ℤ) := by
      exact_mod_cast (hp q.1 q.2).1
    change (wα : ℤ) - ((q.1.1.map F.G.weight).sum : ℤ) ≤ 2 - (lam : ℤ)
    omega
  · intro ξ η hne
    have ht : (terms.map (fun t => t.kernel ξ η)).sum =
        (poly.map (fun q => a ξ * b η *
          (taylorWordMonomial q.1 (F.Θ η ξ) * q.2 (ξ, η) * g (F.Θ η ξ)))).sum := by
      simp only [terms, List.map_map, Function.comp_def, PrincipalTerm.ofTaylorWord_kernel]
      dsimp only [g]
      exact congrArg List.sum (List.attach_map_val (l := poly) (f := fun q =>
        a ξ * b η * (taylorWordMonomial q.1 (F.Θ η ξ) * q.2 (ξ, η) *
          euclideanPartial α (F.pole star) (F.Θ η ξ))))
    rw [ht]
    exact he ξ η

end RothschildStein.P1
