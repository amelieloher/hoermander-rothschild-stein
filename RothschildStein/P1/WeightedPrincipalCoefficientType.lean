-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeightedPrincipalChartExpansion

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

/-- A smooth coefficient whose weighted jets
vanish below low times a whole actual principal operator has the type
dictated by degree(D)-low. The finite decomposition is constructed at
every regularity budget (BB Lemmas 11.16 and 11.18, pp. 548–549). -/
theorem LiftedChart.isTypeKernel_patch_weighted_principal
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (t : PrincipalTerm F) (low lam : ℕ)
    (hdegree : t.degree - (low : ℤ) ≤ 2 - (lam : ℤ))
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u)
    (A : (((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) × (Fin (n + m) → ℝ)) → ℝ)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hjet : ∀ p ∈ tsupport t.a ×ˢ tsupport t.b, ∀ I : List (Fin (n + m)),
      (I.map F.G.weight).sum < low → rsPartial I (fun u => A (p, u)) 0 = 0) :
    IsTypeKernel F lam (fun ξ η => t.a ξ * t.b η *
      (A ((ξ, η), F.Θ η ξ) * t.modelKernel ξ η (F.Θ η ξ))) := by
  classical
  let W : ℕ := ∑ j, F.G.weight j
  have hW : ∀ j, F.G.weight j ≤ W := fun j =>
    Finset.single_le_sum (fun i _ => Nat.zero_le (F.G.weight i)) (Finset.mem_univ j)
  let M : ℕ := t.indices.sup (fun α => ∑ j, F.G.weight j * α j)
  have hM : ∀ α ∈ t.indices, (∑ j, F.G.weight j * α j) ≤ M :=
    fun α hα => Finset.le_sup (f := fun β => ∑ j, F.G.weight j * β j) hα
  intro budget
  let B : ℕ := (budget + 1) * W + F.G.homogeneousDimension + M + low + 1
  have hB : 0 < B := by dsimp only [B]; omega
  have hd : ∀ α ∈ t.indices, (((budget + 1) * W : ℕ) : ℤ) < (B : ℤ) +
      (2 - (F.G.homogeneousDimension : ℤ) - ((∑ j, F.G.weight j * α j : ℕ) : ℤ)) := by
    intro α hα
    have hm := hM α hα
    dsimp only [B]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    omega
  obtain ⟨poly, r, hp, hr, he⟩ := C.exists_weightedPrincipal_chart_expansion F hΘ hVU
    t W budget B low hW hB hΓ hhom hd A hA hjet
  let terms : List (PrincipalTerm F) := poly.attach.map (fun q =>
    t.multiplyModelMonomial q.1.1 q.1.2 (hp q.1 q.2).2.2)
  refine ⟨{
    principal := terms
    principal_degree := ?_
    regular := r
    regular_isRegular := hr
    eq_off_diagonal := ?_ }⟩
  · intro u hu
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hu
    have hweight : (low : ℤ) ≤ ((q.1.1.map F.G.weight).sum : ℤ) := by
      exact_mod_cast (hp q.1 q.2).1
    change t.degree - ((q.1.1.map F.G.weight).sum : ℤ) ≤ 2 - (lam : ℤ)
    omega
  · intro ξ η _
    have hterms : (terms.map (fun u => u.kernel ξ η)).sum =
        (poly.map (fun q => q.2 (ξ, η) * taylorWordMonomial q.1 (F.Θ η ξ) * t.kernel ξ η)).sum := by
      simp only [terms, List.map_map, Function.comp_def, PrincipalTerm.multiplyModelMonomial_kernel]
      exact congrArg List.sum (List.attach_map_val (l := poly) (f := fun q =>
        q.2 (ξ, η) * taylorWordMonomial q.1 (F.Θ η ξ) * t.kernel ξ η))
    rw [hterms]
    exact he ξ η

end RothschildStein.P1
