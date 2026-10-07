-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LocalWeightedPrincipalType
public import RothschildStein.P1.KernelEstimatesChart

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
namespace RothschildStein.P1
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The actual jth chart-remainder coefficient,
smooth only on T, improves a principal term by its exact lower weighted
jet order max(0,1-w_i+weight(j)) (BB Lemma 11.18, p. 549). -/
theorem LiftedChart.isTypeKernel_chart_remainder_coefficient
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hG : F.G = C.G)
    (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (t : PrincipalTerm F) (i : Fin k) (j : Fin (n + m)) (lam : ℕ)
    (hdegree : t.degree - (1 - ((w i : ℕ) : ℤ) + (F.G.weight j : ℤ)).toNat ≤ 2 - (lam : ℤ))
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u) :
    IsTypeKernel F lam (fun ξ η => t.a ξ * t.b η *
      (C.R [i] η (F.Θ η ξ) j * t.modelKernel ξ η (F.Θ η ξ))) := by
  let T : Set ((((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) × (Fin (n + m) → ℝ))) :=
    {q | (q.1.2, q.2) ∈ C.T}
  have hT : IsOpen T := C.isOpen_T.preimage (continuous_fst.snd.prodMk continuous_snd)
  let A := fun q : (((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) × (Fin (n + m) → ℝ)) =>
    C.R [i] q.1.2 q.2 j
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) A T :=
    (contDiff_apply ℝ ℝ j).comp_contDiffOn
      ((C.remainder_smooth [i]).comp (contDiffOn_fst.snd.prodMk contDiffOn_snd) (fun _ hq => hq))
  apply C.isTypeKernel_local_weighted_principal F hΘ hVU t
    (1 - ((w i : ℕ) : ℤ) + (F.G.weight j : ℤ)).toNat lam hdegree hΓ hhom T hT A hA
  · intro p hp
    exact C.mem_T_zero (hVU (t.b.tsupport_subset hp.2))
  · intro p hp
    change (p.2, F.Θ p.2 p.1) ∈ C.T
    rw [hΘ]
    exact C.mem_T_theta hp.2 hp.1
  · intro p hp I hI
    have hη := hVU (t.b.tsupport_subset hp.2)
    have hjet := C.remainder_weight [i] (by simp) p.2 hη
    have hbound : ((I.map C.G.weight).sum : ℤ) <
        1 - (wordWeight w [i] : ℤ) + (C.G.weight j : ℤ) := by
      rw [← hG]
      simp only [wordWeight, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero]
      omega
    exact hjet j I hbound

end RothschildStein.P1
