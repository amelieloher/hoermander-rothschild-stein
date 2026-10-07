-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.GeneratorTransferJets
public import RothschildStein.P1.LocalWeightedPrincipalType

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MvPolynomial
open scoped BigOperators
namespace RothschildStein.P1
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- Multiplication by a coordinate of the
complete transfer remainder improves a principal kernel by its weighted
vanishing order (BB Lemma 11.23, pp. 554–555, with a corrected proof). -/
theorem LiftedChart.isTypeKernel_transfer_remainder_coefficient
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n+m))
    (hΘ : F.Θ = C.Θ) (hG : F.G = C.G)
    (hVU : (F.V : Set (Fin (n+m) → ℝ)) ⊆ C.U)
    (t : PrincipalTerm F) (i : Fin k) (j : Fin (n+m)) (lam : ℕ)
    (hdegree : t.degree - (1 - ((w i : ℕ) : ℤ) + (F.G.weight j : ℤ)).toNat ≤ 2 - (lam : ℤ))
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole t.star) {(0 : Fin (n+m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n+m) → ℝ, u ≠ 0 →
      F.pole t.star (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole t.star u) :
    IsTypeKernel F lam (fun ξ η => t.a ξ * t.b η *
      (C.generatorTransferRemainder i ξ η (F.Θ η ξ) j * t.modelKernel ξ η (F.Θ η ξ))) := by
  classical
  let T : Set ((((Fin (n+m) → ℝ) × (Fin (n+m) → ℝ)) × (Fin (n+m) → ℝ))) :=
    {q | (q.1.2, q.2) ∈ C.T ∧ (q.1.1, -q.2) ∈ C.T}
  have hT : IsOpen T :=
    (C.isOpen_T.preimage (continuous_fst.snd.prodMk continuous_snd)).inter
      (C.isOpen_T.preimage (continuous_fst.fst.prodMk continuous_snd.neg))
  let A := fun q : (((Fin (n+m) → ℝ) × (Fin (n+m) → ℝ)) × (Fin (n+m) → ℝ)) =>
    C.generatorTransferRemainder i q.1.1 q.1.2 q.2 j
  have hR (I : List (Fin k)) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (((Fin (n+m) → ℝ) × (Fin (n+m) → ℝ)) × (Fin (n+m) → ℝ)) =>
        C.R I q.1.1 (-q.2) j) T :=
    (contDiff_apply ℝ ℝ j).comp_contDiffOn
      ((C.remainder_smooth I).comp (contDiffOn_fst.fst.prodMk contDiffOn_snd.neg)
        (fun _ hq => hq.2))
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) A T := by
    have hfirst : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : (((Fin (n+m) → ℝ) × (Fin (n+m) → ℝ)) × (Fin (n+m) → ℝ)) =>
          C.R [i] q.1.2 q.2 j) T :=
      (contDiff_apply ℝ ℝ j).comp_contDiffOn
        ((C.remainder_smooth [i]).comp (contDiffOn_fst.snd.prodMk contDiffOn_snd)
          (fun _ hq => hq.1))
    have hsum := ContDiffOn.sum (s := Finset.univ) fun l _ =>
      ((G2.contDiff_eval (C.generatorTransferCoefficient i l)).contDiffOn.comp
        contDiffOn_snd (fun _ _ => Set.mem_univ _)).mul (hR (C.B l))
    simpa only [A, LiftedChart.generatorTransferRemainder, Pi.sub_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_def] using hfirst.sub hsum
  apply C.isTypeKernel_local_weighted_principal F hΘ hVU t
    (1 - ((w i : ℕ) : ℤ) + (F.G.weight j : ℤ)).toNat lam hdegree hΓ hhom T hT A hA
  · intro p hp
    exact ⟨C.mem_T_zero (hVU (t.b.tsupport_subset hp.2)),
      by simpa only [neg_zero] using C.mem_T_zero (hVU (t.a.tsupport_subset hp.1))⟩
  · intro p hp
    constructor
    · rw [hΘ]; exact C.mem_T_theta hp.2 hp.1
    · change (p.1, -F.Θ p.2 p.1) ∈ C.T
      rw [hΘ, ← C.theta_antisymm _ hp.2 _ hp.1]
      exact C.mem_T_theta hp.1 hp.2
  · intro p hp I hI
    have hξ := hVU (t.a.tsupport_subset hp.1)
    have hη := hVU (t.b.tsupport_subset hp.2)
    apply C.generatorTransferRemainder_weight i hξ hη j I
    rw [← hG]
    omega

end RothschildStein.P1
