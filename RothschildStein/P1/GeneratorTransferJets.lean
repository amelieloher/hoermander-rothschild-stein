-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.GeneratorTransferRemainder
public import RothschildStein.P1.TransferJetReflection
public import RothschildStein.P1.KernelEstimatesChart
public import RothschildStein.G2.PolynomialCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace MvPolynomial
open scoped BigOperators
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- Each polynomial transfer coefficient has
weighted vanishing order equal to its signed difference of weights
(BB Lemma 11.23, pp. 554–555). -/
theorem generatorTransferCoefficient_jet (i : Fin k) (j : Fin (n+m)) :
    JetVan C.G.weight ((C.G.weight j : ℤ) - (w i : ℕ))
      (fun u => eval u (C.generatorTransferCoefficient i j)) := by
  apply JetVan.of_homogeneous C.G (G2.contDiff_eval (C.generatorTransferCoefficient i j))
  intro t ht u
  simpa only [Int.cast_sub, Int.cast_natCast] using
    C.generatorTransferCoefficient_eval_dilate i j t ht u

/-- The complete transfer remainder has
weight at least 1-w_i. This retains every coordinate of the original
remainder, repairing the omission in BB Lemma 11.23, pp. 554–555. -/
theorem generatorTransferRemainder_weight (i : Fin k)
    {ξ η : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) :
    WeightedJet C.G.weight (1 - ((w i : ℕ) : ℤ))
      (C.generatorTransferRemainder i ξ η) := by
  classical
  let V : Opens (Fin (n+m) → ℝ) :=
    ⟨(C.e η).target ∩ (fun u => -u) ⁻¹' (C.e ξ).target,
      (C.e η).open_target.inter ((C.e ξ).open_target.preimage continuous_neg)⟩
  have h0 : (0 : Fin (n+m) → ℝ) ∈ V :=
    ⟨(C.mem_T_zero hη).2, by simpa using (C.mem_T_zero hξ).2⟩
  have hs (I : List (Fin k)) (z : Fin (n+m) → ℝ) (hz : z ∈ C.U) :
      ContDiffOn ℝ (⊤ : ℕ∞) (C.R I z) (C.e z).target :=
    (C.remainder_smooth I).comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun u hu => ⟨hz, hu⟩)
  intro l
  have hfs : ContDiffOn ℝ (⊤ : ℕ∞) (fun u => C.R [i] η u l) V :=
    ((contDiff_apply ℝ ℝ l).comp_contDiffOn (hs [i] η hη)).mono (fun _ hu => hu.1)
  have hgs (j : Fin (n+m)) :
      ContDiffOn ℝ (⊤ : ℕ∞) (fun u => C.R (C.B j) ξ (-u) l) V :=
    ((contDiff_apply ℝ ℝ l).comp_contDiffOn (hs (C.B j) ξ hξ)).comp
      contDiffOn_id.neg (fun _ hu => hu.2)
  have hps (j : Fin (n+m)) :
      ContDiffOn ℝ (⊤ : ℕ∞) (fun u => eval u (C.generatorTransferCoefficient i j)) V :=
    (G2.contDiff_eval (C.generatorTransferCoefficient i j)).contDiffOn
  have hj (j : Fin (n+m)) :
      JetVan C.G.weight (1 - ((w i : ℕ) : ℤ) + C.G.weight l)
        (fun u => eval u (C.generatorTransferCoefficient i j) * C.R (C.B j) ξ (-u) l) := by
    have hr : JetVan C.G.weight (1 - (C.G.weight j : ℤ) + C.G.weight l)
        (fun u => C.R (C.B j) ξ (-u) l) := by
      apply JetVan.reflection ⟨(C.e ξ).target, (C.e ξ).open_target⟩
        ((C.mem_T_zero hξ).2)
        ((contDiff_apply ℝ ℝ l).comp_contDiffOn (hs (C.B j) ξ hξ))
      change ∀ J : List (Fin (n+m)),  ((J.map C.G.weight).sum : ℤ) <
        1 - (C.G.weight j : ℤ) + C.G.weight l → _
      simpa only [← (C.basis_weight j).2.2, Function.comp_def] using
        (C.remainder_weight (C.B j) (C.basis_weight j).1 ξ hξ l)
    have hh := JetVan.mul V h0 (hps j) (hgs j)
      (C.generatorTransferCoefficient_jet i j) hr
    have he : ((C.G.weight j : ℤ) - (w i : ℕ)) +
        (1 - (C.G.weight j : ℤ) + C.G.weight l) =
        1 - ((w i : ℕ) : ℤ) + C.G.weight l := by omega
    rw [he] at hh
    exact hh
  have hsum := JetVan.sum Finset.univ
    (fun j u => eval u (C.generatorTransferCoefficient i j) * C.R (C.B j) ξ (-u) l)
    V h0 (fun j _ => (hps j).mul (hgs j)) (fun j _ => hj j)
  have hfirst : JetVan C.G.weight (1 - ((w i : ℕ) : ℤ) + C.G.weight l)
      (fun u => C.R [i] η u l) := by
    change ∀ J : List (Fin (n+m)),  ((J.map C.G.weight).sum : ℤ) <
      1 - ((w i : ℕ) : ℤ) + C.G.weight l → _
    simpa only [wordWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] using C.remainder_weight [i] (by simp) η hη l
  have htotal := JetVan.add V h0 hfs
    ((ContDiffOn.sum fun j _ => (hps j).mul (hgs j)).neg) hfirst hsum.neg
  change ∀ J : List (Fin (n+m)),  ((J.map C.G.weight).sum : ℤ) < _ → _ at htotal
  simpa only [generatorTransferRemainder, Pi.sub_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, sub_eq_add_neg] using htotal

end RothschildStein.P1.LiftedChart
