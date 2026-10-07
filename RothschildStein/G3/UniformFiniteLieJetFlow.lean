-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.JointFiniteLieFieldJets
public import RothschildStein.G3.FiniteLieFields
public import RothschildStein.G4.TimeOneFlow
public import RothschildStein.G1.UniformBufferedParameterJets
@[expose] public section
noncomputable section
open Set Metric TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- A numerical mixed coefficient-jet bound depending only on the
fixed model and the prescribed primitive finite-jet budget. -/
def jointFiniteLieJetBudget {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (R Q : ℕ) (T B : ℝ) : ℝ :=
  (freeDimension a s p : ℝ) * 2 ^ Q * max T 1 *
    (∑ j, (2 ^ (R+1)) ^ ((modelBasisWord D j).length-1) * B ^ (modelBasisWord D j).length)

/-- Joint flows and finite flow-jet bounds have constants independent of
the primitive fields, by the weighted bracket jet estimate
(BB pp. 413–415). -/
theorem exists_uniform_buffered_finiteLie_jet_flow {a s N R Q : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (ρ T B : ℝ) (hρ : 0 < ρ) (_hT : 0 < T)
    (hB : 0 ≤ B) (hQR : Q+s ≤ R+1) :
    let H := jointFiniteLieJetBudget D R Q T B
    let τ := 2 * (ρ / (16 * (1+H)))
    ∃ ε : ℝ, 0 < ε ∧ 4*ε < τ ∧
      ∀ (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ)),
        (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) →
        (∀ x ∈ Ω, ∀ i j, j ≤ R → ‖iteratedFDeriv ℝ j (X i) x‖ ≤ B) →
        ∀ K : Set ((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)),
          (∀ q ∈ K, closedBall q ρ ⊆ ball 0 T ×ˢ (Ω : Set (Fin N → ℝ))) →
          ∃ U : Set ((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)),
            IsOpen U ∧ K ⊆ U ∧ U ⊆ ball 0 T ×ˢ (Ω : Set (Fin N → ℝ)) ∧
            ∃ Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ),
              ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ) ∧
              (∀ q ∈ U, Φ (q,0) = q.2 ∧ ∀ t ∈ Ioo (-τ) τ,
                Φ (q,t) ∈ Ω ∧ HasDerivAt (fun v => Φ (q,v))
                  (∑ j, q.1 j • wordBracket X (modelBasisWord D j) (Φ (q,t))) t) ∧
              ∀ q ∈ U, ∀ t, |t| < ε → ‖Φ (q,t) - q.2‖ ≤ H * |t| ∧
                ∀ n, 1 ≤ n → n ≤ Q →
                  ‖iteratedFDeriv ℝ n (fun z : ℝ × ((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) =>
                    Φ (z.2,z.1)) (t,q)‖ ≤ 2 * (1+ε⁻¹)^n ∧
                  ‖iteratedFDeriv ℝ n (fun z : ℝ × ((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) =>
                    Φ (z.2,z.1) - z.2.2) (t,q)‖ ≤ 2 * (1+ε⁻¹)^n + 1 := by
  intro H τ
  have hH : 0 ≤ H := by
    dsimp [H,jointFiniteLieJetBudget]
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (pow_nonneg hB _))
  obtain ⟨ε,hε,hετ,hflow⟩ := G1.exists_uniform_buffered_parameterJet_flow
    (P := Fin (freeDimension a s p) → ℝ) (E := Fin N → ℝ) ρ H hρ hH Q
  refine ⟨ε,hε,hετ,?_⟩
  intro Ω X hX hXjet K hK
  let Y := fun j => wordBracket X (modelBasisWord D j)
  have hY : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Y j) Ω :=
    fun j => G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D j)
  have hZ : ContDiffOn ℝ (⊤ : ℕ∞) (G4.constantCombination Y)
      (ball (0 : Fin (freeDimension a s p) → ℝ) T ×ˢ (Ω : Set (Fin N → ℝ))) :=
    (G4.constantCombination_contDiffOn hY).mono
    (Set.prod_mono (subset_univ _) Subset.rfl)
  apply hflow Metric.isOpen_ball Ω.isOpen (G4.constantCombination Y) hZ hK
  intro q hq n hn
  have he := norm_joint_finiteLie_field_jet_le D Ω X hX q hq.2 hB
    (hXjet q.2 hq.2) n (by omega)
  apply he.trans
  dsimp [H,jointFiniteLieJetBudget]
  gcongr
  · norm_num
  · exact (mem_ball_zero_iff.mp hq.1).le
end RothschildStein.G3
