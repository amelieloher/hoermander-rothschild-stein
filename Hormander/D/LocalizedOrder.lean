-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.D.SupportFactorization
public import Hormander.B.Order
public import Hormander.B.Differential
public import Hormander.B.Calculus.B10Facts

@[expose] public section

noncomputable section

namespace Hormander.D

open Hormander.B

private def commutatorLeftLinearMap {N : ℕ} (B : Operator N) :
    Operator N →ₗ[ℂ] Operator N where
  toFun A := operatorComm A B
  map_add' A C := operatorComm_add_left A C B
  map_smul' c A := by
    ext u x
    simp [operatorComm, LinearMap.comp_apply]
    ring

/-- The coefficient produced when a Schwartz vector field is commuted with a real multiplier. -/
def vectorFieldMultiplierCommCoefficient {N : ℕ} (V : RealSchwartzVectorField N)
    (η : SchwartzMap (Carrier N) ℝ) : TestFunction N :=
  ∑ i : Fin N,
    multiplierOperator (complexifyRealSchwartz (V i))
      (coordinateDerivative i (complexifyRealSchwartz η))

private theorem multiplierOperator_sum {N : ℕ} {ι : Type*} [Fintype ι]
    (g : ι → TestFunction N) :
    multiplierOperator (∑ i, g i) = ∑ i, multiplierOperator (g i) := by
  classical
  ext u x
  simp only [multiplierOperator_apply, LinearMap.sum_apply, sum_apply]
  rw [Finset.sum_mul]

private theorem multiplierOperator_commutator_eq_zero {N : ℕ}
    (g h : TestFunction N) :
    operatorComm (multiplierOperator g) (multiplierOperator h) = 0 := by
  apply operatorComm_eq_zero_of_comm
  rw [multiplierOperator_comp, multiplierOperator_comp]
  ext u x
  simp only [multiplierOperator_apply]
  ring

/-- A vector field commuted with a real Schwartz multiplier is again a Schwartz multiplier. -/
theorem vectorFieldOperator_realMultiplierOperator_comm {N : ℕ}
    (V : RealSchwartzVectorField N) (η : SchwartzMap (Carrier N) ℝ) :
    operatorComm (vectorFieldOperator V) (realMultiplierOperator η) =
      multiplierOperator (vectorFieldMultiplierCommCoefficient V η) := by
  classical
  let Mη := multiplierOperator (complexifyRealSchwartz η)
  have hsum :
      operatorComm (∑ i : Fin N,
        (realMultiplierOperator (V i)).comp (coordinateDerivative i)) Mη =
        ∑ i : Fin N,
          operatorComm ((realMultiplierOperator (V i)).comp
            (coordinateDerivative i)) Mη := by
    change commutatorLeftLinearMap Mη (∑ i : Fin N,
      (realMultiplierOperator (V i)).comp (coordinateDerivative i)) = _
    rw [map_sum]
    rfl
  rw [vectorFieldOperator]
  change operatorComm (∑ i : Fin N,
      (realMultiplierOperator (V i)).comp (coordinateDerivative i)) Mη = _
  rw [hsum]
  have hterm (i : Fin N) :
      operatorComm ((realMultiplierOperator (V i)).comp (coordinateDerivative i)) Mη =
        multiplierOperator
          (multiplierOperator (complexifyRealSchwartz (V i))
            (coordinateDerivative i (complexifyRealSchwartz η))) := by
    change operatorComm
      ((multiplierOperator (complexifyRealSchwartz (V i))).comp (coordinateDerivative i))
      (multiplierOperator (complexifyRealSchwartz η)) = _
    rw [operatorComm_comp_left, multiplierOperator_commutator_eq_zero,
      LinearMap.zero_comp, add_zero, operatorComm_coordinateDerivative_multiplier,
      ← multiplierOperator_comp]
  simp_rw [hterm]
  rw [← multiplierOperator_sum]
  rfl

/-- The commutator of a localized Bessel operator with a vector field has order `s`.
This uses the differential bridge and fractional commutator estimate. -/
theorem vectorFieldLocalizedBesselComm_hasOrder {N : ℕ}
    (η₁ η' : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (V : RealSchwartzVectorField N) :
    HasOrder s
      (operatorComm (vectorFieldOperator V) (localizedBesselOperator η₁ η' s)) := by
  let X := vectorFieldOperator V
  let M' := realMultiplierOperator η'
  let M₁ := realMultiplierOperator η₁
  let Λ := lambdaOperator (N := N) s
  have hmult : ∀ g : TestFunction N, HasOrder 0 (multiplierOperator g) :=
    (peetre_and_multiplier_order (N := N)).2
  have hM' : HasOrder 0 M' := by
    change HasOrder 0 (multiplierOperator (complexifyRealSchwartz η'))
    exact hmult _
  have hM₁ : HasOrder 0 M₁ := by
    change HasOrder 0 (multiplierOperator (complexifyRealSchwartz η₁))
    exact hmult _
  have hΛ : HasOrder s Λ := by
    simpa [Λ] using hasOrder_lambdaOperator s
  have hXdiff : IsDiffOp 1 X := by
    exact isDiffOp_vectorFieldOperator V
  have hΛX : HasOrder s (operatorComm Λ X) := by
    simpa [Λ] using fractional_diffOp_order s hXdiff
  have hXM' : HasOrder 0 (operatorComm X M') := by
    rw [vectorFieldOperator_realMultiplierOperator_comm]
    exact hmult _
  have hXM₁ : HasOrder 0 (operatorComm X M₁) := by
    rw [vectorFieldOperator_realMultiplierOperator_comm]
    exact hmult _
  have hXΛ : HasOrder s (operatorComm X Λ) := by
    rw [operatorComm_antisymm]
    exact hΛX.smul (-1 : ℂ)
  change HasOrder s (operatorComm X (M'.comp (Λ.comp M₁)))
  rw [operatorComm_comp_right, operatorComm_comp_right]
  have hΛM₁ : HasOrder s (Λ.comp M₁) := by
    simpa only [add_zero] using hΛ.comp hM₁
  have hfirst : HasOrder s ((operatorComm X M').comp (Λ.comp M₁)) := by
    simpa only [zero_add] using hXM'.comp hΛM₁
  have hinner : HasOrder s
      ((operatorComm X Λ).comp M₁ + Λ.comp (operatorComm X M₁)) := by
    have hleft : HasOrder s ((operatorComm X Λ).comp M₁) := by
      simpa only [add_zero] using hXΛ.comp hM₁
    have hright : HasOrder s (Λ.comp (operatorComm X M₁)) := by
      simpa only [add_zero] using hΛ.comp hXM₁
    exact hleft.add hright
  have hsecond : HasOrder s (M'.comp
      ((operatorComm X Λ).comp M₁ + Λ.comp (operatorComm X M₁))) := by
    simpa only [zero_add] using hM'.comp hinner
  exact hfirst.add hsecond

/-- The operator-class result supplies every order bound used in the energy expansion. -/
theorem localizedBesselOperator_energy_commutator_orders {k N : ℕ}
    (η₁ η' : SchwartzMap (Carrier N) ℝ) (σ : ℝ)
    (V : Fin k → RealSchwartzVectorField N)
    (V₀ : RealSchwartzVectorField N) (c : SchwartzMap (Carrier N) ℝ) :
    (∀ i, HasOrder σ
      (operatorComm (vectorFieldOperator (V i))
        (localizedBesselOperator η₁ η' σ))) ∧
    (∀ i j,
      HasOrder σ (operatorComm (vectorFieldOperator (V j))
        (operatorComm (vectorFieldOperator (V i))
          (localizedBesselOperator η₁ η' σ))) ∧
      HasOrder σ (operatorComm
        (operatorComm (vectorFieldOperator (V j))
          (operatorComm (vectorFieldOperator (V i))
            (localizedBesselOperator η₁ η' σ)))
        (vectorFieldOperator (V j)))) ∧
    (∀ i,
      HasOrder σ (operatorComm (vectorFieldOperator V₀)
        (operatorComm (vectorFieldOperator (V i))
          (localizedBesselOperator η₁ η' σ))) ∧
      HasOrder σ (operatorComm (realMultiplierOperator c)
        (operatorComm (vectorFieldOperator (V i))
          (localizedBesselOperator η₁ η' σ)))) := by
  let A := localizedBesselOperator η₁ η' σ
  have hA : OperatorClass σ A := by
    simpa [A, localizedBesselOperator] using
      Hormander.B.localizedBesselOperator_operatorClass η₁ η' σ
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have h := Hormander.B.localizedBesselOperator_depth_three
      η₁ η' σ (V i) (V i)
    simpa [A, localizedBesselOperator] using h.1
  · intro i j
    have h := Hormander.B.localizedBesselOperator_depth_three
      η₁ η' σ (V j) (V i)
    simpa [A, localizedBesselOperator] using ⟨h.2.1, h.2.2⟩
  · intro i
    have hC := (hA.comm_vectorField (V i)).comm_realMultiplier c
    have hVorder : HasOrder σ
        (operatorComm (vectorFieldOperator V₀)
          (operatorComm (vectorFieldOperator (V i)) A)) := by
      simpa [A, localizedBesselOperator] using
        (Hormander.B.localizedBesselOperator_depth_three
          η₁ η' σ V₀ (V i)).2.1
    have hCorder : HasOrder σ
        (operatorComm (realMultiplierOperator c)
          (operatorComm (vectorFieldOperator (V i)) A)) := by
      have hCclass : OperatorClass σ
          (operatorComm (realMultiplierOperator c)
            (operatorComm (vectorFieldOperator (V i)) A)) := by
        exact hC.mono (by linarith)
      exact hCclass.hasOrder'
    exact ⟨hVorder, hCorder⟩

/-- The localized Bessel operator has its displayed global order on Schwartz functions. -/
theorem localizedBesselOperator_hasOrder {N : ℕ}
    (η₁ η' : SchwartzMap (Carrier N) ℝ) (s : ℝ) :
    HasOrder s (localizedBesselOperator η₁ η' s) := by
  have hmult : ∀ g : TestFunction N, HasOrder 0 (multiplierOperator g) :=
    (peetre_and_multiplier_order (N := N)).2
  have hM' : HasOrder 0 (realMultiplierOperator η') := by
    change HasOrder 0 (multiplierOperator (complexifyRealSchwartz η'))
    exact hmult _
  have hM₁ : HasOrder 0 (realMultiplierOperator η₁) := by
    change HasOrder 0 (multiplierOperator (complexifyRealSchwartz η₁))
    exact hmult _
  have hΛ : HasOrder s (lambdaOperator (N := N) s) := hasOrder_lambdaOperator s
  change HasOrder s
    ((realMultiplierOperator η').comp
      ((lambdaOperator s).comp (realMultiplierOperator η₁)))
  simpa only [zero_add, add_zero] using hM'.comp (hΛ.comp hM₁)

/-- The localized Bessel operator is bounded from the outer localized H^s data to L². -/
theorem localizedBesselOperator_l2_bound {N : ℕ}
    (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (hη₁η₂ : cutoffPrecedes (η₁ : Carrier N → ℝ) (η₂ : Carrier N → ℝ)) :
    ∃ C : NNReal, ∀ v : TestFunction N,
      sobolevNorm 0 (localizedBesselOperator η₁ η' s v) ≤
        (C : ℝ) * sobolevNorm s (realMultiplierOperator η₂ v) := by
  let A := localizedBesselOperator η₁ η' s
  let M₂ := realMultiplierOperator η₂
  have hfactor : A = A.comp M₂ :=
    localizedBesselOperator_right_factorization η₁ η' η₂ s hη₁η₂
  obtain ⟨C, hC⟩ := (localizedBesselOperator_hasOrder η₁ η' s) 0
  refine ⟨C, fun v => ?_⟩
  have hv : A v = A (M₂ v) := by
    have heq := congrArg (fun O : Operator N => O v) hfactor
    simpa [M₂] using heq
  calc
    sobolevNorm 0 (A v) = sobolevNorm 0 (A (M₂ v)) := by rw [hv]
    _ ≤ (C : ℝ) * sobolevNorm s (M₂ v) := by
      simpa [A, zero_add] using hC (M₂ v)

/-- An order estimate becomes a localized L² bound when the operator factors through the data
cutoff on the right. -/
theorem hasOrder_l2_bound_of_right_factorization {N : ℕ}
    (T : Operator N) (η₂ : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (hT : HasOrder s T)
    (hfactor : T = T.comp (realMultiplierOperator η₂)) :
    ∃ C : NNReal, ∀ v : TestFunction N,
      sobolevNorm 0 (T v) ≤ (C : ℝ) *
        sobolevNorm s (realMultiplierOperator η₂ v) := by
  obtain ⟨C, hC⟩ := hT 0
  refine ⟨C, fun v => ?_⟩
  have hv : T v = T (realMultiplierOperator η₂ v) := by
    have heq := congrArg (fun O : Operator N => O v) hfactor
    simpa using heq
  calc
    sobolevNorm 0 (T v) = sobolevNorm 0 (T (realMultiplierOperator η₂ v)) := by
      rw [hv]
    _ ≤ (C : ℝ) * sobolevNorm (0 + s) (realMultiplierOperator η₂ v) := hC _
    _ = (C : ℝ) * sobolevNorm s (realMultiplierOperator η₂ v) := by simp

/-- A finite family of order-bounded operators has one shared localized L² constant when each
member factors through the data cutoff. -/
theorem finiteFamily_hasOrder_l2_bound_of_right_factorization {ι : Type*} [Fintype ι]
    {N : ℕ}
    (T : ι → Operator N) (η₂ : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (hT : ∀ i, HasOrder s (T i))
    (hfactor : ∀ i, T i = (T i).comp (realMultiplierOperator η₂)) :
    ∃ C : NNReal, ∀ i, ∀ v : TestFunction N,
      sobolevNorm 0 (T i v) ≤ (C : ℝ) *
        sobolevNorm s (realMultiplierOperator η₂ v) := by
  classical
  let Cᵢ : ι → NNReal := fun i =>
    Classical.choose (hasOrder_l2_bound_of_right_factorization
      (T i) η₂ s (hT i) (hfactor i))
  have hCᵢ (i : ι) : ∀ v : TestFunction N,
      sobolevNorm 0 (T i v) ≤ (Cᵢ i : ℝ) *
        sobolevNorm s (realMultiplierOperator η₂ v) :=
    Classical.choose_spec (hasOrder_l2_bound_of_right_factorization
      (T i) η₂ s (hT i) (hfactor i))
  refine ⟨Finset.univ.sup Cᵢ, fun i v => ?_⟩
  have hCi : Cᵢ i ≤ Finset.univ.sup Cᵢ := Finset.le_sup (Finset.mem_univ i)
  calc
    sobolevNorm 0 (T i v) ≤
        (Cᵢ i : ℝ) * sobolevNorm s (realMultiplierOperator η₂ v) := hCᵢ i v
    _ ≤ ((Finset.univ.sup Cᵢ : NNReal) : ℝ) *
        sobolevNorm s (realMultiplierOperator η₂ v) := by
      apply mul_le_mul_of_nonneg_right _ (sobolevNorm_nonneg _ _)
      exact_mod_cast hCi

/-- The energy commutators are all bounded on the larger localized data in L². -/
theorem localizedBesselEnergyComm_l2_bounds {N k : ℕ}
    (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (σ : ℝ)
    (V : Fin k → RealSchwartzVectorField N)
    (V₀ : RealSchwartzVectorField N) (c : SchwartzMap (Carrier N) ℝ)
    (hη₁η' : cutoffPrecedes (η₁ : Carrier N → ℝ) (η' : Carrier N → ℝ))
    (hη'η₂ : cutoffPrecedes (η' : Carrier N → ℝ) (η₂ : Carrier N → ℝ)) :
    (∃ C : NNReal, ∀ i v,
      sobolevNorm 0
        (operatorComm (vectorFieldOperator (V i))
          (localizedBesselOperator η₁ η' σ) v) ≤
        (C : ℝ) * sobolevNorm σ (realMultiplierOperator η₂ v)) ∧
    (∃ C : NNReal, ∀ i j v,
      sobolevNorm 0
        (operatorComm (vectorFieldOperator (V j))
          (operatorComm (vectorFieldOperator (V i))
            (localizedBesselOperator η₁ η' σ)) v) ≤
        (C : ℝ) * sobolevNorm σ (realMultiplierOperator η₂ v)) ∧
    (∃ C : NNReal, ∀ i j v,
      sobolevNorm 0
        (operatorComm
          (operatorComm (vectorFieldOperator (V j))
            (operatorComm (vectorFieldOperator (V i))
              (localizedBesselOperator η₁ η' σ)))
          (vectorFieldOperator (V j)) v) ≤
        (C : ℝ) * sobolevNorm σ (realMultiplierOperator η₂ v)) ∧
    (∃ C : NNReal, ∀ i v,
      sobolevNorm 0
        (operatorComm (vectorFieldOperator V₀)
          (operatorComm (vectorFieldOperator (V i))
            (localizedBesselOperator η₁ η' σ)) v) ≤
        (C : ℝ) * sobolevNorm σ (realMultiplierOperator η₂ v)) ∧
    (∃ C : NNReal, ∀ i v,
      sobolevNorm 0
        (operatorComm (realMultiplierOperator c)
          (operatorComm (vectorFieldOperator (V i))
            (localizedBesselOperator η₁ η' σ)) v) ≤
        (C : ℝ) * sobolevNorm σ (realMultiplierOperator η₂ v)) := by
  let A := localizedBesselOperator η₁ η' σ
  let T : Fin k → Operator N := fun i =>
    operatorComm (vectorFieldOperator (V i)) A
  let U : Fin k → Fin k → Operator N := fun i j =>
    operatorComm (vectorFieldOperator (V j)) (T i)
  let W : Fin k → Fin k → Operator N := fun i j =>
    operatorComm (U i j) (vectorFieldOperator (V j))
  let D : Fin k → Operator N := fun i =>
    operatorComm (vectorFieldOperator V₀) (T i)
  let C : Fin k → Operator N := fun i =>
    operatorComm (realMultiplierOperator c) (T i)
  have horders := localizedBesselOperator_energy_commutator_orders
    η₁ η' σ V V₀ c
  have hfactor := localizedBesselEnergyComm_right_factorization
    η₁ η' η₂ σ V V₀ c hη₁η' hη'η₂
  have hTorder : ∀ i, HasOrder σ (T i) := by
    intro i
    simpa [T, A, localizedBesselOperator] using horders.1 i
  have hUorder : ∀ i j, HasOrder σ (U i j) := by
    intro i j
    simpa [U, T, A, localizedBesselOperator] using (horders.2.1 i j).1
  have hWorder : ∀ i j, HasOrder σ (W i j) := by
    intro i j
    simpa [W, U, T, A, localizedBesselOperator] using (horders.2.1 i j).2
  have hDorder : ∀ i, HasOrder σ (D i) := by
    intro i
    simpa [D, T, A, localizedBesselOperator] using (horders.2.2 i).1
  have hCorder : ∀ i, HasOrder σ (C i) := by
    intro i
    simpa [C, T, A, localizedBesselOperator] using (horders.2.2 i).2
  have hTfactor : ∀ i, T i = (T i).comp (realMultiplierOperator η₂) := by
    intro i
    dsimp at hfactor
    simpa [T, A, localizedBesselOperator] using hfactor.1 i
  have hUfactor : ∀ i j, U i j = (U i j).comp (realMultiplierOperator η₂) := by
    intro i j
    dsimp at hfactor
    simpa [U, T, A, localizedBesselOperator] using hfactor.2.1 i j
  have hWfactor : ∀ i j, W i j = (W i j).comp (realMultiplierOperator η₂) := by
    intro i j
    dsimp at hfactor
    simpa [W, U, T, A, localizedBesselOperator] using hfactor.2.2.1 i j
  have hDfactor : ∀ i, D i = (D i).comp (realMultiplierOperator η₂) := by
    intro i
    dsimp at hfactor
    simpa [D, T, A, localizedBesselOperator] using hfactor.2.2.2.1 i
  have hCfactor : ∀ i, C i = (C i).comp (realMultiplierOperator η₂) := by
    intro i
    dsimp at hfactor
    simpa [C, T, A, localizedBesselOperator] using hfactor.2.2.2.2 i
  obtain ⟨CT, hCT⟩ := finiteFamily_hasOrder_l2_bound_of_right_factorization
    T η₂ σ hTorder hTfactor
  obtain ⟨CU, hCU⟩ := finiteFamily_hasOrder_l2_bound_of_right_factorization
    (fun p : Fin k × Fin k => U p.1 p.2) η₂ σ
    (fun p => hUorder p.1 p.2) (fun p => hUfactor p.1 p.2)
  obtain ⟨CW, hCW⟩ := finiteFamily_hasOrder_l2_bound_of_right_factorization
    (fun p : Fin k × Fin k => W p.1 p.2) η₂ σ
    (fun p => hWorder p.1 p.2) (fun p => hWfactor p.1 p.2)
  obtain ⟨CD, hCD⟩ := finiteFamily_hasOrder_l2_bound_of_right_factorization
    D η₂ σ hDorder hDfactor
  obtain ⟨CC, hCC⟩ := finiteFamily_hasOrder_l2_bound_of_right_factorization
    C η₂ σ hCorder hCfactor
  refine ⟨⟨CT, ?_⟩, ⟨CU, ?_⟩, ⟨CW, ?_⟩, ⟨CD, ?_⟩, ⟨CC, ?_⟩⟩
  · intro i v
    simpa [T, A, localizedBesselOperator] using hCT i v
  · intro i j v
    simpa [U, T, A, localizedBesselOperator] using hCU (i, j) v
  · intro i j v
    simpa [W, U, T, A, localizedBesselOperator] using hCW (i, j) v
  · intro i v
    simpa [D, T, A, localizedBesselOperator] using hCD i v
  · intro i v
    simpa [C, T, A, localizedBesselOperator] using hCC i v

/-- Localizing the input to the outer cutoff gives the order-`s` commutator's L² bound. -/
theorem vectorFieldLocalizedBesselComm_l2_bound {N : ℕ}
    (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (V : RealSchwartzVectorField N)
    (hη₁η' : cutoffPrecedes (η₁ : Carrier N → ℝ) (η' : Carrier N → ℝ))
    (hη'η₂ : cutoffPrecedes (η' : Carrier N → ℝ) (η₂ : Carrier N → ℝ)) :
    ∃ C : NNReal, ∀ v : TestFunction N,
      sobolevNorm 0
        (operatorComm (vectorFieldOperator V) (localizedBesselOperator η₁ η' s) v) ≤
      (C : ℝ) * sobolevNorm s (realMultiplierOperator η₂ v) := by
  let X := vectorFieldOperator V
  let A := localizedBesselOperator η₁ η' s
  let M₂ := realMultiplierOperator η₂
  have hη₁support : tsupport (η₁ : Carrier N → ℝ) ⊆
      interior {x | η₂ x = 1} := by
    have hη₁' : tsupport (η₁ : Carrier N → ℝ) ⊆
        interior {x | η' x = 1} :=
      (cutoffPrecedes_eventually_iff_interior _ _).mp hη₁η'.2.2.2.2
    have hη'₂ : tsupport (η' : Carrier N → ℝ) ⊆
        interior {x | η₂ x = 1} :=
      (cutoffPrecedes_eventually_iff_interior _ _).mp hη'η₂.2.2.2.2
    intro x hx
    have hplateau : x ∈ {y : Carrier N | η' y = 1} := interior_subset (hη₁' hx)
    have hη'one : η' x = 1 := hplateau
    have hxsupport : x ∈ tsupport (η' : Carrier N → ℝ) := by
      apply subset_tsupport
      simp [hη'one]
    exact hη'₂ hxsupport
  have hfactor :
      operatorComm X A = (operatorComm X A).comp M₂ := by
    exact localizedBesselComm_eq_comp_of_cutoff η₁ η' η₂ s V hη₁support
  obtain ⟨C, hC⟩ := vectorFieldLocalizedBesselComm_hasOrder η₁ η' s V 0
  refine ⟨C, fun v => ?_⟩
  have hv : operatorComm X A v = operatorComm X A (M₂ v) := by
    have heq := congrArg (fun O : Operator N => O v) hfactor
    simpa [M₂] using heq
  calc
    sobolevNorm 0 (operatorComm X A v) =
        sobolevNorm 0 (operatorComm X A (M₂ v)) := by rw [hv]
    _ ≤ (C : ℝ) * sobolevNorm (0 + s) (M₂ v) := hC (M₂ v)
    _ = (C : ℝ) * sobolevNorm s (realMultiplierOperator η₂ v) := by
      simp [M₂]

/-- The commutator bound is uniform over a finite family of vector fields. -/
theorem localizedBesselCommutator_family_l2_bound {N k : ℕ}
    (η₁ η' η₂ : SchwartzMap (Carrier N) ℝ) (s : ℝ)
    (V : Fin k → RealSchwartzVectorField N)
    (hη₁η' : cutoffPrecedes (η₁ : Carrier N → ℝ) (η' : Carrier N → ℝ))
    (hη'η₂ : cutoffPrecedes (η' : Carrier N → ℝ) (η₂ : Carrier N → ℝ)) :
    ∃ C : NNReal, ∀ i : Fin k, ∀ v : TestFunction N,
      sobolevNorm 0
        (operatorComm (vectorFieldOperator (V i)) (localizedBesselOperator η₁ η' s) v) ≤
      (C : ℝ) * sobolevNorm s (realMultiplierOperator η₂ v) := by
  classical
  let Cᵢ : Fin k → NNReal := fun i =>
    Classical.choose
      (vectorFieldLocalizedBesselComm_l2_bound η₁ η' η₂ s (V i) hη₁η' hη'η₂)
  have hCᵢ (i : Fin k) : ∀ v : TestFunction N,
      sobolevNorm 0
        (operatorComm (vectorFieldOperator (V i)) (localizedBesselOperator η₁ η' s) v) ≤
        (Cᵢ i : ℝ) * sobolevNorm s (realMultiplierOperator η₂ v) :=
    Classical.choose_spec
      (vectorFieldLocalizedBesselComm_l2_bound η₁ η' η₂ s (V i) hη₁η' hη'η₂)
  refine ⟨Finset.univ.sup Cᵢ, fun i v => ?_⟩
  have hCi : Cᵢ i ≤ Finset.univ.sup Cᵢ := Finset.le_sup (Finset.mem_univ i)
  calc
    sobolevNorm 0
        (operatorComm (vectorFieldOperator (V i)) (localizedBesselOperator η₁ η' s) v) ≤
        (Cᵢ i : ℝ) * sobolevNorm s (realMultiplierOperator η₂ v) := hCᵢ i v
    _ ≤ ((Finset.univ.sup Cᵢ : NNReal) : ℝ) *
        sobolevNorm s (realMultiplierOperator η₂ v) := by
      apply mul_le_mul_of_nonneg_right _ (sobolevNorm_nonneg _ _)
      exact_mod_cast hCi

end Hormander.D

end
