-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityReconstructionNear

/-!
# Hölder continuity of the near part of a degree `-Q` term

For one principal term `a(ξ) K(ξ, η) b(η)` of degree `2` (`K = (D Γ)(Θ)`), `0 < α < 1`, and the
near certificate (Data D on every doubled ball, finite localization), the pointwise
principal value on `C^α(V)`, `V ⊆ U` open,

`T_near f (ξ) = lim_{ε ↓ 0} ∫_{ρ(ξ,η) > ε} a(ξ) K^φ(ξ, η) b(η) f(η) dη = a(ξ) ∑_j (T_j (b f))(ξ)`

exists at every `ξ` and satisfies, in terms of `holderENorm` (with the lifted control
distance `C.dl`),
`‖T_near f‖_{C^α(V)} ≤ C ‖f‖_{C^α(V)}` (`exists_nearOutput_holder_bound`).

The proof composes: the controlled Hölder extension of `b f` into the carrier
(`exists_boundedHolder_mul_extension`, the margin `δ_b`), H2's singular integral bound on `C^δ` for every local operator `T_j`
(`localKernelData_principalValue_holder`, the Hölder constant `N₁ + T(1)` of Prop 7.17 and Cor 7.19
with `β₀ = β = ν = 1 > α`), the zero extension of the local outputs, the finite sum, the Lipschitz
multiplier `a`, and the comparison of the carrier norm with `holderENorm`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The test cutoffs `a, b` of a principal term relative to
the patch `V ⊆ U` (open) and the output support `Fs`: `a, b` are smooth with compact support
inside `V`, and `a ≠ 0` only on `Fs`. -/
structure IsTermCutoffs (V Fs : Set (Fin (n + m) → ℝ)) (a b : (Fin (n + m) → ℝ) → ℝ) :
    Prop where
  open_V : IsOpen V
  V_sub : V ⊆ C.U
  a_smooth : ContDiff ℝ (⊤ : ℕ∞) a
  a_compact : HasCompactSupport a
  a_support : tsupport a ⊆ V
  a_Fs : ∀ ξ, a ξ ≠ 0 → ξ ∈ Fs
  b_smooth : ContDiff ℝ (⊤ : ℕ∞) b
  b_compact : HasCompactSupport b
  b_support : tsupport b ⊆ V

variable {C}

/-- The cutoffs `a, b ∈ C_c^∞(V)` of a principal term
(`PrincipalTerm`) are term cutoffs for the patch `V ⊆ U` and the output support `supp a`. -/
theorem IsTermCutoffs.of_testFunction (V : TopologicalSpace.Opens (Fin (n + m) → ℝ))
    (hV : (V : Set (Fin (n + m) → ℝ)) ⊆ C.U) (a b : TestFunction V ℝ (⊤ : ℕ∞)) :
    C.IsTermCutoffs (V : Set (Fin (n + m) → ℝ)) (tsupport a) a b :=
  ⟨V.isOpen, hV, a.contDiff, a.hasCompactSupport, a.tsupport_subset,
    fun _ h => subset_tsupport _ h, b.contDiff, b.hasCompactSupport, b.tsupport_subset⟩

section Cutoffs

variable {V Fs : Set (Fin (n + m) → ℝ)} {a b : (Fin (n + m) → ℝ) → ℝ}

/-- The input cutoff `b` vanishes outside the chart domain. -/
theorem IsTermCutoffs.b_zero (hc : C.IsTermCutoffs V Fs a b) :
    ∀ ξ, ξ ∉ C.U → b ξ = 0 := fun _ hξ =>
  image_eq_zero_of_notMem_tsupport (fun h => hξ (hc.V_sub (hc.b_support h)))

end Cutoffs

section Holder

variable {ν : (Fin (n + m) → ℝ) → ℝ} {Fs V : Set (Fin (n + m) → ℝ)}
  {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
  {Γ : (Fin (n + m) → ℝ) → ℝ} {cert : C.NearCertificate ν Fs}
  {a b : (Fin (n + m) → ℝ) → ℝ}

/-- **Hölder continuity of the near part** (for one degree-2 term; BB pp.
306-309, Prop 7.17 and Cor 7.19 with the Data D). For `0 < α < 1` there is `C_H` such that
for every `f` of finite Hölder norm `‖f‖_{C^α(V)}` (lifted control distance) the `ρ`-principal
value of the near part `a(ξ) K^φ(ξ, η) b(η)` against `f` exists at every point `ξ`, with value
`nearOutput = a(ξ) ∑_j (T_j (b f))(ξ)`, and
`‖T_near f‖_{C^α(V)} ≤ C_H ‖f‖_{C^α(V)}`. -/
theorem exists_nearOutput_holder_bound (dd : C.NearDataD cert D Γ)
    (hνg : C.G.IsHomogeneousGauge ν) (hc : C.IsTermCutoffs V Fs a b) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) :
    ∃ CH : ℝ, 0 < CH ∧ ∀ f : (Fin (n + m) → ℝ) → ℝ, holderENorm C.dl α V f ≠ ⊤ →
      (∀ ξ, HasRhoPV (C.rhoGauge ν) (C.nearKernel ν D Γ cert.φ a b) f ξ
        (nearOutput dd a b f ξ)) ∧
      holderENorm C.dl α V (nearOutput dd a b f) ≤
        ENNReal.ofReal CH * holderENorm C.dl α V f := by
  classical
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ≥0, δ = α.toNNReal := ⟨_, rfl⟩
  have hδα : (δ : ℝ) = α := by rw [hδdef]; exact Real.coe_toNNReal _ hα0.le
  have hδ : 0 < δ := by rw [← NNReal.coe_pos, hδα]; exact hα0
  have hδ1 : δ ≤ 1 := by
    rw [← NNReal.coe_le_coe, hδα]
    exact_mod_cast hα1.le
  obtain ⟨K, hK, hKb⟩ := exists_boundedHolder_mul_extension (C := C) hc.open_V hc.V_sub
    hc.b_smooth hc.b_compact hc.b_support hα0 hα1.le
  rw [← hδdef] at hKb
  obtain ⟨Ma, hMa⟩ := hc.a_smooth.continuous.bounded_above_of_compact_support hc.a_compact
  obtain ⟨La, hLa⟩ := exists_lipschitzWith_of_contDiff_compact (C := C) hc.a_smooth
    (fun ξ => by simpa using hMa ξ) hc.a_compact (hc.a_support.trans hc.V_sub)
  have hAH : H2.BoundedHolder δ univ (fun y : C.Carrier => a y.val) :=
    boundedHolder_univ_of_lipschitz hLa (fun y => by simpa using hMa y.val) hδ1
  obtain ⟨Cz, hCz⟩ : ∃ Cz : cert.t → ℝ≥0∞, Cz = fun z => ENNReal.ofReal
      ((1 + (4 / (3 * (dd.Q z).R)) ^ (δ : ℝ)) * (dd.Q z).operatorHolderConstant δ) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ≥0∞, E = H2.boundedHolderNorm δ univ (fun y : C.Carrier => a y.val) *
      (∑ z, Cz z) * ENNReal.ofReal K := ⟨_, rfl⟩
  have hCztop : ∀ z, Cz z ≠ ⊤ := fun z => by rw [hCz]; exact ENNReal.ofReal_ne_top
  have hEtop : E ≠ ⊤ := by
    rw [hE]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hAH.ne
      (ENNReal.sum_ne_top.mpr fun z _ => hCztop z)) ENNReal.ofReal_ne_top
  have hδ₀ : ∀ z : cert.t, (δ : ℝ) < (dd.Q z).β₀ := fun z => by
    rw [(dd.split z).β₀_eq, hδα]; exact hα1
  have hδβ : ∀ z : cert.t, (δ : ℝ) < (dd.Q z).β := fun z => by
    rw [(dd.split z).β_eq, hδα]; exact hα1
  have hδν : ∀ z : cert.t, (δ : ℝ) < (dd.Q z).ν := fun z => by
    rw [(dd.split z).ν_eq, hδα]; exact hα1
  refine ⟨E.toReal + 1, by positivity, fun f hf => ?_⟩
  have hgU : H2.BoundedHolder δ univ (C.inputCarrier b f) :=
    (hKb f).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hf))
  have hgz : ∀ z : cert.t, H2.BoundedHolder δ (ball z.1 cert.r) (C.inputCarrier b f) :=
    fun z => (H2.boundedHolderNorm_restrict (subset_univ _)).trans_lt hgU
  refine ⟨fun ξ => hasRhoPV_near dd hνg hc.a_Fs hc.b_zero hδ hgz ξ, ?_⟩
  have hpv : ∀ z : cert.t, H2.boundedHolderNorm δ univ
      ((dd.Q z).principalValue (C.inputCarrier b f)) ≤
        Cz z * H2.boundedHolderNorm δ univ (C.inputCarrier b f) := by
    intro z
    have h1 := localKernelData_principalValue_holder (dd.Q z) hδ (hδ₀ z) (hδβ z) (hδν z)
      (fun x hx => Q_a_eq_zero_of_not_mem dd z hx) (boundedHolder_Q_ball dd hgz z)
    rw [hCz]
    refine h1.trans ?_
    gcongr
    exact H2.boundedHolderNorm_restrict (subset_univ _)
  have hsum : H2.boundedHolderNorm δ univ
      (fun y : C.Carrier => ∑ z : cert.t, (dd.Q z).principalValue (C.inputCarrier b f) y) ≤
        (∑ z, Cz z) * H2.boundedHolderNorm δ univ (C.inputCarrier b f) := by
    calc _ ≤ ∑ z : cert.t, H2.boundedHolderNorm δ univ
          ((dd.Q z).principalValue (C.inputCarrier b f)) :=
          H2.boundedHolderNorm_sum_le _ _ _ _
      _ ≤ ∑ z : cert.t, Cz z * H2.boundedHolderNorm δ univ (C.inputCarrier b f) :=
          Finset.sum_le_sum fun z _ => hpv z
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hsumH : H2.BoundedHolder δ univ
      (fun y : C.Carrier => ∑ z : cert.t, (dd.Q z).principalValue (C.inputCarrier b f) y) :=
    hsum.trans_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr
      (ENNReal.sum_ne_top.mpr fun z _ => hCztop z)) hgU)
  have hprod := H2.boundedHolderNorm_mul_le hAH hsumH
  have hO : (fun y : C.Carrier => nearOutput dd a b f y.val) = fun y => a y.val *
      ∑ z : cert.t, (dd.Q z).principalValue (C.inputCarrier b f) y := by
    funext y
    simp only [nearOutput, y.val_mem, ↓reduceDIte, Carrier.mk_val]
  have hle : E ≤ ENNReal.ofReal (E.toReal + 1) :=
    calc E = ENNReal.ofReal E.toReal := (ENNReal.ofReal_toReal hEtop).symm
      _ ≤ ENNReal.ofReal (E.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  calc holderENorm C.dl α V (nearOutput dd a b f)
      ≤ H2.boundedHolderNorm α.toNNReal univ (fun y : C.Carrier => nearOutput dd a b f y.val) :=
        holderENorm_le_boundedHolderNorm hc.V_sub hα0 _
    _ = H2.boundedHolderNorm δ univ (fun y : C.Carrier => a y.val *
        ∑ z : cert.t, (dd.Q z).principalValue (C.inputCarrier b f) y) := by
        rw [hO, ← hδdef]
    _ ≤ H2.boundedHolderNorm δ univ (fun y : C.Carrier => a y.val) *
        H2.boundedHolderNorm δ univ
          (fun y : C.Carrier => ∑ z : cert.t, (dd.Q z).principalValue (C.inputCarrier b f) y) :=
        hprod
    _ ≤ H2.boundedHolderNorm δ univ (fun y : C.Carrier => a y.val) *
        ((∑ z, Cz z) * (ENNReal.ofReal K * holderENorm C.dl α V f)) := by
        gcongr
        exact hsum.trans (by gcongr; exact hKb f)
    _ = E * holderENorm C.dl α V f := by rw [hE]; ring
    _ ≤ ENNReal.ofReal (E.toReal + 1) * holderENorm C.dl α V f := by gcongr

end Holder

end LiftedChart
end RothschildStein.P1
