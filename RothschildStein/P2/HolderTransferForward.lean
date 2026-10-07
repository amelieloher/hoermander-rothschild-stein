-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.NormTransfer
public import RothschildStein.S.IntrinsicCurveExistence
public import RothschildStein.G1.WeightedTriangle
public import RothschildStein.Definitions.holderXENorm
public import RothschildStein.Definitions.memHolderX

/-!
# The forward Hölder inequality

For `f̃ = f ∘ π` on a lifted chart, the projection `π = basePoint` is `1`-Lipschitz for the control
distances, `d(π ξ, π ξ') ≤ d̃(ξ, ξ')` (a controlled curve of the lifted fields projects to a
controlled curve of the base fields with the same controls), and the intrinsic derivative of
`f ∘ π` along `X̃ᵢ` is the lift of that of `f` along `Xᵢ` (the `∂_t` part of `X̃ᵢ` does not see
`f ∘ π`). Hence `‖f̃‖_{C^α(U)} ≤ ‖f‖_{C^α(V)}` for the sup norm, the Hölder seminorm and every word
`X_I f` (BB pp. 597-599, Thm 11.54, Prop 11.56, (11.88)-(11.91)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2
variable {n k m : ℕ} {w : Fin k → ℕ+} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}
  {P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ}

/-- The projection `π = basePoint` as a continuous linear map. -/
def basePointCLM (n m : ℕ) : (Fin (n + m) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.castAdd m j)

theorem basePointCLM_apply (ξ : Fin (n + m) → ℝ) : basePointCLM n m ξ = basePoint ξ := rfl

/-- The horizontal part of a triangular lift is the original field at the projected point. -/
theorem basePoint_triangularLift (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ) (i : Fin k) (ξ : Fin (n + m) → ℝ) :
    basePoint (triangularLift X P i ξ) = X i (basePoint ξ) := by
  funext j
  simp [basePoint, triangularLift]

/-- A controlled curve of the lifted fields projects to a controlled
curve of the base fields with the same control parameter. -/
theorem isControlledCurve_basePoint {Ω : Set (Fin n → ℝ)} {δ : ℝ} {γ : ℝ → Fin (n + m) → ℝ}
    (hγ : isControlledCurve {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X P) δ γ) :
    isControlledCurve Ω w X δ (fun t => basePoint (γ t)) := by
  obtain ⟨hδ, hac, hmaps, a, ha, hae⟩ := hγ
  refine ⟨hδ, ?_, ?_, a, ha, ?_⟩
  · exact (basePointCLM n m).lipschitzWith.comp_absolutelyContinuousOnInterval hac
  · intro t ht
    exact hmaps ht
  · filter_upwards [hae] with t ht
    refine ⟨ht.1, ?_⟩
    have h2 := (basePointCLM n m).hasFDerivAt.comp_hasDerivAt t ht.2
    have h3 : (basePointCLM n m) (∑ i, a i t • triangularLift X P i (γ t)) =
        ∑ i, a i t • X i (basePoint (γ t)) := by
      simp only [map_sum, map_smul, basePointCLM_apply, basePoint_triangularLift]
    rw [h3] at h2
    exact h2

/-- `d(π ξ, π ξ') ≤ d̃(ξ, ξ')` (BB p. 598). -/
theorem controlDistance_basePoint_le (Ω : Set (Fin n → ℝ)) (w : Fin k → ℕ+)
    (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ) (ξ ξ' : Fin (n + m) → ℝ) :
    controlDistance Ω w X (basePoint ξ) (basePoint ξ') ≤
      controlDistance {ζ : Fin (n + m) → ℝ | basePoint ζ ∈ Ω} w (triangularLift X P) ξ ξ' := by
  apply sInf_le_sInf
  rintro r ⟨δ, rfl, γ, hγ, h0, h1⟩
  exact ⟨δ, rfl, fun t => basePoint (γ t), isControlledCurve_basePoint hγ,
    by simp [h0], by simp [h1]⟩

/-- Projection of balls: `π (B̃(η, r)) ⊆ B(π η, r)`. -/
theorem basePoint_mem_rsBall {Ω : Set (Fin n → ℝ)} {η ξ : Fin (n + m) → ℝ} {r : ℝ}
    (hξ : ξ ∈ rsBall {ζ : Fin (n + m) → ℝ | basePoint ζ ∈ Ω} w (triangularLift X P) η r) :
    basePoint ξ ∈ rsBall Ω w X (basePoint η) r :=
  ⟨hξ.1, lt_of_le_of_lt (controlDistance_basePoint_le Ω w X P η ξ) hξ.2⟩

/-- Composition with a map that does not increase the distance: the Hölder seminorm of `g ∘ π`
over `A` is at most that of `g` over `V`. -/
theorem holderSeminorm_comp_le {d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞}
    {dl : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ≥0∞} {α : ℝ} (hα : 0 ≤ α)
    {A : Set (Fin (n + m) → ℝ)} {V : Set (Fin n → ℝ)} (hAV : ∀ ξ ∈ A, basePoint ξ ∈ V)
    (hd : ∀ ξ ∈ A, ∀ ξ' ∈ A, d (basePoint ξ) (basePoint ξ') ≤ dl ξ ξ') (g : (Fin n → ℝ) → ℝ) :
    holderSeminorm dl α A (fun ξ => g (basePoint ξ)) ≤ holderSeminorm d α V g := by
  apply sInf_le_sInf
  rintro C ⟨hC, hCV⟩
  refine ⟨hC, fun ξ hξ ξ' hξ' hlt => ?_⟩
  have hlt' : d (basePoint ξ) (basePoint ξ') < ⊤ := lt_of_le_of_lt (hd ξ hξ ξ' hξ') hlt
  exact (hCV _ (hAV ξ hξ) _ (hAV ξ' hξ') hlt').trans
    (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hd ξ hξ ξ' hξ') hα))

/-- The Hölder norm of `g ∘ π` over `A` is at most that of `g` over `V`. -/
theorem holderENorm_comp_le {d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞}
    {dl : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ≥0∞} {α : ℝ} (hα : 0 ≤ α)
    {A : Set (Fin (n + m) → ℝ)} {V : Set (Fin n → ℝ)} (hAV : ∀ ξ ∈ A, basePoint ξ ∈ V)
    (hd : ∀ ξ ∈ A, ∀ ξ' ∈ A, d (basePoint ξ) (basePoint ξ') ≤ dl ξ ξ') (g : (Fin n → ℝ) → ℝ) :
    holderENorm dl α A (fun ξ => g (basePoint ξ)) ≤ holderENorm d α V g := by
  unfold holderENorm
  refine add_le_add ?_ (holderSeminorm_comp_le hα hAV hd g)
  exact iSup_le fun ξ => le_iSup_of_le (⟨basePoint ξ.1, hAV ξ.1 ξ.2⟩ : V) le_rfl

/-- The lift of an intrinsic derivative: if `g` is the intrinsic `Xᵢ`-derivative of `h` on `Vo`,
then `g ∘ π` is the intrinsic `X̃ᵢ`-derivative of `h ∘ π` on `Uo` (the integral curves of `X̃ᵢ`
project to integral curves of `Xᵢ`). -/
theorem hasIntrinsicDeriv_comp_basePoint (Uo : Opens (Fin (n + m) → ℝ)) (Vo : Opens (Fin n → ℝ))
    (hproj : ∀ ξ ∈ (Uo : Set (Fin (n + m) → ℝ)), basePoint ξ ∈ (Vo : Set (Fin n → ℝ)))
    (i : Fin k) (hXt : ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    {h g : (Fin n → ℝ) → ℝ} (hg : hasIntrinsicDeriv Vo (X i) h g) :
    hasIntrinsicDeriv Uo (triangularLift X P i) (fun ξ => h (basePoint ξ))
      (fun ξ => g (basePoint ξ)) := by
  intro ξ hξ
  refine ⟨RothschildStein.S.exists_intrinsic_integral_curve Uo _ hXt hξ, ?_⟩
  intro γ hγ0 hγ hev
  have hπ : IsIntegralCurveAt (fun t => basePoint (γ t)) (fun _ => X i) 0 := by
    filter_upwards [hγ] with t ht
    have h2 := (basePointCLM n m).hasFDerivAt.comp_hasDerivAt t ht
    simp only [basePointCLM_apply, basePoint_triangularLift] at h2
    exact h2
  exact (hg (basePoint ξ) (hproj ξ hξ)).2 (fun t => basePoint (γ t)) (by simp [hγ0]) hπ
    (by filter_upwards [hev] with t ht using hproj _ ht)

/-- Lift identity: an intrinsic word derivative `X_I f = g` on `Vo`
lifts to `X̃_I (f ∘ π) = g ∘ π` on `Uo`. -/
theorem hasIntrinsicWordDeriv_comp_basePoint (Uo : Opens (Fin (n + m) → ℝ))
    (Vo : Opens (Fin n → ℝ))
    (hproj : ∀ ξ ∈ (Uo : Set (Fin (n + m) → ℝ)), basePoint ξ ∈ (Vo : Set (Fin n → ℝ)))
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ))) :
    ∀ (I : List (Fin k)) {f g : (Fin n → ℝ) → ℝ}, hasIntrinsicWordDeriv X Vo I f g →
      hasIntrinsicWordDeriv (triangularLift X P) Uo I (fun ξ => f (basePoint ξ))
        (fun ξ => g (basePoint ξ))
  | [], _, _, h => fun ξ hξ => h (hproj ξ hξ)
  | i :: I, _, _, ⟨h', h1, h2⟩ =>
      ⟨fun ξ => h' (basePoint ξ), hasIntrinsicWordDeriv_comp_basePoint Uo Vo hproj hXt I h1,
        hasIntrinsicDeriv_comp_basePoint Uo Vo hproj i (hXt i) h2⟩

/-- Per word: `‖X̃_I f̃‖_{C^α(Uo)} ≤ ‖X_I f‖_{C^α(Vo)}` (the intrinsic
norm is an infimum over the derivatives, which lift). -/
theorem intrinsicWordENorm_comp_le (Ω : Set (Fin n → ℝ)) (Uo : Opens (Fin (n + m) → ℝ))
    (Vo : Opens (Fin n → ℝ))
    (hproj : ∀ ξ ∈ (Uo : Set (Fin (n + m) → ℝ)), basePoint ξ ∈ (Vo : Set (Fin n → ℝ)))
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    {α : ℝ} (hα : 0 ≤ α) (I : List (Fin k)) (f : (Fin n → ℝ) → ℝ) :
    intrinsicWordENorm (triangularLift X P)
        (controlDistance {ζ : Fin (n + m) → ℝ | basePoint ζ ∈ Ω} w (triangularLift X P))
        Uo I α (fun ξ => f (basePoint ξ)) ≤
      intrinsicWordENorm X (controlDistance Ω w X) Vo I α f := by
  unfold intrinsicWordENorm
  refine le_sInf ?_
  rintro r ⟨g, hg, rfl⟩
  refine sInf_le_of_le ⟨fun ξ => g (basePoint ξ),
    hasIntrinsicWordDeriv_comp_basePoint Uo Vo hproj hXt I hg, rfl⟩ ?_
  exact holderENorm_comp_le hα hproj (fun ξ _ ξ' _ => controlDistance_basePoint_le Ω w X P ξ ξ') g

/-- The weighted `C^{j,α}` norm of `f̃ = f ∘ π` over `Uo` is at most
that of `f` over `Vo`, for any lifted open set `Uo` projecting into `Vo` (BB pp. 597-599). -/
theorem holderXENorm_comp_le (Ω : Set (Fin n → ℝ)) (Uo : Opens (Fin (n + m) → ℝ))
    (Vo : Opens (Fin n → ℝ))
    (hproj : ∀ ξ ∈ (Uo : Set (Fin (n + m) → ℝ)), basePoint ξ ∈ (Vo : Set (Fin n → ℝ)))
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    {α : ℝ} (hα : 0 ≤ α) (j : ℕ) (f : (Fin n → ℝ) → ℝ) :
    holderXENorm w (triangularLift X P)
        (controlDistance {ζ : Fin (n + m) → ℝ | basePoint ζ ∈ Ω} w (triangularLift X P))
        Uo j α (fun ξ => f (basePoint ξ)) ≤
      holderXENorm w X (controlDistance Ω w X) Vo j α f := by
  unfold holderXENorm
  exact Finset.sum_le_sum fun I _ =>
    intrinsicWordENorm_comp_le (w := w) Ω Uo Vo hproj hXt hα I f

/-- Membership in the lifted weighted Hölder space is inherited:
if `f ∈ C^{j,α}_X(Vo)` then `f ∘ π ∈ C^{j,α}_{X̃}(Uo)`. -/
theorem memHolderX_comp_basePoint (Ω : Set (Fin n → ℝ)) (Uo : Opens (Fin (n + m) → ℝ))
    (Vo : Opens (Fin n → ℝ))
    (hproj : ∀ ξ ∈ (Uo : Set (Fin (n + m) → ℝ)), basePoint ξ ∈ (Vo : Set (Fin n → ℝ)))
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    {α : ℝ} (hα : 0 ≤ α) (j : ℕ) {f : (Fin n → ℝ) → ℝ}
    (hf : memHolderX w X (controlDistance Ω w X) Vo j α f) :
    memHolderX w (triangularLift X P)
      (controlDistance {ζ : Fin (n + m) → ℝ | basePoint ζ ∈ Ω} w (triangularLift X P))
      Uo j α (fun ξ => f (basePoint ξ)) := by
  obtain ⟨hf0, hfI⟩ := hf
  refine ⟨lt_of_le_of_lt (holderENorm_comp_le hα hproj
    (fun ξ _ ξ' _ => controlDistance_basePoint_le Ω w X P ξ ξ') f) hf0, fun I hI => ?_⟩
  obtain ⟨g, hg, hgf⟩ := hfI I hI
  exact ⟨fun ξ => g (basePoint ξ), hasIntrinsicWordDeriv_comp_basePoint Uo Vo hproj hXt I hg,
    lt_of_le_of_lt (holderENorm_comp_le hα hproj
      (fun ξ _ ξ' _ => controlDistance_basePoint_le Ω w X P ξ ξ') g) hgf⟩

/-- (BB Thm 11.54, (11.88)): on the control balls of a lifted chart,
`‖f̃‖_{C^{j,α}_{X̃}(U_r)} ≤ ‖f‖_{C^{j,α}_X(V_r)}` for `U_r = B̃(η, r)`, `V_r = B(π η, r)`, every
`α ≥ 0`, `j` and `f`. The sup norm, the Hölder seminorm and every `X_I f` are compared. -/
theorem holderTransfer_forward {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω} {x₀ : Fin n → ℝ}
    (C : LiftedChart w s Ω hΩ X x₀ m) {α : ℝ} (hα : 0 ≤ α) (η : Fin (n + m) → ℝ) (r : ℝ)
    (Vr : Opens (Fin n → ℝ)) (Ur : Opens (Fin (n + m) → ℝ))
    (hVr : (Vr : Set (Fin n → ℝ)) = rsBall Ω w X (basePoint η) r)
    (hUr : (Ur : Set (Fin (n + m) → ℝ)) = rsBall C.O w C.Xl η r) (j : ℕ)
    (f : (Fin n → ℝ) → ℝ) :
    holderXENorm w C.Xl C.dl Ur j α (fun ξ => f (basePoint ξ)) ≤
      holderXENorm w X (controlDistance Ω w X) Vr j α f := by
  have hUO : (Ur : Set (Fin (n + m) → ℝ)) ⊆ C.O := by
    rw [hUr]
    exact fun ξ hξ => hξ.1
  have hproj : ∀ ξ ∈ (Ur : Set (Fin (n + m) → ℝ)), basePoint ξ ∈ (Vr : Set (Fin n → ℝ)) := by
    intro ξ hξ
    rw [hVr]
    exact basePoint_mem_rsBall (P := C.P) (hUr ▸ hξ)
  exact holderXENorm_comp_le (P := C.P) Ω Ur Vr hproj
    (fun i => (C.lift_smooth i).mono hUO) hα j f

end RothschildStein.P2
