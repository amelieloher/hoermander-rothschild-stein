-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ParametrixKernelBoundsChart
public import RothschildStein.P1.RightPoleComputation

/-!
# Differentiation operators on symbols and the chain rule of the chart

With a chart extension `ex : C.ChartExt L` (`ParametrixKernelBoundsChart`) the first-order chain
rule `X̃_{i,ξ}[A(ξ, η, Θ(η, ξ))] = (D_i A)(ξ, η, Θ(η, ξ))` of the kernel estimates (`fderiv_kernel_field`),
`D_i A(ξ, η, u) = D_ξ A · X̃_i(ξ) + D_u A · (Y_i(u) + R_{[i],η}(u))`, becomes an operator `ex.Do i`
on globally defined families that lowers the degree of a symbol by the weight `w_i`
(`ChartExt.Do_class`). Iterating, the second derivatives of a kernel in the output variable are
`D_j D_i A` evaluated on `Θ(η, ξ)`. The operators `ex.dY i`, `ex.dR i` (derivative along the
model field `Y_i` and along the extended remainder `Rt_{[i]}`) build the error terms of the right pole computation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.P1

section Field

variable {N : ℕ} {G : HomogeneousGroup N} {K : Set ((Fin N → ℝ) × (Fin N → ℝ))} {R : ℝ}

/-- Differentiation along `(0, 0, v(ξ, η, u))`: if the coordinates `v_j` have degree
`w_j - e`, the degree drops by `e`. -/
theorem WtSym.field_u {k : ℕ} {d e : ℤ} (v : KZ N → (Fin N → ℝ))
    (hv : ∀ j : Fin N, WtSym G K R k ((G.weight j : ℤ) - e) (fun z => v z j)) {A : KZ N → ℝ}
    (hA : WtSym G K R (k + 1) d A) :
    WtSym G K R k (d - e) (fun z => fderiv ℝ A z (0, 0, v z)) := by
  refine WtSym.field (fun z => ((0 : Fin N → ℝ), (0 : Fin N → ℝ), v z)) (fun s => ?_) hA
  rcases s with l | l | j
  · refine WtSym.congr (fun z _ => rfl) (WtSym.zero_fun (k := k) (d := symWt G (Sum.inl l) - e))
  · refine WtSym.congr (fun z _ => rfl)
      (WtSym.zero_fun (k := k) (d := symWt G (Sum.inr (Sum.inl l)) - e))
  · exact hv j

/-- Differentiation along `(a(ξ, η, u), 0, v(ξ, η, u))` with `a` of degree `≤ -e` in each
coordinate and `v_j` of degree `w_j - e`: the degree drops by `e`. -/
theorem WtSym.field_xu {k : ℕ} {d e : ℤ} (a v : KZ N → (Fin N → ℝ))
    (ha : ∀ l : Fin N, WtSym G K R k (-e) (fun z => a z l))
    (hv : ∀ j : Fin N, WtSym G K R k ((G.weight j : ℤ) - e) (fun z => v z j)) {A : KZ N → ℝ}
    (hA : WtSym G K R (k + 1) d A) :
    WtSym G K R k (d - e) (fun z => fderiv ℝ A z (a z, 0, v z)) := by
  refine WtSym.field (fun z => (a z, (0 : Fin N → ℝ), v z)) (fun s => ?_) hA
  rcases s with l | l | j
  · exact (ha l).degree_congr (by simp [symWt])
  · refine WtSym.congr (fun z _ => rfl)
      (WtSym.zero_fun (k := k) (d := symWt G (Sum.inr (Sum.inl l)) - e))
  · exact hv j

end Field

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {L : Set (Fin (n + m) → ℝ)}

namespace ChartExt

variable (ex : C.ChartExt L)

/-- Derivative of a family along the model field `Y_i(u)`. -/
def dY (i : Fin k) (A : KZ (n + m) → ℝ) : KZ (n + m) → ℝ :=
  fun z => fderiv ℝ A z (0, 0, C.Y i z.2.2)

/-- Derivative of a family along the extended remainder field `Rt_{[i]}(η, u)`. -/
def dR (i : Fin k) (A : KZ (n + m) → ℝ) : KZ (n + m) → ℝ :=
  fun z => fderiv ℝ A z (0, 0, ex.Rt i z.2.1 z.2.2)

/-- The output-variable chain-rule operator `D_i A = D_ξ A · X̃_i(ξ) + D_u A · (Y_i + Rt_{[i]})`
(with the extended lifted field `Xb_i`). -/
def Do (i : Fin k) (A : KZ (n + m) → ℝ) : KZ (n + m) → ℝ :=
  fun z => fderiv ℝ A z (ex.Xb i z.1, 0, C.Y i z.2.2 + ex.Rt i z.2.1 z.2.2)

variable {K : Set ((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ))} {R : ℝ}

/-- `dY_i` lowers the degree by `w_i`. -/
theorem dY_class {dp : ℕ} {d : ℤ} {A : KZ (n + m) → ℝ} (hA : WtSym C.G K R (dp + 1) d A)
    (i : Fin k) : WtSym C.G K R dp (d - ((w i : ℕ) : ℤ)) (dY (C := C) i A) :=
  WtSym.field_u (fun z => C.Y i z.2.2)
    (fun j => WtSym.fieldCoord C.G K R dp (a := (w i : ℕ)) (C.model_field_smooth i)
      (fun t ht u => C.model_field_homogeneous i t ht u) j) hA

/-- `dR_i` lowers the degree by `w_i - 1` (the remainder field has weight `≥ 1 - w_i`). -/
theorem dR_class (hK : IsCompact K) (hR : 0 < R) {dp : ℕ} {d : ℤ} {A : KZ (n + m) → ℝ}
    (hA : WtSym C.G K R (dp + 1) d A) (i : Fin k) :
    WtSym C.G K R dp (d - (((w i : ℕ) : ℤ) - 1)) (ex.dR i A) :=
  WtSym.field_u (fun z => ex.Rt i z.2.1 z.2.2)
    (fun j => (ex.Rt_class i j K hK R hR dp).degree_congr (by ring)) hA

/-- **`D_i` lowers the degree by `w_i`**: the derivative of a symbol along the chain-rule
field of `X̃_i` (parameter part of degree `0`, `u`-part `Y_i + Rt_{[i]}` of weight `w_i`). -/
theorem Do_class (hK : IsCompact K) (hR : 0 < R) {dp : ℕ} {d : ℤ} {A : KZ (n + m) → ℝ}
    (hA : WtSym C.G K R (dp + 1) d A) (i : Fin k) :
    WtSym C.G K R dp (d - ((w i : ℕ) : ℤ)) (ex.Do i A) := by
  refine WtSym.field_xu (fun z => ex.Xb i z.1) (fun z => C.Y i z.2.2 + ex.Rt i z.2.1 z.2.2)
    (fun l => ?_) (fun j => ?_) hA
  · have h0 := WtSym.param (G := C.G) (R := R) (k := dp) hK
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => ex.Xb i p.1 l)
      ((ex.Xb_smooth i l).comp contDiff_fst)
    exact WtSym.mono_d hR (by have := (w i).pos; omega) h0
  · have h1 := WtSym.fieldCoord C.G K R dp (a := (w i : ℕ)) (C.model_field_smooth i)
      (fun t ht u => C.model_field_homogeneous i t ht u) j
    have h2 := WtSym.mono_d hR (d := (C.G.weight j : ℤ) - ((w i : ℕ) : ℤ) + 1)
      (d' := (C.G.weight j : ℤ) - ((w i : ℕ) : ℤ)) (by omega) (ex.Rt_class i j K hK R hR dp)
    exact WtSym.add h1 h2

/-- `D_i A` is smooth off `u = 0` when `A` is. -/
theorem contDiffOn_Do {A : KZ (n + m) → ℝ} (hA : ContDiffOn ℝ (⊤ : ℕ∞) A {z | z.2.2 ≠ 0})
    (i : Fin k) : ContDiffOn ℝ (⊤ : ℕ∞) (ex.Do i A) {z | z.2.2 ≠ 0} := by
  have hV : ContDiff ℝ (⊤ : ℕ∞) (fun z : KZ (n + m) =>
      ((ex.Xb i z.1, (0 : Fin (n + m) → ℝ), C.Y i z.2.2 + ex.Rt i z.2.1 z.2.2) : KZ (n + m))) := by
    refine ContDiff.prodMk ?_ (contDiff_const.prodMk ?_)
    · exact contDiff_pi.2 (fun l => (ex.Xb_smooth i l).comp contDiff_fst)
    · refine ContDiff.add ((C.model_field_smooth i).comp contDiff_snd.snd) ?_
      exact contDiff_pi.2 (fun j => (ex.Rt_smooth i j).comp contDiff_snd)
  exact (hA.fderiv_of_isOpen isOpen_kernelDomain (by simp)).clm_apply hV.contDiffOn

/-- **Chain rule of the chart for the output variable.** For `η, ξ ∈ U`, `ξ ≠ η` with
`(η, Θ(η, ξ)) ∈ V` (where `Rt = R`) and `A` smooth off `u = 0`:
`X̃_{i,ξ}[A(ξ, η, Θ(η, ξ))] = (D_i A)(ξ, η, Θ(η, ξ))` (`fderiv_kernel_field`). -/
theorem fieldDerivative_kernel_eq_Do {A : KZ (n + m) → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A {z | z.2.2 ≠ 0}) {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (hξ : ξ ∈ C.U) (hne : ξ ≠ η) (hV : (η, C.Θ η ξ) ∈ ex.V) (i : Fin k) :
    fieldDerivative (C.Xl i) (fun ξ' => A (ξ', η, C.Θ η ξ')) ξ = ex.Do i A (ξ, η, C.Θ η ξ) := by
  have hΨ : ContDiffOn ℝ 1 (kernelUncurry fun ξ η u => A (ξ, η, u)) {z | z.2.2 ≠ 0} :=
    hA.of_le (by simp)
  have h := C.fderiv_kernel_field hΨ hη hξ hne i
  have e1 : (kernelUncurry fun ξ η u => A (ξ, η, u)) = A := rfl
  rw [e1] at h
  show fderiv ℝ (fun ξ' => A (ξ', η, C.Θ η ξ')) ξ (C.Xl i ξ) = _
  rw [h]
  have hRt := ex.Rt_eq i (η, C.Θ η ξ) hV
  have hXb := ex.Xb_eq i ξ hξ
  have hRt' : ex.Rt i η (C.Θ η ξ) = C.R [i] η (C.Θ η ξ) := hRt
  unfold Do
  dsimp only
  rw [hXb, hRt']
  have hsplit : ((C.Xl i ξ, (0 : Fin (n + m) → ℝ),
      C.Y i (C.Θ η ξ) + C.R [i] η (C.Θ η ξ)) : KZ (n + m)) =
      (C.Xl i ξ, 0, 0) + (0, 0, C.Y i (C.Θ η ξ) + C.R [i] η (C.Θ η ξ)) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
  rw [hsplit, map_add]

/-- **Second-order chain rule.** Under the hypotheses of
`fieldDerivative_kernel_eq_Do`: `X̃_{j,ξ} X̃_{i,ξ}[A(ξ, η, Θ(η, ξ))] = (D_j D_i A)(ξ, η, Θ(η, ξ))`. -/
theorem fieldDerivative_fieldDerivative_kernel_eq_Do {A : KZ (n + m) → ℝ}
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) A {z | z.2.2 ≠ 0}) {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (hξ : ξ ∈ C.U) (hne : ξ ≠ η) (hV : (η, C.Θ η ξ) ∈ ex.V) (i j : Fin k) :
    fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) (fun ξ' => A (ξ', η, C.Θ η ξ'))) ξ =
      ex.Do j (ex.Do i A) (ξ, η, C.Θ η ξ) := by
  have hDo := ex.contDiffOn_Do hA i
  have hcont : ContinuousOn (fun ξ' : Fin (n + m) → ℝ => (η, C.Θ η ξ')) C.U :=
    continuousOn_const.prodMk (C.contDiffOn_theta hη).continuousOn
  have hNo : IsOpen ((C.U ∩ (fun ξ' : Fin (n + m) → ℝ => (η, C.Θ η ξ')) ⁻¹' ex.V) \ {η}) :=
    (hcont.isOpen_inter_preimage C.isOpen_U ex.isOpen_V).sdiff isClosed_singleton
  have hξN : ξ ∈ (C.U ∩ (fun ξ' : Fin (n + m) → ℝ => (η, C.Θ η ξ')) ⁻¹' ex.V) \ {η} :=
    ⟨⟨hξ, hV⟩, hne⟩
  have hev : fieldDerivative (C.Xl i) (fun ξ' => A (ξ', η, C.Θ η ξ')) =ᶠ[𝓝 ξ]
      fun ξ' => ex.Do i A (ξ', η, C.Θ η ξ') :=
    Filter.eventuallyEq_of_mem (hNo.mem_nhds hξN)
      (fun ξ' h => ex.fieldDerivative_kernel_eq_Do hA hη h.1.1 h.2 h.1.2 i)
  show fderiv ℝ (fieldDerivative (C.Xl i) (fun ξ' => A (ξ', η, C.Θ η ξ'))) ξ (C.Xl j ξ) = _
  rw [hev.fderiv_eq]
  exact ex.fieldDerivative_kernel_eq_Do hDo hη hξ hne hV j

end ChartExt

end LiftedChart

end RothschildStein.P1
