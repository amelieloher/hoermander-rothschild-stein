-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ErrorTypesJetCoef
public import RothschildStein.P1.ErrorTypesClosure
public import RothschildStein.P1.LocalWeightedCoefficientType
public import RothschildStein.P1.CoordinatePartialSuccessor
public import RothschildStein.H3.CoordinatePartialOne

/-!
# Parametrix error types: differential operators with small weighted coefficients on a pole

The core of the type classification of the error kernels (BB pp. 561-563, "the differential errors are of
local degrees at most `1, 1, 0, 1`, hence of types at least `1, 1, 2, 1`"). Let `K = F.pole star` be the
selected pole of a frame `F` of the chart `C` (smooth off the origin and homogeneous), and `V, W` jet fields of
orders `dV, dW` (`LiftedChart.IsJetField`: coefficient `j` of order `d + weight j`; the model fields `Y i` have
order `-w i`, the chart remainders `R_{[i],η}` order `1 - w i`). Then, for cutoffs `a, b ∈ C_c^∞(F.V)`:

* `isTypeKernelOn_jetCoef_partial`: `a(ξ) b(η) A(η, Θ(η, ξ)) (∂^α K)(Θ(η, ξ))` is a kernel of type `lam`
  modeled on `star` as soon as `A` is smooth on `C.T` with vanishing weighted jets below `low` and
  `weight α - low ≤ 2 - lam` (the pole-tracked version of `isTypeKernel_local_weighted_coefficient_partial`);
* `isTypeKernelOn_fieldDerivative`: the same for `a(ξ) b(η) (W_η K)(Θ(η, ξ))` of type `lam` with
  `-dW ≤ 2 - lam`;
* `isTypeKernelOn_fieldDerivative_comp`: the same for `a(ξ) b(η) (V_η (W_η K))(Θ(η, ξ))` with
  `-(dV + dW) ≤ 2 - lam`.

The last two expand the operator in coordinates (`fieldDerivative_comp_expand`) into finitely many terms of the
first form, whose coefficients are jet coefficients by the calculus of `ErrorTypesJetCoef`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.P1

section Expansion

variable {N : ℕ}

/-- The first-order multi-index `e_l` has weight `w_l`. -/
theorem weight_single_index (G : HomogeneousGroup N) (l : Fin N) :
    (∑ j, G.weight j * (Pi.single l 1 : Fin N → ℕ) j) = G.weight l := by
  simp [Pi.single_apply]

/-- The second-order multi-index `e_l + e_j` has weight `w_l + w_j`. -/
theorem weight_single_add_single_index (G : HomogeneousGroup N) (l j : Fin N) :
    (∑ i, G.weight i * ((Pi.single l 1 + Pi.single j 1 : Fin N → ℕ) i)) =
      G.weight l + G.weight j := by
  simp [Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.single_apply]

/-- A directional derivative is the sum of coordinate derivatives of the
`euclideanPartial` form. -/
theorem fieldDerivative_eq_sum_euclideanPartial (V : (Fin N → ℝ) → (Fin N → ℝ))
    (f : (Fin N → ℝ) → ℝ) (u : Fin N → ℝ) :
    fieldDerivative V f u = ∑ l, V u l * euclideanPartial (Pi.single l 1) f u := by
  rw [L1.fieldDerivative_eq_coordinate_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  exact (congrFun (H3.euclideanPartial_single_one l f) u).symm

/-- The coordinate expansion of a second-order composite `V (W K)` of two
vector fields at a point `u` where `K` is smooth and the coefficients of `W` are differentiable:
`V (W K) = ∑ₗ V(Wˡ) ∂ₗ K + ∑ₗ ∑ⱼ Vʲ Wˡ ∂ⱼ ∂ₗ K`. -/
theorem fieldDerivative_comp_expand (O : Opens (Fin N → ℝ)) {K : (Fin N → ℝ) → ℝ}
    (hK : ContDiffOn ℝ (⊤ : ℕ∞) K O) {u : Fin N → ℝ} (hu : u ∈ O)
    (V W : (Fin N → ℝ) → (Fin N → ℝ)) (hW : ∀ l, DifferentiableAt ℝ (fun v => W v l) u) :
    fieldDerivative V (fieldDerivative W K) u =
      ∑ l, fieldDerivative V (fun v => W v l) u * euclideanPartial (Pi.single l 1) K u +
      ∑ l, ∑ j, (V u j * W u l) *
        euclideanPartial (Pi.single l 1 + Pi.single j 1) K u := by
  have hE : ∀ l, ContDiffOn ℝ (⊤ : ℕ∞) (euclideanPartial (Pi.single l 1) K) O := by
    intro l
    have h := L1.rsPartial_contDiffOn O [l] K hK
    have e : rsPartial [l] K = euclideanPartial (Pi.single l 1) K :=
      (H3.euclideanPartial_single_one l K).symm
    rwa [e] at h
  have hEd : ∀ l, DifferentiableAt ℝ (euclideanPartial (Pi.single l 1) K) u := fun l =>
    ((hE l).contDiffAt (O.isOpen.mem_nhds hu)).differentiableAt (by simp)
  have e1 : fieldDerivative W K =
      fun v => ∑ l, W v l * euclideanPartial (Pi.single l 1) K v :=
    funext fun v => fieldDerivative_eq_sum_euclideanPartial W K v
  have hmul : ∀ l, DifferentiableAt ℝ
      (fun v => W v l * euclideanPartial (Pi.single l 1) K v) u := fun l => (hW l).mul (hEd l)
  have hfd : fderiv ℝ (fun v => ∑ l, W v l * euclideanPartial (Pi.single l 1) K v) u (V u) =
      ∑ l, (W u l * fderiv ℝ (euclideanPartial (Pi.single l 1) K) u (V u) +
        euclideanPartial (Pi.single l 1) K u * fderiv ℝ (fun v => W v l) u (V u)) := by
    rw [fderiv_fun_sum (fun l _ => hmul l), sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [fderiv_fun_mul (hW l) (hEd l)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hsucc : ∀ l j, fderiv ℝ (euclideanPartial (Pi.single l 1) K) u (Pi.single j 1) =
      euclideanPartial (Pi.single l 1 + Pi.single j 1) K u := fun l j =>
    euclideanPartial_coordinate_successor_local O (Pi.single l 1) j K hK u hu
  have hfdE : ∀ l, fderiv ℝ (euclideanPartial (Pi.single l 1) K) u (V u) =
      ∑ j, V u j * euclideanPartial (Pi.single l 1 + Pi.single j 1) K u := by
    intro l
    have h := L1.fieldDerivative_eq_coordinate_sum V (euclideanPartial (Pi.single l 1) K) u
    unfold fieldDerivative at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hsucc l j]
    rfl
  have h1 : ∑ l, euclideanPartial (Pi.single l 1) K u * fderiv ℝ (fun v => W v l) u (V u) =
      ∑ l, fieldDerivative V (fun v => W v l) u * euclideanPartial (Pi.single l 1) K u := by
    refine Finset.sum_congr rfl fun l _ => ?_
    unfold fieldDerivative
    ring
  have h2 : ∑ l, W u l * fderiv ℝ (euclideanPartial (Pi.single l 1) K) u (V u) =
      ∑ l, ∑ j, (V u j * W u l) * euclideanPartial (Pi.single l 1 + Pi.single j 1) K u := by
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hfdE l, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  change fderiv ℝ (fieldDerivative W K) u (V u) = _
  rw [e1, hfd, Finset.sum_add_distrib, h1, h2]
  ring

end Expansion

namespace LiftedChart

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The pole-tracked form of `isTypeKernel_local_weighted_coefficient_partial`: a
coefficient `A (η, u)` smooth on `C.T` with vanishing weighted jets below `low`, times a partial `∂^α` of
the selected pole, gives a kernel of type `lam` modeled on the pole, when `weight α - low ≤ 2 - lam`. -/
theorem isTypeKernelOn_jetCoef_partial (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hG : F.G = C.G) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (star : Bool) (α : Fin (n + m) → ℕ) (lam low : ℕ)
    (hdegree : ((∑ j, F.G.weight j * α j : ℕ) : ℤ) - (low : ℤ) ≤ 2 - (lam : ℤ))
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole star (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole star u)
    (a b : TestFunction F.V ℝ (⊤ : ℕ∞))
    (A : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => A z.1 z.2) C.T)
    (hjet : ∀ η ∈ C.U, ∀ I : List (Fin (n + m)), (I.map C.G.weight).sum < low →
      rsPartial I (A η) 0 = 0) :
    IsTypeKernelOn F star lam (fun ξ η => a ξ * b η *
      (A η (F.Θ η ξ) * euclideanPartial α (F.pole star) (F.Θ η ξ))) := by
  apply IsTypeKernelOn.of_withPole
  have hpole : (F.withPole star).pole star = F.pole star := KernelFrame.withPole_pole F star star
  let T : Set (((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) × (Fin (n + m) → ℝ)) :=
    {q | (q.1.2, q.2) ∈ C.T}
  have hT : IsOpen T := C.isOpen_T.preimage (continuous_fst.snd.prodMk continuous_snd)
  let A' := fun q : ((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) × (Fin (n + m) → ℝ) => A q.1.2 q.2
  have hA' : ContDiffOn ℝ (⊤ : ℕ∞) A' T :=
    hA.comp (contDiffOn_fst.snd.prodMk contDiffOn_snd) (fun _ hq => hq)
  have h := C.isTypeKernel_local_weighted_coefficient_partial (F.withPole star) hΘ hVU star α low lam
    hdegree (by rw [hpole]; exact hΓ) (by rw [hpole]; exact hhom) a b T hT A' hA'
    (fun p hp => C.mem_T_zero (hVU (b.tsupport_subset hp.2)))
    (fun p hp => by
      change (p.2, F.Θ p.2 p.1) ∈ C.T
      rw [hΘ]
      exact C.mem_T_theta hp.2 hp.1)
    (fun p hp I hI => hjet p.2 (hVU (b.tsupport_subset hp.2)) I (by
      rw [← hG]
      exact hI))
  rw [hpole] at h
  exact h

variable {C}

/-- The coordinate jets of a jet coefficient of order `o` vanish below `o.toNat`. -/
theorem IsJetCoef.jets_toNat {o : ℤ} {A : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hA : C.IsJetCoef o A) : ∀ η ∈ C.U, ∀ I : List (Fin (n + m)),
      (I.map C.G.weight).sum < o.toNat → rsPartial I (A η) 0 = 0 :=
  fun η hη I hI => hA.jets η hη I (by omega)

/-- A jet coefficient times a partial `∂^α` of the pole gives a kernel of type `lam`
modeled on the pole when the order of the coefficient is at least `weight α - (2 - lam)`. -/
theorem isTypeKernelOn_jetCoef (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hG : F.G = C.G) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (star : Bool) (α : Fin (n + m) → ℕ) (lam : ℕ) {o : ℤ}
    {A : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} (hA : C.IsJetCoef o A)
    (hdegree : ((∑ j, F.G.weight j * α j : ℕ) : ℤ) - o ≤ 2 - (lam : ℤ))
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole star (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole star u)
    (a b : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    IsTypeKernelOn F star lam (fun ξ η => a ξ * b η *
      (A η (F.Θ η ξ) * euclideanPartial α (F.pole star) (F.Θ η ξ))) :=
  C.isTypeKernelOn_jetCoef_partial F hΘ hG hVU star α lam o.toNat (by omega) hΓ hhom a b A
    hA.smooth hA.jets_toNat

/-- A jet field `W` of order `d` applied to the pole: `a(ξ) b(η) (W_η K)(Θ(η, ξ))` is a
kernel of type `lam` modeled on the pole as soon as `-d ≤ 2 - lam`. -/
theorem isTypeKernelOn_fieldDerivative (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hG : F.G = C.G) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (star : Bool) (lam : ℕ) {d : ℤ}
    {W : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)} (hW : C.IsJetField d W)
    (hdeg : -d ≤ 2 - (lam : ℤ))
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole star (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole star u)
    (a b : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    IsTypeKernelOn F star lam (fun ξ η => a ξ * b η *
      fieldDerivative (W η) (F.pole star) (F.Θ η ξ)) := by
  have hsum := IsTypeKernelOn.sum (Finset.univ : Finset (Fin (n + m))) (fun l _ =>
    isTypeKernelOn_jetCoef F hΘ hG hVU star (Pi.single l 1) lam (hW l)
      (by rw [weight_single_index, hG]; omega) hΓ hhom a b)
  refine hsum.congr_off_diagonal fun ξ η _ => ?_
  rw [fieldDerivative_eq_sum_euclideanPartial, Finset.mul_sum]

/-- A composite `V_η (W_η K)` of jet fields of orders `dV, dW` applied to the pole:
`a(ξ) b(η) (V_η (W_η K))(Θ(η, ξ))` is a kernel of type `lam` modeled on the pole as soon as
`-(dV + dW) ≤ 2 - lam`. -/
theorem isTypeKernelOn_fieldDerivative_comp (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hG : F.G = C.G) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (star : Bool) (lam : ℕ) {dV dW : ℤ}
    {V W : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)}
    (hV : C.IsJetField dV V) (hW : C.IsJetField dW W)
    (hdeg : -(dV + dW) ≤ 2 - (lam : ℤ))
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) (F.pole star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole star (F.G.dilate r u) = r ^ ((2 : ℝ) - F.G.homogeneousDimension) * F.pole star u)
    (a b : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    IsTypeKernelOn F star lam (fun ξ η => a ξ * b η *
      fieldDerivative (V η) (fieldDerivative (W η) (F.pole star)) (F.Θ η ξ)) := by
  have h1 := IsTypeKernelOn.sum (Finset.univ : Finset (Fin (n + m))) (fun l _ =>
    isTypeKernelOn_jetCoef F hΘ hG hVU star (Pi.single l 1) lam
      (A := fun η u => fieldDerivative (V η) (fun v => W η v l) u) (hV.fieldDerivative (hW l))
      (by rw [weight_single_index, hG]; omega) hΓ hhom a b)
  have h2 := IsTypeKernelOn.sum (Finset.univ : Finset (Fin (n + m))) (fun l _ =>
    IsTypeKernelOn.sum (Finset.univ : Finset (Fin (n + m))) (fun j _ =>
      isTypeKernelOn_jetCoef F hΘ hG hVU star (Pi.single l 1 + Pi.single j 1) lam
        (A := fun η u => V η u j * W η u l) ((hV j).mul (hW l))
        (by rw [weight_single_add_single_index, hG]; omega) hΓ hhom a b))
  refine (h1.add h2).congr_off_diagonal ?_
  intro ξ η hne
  by_cases ha : a ξ = 0
  · simp [ha]
  by_cases hb : b η = 0
  · simp [hb]
  have hξ : ξ ∈ F.V := a.tsupport_subset (subset_tsupport a ha)
  have hη : η ∈ F.V := b.tsupport_subset (subset_tsupport b hb)
  have hξU : ξ ∈ C.U := hVU hξ
  have hηU : η ∈ C.U := hVU hη
  have hu : F.Θ η ξ ≠ 0 := by
    rw [hΘ]
    exact C.theta_ne_zero hηU hξU hne
  have hmem : F.Θ η ξ ∈ (C.e η).target := by
    rw [hΘ]
    exact C.theta_mem_target hηU hξU
  have hWd : ∀ l, DifferentiableAt ℝ (fun v => W η v l) (F.Θ η ξ) := fun l =>
    (((hW l).slice hηU).contDiffAt ((C.e η).open_target.mem_nhds hmem)).differentiableAt (by simp)
  have hexp := fieldDerivative_comp_expand (⟨{(0 : Fin (n + m) → ℝ)}ᶜ, isOpen_compl_singleton⟩ :
    Opens (Fin (n + m) → ℝ)) hΓ (u := F.Θ η ξ) hu (V η) (W η) hWd
  rw [hexp]
  simp only [Finset.mul_sum, mul_add]

end LiftedChart

end RothschildStein.P1
