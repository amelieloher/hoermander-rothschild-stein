-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ErrorTypesJets
public import RothschildStein.P1.RightPoleComputationChain
public import RothschildStein.P1.RightParametrixTransport
public import RothschildStein.L1.WeightedFieldAction
public import RothschildStein.P1.ModelHypotheses

/-!
# Parametrix error types: weighted coefficient families on the chart

A *jet coefficient of order `o`* (`LiftedChart.IsJetCoef C o A`) is a family `A (η, u)` of functions of the
model variable, smooth jointly in `(η, u)` on the domain `C.T` of the remainders, whose slices
`u ↦ A η u`, `η ∈ C.U`, have `JetVan` order `o` at the origin of the model variable. A *jet field of order
`d`* (`LiftedChart.IsJetField C d V`) is a family of vector fields `V η` whose `j`th coefficient has order
`d + weight j`. The model fields `Y i` are jet fields of order `-w i` (homogeneity, `JetVan.of_homogeneous`) and
the chart remainders `R_{[i],η}` are jet fields of order `1 - w i` (`LiftedChart.remainder_weight`).

The calculus: orders add under products, a coordinate derivative lowers the order by its weight, and a jet
field of order `d` acting on a jet coefficient of order `b` gives a jet coefficient of order `d + b`
(`IsJetField.fieldDerivative`). Everything is proved from the ordered Leibniz formula; no remainder
estimate is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- A coefficient family `A (η, u)`, smooth on the remainder domain `C.T`, whose
slices have weighted jet order `o` at the origin of the model variable. -/
structure IsJetCoef (o : ℤ) (A : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ) : Prop where
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => A z.1 z.2) C.T
  jets : ∀ η ∈ C.U, JetVan C.G.weight o (A η)

/-- A family of vector fields `V η` whose `j`th coefficient is a jet coefficient of
order `d + weight j`. -/
def IsJetField (d : ℤ)
    (V : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)) : Prop :=
  ∀ j : Fin (n + m), C.IsJetCoef (d + (C.G.weight j : ℤ)) (fun η u => V η u j)

variable {C}
variable {o o' a b d : ℤ} {A B : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}

/-- The slice of a jet coefficient is smooth on the target of the endpoint chart. -/
theorem IsJetCoef.slice (hA : C.IsJetCoef o A) {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (A η) (C.e η).target := by
  have hmap : MapsTo (fun u : Fin (n + m) → ℝ => (η, u)) (C.e η).target C.T :=
    fun u hu => ⟨hη, hu⟩
  exact hA.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn hmap

/-- Lowering the order. -/
theorem IsJetCoef.mono (hA : C.IsJetCoef o A) (h : o' ≤ o) : C.IsJetCoef o' A :=
  ⟨hA.smooth, fun η hη => (hA.jets η hη).mono h⟩

/-- Equal orders. -/
theorem IsJetCoef.congr_order (hA : C.IsJetCoef o A) (h : o = o') : C.IsJetCoef o' A :=
  hA.mono h.ge

/-- Pointwise equal families have the same order. -/
theorem IsJetCoef.congr (hA : C.IsJetCoef o A) (he : ∀ η u, A η u = B η u) :
    C.IsJetCoef o B := by
  have : A = B := funext fun η => funext fun u => he η u
  rwa [← this]

/-- Finite sums of jet coefficients of order `o` have order `o`. -/
theorem IsJetCoef.sum {ι : Type*} (T : Finset ι) {A : ι → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hA : ∀ i ∈ T, C.IsJetCoef o (A i)) : C.IsJetCoef o (fun η u => ∑ i ∈ T, A i η u) :=
  ⟨ContDiffOn.sum fun i hi => (hA i hi).smooth, fun η hη =>
    JetVan.sum T (fun i => A i η) (C.modelOpens η) (C.zero_mem_target hη)
      (fun i hi => (hA i hi).slice hη) (fun i hi => (hA i hi).jets η hη)⟩

/-- Orders add under products. -/
theorem IsJetCoef.mul (hA : C.IsJetCoef a A) (hB : C.IsJetCoef b B) :
    C.IsJetCoef (a + b) (fun η u => A η u * B η u) :=
  ⟨hA.smooth.mul hB.smooth, fun η hη =>
    JetVan.mul (C.modelOpens η) (C.zero_mem_target hη) (hA.slice hη) (hB.slice hη)
      (hA.jets η hη) (hB.jets η hη)⟩

/-- The coordinate derivative of the slices of a jet coefficient is a jet coefficient whose order is
lowered by the weight of the coordinate. -/
theorem IsJetCoef.coordPartial (hA : C.IsJetCoef a A) (j : Fin (n + m)) :
    C.IsJetCoef (a - (C.G.weight j : ℤ)) (fun η u => fderiv ℝ (A η) u (Pi.single j 1)) := by
  refine ⟨?_, fun η hη => (hA.jets η hη).coordPartial j⟩
  have hT : IsOpen C.T := C.isOpen_T
  have hD : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
        fderiv ℝ (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => A z.1 z.2) z
          ((0 : Fin (n + m) → ℝ), (Pi.single j (1 : ℝ) : Fin (n + m) → ℝ))) C.T :=
    (hA.smooth.fderiv_of_isOpen hT (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffOn_const
  refine hD.congr ?_
  rintro ⟨η, u⟩ hz
  have hdiff : DifferentiableAt ℝ (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => A z.1 z.2)
      (η, u) :=
    (hA.smooth.contDiffAt (hT.mem_nhds hz)).differentiableAt (by simp)
  have h1 : HasFDerivAt (fun v : Fin (n + m) → ℝ => A η v)
      ((fderiv ℝ (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => A z.1 z.2) (η, u)).comp
        (ContinuousLinearMap.inr ℝ (Fin (n + m) → ℝ) (Fin (n + m) → ℝ))) u :=
    hdiff.hasFDerivAt.comp u (hasFDerivAt_prodMk_right η u)
  show fderiv ℝ (fun v : Fin (n + m) → ℝ => A η v) u (Pi.single j 1) = _
  rw [h1.fderiv]
  simp

/-- A globally smooth function of the model variable homogeneous of integer degree `β` is a jet
coefficient of order `β` (independent of `η`; smooth on `C.T`). -/
theorem IsJetCoef.of_homogeneous {f : (Fin (n + m) → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {β : ℤ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, f (C.G.dilate t x) = t ^ (β : ℝ) * f x) :
    C.IsJetCoef β (fun _ u => f u) :=
  ⟨(hf.comp contDiff_snd).contDiffOn, fun _ _ => JetVan.of_homogeneous C.G hf hhom⟩

/-- A jet field of order `d` acting on a jet coefficient of order `b` gives a jet coefficient of order
`d + b`: `V f = ∑ⱼ Vʲ ∂ⱼ f`, with orders `(d + wⱼ) + (b - wⱼ)`. -/
theorem IsJetField.fieldDerivative {V : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)}
    (hV : C.IsJetField d V) (hA : C.IsJetCoef b A) :
    C.IsJetCoef (d + b) (fun η u => fieldDerivative (V η) (A η) u) := by
  have hs : C.IsJetCoef (d + b)
      (fun η u => ∑ j : Fin (n + m), V η u j * fderiv ℝ (A η) u (Pi.single j 1)) := by
    apply IsJetCoef.sum
    intro j _
    refine ((hV j).mul (hA.coordPartial j)).congr_order ?_
    ring
  refine hs.congr fun η u => ?_
  exact (L1.fieldDerivative_eq_coordinate_sum (V η) (A η) u).symm

/-- The model fields `Y i` form a jet field of order `-(w i)`: the coefficient `(Y i)ʲ` is smooth and
homogeneous of degree `wⱼ - w i`. -/
theorem isJetField_Y (i : Fin k) : C.IsJetField (-((w i : ℕ) : ℤ)) (fun _ u => C.Y i u) := by
  intro j
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun u => C.Y i u j) :=
    (contDiff_apply ℝ ℝ j).comp (C.model_field_smooth i)
  have hhom := (G2.isHomogeneousField_iff_coefficients C.G (C.Y i) ((w i : ℕ) : ℝ)).mp
    (C.isHomogeneousField i) j
  have := IsJetCoef.of_homogeneous (C := C) hf (β := (C.G.weight j : ℤ) - ((w i : ℕ) : ℤ))
    (fun t ht x => by
      have e : (((C.G.weight j : ℤ) - ((w i : ℕ) : ℤ) : ℤ) : ℝ) =
          (C.G.weight j : ℝ) - ((w i : ℕ) : ℝ) := by simp
      show C.Y i (C.G.dilate t x) j = _
      rw [hhom t ht x, e])
  exact this.congr_order (by ring)

/-- The chart remainders `R_{[i],η}` form a jet field of order `1 - w i`
(`LiftedChart.remainder_weight`). -/
theorem isJetField_R (i : Fin k) : C.IsJetField (1 - ((w i : ℕ) : ℤ)) (fun η u => C.R [i] η u) := by
  intro j
  refine ⟨(contDiff_apply ℝ ℝ j).comp_contDiffOn (C.remainder_smooth [i]), ?_⟩
  intro η hη I hI
  have hjet := C.remainder_weight [i] (List.cons_ne_nil i []) η hη
  apply hjet j I
  simp only [wordWeight, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero]
  omega

end LiftedChart

end RothschildStein.P1
