-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.GeneralLieBCHOpenBuffer
public import RothschildStein.G3.DilatedInputCoordinates
@[expose] public section
noncomputable section
open Set Metric TopologicalSpace
namespace RothschildStein.G3

def generalLieSuccessivePointMap {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (f g : formalSpan a s p) (δ : ℝ) (x : Fin N → ℝ) : Fin N → ℝ :=
  finiteLieTimeOneMap Φ (dilatedInputCoordinates D g δ,
    finiteLieTimeOneMap Φ (dilatedInputCoordinates D f δ,x))

def generalLieBCHPointMap {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (f g : formalSpan a s p) (δ : ℝ) (x : Fin N → ℝ) : Fin N → ℝ :=
  finiteLieTimeOneMap Φ (dilatedInputCoordinates D (modelProduct f g) δ,x)

/-- Actual endpoint comparison on one common finite Lie-field flow family. -/
theorem generalLiePointMaps_error_of_common_flow {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω Ω₀ : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (Φ : (((Fin (freeDimension a s p) → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    {σ : ℝ}
    (hODE : ∀ z : formalSpan a s p, D.basis.equivFun z ∈ ball 0 σ →
      ∀ x ∈ Ω₀, Φ ((D.basis.equivFun z,x),0) = x ∧
        ∀ t ∈ Ioo (-2 : ℝ) 2, Φ ((D.basis.equivFun z,x),t) ∈ Ω ∧
          HasDerivAt (fun v => Φ ((D.basis.equivFun z,x),v))
            (finiteLieField D X z (Φ ((D.basis.equivFun z,x),t))) t)
    (f g : formalSpan a s p) (δ : ℝ) (hs : 1 ≤ s)
    {B : ℝ} (hB : 0 ≤ B) (hδ : |δ| ≤ 1)
    (hjets : ∀ x ∈ Ω, ∀ i k, k ≤ 3*s+2 → ‖iteratedFDeriv ℝ k (X i) x‖ ≤ B)
    (hf : dilatedInputCoordinates D f δ ∈ ball 0 σ)
    (hg : dilatedInputCoordinates D g δ ∈ ball 0 σ)
    (hh : dilatedInputCoordinates D (modelProduct f g) δ ∈ ball 0 σ)
    {x : Fin N → ℝ} (hx : x ∈ Ω₀)
    (hy : finiteLieTimeOneMap Φ (dilatedInputCoordinates D f δ,x) ∈ Ω₀) :
    ‖generalLieSuccessivePointMap D Φ f g δ x-generalLieBCHPointMap D Φ f g δ x‖ ≤
      |δ|^(s+1)*generalLieBCHErrorCoefficient D f g
        (primitiveWordJetBudget D (3*s+2) B)
        (max (generalLieTravelBudget D f B + generalLieTravelBudget D g B +
          generalLieTravelBudget D (modelProduct f g) B) 1) := by
  let fd : formalSpan a s p := ⟨finiteDilate δ f.val,finiteDilate_mem_formalSpan δ f.property⟩
  let gd : formalSpan a s p := ⟨finiteDilate δ g.val,finiteDilate_mem_formalSpan δ g.property⟩
  let hd : formalSpan a s p := ⟨finiteDilate δ (modelProduct f g).val,
    finiteDilate_mem_formalSpan δ (modelProduct f g).property⟩
  have hfd : D.basis.equivFun fd = dilatedInputCoordinates D f δ :=
    (dilatedInputCoordinates_eq D f δ).symm
  have hgd : D.basis.equivFun gd = dilatedInputCoordinates D g δ :=
    (dilatedInputCoordinates_eq D g δ).symm
  have hhd : D.basis.equivFun hd = dilatedInputCoordinates D (modelProduct f g) δ :=
    (dilatedInputCoordinates_eq D (modelProduct f g) δ).symm
  have ha := hODE fd (by simpa only [hfd] using hf) x hx
  have hb := hODE gd (by simpa only [hgd] using hg)
    (finiteLieTimeOneMap Φ (dilatedInputCoordinates D f δ,x)) hy
  have hc := hODE hd (by simpa only [hhd] using hh) x hx
  have he := generalLie_BCH_point_error_on_open_buffer D Ω X hX f g δ hs
    (fun t => Φ ((D.basis.equivFun fd,x),t))
    (fun t => Φ ((D.basis.equivFun gd,finiteLieTimeOneMap Φ (dilatedInputCoordinates D f δ,x)),t))
    (fun t => Φ ((D.basis.equivFun hd,x),t))
    (fun t ht => (ha.2 t ht).2) (fun t ht => (hb.2 t ht).2) (fun t ht => (hc.2 t ht).2)
    (fun t ht => (ha.2 t ht).1) (fun t ht => (hb.2 t ht).1) (fun t ht => (hc.2 t ht).1)
    (by rw [hb.1]; rw [hfd]; rfl)
    (by rw [hc.1,ha.1]) hB hδ hjets
  simpa only [generalLieSuccessivePointMap,generalLieBCHPointMap,finiteLieTimeOneMap,
    hfd,hgd,hhd] using he
end RothschildStein.G3
