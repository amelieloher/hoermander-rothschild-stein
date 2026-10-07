-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.OneStepFinal.Basic
public import Hormander.E.OneStepEnergy.Commutators
public import Hormander.C.C9Bridges
public import Hormander.C.Energy.Estimate

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap

namespace Hormander.E
open Hormander.B

variable {N : ℕ}

theorem hct_mollOp (δ : ℝ) (hδ : 0 < δ) : HasContinuousTranspose (mollOp N δ hδ) :=
  mollifierOperator_hasContinuousTranspose δ hδ

theorem hct_realMult (ζ : SchwartzMap (Carrier N) ℝ) :
    HasContinuousTranspose (realMultiplierOperator ζ) :=
  realMultiplierOperator_hasContinuousTranspose ζ

theorem hct_vf (V : RealSchwartzVectorField N) :
    HasContinuousTranspose (vectorFieldOperator V) :=
  vectorFieldOperator_hasContinuousTranspose V

theorem hct_lambda (s : ℝ) : HasContinuousTranspose (lambdaOperator (N := N) s) :=
  lambdaOperator_hasContinuousTranspose s

theorem hct_energyT (θ : SchwartzMap (Carrier N) ℝ) (r : ℝ) :
    HasContinuousTranspose (energyT θ r) :=
  ((hct_realMult θ).comp (hct_lambda r)).comp (hct_realMult θ)

theorem hct_energyA (θ : SchwartzMap (Carrier N) ℝ) (r δ : ℝ) (hδ : 0 < δ) :
    HasContinuousTranspose (energyA θ r δ hδ) :=
  (hct_mollOp δ hδ).comp (hct_energyT θ r)

theorem hct_diffusion {k : ℕ} (Vs : Fin (k + 1) → RealSchwartzVectorField N)
    (cs : SchwartzMap (Carrier N) ℝ) :
    HasContinuousTranspose (Hormander.C.diffusionOperator Vs cs) := by
  unfold Hormander.C.diffusionOperator
  refine HasContinuousTranspose.add (HasContinuousTranspose.add ?_ (hct_vf _)) (hct_realMult _)
  exact HasContinuousTranspose.sum _ _ (fun i _ => (hct_vf _).comp (hct_vf _))

/-- Typeclass version of `HasContinuousTranspose`, used to discharge side conditions
structurally. -/
class HCT (T : Operator N) : Prop where
  out : HasContinuousTranspose T

instance (θ : SchwartzMap (Carrier N) ℝ) : HCT (realMultiplierOperator θ) := ⟨hct_realMult θ⟩
instance (V : RealSchwartzVectorField N) : HCT (vectorFieldOperator V) := ⟨hct_vf V⟩
instance (s : ℝ) : HCT (lambdaOperator (N := N) s) := ⟨hct_lambda s⟩
instance (δ : ℝ) (hδ : 0 < δ) : HCT (mollOp N δ hδ) := ⟨hct_mollOp δ hδ⟩
instance (θ : SchwartzMap (Carrier N) ℝ) (r : ℝ) : HCT (energyT θ r) := ⟨hct_energyT θ r⟩
instance (θ : SchwartzMap (Carrier N) ℝ) (r δ : ℝ) (hδ : 0 < δ) : HCT (energyA θ r δ hδ) :=
  ⟨hct_energyA θ r δ hδ⟩
instance {k : ℕ} (Vs : Fin (k + 1) → RealSchwartzVectorField N) (cs : SchwartzMap (Carrier N) ℝ) :
    HCT (Hormander.C.diffusionOperator Vs cs) := ⟨hct_diffusion Vs cs⟩
instance (A B : Operator N) [hA : HCT A] [hB : HCT B] : HCT (A.comp B) := ⟨hA.out.comp hB.out⟩
instance (A B : Operator N) [hA : HCT A] [hB : HCT B] : HCT (A + B) := ⟨hA.out.add hB.out⟩
instance (A B : Operator N) [hA : HCT A] [hB : HCT B] : HCT (A - B) :=
  ⟨HasContinuousTranspose.sub' hA.out hB.out⟩
instance (c : ℂ) (A : Operator N) [hA : HCT A] : HCT (c • A) := ⟨hA.out.smul c⟩
instance (A B : Operator N) [hA : HCT A] [hB : HCT B] : HCT (operatorComm A B) :=
  ⟨HasContinuousTranspose.comm' hA.out hB.out⟩

theorem Eop_vf (X : Carrier N → Carrier N) (V : RealSchwartzVectorField N)
    (hV : ∀ i x, V i x = X x i) : Eop (vectorFieldOperator V) = Hormander.vectorFieldOp X := by
  have := Eop_eq_ext (ExtOp.vectorField V) (hct_vf V)
  rw [show (ExtOp.vectorField V).op = vectorFieldOperator V from rfl] at this
  rw [this]
  ext u : 1
  exact ExtOp.ext_vectorField X V hV u

theorem Eop_realMult (ζ : SchwartzMap (Carrier N) ℝ) :
    Eop (realMultiplierOperator ζ) = cutoffDistr ζ := by
  have := Eop_eq_ext (ExtOp.realMult ζ) (hct_realMult ζ)
  rw [show (ExtOp.realMult ζ).op = realMultiplierOperator ζ from rfl] at this
  rw [this]
  exact ExtOp.ext_realMult ζ

/-- The distributional operator `hormanderOp X c` is the extension of the Schwartz-side
`diffusionOperator` of the realization. -/
theorem Eop_diffusion_eq {k : ℕ} (X : Fin (k + 1) → Carrier N → Carrier N) (c : Carrier N → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c) :
    Eop (Hormander.C.diffusionOperator (Hormander.C.c9SchwartzVectorField X hX hXc)
      (Hormander.C.c9SchwartzMultiplier c hc hcc)) = Hormander.hormanderOp X c := by
  have hV : ∀ i (j : Fin N) x, Hormander.C.c9SchwartzVectorField X hX hXc i j x = X i x j :=
    fun i j x => rfl
  unfold Hormander.C.diffusionOperator Hormander.hormanderOp
  rw [Eop_add (HasContinuousTranspose.add
      (HasContinuousTranspose.sum _ _ (fun i _ => (hct_vf _).comp (hct_vf _))) (hct_vf _))
      (hct_realMult _),
    Eop_add (HasContinuousTranspose.sum _ _ (fun i _ => (hct_vf _).comp (hct_vf _))) (hct_vf _),
    Eop_sum _ _ (fun i _ => (hct_vf _).comp (hct_vf _)), Eop_vf (X 0) _ (hV 0),
    Eop_realMult]
  congr 2
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Eop_comp (hct_vf _) (hct_vf _), Eop_vf (X i.succ) _ (hV i.succ)]

end Hormander.E
