import QuaternionicSymmetry.ManifoldQuaternionicFourTwistorHodgeFiber

/-! The actual tangent-fiber form associated to a quaternionic sphere
coordinate lies in the negative Hodge half for the reversed quaternionic
orientation. This is a pointwise statement, not yet source spinor naming. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourTwistorHodgeEigen

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorQuaternionicHalf
open FourDimensionalExteriorCanonicalHodge
open FourDimensionalQuaternionicHodgeFrame
open ManifoldQuaternionicFourHodgeOverlapExterior
open ManifoldQuaternionicFourGlobalHodge
open ManifoldQuaternionicFourTangentOrientation
open ManifoldQuaternionicFourTwistorHodgeFiber
open ManifoldQuaternionicMetric
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem localTangentTwoForm_canonicalStar
    (Q : SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (hdim : Module.finrank ℝ E = 4)
    (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (a : Fin 3 → ℝ) :
    tangentHodgeStar Q hdim x
      (localTangentTwoForm Q hdim i x hi a) =
    localTangentTwoForm Q hdim i x hi a := by
  let C := localToTangentEquiv Q i x hi
  let α := localTangentTwoForm Q hdim i x hi a
  let β := (Real.sqrt 2)⁻¹ • operatorForm
      (ManifoldQuaternionicFourTwistorHodgeFiber.localBasis Q hdim i)
      (synth (Q.reduction.Q i) a)
  have hβ : canonicalStar (Q.reduction.Q i) hdim β = β := by
    rw [canonicalStar_eq_frameStar _ _
      ManifoldQuaternionicFourTwistorHodgeFiber.unit
      ManifoldQuaternionicFourTwistorHodgeFiber.unit_norm]
    apply (mem_positiveExteriorHalf _ _).mp
    rw [positiveExteriorHalf_eq_quaternionicFormImage]
    exact Submodule.smul_mem _ _
      ⟨synth (Q.reduction.Q i) a, synth_mem _ a, rfl⟩
  have hp (b : Basis (Fin 4) ℝ E) :
      pullbackTwoForm b C.toLinearMap α = β := by
    exact localTangentTwoForm_pullback Q hdim i x hi b a
  have h := tangentHodgeStar_local Q hdim i x hi
    (ManifoldQuaternionicFourTwistorHodgeFiber.localBasis Q hdim i) α
  rw [hp, hβ] at h
  apply ExteriorDuality.twoform_ext
    (ManifoldQuaternionicFourTwistorHodgeFiber.localBasis Q hdim i)
  intro v w
  have he := congrArg (fun θ : TwoForm E =>
      BilinearExterior.evaluate (C.symm v) (C.symm w) θ) h
  have he' := congrArg (fun θ : TwoForm E =>
      BilinearExterior.evaluate (C.symm v) (C.symm w) θ)
    (hp (ManifoldQuaternionicFourTwistorHodgeFiber.localBasis Q hdim i))
  change BilinearExterior.evaluate (C.symm v) (C.symm w)
      (pullbackTwoForm _ C.toLinearMap (tangentHodgeStar Q hdim x α)) =
    BilinearExterior.evaluate (C.symm v) (C.symm w) β at he
  change BilinearExterior.evaluate (C.symm v) (C.symm w)
      (pullbackTwoForm _ C.toLinearMap α) =
    BilinearExterior.evaluate (C.symm v) (C.symm w) β at he'
  rw [evaluate_pullbackTwoForm] at he he'
  change BilinearExterior.evaluate (C (C.symm v) : E)
      (C (C.symm w) : E) (tangentHodgeStar Q hdim x α) =
    BilinearExterior.evaluate (C.symm v) (C.symm w) β at he
  change BilinearExterior.evaluate (C (C.symm v) : E)
      (C (C.symm w) : E) α =
    BilinearExterior.evaluate (C.symm v) (C.symm w) β at he'
  have hv : (C (C.symm v) : E) = v := C.apply_symm_apply v
  have hw : (C (C.symm w) : E) = w := C.apply_symm_apply w
  rw [hv, hw] at he he'
  exact he.trans he'.symm

theorem localTangentTwoForm_reversedStar
    (Q : SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (hdim : Module.finrank ℝ E = 4)
    (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (a : Fin 3 → ℝ) :
    (-(tangentHodgeStar Q hdim x))
      (localTangentTwoForm Q hdim i x hi a) =
    -localTangentTwoForm Q hdim i x hi a := by
  rw [LinearMap.neg_apply,
    localTangentTwoForm_canonicalStar Q hdim i x hi a]

end
end QuaternionicSymmetry.ManifoldQuaternionicFourTwistorHodgeEigen
