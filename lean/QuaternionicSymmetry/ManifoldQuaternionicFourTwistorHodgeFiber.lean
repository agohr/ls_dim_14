import QuaternionicSymmetry.ManifoldQuaternionicFourSphereFormOverlap
import QuaternionicSymmetry.ManifoldQuaternionicFourGlobalHodge
import QuaternionicSymmetry.ManifoldTwistorSphereBundle

/-! The quaternionic coefficient sphere maps to genuine exterior two-covectors
on the actual tangent fiber. The target's opposite Hodge sign is certified
pointwise; the bundle-level homeomorphism and source spinor convention remain
separate obligations. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourTwistorHodgeFiber

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorQuaternionicHalf
open FourDimensionalExteriorCanonicalHodge
open FourDimensionalQuaternionicHodgeFrame
open FourDimensionalExteriorQuaternionicUnitSphere
open ManifoldQuaternionicFourHodgeOverlapExterior
open ManifoldQuaternionicFourGlobalHodge
open ManifoldQuaternionicFourTangentOrientation
open ManifoldQuaternionicMetric
open ManifoldTwistorSphereBundle
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

def unit : E := NormedSpace.normalize (Classical.choose (exists_ne (0 : E)))
theorem unit_norm : ‖(unit : E)‖ = 1 :=
  NormedSpace.norm_normalize (Classical.choose_spec (exists_ne (0 : E)))

def localBasis (i : atlas E M) : Basis (Fin 4) ℝ E :=
  (frameBasis (Q.reduction.Q i) hdim unit unit_norm).toBasis

def localTangentTwoForm (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (a : Fin 3 → ℝ) : TwoForm (TangentSpace 𝓘(ℝ,E) x) := by
  change TwoForm E
  exact pullbackTwoForm (localBasis Q hdim i)
    (localToTangentEquiv Q i x hi).symm.toLinearMap
      ((Real.sqrt 2)⁻¹ • operatorForm (localBasis Q hdim i)
        (synth (Q.reduction.Q i) a))

theorem localTangentTwoForm_pullback (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (b : Basis (Fin 4) ℝ E) (a : Fin 3 → ℝ) :
    pullbackTwoForm b (localToTangentEquiv Q i x hi).toLinearMap
      (localTangentTwoForm Q hdim i x hi a) =
    (Real.sqrt 2)⁻¹ • operatorForm (localBasis Q hdim i)
      (synth (Q.reduction.Q i) a) := by
  apply ExteriorDuality.twoform_ext b
  intro v w
  rw [evaluate_pullbackTwoForm]
  dsimp only [localTangentTwoForm, id_eq]
  rw [evaluate_pullbackTwoForm]
  change BilinearExterior.evaluate
      ((localToTangentEquiv Q i x hi).symm
        (localToTangentEquiv Q i x hi v))
      ((localToTangentEquiv Q i x hi).symm
        (localToTangentEquiv Q i x hi w)) _ = _
  simp

end
end QuaternionicSymmetry.ManifoldQuaternionicFourTwistorHodgeFiber
