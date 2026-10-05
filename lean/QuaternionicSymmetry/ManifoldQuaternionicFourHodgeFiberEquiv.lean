import QuaternionicSymmetry.ManifoldQuaternionicFourHodgeFiberInjective

/-! A literal bijection between the original coefficient two-sphere and the
negative-Hodge unit sphere on each actual tangent fiber. This is not yet a
homeomorphism of total bundles. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourHodgeFiberEquiv

open FourDimensionalExteriorHodge
open FourDimensionalExteriorQuaternionicUnitSphere
open ManifoldQuaternionicFourHodgeOverlapExterior
open ManifoldQuaternionicFourTangentOrientation
open ManifoldQuaternionicFourTwistorHodgeFiber
open ManifoldQuaternionicFourTwistorHodgeGlobalMap
open ManifoldQuaternionicFourNegativeHodgeSphere
open ManifoldQuaternionicFourHodgeFiberSurjective
open ManifoldQuaternionicFourHodgeFiberInjective
open ManifoldQuaternionicMetric
open ManifoldTwistorSphereBundle
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

def localHodgeSphereMap (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) :
    coefficientSphere → {α : TwoForm (TangentSpace 𝓘(ℝ,E) x) //
      α ∈ negativeTangentUnitHalf Q hdim x} := by
  intro a
  refine ⟨localTangentTwoForm Q hdim i x hi a.1, ?_⟩
  let z := pointOfLocal Q i x hi a
  have hm := twistorTangentTwoForm_mem_negativeTangentUnitHalf Q hdim z
  have hl := twistorTangentTwoForm_local Q hdim z i
    (by simpa [z, projection_pointOfLocal] using hi)
  have hc := localCoordinate_pointOfLocal Q i x hi a
  simpa only [z, projection_pointOfLocal, hl, hc] using hm

theorem localHodgeSphereMap_injective (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) :
    Function.Injective (localHodgeSphereMap Q hdim i x hi) := by
  intro a c h
  apply Subtype.ext
  exact localTangentTwoForm_injective Q hdim i x hi a.1 c.1
    (congrArg Subtype.val h)

theorem localHodgeSphereMap_surjective (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) :
    Function.Surjective (localHodgeSphereMap Q hdim i x hi) := by
  intro α
  obtain ⟨z,hx,hform⟩ := negativeTangentUnitHalf_exists_twistor
    Q hdim x α.1 α.2
  subst x
  let a := localCoordinate Q i z hi
  refine ⟨a, ?_⟩
  apply Subtype.ext
  have hl := twistorTangentTwoForm_local Q hdim z i hi
  exact hl.symm.trans hform

def localHodgeSphereEquiv (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) :
    coefficientSphere ≃
      {α : TwoForm (TangentSpace 𝓘(ℝ,E) x) //
        α ∈ negativeTangentUnitHalf Q hdim x} :=
  Equiv.ofBijective (localHodgeSphereMap Q hdim i x hi)
    ⟨localHodgeSphereMap_injective Q hdim i x hi,
      localHodgeSphereMap_surjective Q hdim i x hi⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicFourHodgeFiberEquiv
