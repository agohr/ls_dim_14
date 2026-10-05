import QuaternionicSymmetry.QuaternionicManifoldProjectiveSmooth
import QuaternionicSymmetry.QuaternionicProjectiveStandardSkew

/-! Local connection on the smooth projective adjoint bundle, induced by
the actual compatible tangent connection through the standard Hilbert
representation.  The operator on a fiber endomorphism is a commutator. -/

namespace QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointConnection

open QuaternionicProjectiveStandardL2 QuaternionicProjectiveStandardAdjoint
  QuaternionicManifoldProjectiveStandardConnection
  QuaternionicManifoldProjectiveSmooth
  ManifoldQuaternionicConnection
open scoped ContDiff Manifold Quaternion
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance
local instance : NormedSpace ℝ (StandardEnd (E := E)) := inferInstance
local instance : NormedSpace ℝ
    (StandardEnd (E := E) →L[ℝ] StandardEnd (E := E)) := inferInstance

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def adjointLie : StandardEnd (E := E) →L[ℝ]
    (StandardEnd (E := E) →L[ℝ] StandardEnd (E := E)) :=
  (ContinuousLinearMap.compL ℝ (StandardSpace (E := E))
      (StandardSpace (E := E)) (StandardSpace (E := E))) -
    (ContinuousLinearMap.compL ℝ (StandardSpace (E := E))
      (StandardSpace (E := E)) (StandardSpace (E := E))).flip

omit [FiniteDimensional ℝ E] [Nontrivial E] in
@[simp] theorem adjointLie_apply (A B : StandardEnd (E := E)) :
    adjointLie (E := E) A B = A * B - B * A := rfl

def adjointConnection (p : M) :
    LocalConnection.Form (E := E)
      (A := StandardEnd (E := E) →L[ℝ] StandardEnd (E := E)) :=
  fun y => (adjointLie (E := E)).comp (standardConnection S Q D p y)

theorem adjointConnection_apply (p : M) (y u : E)
    (B : StandardEnd (E := E)) :
    adjointConnection S Q D p y u B =
      standardConnection S Q D p y u * B -
        B * standardConnection S Q D p y u := rfl


end
end QuaternionicSymmetry.QuaternionicManifoldProjectiveAdjointConnection
