import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry

/-! Exact equivalence between the intrinsic positive quaternionic Kähler
package and the pre-existing dependent Q/G API. No extra geometric premise
is introduced by the package. -/
namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerEquiv
open ManifoldQuaternionicConnection
open ManifoldQuaternionicScalarCurvature
open ManifoldPositiveQuaternionicKahlerGeometry
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def fromPair
    (P : Σ Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞),
      PositiveScalarTangentGeometry Q) :
    PositiveQuaternionicKahlerGeometry (E := E) (M := M) where
  tangent := P.1
  connection := P.2.connection
  scalar_pos := P.2.scalar_pos

def toPair
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M)) :
    Σ Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞),
      PositiveScalarTangentGeometry Q :=
  ⟨P.tangent, P.toPositiveScalarTangentGeometry⟩

def pairEquiv :
    (Σ Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞),
      PositiveScalarTangentGeometry Q) ≃
      PositiveQuaternionicKahlerGeometry (E := E) (M := M) where
  toFun := fromPair
  invFun := toPair
  left_inv := by intro P; cases P with | mk Q G => cases G; rfl
  right_inv := by intro P; cases P; rfl

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerEquiv
