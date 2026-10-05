import QuaternionicSymmetry.QuaternionicManifoldCorrectedConnection
import QuaternionicSymmetry.QuaternionicManifoldStandardSolderClosed
import QuaternionicSymmetry.QuaternionicManifoldStandardCurvatureRepresentation
import QuaternionicSymmetry.QuaternionicStandardSolderSquare

/-! The actual torsion-free solder correction has no linear curvature term.
Its remaining two diagonal blocks are computed explicitly. -/
namespace QuaternionicSymmetry.QuaternionicManifoldCorrectedConnection
open QuaternionicManifoldStandardSolder QuaternionicManifoldFixedSolder
open QuaternionicManifoldStandardSolderClosed
open QuaternionicManifoldProjectiveStandardConnection
open QuaternionicManifoldStandardCurvatureRepresentation
open QuaternionicProjectiveStandardL2 QuaternionicProjectiveStandardLie
open QuaternionicStandardSolderSquare QuaternionicStandardSolderOperator
open scoped Manifold ContDiff Quaternion
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance curvatureNormedSpaceE : NormedSpace ℝ E := inferInstance
local instance curvatureNormedSpaceW : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance
local instance curvatureNormedSpaceEnd : NormedSpace ℝ
    (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) := inferInstance
local instance curvatureNormedSpaceBilinear : NormedSpace ℝ
    (LocalConnection.Bilinear (E := E)
      (A := StandardSpace (E := E) →L[ℝ] StandardSpace (E := E))) := inferInstance
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

set_option maxHeartbeats 800000 in
theorem correctedCurvature_eq (t : ℝ) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    LocalConnection.curvature (correctedConnection S Q D t p) y =
      LocalConnection.curvature (standardConnection S Q D p) y +
        t ^ 2 • LocalConnection.wedgeSquare (standardSolder S Q p) y := by
  rw [correctedConnection_curvature S Q D t p y hy,
    standardSolder_covariantly_closed S Q D p y hy]
  have hz : t • (0 : LocalConnection.Bilinear (E := E)
      (A := StandardSpace (E := E) →L[ℝ] StandardSpace (E := E))) = 0 := by
    ext u v z
    change t • (0 : StandardSpace (E := E)) = 0
    exact smul_zero t
  rw [hz, add_zero]

theorem correctedCurvature_blocks (t : ℝ) (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (z : StandardSpace (E := E)) :
    (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ)
      (LocalConnection.curvature (correctedConnection S Q D t p) y u v z) =
    (QuaternionicLieAlgebraProjection.symplecticProjection S
        (fixedTangentConjugation S Q p (D.curvature Q p y u v)) z.fst +
        t ^ 2 • upperSquare S (fixedSolder S Q p y u) (fixedSolder S Q p y v) z.fst,
      scalarLineLie S (fixedTangentConjugation S Q p (D.curvature Q p y u v)) z.snd +
        t ^ 2 • lowerSquare S (fixedSolder S Q p y u) (fixedSolder S Q p y v) z.snd) := by
  rw [correctedCurvature_eq S Q D t p y hy]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  rw [standardCurvature_eq_representation S Q D p y u v hy]
  have hs : LocalConnection.wedgeSquare (standardSolder S Q p) y u v =
      OperatorBlockDerivative.blockOperator (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ)
        (upperSquare S (fixedSolder S Q p y u) (fixedSolder S Q p y v))
        (lowerSquare S (fixedSolder S Q p y u) (fixedSolder S Q p y v)) :=
    solder_commutator S _ _
  rw [hs, map_add, map_smul, standardLie_blocks]
  rfl

end
end QuaternionicSymmetry.QuaternionicManifoldCorrectedConnection
