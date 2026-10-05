import QuaternionicSymmetry.QuaternionicManifoldCorrectedConnection
import QuaternionicSymmetry.QuaternionicManifoldStandardQuaternionicCurvature
import QuaternionicSymmetry.QuaternionicProjectiveStandardSkew

/-! The solder-corrected connection remains metric and quaternionic for
every real parameter. -/
namespace QuaternionicSymmetry.QuaternionicManifoldCorrectedConnection
open QuaternionicManifoldStandardSolder QuaternionicManifoldFixedSolder
open QuaternionicManifoldProjectiveStandardConnection
open QuaternionicManifoldStandardQuaternionicCurvature QuaternionicProjectiveStandardSkew
open QuaternionicStandardSolderOperator QuaternionicStandardSolderQuaternionic
open QuaternionicProjectiveStandardL2 QuaternionicProjectiveStandardHilbertStructure
open scoped Manifold ContDiff Quaternion
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedSpace ℝ (StandardSpace (E := E)) := inferInstance
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem correctedConnection_I (t : ℝ) (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (z : StandardSpace (E := E)) :
    correctedConnection S Q D t p y u ((standardStructure S).I z) =
      (standardStructure S).I (correctedConnection S Q D t p y u z) := by
  change standardConnection S Q D p y u ((standardStructure S).I z) +
      t • solderOperator S (fixedSolder S Q p y u) ((standardStructure S).I z) =
    (standardStructure S).I (standardConnection S Q D p y u z +
      t • solderOperator S (fixedSolder S Q p y u) z)
  rw [standardConnection_commutes_I S Q D p y u hy, solderOperator_I, map_add, map_smul]

theorem correctedConnection_J (t : ℝ) (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (z : StandardSpace (E := E)) :
    correctedConnection S Q D t p y u ((standardStructure S).J z) =
      (standardStructure S).J (correctedConnection S Q D t p y u z) := by
  change standardConnection S Q D p y u ((standardStructure S).J z) +
      t • solderOperator S (fixedSolder S Q p y u) ((standardStructure S).J z) =
    (standardStructure S).J (standardConnection S Q D p y u z +
      t • solderOperator S (fixedSolder S Q p y u) z)
  rw [standardConnection_commutes_J S Q D p y u hy, solderOperator_J, map_add, map_smul]

theorem correctedConnection_skew (t : ℝ) (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (z w : StandardSpace (E := E)) :
    inner ℝ (correctedConnection S Q D t p y u z) w +
      inner ℝ z (correctedConnection S Q D t p y u w) = 0 := by
  change inner ℝ (standardConnection S Q D p y u z +
      t • solderOperator S (fixedSolder S Q p y u) z) w +
    inner ℝ z (standardConnection S Q D p y u w +
      t • solderOperator S (fixedSolder S Q p y u) w) = 0
  rw [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  have hΓ := standardConnection_skew S Q D p y u hy z w
  have hθ := solderOperator_skew S (fixedSolder S Q p y u) z w
  linear_combination hΓ + t * hθ

end
end QuaternionicSymmetry.QuaternionicManifoldCorrectedConnection
