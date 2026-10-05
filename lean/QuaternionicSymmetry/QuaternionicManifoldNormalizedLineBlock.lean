import QuaternionicSymmetry.ManifoldQuaternionicKSWScalarInput
import QuaternionicSymmetry.QuaternionicManifoldCorrectedCurvature

/-! The actual corrected curvature has zero quaternionic-line block at
the KSW normalization, relative to the precisely named scalar source input. -/
namespace QuaternionicSymmetry.QuaternionicManifoldNormalizedLineBlock
open ManifoldQuaternionicKSWScalarInput ManifoldQuaternionicScalarCurvature
open QuaternionicManifoldCorrectedConnection QuaternionicProjectiveStandardL2
open QuaternionicManifoldFixedSolder QuaternionicManifoldProjectiveStandardConnection
open QuaternionicProjectiveStandardLie QuaternionicStandardSolderSquare
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

theorem correctedCurvature_line_zero (hsource : KSWSp1CurvatureFormula S Q D)
    (t : ℝ) (p : M) (y u v : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (ht : t ^ 2 = scalarRatio S Q D p y hy) (z : StandardSpace (E := E)) :
    (LocalConnection.curvature (correctedConnection S Q D t p) y u v z).snd = 0 := by
  have h := congrArg Prod.snd (correctedCurvature_blocks S Q D t p y u v hy z)
  have hline := congrArg (fun A : ℍ →L[ℝ] ℍ => A z.snd)
    (lineCurvature_cancel S Q D hsource t p y u v hy ht)
  exact h.trans hline

def scalarParameter (κ : ℝ) : ℝ :=
  Real.sqrt (κ / (16 * (S.quaternionicDimension : ℝ) * ((S.quaternionicDimension : ℝ) + 2)))

omit [FiniteDimensional ℝ E] [Nontrivial E] in
theorem scalarParameter_sq (κ : ℝ) (hκ : 0 ≤ κ) (hn : 0 < S.quaternionicDimension) :
    scalarParameter S κ ^ 2 =
      κ / (16 * (S.quaternionicDimension : ℝ) * ((S.quaternionicDimension : ℝ) + 2)) := by
  apply Real.sq_sqrt
  apply div_nonneg hκ
  have hn' : (0 : ℝ) < S.quaternionicDimension := by exact_mod_cast hn
  positivity

theorem correctedCurvature_line_zero_constant
    (hsource : KSWSp1CurvatureFormula S Q D) (κ : ℝ) (hκ : 0 ≤ κ)
    (hn : 0 < S.quaternionicDimension)
    (hconstant : ∀ p y hy, localScalarCurvature Q D p y hy = κ)
    (p : M) (y u v : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (z : StandardSpace (E := E)) :
    (LocalConnection.curvature (correctedConnection S Q D (scalarParameter S κ) p)
      y u v z).snd = 0 := by
  apply correctedCurvature_line_zero S Q D hsource _ p y u v hy
  rw [scalarRatio, hconstant, scalarParameter_sq S κ hκ hn]

end
end QuaternionicSymmetry.QuaternionicManifoldNormalizedLineBlock
