import QuaternionicSymmetry.QuaternionicSpCoordinateExtension
import QuaternionicSymmetry.ManifoldQuaternionicMetricCurvature
import QuaternionicSymmetry.ManifoldQuaternionicSymplecticCurvature
import QuaternionicSymmetry.QuaternionicCurvatureExteriorCoordinates

/-! Fixed finite centralizer coordinates for the actual symplectic
curvature on an adapted chart. -/
namespace QuaternionicSymmetry.QuaternionicActualSpCurvatureCoordinates
open QuaternionicCurvatureFiniteExpansion QuaternionicSpCoordinateExtension
  ManifoldQuaternionicConnectionSplitting
  ManifoldQuaternionicSymplecticCurvature ManifoldQuaternionicMetricCurvature
  QuaternionicCurvatureExteriorCoordinates ExteriorContinuousPairing
  LocalConnectionForms
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

abbrev chartStructure (p : M) : QuaternionicStructure E :=
  Q.reduction.Q (achart E p)

theorem symplecticCurvature_mem (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    LocalConnection.curvature (symplecticConnection Q D p) y u v ∈
      operatorSpace (chartStructure Q p) := by
  change (LocalConnection.curvature (symplecticConnection Q D p) y u v).toLinearMap ∈
    (chartStructure Q p).skewCentralizer
  apply ((chartStructure Q p).mem_skewCentralizer_iff _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    have h := symplecticCurvature_skew Q D p y u v a b hy
    exact eq_neg_of_add_eq_zero_left h
  · intro a
    have h := congrArg (fun T : E →L[ℝ] E => T a)
      (symplecticCurvature_commutes Q D p y u v hy
        (Pi.basisFun ℝ (Fin 3) 0))
    simpa only [ManifoldQuaternionicRankThreeOrthogonal.synth_basis,
      VectorBundleFrameTransitions.quaternionicGenerator,
      ContinuousLinearMap.mul_apply] using h
  · intro a
    have h := congrArg (fun T : E →L[ℝ] E => T a)
      (symplecticCurvature_commutes Q D p y u v hy
        (Pi.basisFun ℝ (Fin 3) 1))
    simpa only [ManifoldQuaternionicRankThreeOrthogonal.synth_basis,
      VectorBundleFrameTransitions.quaternionicGenerator,
      ContinuousLinearMap.mul_apply] using h

def spCoefficientTwoForm (p : M) (y : E) (a : Index (chartStructure Q p)) :
    E [⋀^Fin 2]→L[ℝ] ℝ :=
  (coordinate (chartStructure Q p) a).compContinuousAlternatingMap
    (curvatureForm (symplecticConnection Q D p) y)

def spCoefficientPower (p : M) (y : E) (a : Index (chartStructure Q p)) :
    Power E 2 :=
  (equiv (V := E) 2).symm (spCoefficientTwoForm Q D p y a)

@[simp] theorem spCoefficientPower_toContinuous (p : M) (y : E)
    (a : Index (chartStructure Q p)) :
    toContinuous 2 (spCoefficientPower Q D p y a) =
      spCoefficientTwoForm Q D p y a :=
  (equiv (V := E) 2).apply_symm_apply _

theorem symplecticCurvature_expansion (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    ∑ a : Index (chartStructure Q p),
      (spCoefficientTwoForm Q D p y a) ![u,v] •
        (operatorBasis (chartStructure Q p) a).val =
      LocalConnection.curvature (symplecticConnection Q D p) y u v := by
  let T : operatorSpace (chartStructure Q p) :=
    ⟨LocalConnection.curvature (symplecticConnection Q D p) y u v,
      symplecticCurvature_mem Q D p y u v hy⟩
  have h := expansion_mem (chartStructure Q p) T
  convert h using 1
  · apply Finset.sum_congr rfl
    intro a ha
    change coordinate (chartStructure Q p) a
      (curvatureForm (symplecticConnection Q D p) y ![u,v]) • _ = _
    simp only [curvatureForm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rfl

end
end QuaternionicSymmetry.QuaternionicActualSpCurvatureCoordinates
