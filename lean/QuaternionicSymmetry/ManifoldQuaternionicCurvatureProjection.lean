import QuaternionicSymmetry.ManifoldQuaternionicCurvatureSplitting
import QuaternionicSymmetry.QuaternionicLieAlgebraProjectionBracket

/-! The actual curvature components equal the fixed Lie algebra projections
of tangent curvature in each adapted chart. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicCurvatureProjection

open ManifoldQuaternionicConnectionSplitting ManifoldQuaternionicConnection
  ManifoldQuaternionicCurvatureSplitting QuaternionicLieAlgebraProjection
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ, E)) (M := M) (n := ∞)) (D : CompatibleTangentConnection Q)

theorem fderiv_scalarConnection (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    fderiv ℝ (scalarConnection Q D p) y =
      (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) (E →L[ℝ] E)
        (scalarProjection (Q.reduction.Q (achart E p)))).comp
          (fderiv ℝ (D.form p) y) := by
  let L := ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) (E →L[ℝ] E)
    (scalarProjection (Q.reduction.Q (achart E p)))
  have hd : DifferentiableAt ℝ (D.form p) y :=
    ((D.smooth_form p).differentiableOn (by norm_num)).differentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).mem_nhds hy)
  change fderiv ℝ (L ∘ D.form p) y = L.comp (fderiv ℝ (D.form p) y)
  simpa only [L.fderiv] using fderiv_comp y (g := L) L.differentiableAt hd

theorem scalarCurvature_eq_projection (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    LocalConnection.curvature (scalarConnection Q D p) y u v =
      scalarProjection (Q.reduction.Q (achart E p)) (D.curvature Q p y u v) := by
  let S := Q.reduction.Q (achart E p)
  have hLie := scalarProjection_commutator S (D.form p y u) (D.form p y v)
    (fun a => symplecticConnection_commutes Q D p y u hy a)
    (fun a => symplecticConnection_commutes Q D p y v hy a)
  rw [CompatibleTangentConnection.curvature, LocalConnection.curvature_apply,
    LocalConnection.curvature_apply, fderiv_scalarConnection Q D p y hy]
  change scalarProjection S (fderiv ℝ (D.form p) y u v) -
      scalarProjection S (fderiv ℝ (D.form p) y v u) +
        scalarProjection S (D.form p y u) * scalarProjection S (D.form p y v) -
        scalarProjection S (D.form p y v) * scalarProjection S (D.form p y u) =
    scalarProjection S (fderiv ℝ (D.form p) y u v - fderiv ℝ (D.form p) y v u +
      D.form p y u * D.form p y v - D.form p y v * D.form p y u)
  calc
    _ = scalarProjection S (fderiv ℝ (D.form p) y u v - fderiv ℝ (D.form p) y v u) +
        scalarProjection S (D.form p y u * D.form p y v - D.form p y v * D.form p y u) := by
          rw [map_sub, hLie]
          abel
    _ = _ := by rw [← map_add]; congr 1; abel

theorem symplecticCurvature_eq_projection (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target) :
    LocalConnection.curvature (symplecticConnection Q D p) y u v =
      symplecticProjection (Q.reduction.Q (achart E p)) (D.curvature Q p y u v) := by
  have hs := congrArg (fun F : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E) =>
    F u v) (curvature_split Q D p y hy)
  simp only [ContinuousLinearMap.add_apply, scalarCurvature_eq_projection Q D p y u v hy] at hs
  change _ = D.curvature Q p y u v - scalarProjection _ (D.curvature Q p y u v)
  exact eq_sub_of_add_eq hs.symm

end
end QuaternionicSymmetry.ManifoldQuaternionicCurvatureProjection
