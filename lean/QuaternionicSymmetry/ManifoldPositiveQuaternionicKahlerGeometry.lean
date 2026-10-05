import QuaternionicSymmetry.ManifoldQuaternionicConnectionUniqueness
import QuaternionicSymmetry.ManifoldQuaternionicKSWDerivedEndpoints

/-!
A positive quaternionic Kähler geometry on a genuine smooth manifold, using
natural geometric data: a smooth quaternionic Hermitian tangent reduction,
its metric and torsion-free connection preserving the quaternionic span,
and positivity of the scalar curvature computed from that connection.

The connection is unique on valid charts by the metric and torsion laws.
Compactness and connectedness are separate fields only in the compact
package. Neither structure contains an index, curvature decomposition,
symmetry, or classification conclusion. The pinned library does not construct
the Levi-Civita connection from an arbitrary metric; its existence here is
part of the geometric input.

For quaternionic dimension at least two these are the natural positive
quaternionic Kähler data. In quaternionic dimension one, preservation of the
rank-three quaternionic span does not impose the self-dual Einstein condition
used in the four-dimensional classification; that case needs separate genuine
geometric input and is not claimed from this structure alone.
-/
namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicConnection
open ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicConnectionUniqueness
open ManifoldQuaternionicKSWDerivedEndpoints
open scoped Manifold ContDiff Topology Quaternion
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

structure PositiveQuaternionicKahlerGeometry where
  tangent : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞)
  connection : CompatibleTangentConnection tangent
  scalar_pos : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
    0 < localScalarCurvature tangent connection p y hy

def PositiveQuaternionicKahlerGeometry.toPositiveScalarTangentGeometry
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M)) :
    PositiveScalarTangentGeometry P.tangent where
  connection := P.connection
  scalar_pos := P.scalar_pos

def PositiveQuaternionicKahlerGeometry.riemannianMetric
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M)) :
    Bundle.ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (TangentSpace 𝓘(ℝ,E) : M → Type _) :=
  P.tangent.riemannianMetric

omit [Nontrivial E] in
theorem PositiveQuaternionicKahlerGeometry.connection_unique_on_chart
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (D : CompatibleTangentConnection P.tangent)
    (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    P.connection.form p y = D.form p y :=
  form_eq_on_chart P.tangent P.connection D p y hy

structure CompactConnectedPositiveQuaternionicKahlerGeometry extends
    PositiveQuaternionicKahlerGeometry (E := E) (M := M) where
  compact : IsCompact (Set.univ : Set M)
  connected : IsPreconnected (Set.univ : Set M)

set_option maxHeartbeats 1000000 in
theorem CompactConnectedPositiveQuaternionicKahlerGeometry.exists_common_parameter
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (S : QuaternionicStructure E)
    (hn : 2 ≤ S.quaternionicDimension)
    (hsp : ManifoldQuaternionicKSWScalarInput.KSWLemma310OnModel (E := E) (M := M))
    (heq38 : ManifoldQuaternionicKSWEq38Input.KSWEq38OnModel (E := E) (M := M)) :
    ∃ t : ℝ, 0 < t ∧
      ManifoldQuaternionicAdjointChernWeil.quarterPontryaginCandidateForm
          P.tangent P.connection =
        (t ^ 4 / Real.pi ^ 2) •
          ManifoldQuaternionicFundamentalClass.closedFundamental
            P.tangent P.connection ∧
      (∀ (p : M) (y : E)
        (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
        ∃ W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E),
          ManifoldQuaternionicKSWEq38Input.HyperWeylFiber S W ∧
          ∀ (a b : E) (z : QuaternionicProjectiveStandardL2.StandardSpace (E := E)),
            (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ)
              (LocalConnection.curvature
                (QuaternionicManifoldCorrectedConnection.correctedConnection
                  S P.tangent P.connection t p) y
                ((ManifoldQuaternionicKSWEq38Input.fixedSolderEquiv
                  S P.tangent p y hy).symm a)
                ((ManifoldQuaternionicKSWEq38Input.fixedSolderEquiv
                  S P.tangent p y hy).symm b) z) =
              (W a b z.fst, 0)) :=
  exists_common_hyper_and_fundamental_parameter S P.tangent
    hsp heq38 P.toPositiveScalarTangentGeometry hn P.connected

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry
