import QuaternionicSymmetry.ManifoldQuaternionicInducedTotalGeodesy
import QuaternionicSymmetry.ManifoldRiemannianFixedComponentInput

/-! Narrow BG-R2 companion to Petersen, Riemannian Geometry, 3rd ed.,
Proposition 5.6.5 (printed p. 165): every connected component of the common
fixed locus of a set of isometries is totally geodesic. The conclusion is
only vanishing of the actual adapted-gauge covariant Hessian. -/
namespace QuaternionicSymmetry.ManifoldRiemannianFixedTotalGeodesyInput
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedTotalGeodesy
open ManifoldQuaternionicConnection
open ManifoldQuaternionicSpanSymmetry
open ManifoldRiemannianFixedComponentInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- BG-R2's total-geodesy clause for the genuine fixed component, stated
only after its actual inherited smooth atlas and metric have been supplied.
It imposes no contact, twistor-horizontal, curvature, or classification
conclusion. -/
def FixedComponentTotalGeodesyOnModel : Prop :=
  ∀ [T2Space M] [SecondCountableTopology M],
    ∀ (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (S : Subgroup (QuaternionicIsometries P.tangent)) (x : M)
    (k : ℕ) (C : FixedComponentAtlas P.tangent S x k),
    letI := C.charts
    letI := C.manifold
    ∀ (R : PositiveQuaternionicKahlerGeometry
        (E := EuclideanSpace ℝ (Fin k)) (M := FixedComponent P.tangent S x))
      (_hR : IsInducedQuaternionicGeometry P R
        (Subtype.val : FixedComponent P.tangent S x → M))
      (DP : CompatibleTangentConnection P.tangent)
      (DR : CompatibleTangentConnection R.tangent),
      IsTotallyGeodesic P R
        (Subtype.val : FixedComponent P.tangent S x → M) DP DR

theorem fixedComponent_totallyGeodesic_of_source
    [T2Space M] [SecondCountableTopology M]
    (hBG : FixedComponentTotalGeodesyOnModel (E := E) (M := M))
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (S : Subgroup (QuaternionicIsometries P.tangent)) (x : M)
    (k : ℕ) (C : FixedComponentAtlas P.tangent S x k) :
    letI := C.charts
    letI := C.manifold
    ∀ (R : PositiveQuaternionicKahlerGeometry
        (E := EuclideanSpace ℝ (Fin k)) (M := FixedComponent P.tangent S x))
      (_hR : IsInducedQuaternionicGeometry P R
        (Subtype.val : FixedComponent P.tangent S x → M))
      (DP : CompatibleTangentConnection P.tangent)
      (DR : CompatibleTangentConnection R.tangent),
      IsTotallyGeodesic P R
        (Subtype.val : FixedComponent P.tangent S x → M) DP DR :=
  hBG P S x k C

end
end QuaternionicSymmetry.ManifoldRiemannianFixedTotalGeodesyInput
