import QuaternionicSymmetry.ManifoldRiemannianFixedComponentInput

/-! Source-faithful general form of BG-R2: Petersen, *Riemannian Geometry*,
third edition, Proposition 5.6.5 and proof, printed p. 165 (author-hosted
manuscript PDF p. 180). Any set of actual Riemannian isometries has common
fixed components that are smooth submanifolds, with tangent equal to the
common derivative-fixed subspace. Total geodesicity is separate. -/

namespace QuaternionicSymmetry.ManifoldRiemannianFixedComponentGenericInput

open scoped Manifold ContDiff
noncomputable section

variable {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
variable (I : ModelWithCorners ℝ F H) [IsManifold I ∞ N]

abbrev SmoothMetric := Bundle.ContMDiffRiemannianMetric
  I ∞ F (TangentSpace I : N → Type _)

/-- Differential preservation of an actual smooth Riemannian metric. -/
def PreservesMetric (g : SmoothMetric (F := F) (N := N) I)
    (f : Diffeomorph I I N N ∞) : Prop :=
  ∀ x (u v : TangentSpace I x),
    g.inner (f x) (mfderiv I I (f : N → N) x u)
      (mfderiv I I (f : N → N) x v) =
    g.inner x u v

def fixedPoints (S : Set (Diffeomorph I I N N ∞)) : Set N :=
  {x | ∀ f ∈ S, f x = x}

abbrev FixedComponent
    (S : Set (Diffeomorph I I N N ∞)) (x : N) :=
  ↥(connectedComponentIn (fixedPoints I S) x)

/-- The common derivative-fixed vectors, transported along the actual
pointwise fixedness equality rather than treated as an unrelated model. -/
def fixedVectors
    (S : Set (Diffeomorph I I N N ∞))
    (x : N) (hx : x ∈ fixedPoints I S) :
    Set (TangentSpace I x) :=
  {v | ∀ f, ∀ hf : f ∈ S,
    (hx f hf) ▸ mfderiv I I (f : N → N) x v = v}

/-- The real smooth fixed-component conclusion supplied by BG-R2, with
its actual inclusion and exact tangent identification. -/
structure FixedComponentAtlas
    (S : Set (Diffeomorph I I N N ∞))
    (x : N) (k : ℕ) where
  charts : ChartedSpace (EuclideanSpace ℝ (Fin k)) (FixedComponent I S x)
  manifold : letI := charts
    IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) ∞ (FixedComponent I S x)
  inclusion_smooth : letI := charts
    ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) I ∞
      (Subtype.val : FixedComponent I S x → N)
  inclusion_injective_derivative : letI := charts
    ∀ y : FixedComponent I S x, Function.Injective
      (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) I
        (Subtype.val : FixedComponent I S x → N) y)
  tangent_eq : letI := charts
    ∀ y : FixedComponent I S x, ∀ v : TangentSpace I y.1,
      v ∈ LinearMap.range
        (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) I
          (Subtype.val : FixedComponent I S x → N) y).toLinearMap ↔
      v ∈ fixedVectors I S y.1
        (connectedComponentIn_subset _ _ y.2)

/-- Exactly the smooth-submanifold and tangent-space clauses of Petersen
Proposition 5.6.5. This is a literature premise, not a hypothesis that a
particular twistor fixed component has a complex atlas or any classification
property. -/
def RiemannianFixedComponentOnModel : Prop :=
  ∀ [I.Boundaryless] [T2Space N] [SecondCountableTopology N],
    ∀ (g : SmoothMetric (F := F) (N := N) I)
      (S : Set (Diffeomorph I I N N ∞)),
      (∀ f ∈ S, PreservesMetric I g f) →
      ∀ (x : N), x ∈ fixedPoints I S →
        ∃ k : ℕ, Nonempty (FixedComponentAtlas I S x k)

end
end QuaternionicSymmetry.ManifoldRiemannianFixedComponentGenericInput
