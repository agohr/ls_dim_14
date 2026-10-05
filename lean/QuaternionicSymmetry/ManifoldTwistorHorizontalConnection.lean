import QuaternionicSymmetry.ManifoldTwistorVerticalCovariance
import QuaternionicSymmetry.ManifoldQuaternionicInducedSkew
/-! Local horizontal graph of the connection induced on the genuine
quaternionic three-plane, using metric skewness to remain tangent to S². -/

namespace QuaternionicSymmetry.ManifoldTwistorHorizontalConnection
open QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection
open QuaternionicSymmetry.ManifoldQuaternionicInducedSkew
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Matrix Manifold ContDiff
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

def connectionVertical (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : coefficientSphere) : E →ₗ[ℝ] verticalSubmodule a where
  toFun u := ⟨inducedForm Q D p y u a.1, by
    have hs := inducedForm_dot_skew Q D p y u hy a.1 a.1
    have heq : (∑ t : Fin 3, (inducedForm Q D p y u a.1) t * a.1 t) =
        ∑ t : Fin 3, a.1 t * (inducedForm Q D p y u a.1) t := by
      apply Finset.sum_congr rfl
      intro t _
      ring
    rw [heq] at hs
    change a.1 ⬝ᵥ (inducedForm Q D p y u a.1) = 0
    simp only [dotProduct]
    linarith⟩
  map_add' u v := by
    apply Subtype.ext
    simp [inducedForm, map_add]
  map_smul' r u := by
    apply Subtype.ext
    simp [inducedForm, map_smul]

/-- Local horizontal graph of the induced quaternionic rank-three
connection in a sphere-bundle trivialization. -/
def horizontalLift (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : coefficientSphere) : E →ₗ[ℝ] E × verticalSubmodule a where
  toFun u := (u, -(connectionVertical Q D p y hy a u))
  map_add' u v := by
    simp [map_add]
    abel
  map_smul' r u := by
    simp [map_smul]

/-- Local connection splitting: the second coordinate becomes the
covariant vertical derivative. -/
def connectionSplit (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : coefficientSphere) :
    (E × verticalSubmodule a) ≃ₗ[ℝ] (E × verticalSubmodule a) where
  toFun uv := (uv.1, uv.2 + connectionVertical Q D p y hy a uv.1)
  invFun uw := (uw.1, uw.2 - connectionVertical Q D p y hy a uw.1)
  left_inv uv := by
    apply Prod.ext
    · rfl
    · simp
  right_inv uw := by
    apply Prod.ext
    · rfl
    · simp
  map_add' uv uw := by
    apply Prod.ext
    · rfl
    · simp [map_add]
      abel
  map_smul' r uv := by
    apply Prod.ext
    · rfl
    · simp [map_smul, smul_add]

theorem connectionSplit_horizontal (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : coefficientSphere) (u : E) :
    connectionSplit Q D p y hy a (horizontalLift Q D p y hy a u) = (u,0) := by
  apply Prod.ext
  · rfl
  · simp [horizontalLift, connectionSplit]

end
end QuaternionicSymmetry.ManifoldTwistorHorizontalConnection
