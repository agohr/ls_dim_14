import QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaSolder

/-! The genuine adapted Levi-Civita form satisfies the repository's
solder-coordinate torsion-free law, derived from ordinary LC torsion. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaTorsion

open Manifold Bundle GeneralLeviCivitaSource
open ManifoldQuaternionicConnection
open ManifoldQuaternionicAdaptedLeviCivitaForm
open ManifoldQuaternionicAdaptedLeviCivitaSolder
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ConnectedSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
    (TangentSpace 𝓘(ℝ,E) : M → Type _))
  (D : CoordinateLeviCivitaConnection g)

theorem adaptedLeviCivitaForm_torsion (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u v : E) :
    fderiv ℝ (solder Q p) y u v - fderiv ℝ (solder Q p) y v u +
      adaptedLeviCivitaForm Q g D p y u (solder Q p y v) -
      adaptedLeviCivitaForm Q g D p y v (solder Q p y u) = 0 := by
  rw [adaptedLeviCivitaForm_apply_solder Q g D p y hy u v,
    adaptedLeviCivitaForm_apply_solder Q g D p y hy v u]
  have ht := D.torsion p y u v hy
  rw [ht]
  abel

end
end QuaternionicSymmetry.ManifoldQuaternionicAdaptedLeviCivitaTorsion
