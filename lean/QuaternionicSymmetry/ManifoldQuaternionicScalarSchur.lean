import QuaternionicSymmetry.ManifoldQuaternionicPreferredEinsteinLocallyConstant

/-! Scalar curvature constancy from actual Ricci, metric compatibility and
second Bianchi under the registered quaternionic Einstein decomposition. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicScalarSchur
open ManifoldQuaternionicConnection
open ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicEinsteinFactor
open ManifoldQuaternionicPreferredEinsteinFactor
open ManifoldQuaternionicPreferredEinsteinLocallyConstant
open ManifoldQuaternionicKSWScalarInput
open ManifoldQuaternionicKSWEq38Input
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance : NormedSpace ℝ E := inferInstance
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

theorem preferredEinsteinFactor_eq_scaledScalar
    (S : QuaternionicStructure E)
    (hdecomp : KSWEq38Decomposition S Q D)
    (c : E) (hc : c ≠ 0) (x : M) :
    preferredEinsteinFactor Q D c x =
      (preferredScalarCurvature Q D x /
        (16 * (S.quaternionicDimension : ℝ) *
          ((S.quaternionicDimension : ℝ) + 2))) *
        ((Module.finrank ℝ E : ℝ) + 8) := by
  rw [preferredEinsteinFactor,
    einsteinFactor_eq_scalarRatio Q D S hdecomp x
      (extChartAt 𝓘(ℝ,E) x x)
      ((extChartAt 𝓘(ℝ,E) x).map_source (by simp)) c hc]
  rfl

theorem preferredScalarCurvature_eq_of_factor_eq
    (S : QuaternionicStructure E)
    (hdecomp : KSWEq38Decomposition S Q D)
    (hn : 2 ≤ S.quaternionicDimension)
    (c : E) (hc : c ≠ 0) (x y : M)
    (hfactor : preferredEinsteinFactor Q D c x =
      preferredEinsteinFactor Q D c y) :
    preferredScalarCurvature Q D x =
      preferredScalarCurvature Q D y := by
  let den : ℝ := 16 * (S.quaternionicDimension : ℝ) *
    ((S.quaternionicDimension : ℝ) + 2)
  let dim : ℝ := (Module.finrank ℝ E : ℝ) + 8
  have hden : den ≠ 0 := by
    dsimp [den]
    have hq : (0 : ℝ) < (S.quaternionicDimension : ℝ) := by
      exact_mod_cast (by omega : 0 < S.quaternionicDimension)
    positivity
  have hdim : dim ≠ 0 := by
    dsimp [dim]
    positivity
  rw [preferredEinsteinFactor_eq_scaledScalar Q D S hdecomp c hc x,
    preferredEinsteinFactor_eq_scaledScalar Q D S hdecomp c hc y] at hfactor
  change preferredScalarCurvature Q D x / den * dim =
    preferredScalarCurvature Q D y / den * dim at hfactor
  exact (div_left_inj' hden).mp (mul_right_cancel₀ hdim hfactor)

theorem preferredScalarCurvature_eq_of_preconnected
    (S : QuaternionicStructure E)
    (hdecomp : KSWEq38Decomposition S Q D)
    (hn : 2 ≤ S.quaternionicDimension)
    (hconn : IsPreconnected (Set.univ : Set M))
    (c : E) (hc : c ≠ 0) (x y : M) :
    preferredScalarCurvature Q D x =
      preferredScalarCurvature Q D y := by
  have hcard : 3 ≤ Module.finrank ℝ E := by
    have hdim := S.real_finrank
    omega
  apply preferredScalarCurvature_eq_of_factor_eq Q D S hdecomp hn c hc
  exact (preferredEinsteinFactor_isLocallyConstant Q D S hdecomp c hc hcard).apply_eq_of_isPreconnected
    hconn (by simp) (by simp)

end
end QuaternionicSymmetry.ManifoldQuaternionicScalarSchur
