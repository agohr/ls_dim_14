import QuaternionicSymmetry.ManifoldQuaternionicScalarSchur
import QuaternionicSymmetry.ManifoldQuaternionicKSWConstantScalarInput

/-! The constant scalar-normalization parameter follows internally from
the actual metric connection's Bianchi identities and the registered
Eq. (3.8) Einstein decomposition. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicKSWScalarConstancyDerived
open ManifoldQuaternionicConnection
open ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicScalarSchur
open ManifoldQuaternionicKSWScalarInput
open ManifoldQuaternionicKSWConstantScalarInput
open ManifoldQuaternionicKSWEq38Input
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem exists_constant_scalar_of_eq38
    (G : PositiveScalarTangentGeometry Q)
    (hdecomp : KSWEq38Decomposition S Q G.connection)
    (hn : 2 ≤ S.quaternionicDimension)
    (hconn : IsPreconnected (Set.univ : Set M)) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ x : M, preferredScalarCurvature Q G.connection x = κ := by
  by_cases hM : Nonempty M
  · obtain ⟨x⟩ := hM
    obtain ⟨c, hc⟩ : ∃ c : E, c ≠ 0 := exists_ne 0
    refine ⟨preferredScalarCurvature Q G.connection x,
      G.preferredScalarCurvature_pos Q x, ?_⟩
    intro y
    exact (preferredScalarCurvature_eq_of_preconnected Q G.connection S
      hdecomp hn hconn c hc y x)
  · refine ⟨1, by norm_num, ?_⟩
    intro x
    exact (hM ⟨x⟩).elim

theorem exists_global_parameter_of_eq38
    (G : PositiveScalarTangentGeometry Q)
    (hdecomp : KSWEq38Decomposition S Q G.connection)
    (hn : 2 ≤ S.quaternionicDimension)
    (hconn : IsPreconnected (Set.univ : Set M)) :
    ∃ t : ℝ, 0 < t ∧
      ∀ (p : M) (y : E)
        (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
        t ^ 2 = scalarRatio S Q G.connection p y hy := by
  obtain ⟨κ, hκpos, hκ⟩ :=
    exists_constant_scalar_of_eq38 S Q G hdecomp hn hconn
  let den : ℝ := 16 * (S.quaternionicDimension : ℝ) *
    ((S.quaternionicDimension : ℝ) + 2)
  have hq : (0 : ℝ) < (S.quaternionicDimension : ℝ) := by
    exact_mod_cast (by omega : 0 < S.quaternionicDimension)
  have hden : 0 < den := by dsimp [den]; positivity
  let r : ℝ := κ / den
  have hr : 0 < r := div_pos hκpos hden
  refine ⟨Real.sqrt r, Real.sqrt_pos.2 hr, ?_⟩
  intro p y hy
  rw [Real.sq_sqrt (le_of_lt hr)]
  simpa only [r, den] using
    (scalarRatio_eq_const S Q G κ hκ p y hy).symm

end
end QuaternionicSymmetry.ManifoldQuaternionicKSWScalarConstancyDerived
