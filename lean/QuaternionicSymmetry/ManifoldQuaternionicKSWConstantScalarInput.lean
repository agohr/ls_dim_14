import QuaternionicSymmetry.ManifoldQuaternionicKSWEq38Input

/-!
The standard Einstein/constant-scalar theorem for quaternionic-Kähler
manifolds is registered separately from the pointwise curvature
decomposition. KSW arXiv:dg-ga/9709014v1, Introduction p. 2, states that
quaternionic-Kähler manifolds have constant scalar curvature (citing
Alekseevskii and Ishihara). Connectedness is explicit because the scalar
may differ on distinct connected components.

No instance or axiom supplies the source premise below. The actual global
normalization parameter is derived from it and from the computed scalar
contraction of the tangent connection.
-/
namespace QuaternionicSymmetry.ManifoldQuaternionicKSWConstantScalarInput
open ManifoldQuaternionicConnection
open ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicKSWScalarInput
open ManifoldQuaternionicKSWEq38Input
open scoped Manifold ContDiff Topology Quaternion
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- Explicit external constant-scalar theorem premise for positive
quaternionic-Kähler geometry in quaternionic dimension at least two. -/
def KSWConstantScalarOnConnectedModel : Prop :=
  ∀ (S : QuaternionicStructure E)
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (G : PositiveScalarTangentGeometry Q),
    2 ≤ S.quaternionicDimension →
    IsPreconnected (Set.univ : Set M) →
    ∃ κ : ℝ, 0 < κ ∧
      ∀ x : M, preferredScalarCurvature Q G.connection x = κ

omit [Nontrivial E] in
theorem exists_constant_scalar
    (hsource : KSWConstantScalarOnConnectedModel (E := E) (M := M))
    (G : PositiveScalarTangentGeometry Q)
    (hn : 2 ≤ S.quaternionicDimension)
    (hconn : IsPreconnected (Set.univ : Set M)) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ x : M, preferredScalarCurvature Q G.connection x = κ :=
  hsource S Q G hn hconn

omit [Nontrivial E] in
theorem scalarRatio_eq_const
    (G : PositiveScalarTangentGeometry Q)
    (κ : ℝ)
    (hκ : ∀ x : M, preferredScalarCurvature Q G.connection x = κ)
    (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    scalarRatio S Q G.connection p y hy =
      κ / (16 * (S.quaternionicDimension : ℝ) *
        ((S.quaternionicDimension : ℝ) + 2)) := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  have hx : x ∈ (extChartAt 𝓘(ℝ,E) p).source :=
    (extChartAt 𝓘(ℝ,E) p).map_target hy
  have hlocal := localScalarCurvature_eq_preferred Q G.connection p x hx
    (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)
  have hxy : (extChartAt 𝓘(ℝ,E) p) x = y :=
    (extChartAt 𝓘(ℝ,E) p).right_inv hy
  have hlocal' : localScalarCurvature Q G.connection p y hy =
      preferredScalarCurvature Q G.connection x := by
    simpa only [hxy] using hlocal
  have hscalar : localScalarCurvature Q G.connection p y hy = κ :=
    hlocal'.trans (hκ x)
  simp only [scalarRatio, hscalar]

omit [Nontrivial E] in
/-- A single positive scalar-normalization parameter works in every
adapted chart on a connected positive quaternionic-Kähler manifold, once
the classical constant-scalar theorem is supplied. -/
theorem exists_global_parameter
    (hsource : KSWConstantScalarOnConnectedModel (E := E) (M := M))
    (G : PositiveScalarTangentGeometry Q)
    (hn : 2 ≤ S.quaternionicDimension)
    (hconn : IsPreconnected (Set.univ : Set M)) :
    ∃ t : ℝ, 0 < t ∧
      ∀ (p : M) (y : E)
        (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
        t ^ 2 = scalarRatio S Q G.connection p y hy := by
  obtain ⟨κ, hκpos, hκ⟩ := exists_constant_scalar S Q hsource G hn hconn
  let d : ℝ := 16 * (S.quaternionicDimension : ℝ) *
    ((S.quaternionicDimension : ℝ) + 2)
  have hnpos : (0 : ℝ) < S.quaternionicDimension := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
  have hd : 0 < d := by
    dsimp [d]
    positivity
  let t : ℝ := Real.sqrt (κ / d)
  refine ⟨t, Real.sqrt_pos.2 (div_pos hκpos hd), ?_⟩
  intro p y hy
  rw [scalarRatio_eq_const S Q G κ hκ p y hy]
  exact Real.sq_sqrt (le_of_lt (div_pos hκpos hd))

/-- The global scalar-normalized corrected connection has the source
hyper-Weyl curvature block in every fixed quaternionic chart. The only
external inputs are the three explicitly named classical curvature and
constant-scalar statements. -/
theorem exists_global_hyper_curvature_parameter
    (hconstant : KSWConstantScalarOnConnectedModel (E := E) (M := M))
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (G : PositiveScalarTangentGeometry Q)
    (hn : 2 ≤ S.quaternionicDimension)
    (hconn : IsPreconnected (Set.univ : Set M)) :
    ∃ t : ℝ, 0 < t ∧
      ∀ (p : M) (y : E)
        (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
        ∃ W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E),
          HyperWeylFiber S W ∧
          ∀ (a b : E) (z : QuaternionicProjectiveStandardL2.StandardSpace (E := E)),
            (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ)
              (LocalConnection.curvature
                (QuaternionicManifoldCorrectedConnection.correctedConnection
                  S Q G.connection t p) y
                ((fixedSolderEquiv S Q p y hy).symm a)
                ((fixedSolderEquiv S Q p y hy).symm b) z) =
              (W a b z.fst, 0) := by
  obtain ⟨t, htpos, ht⟩ := exists_global_parameter S Q hconstant G hn hconn
  refine ⟨t, htpos, ?_⟩
  intro p y hy
  exact correctedCurvature_eq_hyper_fixed S Q G.connection
    (formula_of_KSWLemma310OnModel S Q hsp G hn)
    (decomposition_of_KSWEq38OnModel S Q heq38 G hn)
    t p y hy (ht p y hy)

end
end QuaternionicSymmetry.ManifoldQuaternionicKSWConstantScalarInput
