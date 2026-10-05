import QuaternionicSymmetry.ManifoldQuaternionicRiemannSymmetry
import QuaternionicSymmetry.QuaternionicManifoldCorrectedConnection
import QuaternionicSymmetry.QuaternionicManifoldCorrectedCurvature
import QuaternionicSymmetry.QuaternionicStandardSolderLine
import QuaternionicSymmetry.QuaternionicProjectiveStandardLieBracket

/-!
An explicit pointwise registration of the `Sp(1)` curvature formula in
Kramer--Semmelmann--Weingart, Lemma 3.10 (arXiv:dg-ga/9709014v1).

The proposition below is a named curvature interface. It refers to the
actual curvature and scalar contraction of the compatible tangent connection.
No corrected connection or cancellation appears in its statement. The source
uses the scalar curvature `κ`, quaternionic dimension `n`, and the two-form
coefficient `2⟪u,Iv⟫`; the coefficient here is transported to our generators
and sign convention. `ManifoldQuaternionicKSWScalarFromDecomposition` derives
it from the retained KSW Equation (3.8) contract, so it is no longer an
independent literature input of the final development.
-/
namespace QuaternionicSymmetry.ManifoldQuaternionicKSWScalarInput
open ManifoldQuaternionicConnection
open ManifoldQuaternionicScalarCurvature
open QuaternionicManifoldFixedSolder
open QuaternionicManifoldProjectiveStandardConnection
open QuaternionicProjectiveStandardLie
open QuaternionicProjectiveStandardLieBracket
open QuaternionicLieAlgebraProjection
open QuaternionicStandardSolderSquare
open QuaternionicStandardSolderLine
open QuaternionicManifoldCorrectedConnection
open QuaternionicProjectiveStandardL2
open VectorBundleFrameTransitions
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff Topology Quaternion
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

/-- The source's `κ/(16n(n+2))`, with `κ` calculated from actual curvature. -/
def scalarRatio (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) : ℝ :=
  localScalarCurvature Q D p y hy /
    (16 * (S.quaternionicDimension : ℝ) * ((S.quaternionicDimension : ℝ) + 2))

/-- The local Kähler two-form coefficients in the fixed quaternionic model. -/
def kahlerCoefficients (p : M) (y u v : E) : Fin 3 → ℝ :=
  fun i => inner ℝ ((quaternionicGenerator S i) (fixedSolder S Q p y u))
    (fixedSolder S Q p y v)

/-- The pointwise `Sp(1)` component formula of KSW Lemma 3.10, stated for
the actual metric, torsion-free, quaternionic compatible connection. This is
an explicitly named source premise, not a field of the PQK geometry. -/
def KSWSp1CurvatureFormula : Prop :=
  ∀ (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
    scalarProjection S (fixedTangentConjugation S Q p
      (D.curvature Q p y u v)) =
      (-(2 * scalarRatio S Q D p y hy)) •
        synth S (kahlerCoefficients S Q p y u v)

/-- The explicitly quantified mathematical source premise. The hypotheses
match the positive scalar quaternionic-Kähler setting and dimension `n ≥ 2`
used in KSW. This definition carries no assertion that the premise has been
proved in Lean. -/
def KSWLemma310OnModel : Prop :=
  ∀ (S : QuaternionicStructure E)
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (G : PositiveScalarTangentGeometry Q),
    2 ≤ S.quaternionicDimension →
    KSWSp1CurvatureFormula S Q G.connection

theorem formula_of_KSWLemma310OnModel
    (hsource : KSWLemma310OnModel (E := E) (M := M))
    (G : PositiveScalarTangentGeometry Q)
    (hn : 2 ≤ S.quaternionicDimension) :
    KSWSp1CurvatureFormula S Q G.connection :=
  hsource S Q G hn

omit [Nontrivial E] in
private theorem lowerSquare_one_coordinates (u v : E) :
    lowerSquare S u v 1 =
      (-(2 : ℝ)) • imaginary (fun i =>
        inner ℝ ((quaternionicGenerator S i) u) v) := by
  rw [lowerSquare_one]
  apply Quaternion.ext <;>
    simp [imaginary_re, imaginary_imI, imaginary_imJ, imaginary_imK,
      quaternionicGenerator]

/-- The line block of the corrected curvature vanishes at the pointwise
KSW scalar normalization. This is derived from the source `Sp(1)` formula,
the actual standard representation, and the computed solder square. -/
theorem lineCurvature_cancel
    (hsource : KSWSp1CurvatureFormula S Q D)
    (t : ℝ) (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (ht : t ^ 2 = scalarRatio S Q D p y hy) :
    scalarLineLie S (fixedTangentConjugation S Q p (D.curvature Q p y u v)) +
      t ^ 2 • lowerSquare S (fixedSolder S Q p y u) (fixedSolder S Q p y v) = 0 := by
  apply ContinuousLinearMap.ext
  intro q
  have hline : scalarLineLie S
      (fixedTangentConjugation S Q p (D.curvature Q p y u v)) q =
      (-(2 * scalarRatio S Q D p y hy)) •
        (q * -(imaginary (kahlerCoefficients S Q p y u v))) := by
    calc
      _ = scalarLineLie S (scalarProjection S
          (fixedTangentConjugation S Q p (D.curvature Q p y u v))) q := by
          rw [scalarLineLie_scalarProjection]
      _ = _ := by rw [hsource p y u v hy, map_smul, ContinuousLinearMap.smul_apply,
        scalarLineLie_synth]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.zero_apply]
  rw [lowerSquare_apply, lowerSquare_one_coordinates]
  rw [hline, ht]
  simp only [smul_neg, mul_neg, mul_smul_comm]
  let k := q * imaginary (kahlerCoefficients S Q p y u v)
  change -(-(2 * scalarRatio S Q D p y hy) • k) +
    scalarRatio S Q D p y hy • ((-2 : ℝ) • k) = 0
  module

theorem correctedCurvature_line_zero
    (hsource : KSWSp1CurvatureFormula S Q D)
    (t : ℝ) (p : M) (y u v : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (ht : t ^ 2 = scalarRatio S Q D p y hy)
    (z : StandardSpace (E := E)) :
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ)
      (LocalConnection.curvature (correctedConnection S Q D t p) y u v z)).snd = 0 := by
  rw [correctedCurvature_blocks S Q D t p y u v hy z]
  have h := congrArg (fun L : ℍ →L[ℝ] ℍ => L z.snd)
    (lineCurvature_cancel S Q D hsource t p y u v hy ht)
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.zero_apply] using h

end
end QuaternionicSymmetry.ManifoldQuaternionicKSWScalarInput
