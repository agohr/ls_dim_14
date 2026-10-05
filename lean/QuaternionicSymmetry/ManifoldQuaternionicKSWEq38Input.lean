import QuaternionicSymmetry.ManifoldQuaternionicKSWScalarInput
import QuaternionicSymmetry.QuaternionicKSWUpperModel

/-!
A real-model registration of KSW Eq. (3.8), arXiv:dg-ga/9709014v1.
The paper writes `R = -κ/(8n(n+2)) (R_H + R_E) + R_hyper`, where
`R_hyper` is the quaternionic Weyl term represented by a section of
`Sym⁴ E*`. The two model tensors below use actual fixed-frame solder
coordinates. `R_E` is one half of the four-wedge sum; the factor follows
from evaluating the source's wedge-valued form on two tangent vectors.

The source theorem is a named premise. Its conclusion is a decomposition of
the original tangent curvature, not a corrected-connection identity. The
upper corrected curvature comparison is proved below from this premise,
the independently computed solder square, and the Sp(1) source formula.
-/
namespace QuaternionicSymmetry.ManifoldQuaternionicKSWEq38Input
open ManifoldQuaternionicConnection
open ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicKSWScalarInput
open QuaternionicKSWUpperModel
open QuaternionicStandardSolderSquare
open QuaternionicLieAlgebraProjection
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open QuaternionicManifoldProjectiveStandardConnection
open QuaternionicManifoldFixedSolder
open QuaternionicManifoldFixedNormalizer
open QuaternionicManifoldCorrectedConnection
open QuaternionicProjectiveStandardL2
open scoped Manifold ContDiff Topology Quaternion
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

/-- The actual chart tangent to fixed quaternionic model identification. -/
def fixedSolderEquiv (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) : E ≃L[ℝ] E :=
  (solderEquiv Q p y hy).trans
    (modelGauge S (Q.reduction.Q (achart E p))).symm.toContinuousLinearEquiv

omit [Nontrivial E] in
theorem fixedSolderEquiv_apply (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) (u : E) :
    fixedSolderEquiv S Q p y hy u = fixedSolder S Q p y u := rfl

/-- The `R_H` action in the fixed real quaternionic model. -/
def sourceRH (p : M) (y u v : E) : E →L[ℝ] E :=
  synth S (kahlerCoefficients S Q p y u v)

/-- The source's real quaternionic Weyl type at a single tangent fiber.
Only properties needed downstream are recorded; no such tensor is assumed
as part of the PQK geometry. -/
def HyperWeylFiber (W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E)) : Prop :=
  (∀ u v, W u v = -W v u) ∧
  (∀ u v w z, inner ℝ (W u v w) z = -inner ℝ w (W u v z)) ∧
  (∀ u v, W u v * S.I.toContinuousLinearMap = S.I.toContinuousLinearMap * W u v) ∧
  (∀ u v, W u v * S.J.toContinuousLinearMap = S.J.toContinuousLinearMap * W u v) ∧
  (∀ u v w z, inner ℝ (W u v w) z = inner ℝ (W w z u) v) ∧
  (∀ v w, (∑ a : Fin (Module.finrank ℝ E),
    inner ℝ (W (stdOrthonormalBasis ℝ E a) v w)
      (stdOrthonormalBasis ℝ E a)) = 0)

omit [Nontrivial E] in
theorem HyperWeylFiber.mem_skewCentralizer
    {W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E)}
    (hW : HyperWeylFiber S W) (u v : E) :
    (W u v).toLinearMap ∈ S.skewCentralizer := by
  rcases hW with ⟨_, hsk, hI, hJ, _, _⟩
  apply (S.mem_skewCentralizer_iff _).mpr
  refine ⟨hsk u v, ?_, ?_⟩
  · intro w
    have h := congrArg (fun A : E →L[ℝ] E => A w) (hI u v)
    simpa only [ContinuousLinearMap.mul_apply] using h
  · intro w
    have h := congrArg (fun A : E →L[ℝ] E => A w) (hJ u v)
    simpa only [ContinuousLinearMap.mul_apply] using h

/-- Literal Eq. (3.8) as a source premise in the actual local tangent model.
The source's `κ` is our computed scalar contraction and the dimension is
the quaternionic dimension of the fixed model. -/
def KSWEq38Decomposition : Prop :=
  ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
    ∃ W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E),
      HyperWeylFiber S W ∧
      ∀ u v : E,
        fixedTangentConjugation S Q p (D.curvature Q p y u v) =
          (-(2 * scalarRatio S Q D p y hy)) •
            (sourceRH S Q p y u v +
              sourceREOperator S (fixedSolder S Q p y u)
                (fixedSolder S Q p y v)) +
          W (fixedSolder S Q p y u) (fixedSolder S Q p y v)

/-- The explicitly quantified literature premise, with the positive scalar
and dimension hypotheses of the source. This is not a Lean proof of KSW. -/
def KSWEq38OnModel : Prop :=
  ∀ (S : QuaternionicStructure E)
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (G : PositiveScalarTangentGeometry Q),
    2 ≤ S.quaternionicDimension →
    KSWEq38Decomposition S Q G.connection

theorem decomposition_of_KSWEq38OnModel
    (hsource : KSWEq38OnModel (E := E) (M := M))
    (G : PositiveScalarTangentGeometry Q)
    (hn : 2 ≤ S.quaternionicDimension) :
    KSWEq38Decomposition S Q G.connection :=
  hsource S Q G hn

/-- Eq. (3.8) and Lemma 3.10 together identify the corrected upper block
with the source's hyperkähler/Weyl curvature term. The equality here is
derived after matching `R_E` to the genuine solder square. -/
theorem correctedUpper_eq_hyper
    (hsp : KSWSp1CurvatureFormula S Q D)
    (hdecomp : KSWEq38Decomposition S Q D)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    ∃ W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E),
      HyperWeylFiber S W ∧
      ∀ u v : E,
        symplecticProjection S
          (fixedTangentConjugation S Q p (D.curvature Q p y u v)) +
          scalarRatio S Q D p y hy •
            upperSquare S (fixedSolder S Q p y u) (fixedSolder S Q p y v) =
          W (fixedSolder S Q p y u) (fixedSolder S Q p y v) := by
  obtain ⟨W, hW, hR⟩ := hdecomp p y hy
  refine ⟨W, hW, ?_⟩
  intro u v
  have hs := hsp p y u v hy
  have hr := hR u v
  have hsplit := projection_sum S
    (fixedTangentConjugation S Q p (D.curvature Q p y u v))
  rw [hs] at hsplit
  rw [← hsplit] at hr
  simp only [sourceRH, sourceREOperator] at hr
  let F := symplecticProjection S
    (fixedTangentConjugation S Q p (D.curvature Q p y u v))
  let H := synth S (kahlerCoefficients S Q p y u v)
  let T := upperSquare S (fixedSolder S Q p y u)
    (fixedSolder S Q p y v)
  let U := W (fixedSolder S Q p y u) (fixedSolder S Q p y v)
  let l := scalarRatio S Q D p y hy
  change F + l • T = U
  change F + (-(2 * l)) • H =
    (-(2 * l)) • (H + (1 / 2 : ℝ) • T) + U at hr
  calc
    F + l • T = (F + (-(2 * l)) • H) - (-(2 * l)) • H + l • T := by module
    _ = ((-(2 * l)) • (H + (1 / 2 : ℝ) • T) + U) -
        (-(2 * l)) • H + l • T := by rw [hr]
    _ = U := by module

/-- At the KSW scalar normalization, the actual corrected standard
curvature has the hyperkähler/Weyl tensor in its tangent block and zero in
the quaternionic line block. Both statements are consequences of the two
explicit source inputs and the constructed standard connection. -/
theorem correctedCurvature_eq_hyper_block
    (hsp : KSWSp1CurvatureFormula S Q D)
    (hdecomp : KSWEq38Decomposition S Q D)
    (t : ℝ) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (ht : t ^ 2 = scalarRatio S Q D p y hy) :
    ∃ W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E),
      HyperWeylFiber S W ∧
      ∀ (u v : E) (z : StandardSpace (E := E)),
        (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ)
          (LocalConnection.curvature (correctedConnection S Q D t p) y u v z) =
            (W (fixedSolder S Q p y u) (fixedSolder S Q p y v) z.fst, 0) := by
  obtain ⟨W, hW, hupper⟩ := correctedUpper_eq_hyper S Q D hsp hdecomp p y hy
  refine ⟨W, hW, ?_⟩
  intro u v z
  rw [correctedCurvature_blocks S Q D t p y u v hy z]
  apply Prod.ext
  · have h := congrArg (fun A : E →L[ℝ] E => A z.fst) (hupper u v)
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ← ht] using h
  · have h := congrArg (fun A : ℍ →L[ℝ] ℍ => A z.snd)
      (lineCurvature_cancel S Q D hsp t p y u v hy ht)
    simpa only [Prod.snd, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply] using h

/-- The same comparison with both curvature inputs expressed in the fixed
orthonormal quaternionic model. This is the coordinate tensor consumed by
finite coefficient expansion. -/
theorem correctedCurvature_eq_hyper_fixed
    (hsp : KSWSp1CurvatureFormula S Q D)
    (hdecomp : KSWEq38Decomposition S Q D)
    (t : ℝ) (p : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (ht : t ^ 2 = scalarRatio S Q D p y hy) :
    ∃ W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E),
      HyperWeylFiber S W ∧
      ∀ (a b : E) (z : StandardSpace (E := E)),
        (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ)
          (LocalConnection.curvature (correctedConnection S Q D t p) y
            ((fixedSolderEquiv S Q p y hy).symm a)
            ((fixedSolderEquiv S Q p y hy).symm b) z) =
          (W a b z.fst, 0) := by
  obtain ⟨W, hW, hblock⟩ :=
    correctedCurvature_eq_hyper_block S Q D hsp hdecomp t p y hy ht
  refine ⟨W, hW, ?_⟩
  intro a b z
  have h := hblock ((fixedSolderEquiv S Q p y hy).symm a)
    ((fixedSolderEquiv S Q p y hy).symm b) z
  rw [← fixedSolderEquiv_apply S Q p y hy,
    ← fixedSolderEquiv_apply S Q p y hy,
    (fixedSolderEquiv S Q p y hy).apply_symm_apply,
    (fixedSolderEquiv S Q p y hy).apply_symm_apply] at h
  exact h

end
end QuaternionicSymmetry.ManifoldQuaternionicKSWEq38Input
