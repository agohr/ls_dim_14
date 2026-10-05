import QuaternionicSymmetry.QuaternionicProjectiveStandardLie
import QuaternionicSymmetry.QuaternionicManifoldFixedNormalizer
import QuaternionicSymmetry.ManifoldQuaternionicConnectionSplitting

/-! The local standard connection form obtained from the actual compatible
tangent connection.  Each adapted chart is first identified with one fixed
quaternionic model, then the infinitesimal `Sp(n)·Sp(1)` representation acts
on the Hilbert standard space.  Gauge descent is a separate theorem. -/

namespace QuaternionicSymmetry.QuaternionicManifoldProjectiveStandardConnection

open QuaternionicProjectiveStandardL2 QuaternionicProjectiveStandardLie
  QuaternionicManifoldFixedNormalizer ManifoldQuaternionicConnection
  ManifoldQuaternionicConnectionSplitting QuaternionicIsometryNormalizer
  QuaternionicLieAlgebraProjection VectorBundleFrameTransitions
open scoped ContDiff Manifold Quaternion
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def fixedTangentConjugation (p : M) :
    (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  let e : E ≃L[ℝ] E :=
    (modelGauge S (Q.reduction.Q (achart E p))).symm.toContinuousLinearEquiv
  (e.conjContinuousAlgEquiv).toContinuousLinearEquiv.toContinuousLinearMap

/-- Infinitesimal standard action in one adapted chart.  The E block is
the proven quaternion-linear part of the actual tangent connection,
transported to the fixed model. -/
def chartLie (p : M) : (E →L[ℝ] E) →L[ℝ]
    (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) :=
  let c := WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ
  let g := modelGauge S (Q.reduction.Q (achart E p))
  let T := Q.reduction.Q (achart E p)
  let L : (E →L[ℝ] E) →ₗ[ℝ]
      (StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) := {
    toFun A := c.symm.toContinuousLinearMap.comp
      (((conjugation g.symm (symplecticProjection T A)).prodMap
        (scalarLineLie S (fixedTangentConjugation S Q p A))).comp
          c.toContinuousLinearMap)
    map_add' := by
      intro A B
      ext z
      apply c.injective
      apply Prod.ext <;> simp [map_add]
    map_smul' := by
      intro r A
      ext z
      apply c.injective
      apply Prod.ext <;> simp [map_smul]
  }
  L.toContinuousLinearMap

theorem chartLie_blocks (p : M) (A : E →L[ℝ] E)
    (z : StandardSpace (E := E)) :
    (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ) (chartLie S Q p A z) =
      ((conjugation
          (modelGauge S (Q.reduction.Q (achart E p))).symm
          (symplecticProjection (Q.reduction.Q (achart E p)) A))
        ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ) z).1,
       (scalarLineLie S (fixedTangentConjugation S Q p A))
        ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ) z).2) := rfl

theorem chartLie_commutes_I (p : M) (A : E →L[ℝ] E)
    (hI : ∀ v, symplecticProjection (Q.reduction.Q (achart E p)) A
        ((Q.reduction.Q (achart E p)).I v) =
      (Q.reduction.Q (achart E p)).I
        (symplecticProjection (Q.reduction.Q (achart E p)) A v))
    (z : StandardSpace (E := E)) :
    chartLie S Q p A ((QuaternionicProjectiveStandardHilbertStructure.standardStructure S).I z) =
      (QuaternionicProjectiveStandardHilbertStructure.standardStructure S).I
        (chartLie S Q p A z) := by
  let T := Q.reduction.Q (achart E p)
  let g := modelGauge S T
  have hg (v : E) : g.symm (T.I v) = S.I (g.symm v) := by
    apply g.injective
    rw [g.apply_symm_apply, modelGauge_I, g.apply_symm_apply]
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
  apply Prod.ext
  · change g.symm ((symplecticProjection T A) (g (S.I z.fst))) =
      S.I (g.symm ((symplecticProjection T A) (g z.fst)))
    rw [modelGauge_I, hI, hg]
  · change (QuaternionicUnitQuaternionTransport.basisI * z.snd) *
      (-(imaginary (axialProjection
        (ManifoldQuaternionicAdjointConnection.adjointRepresentation S
          (fixedTangentConjugation S Q p A))))) =
      QuaternionicUnitQuaternionTransport.basisI *
        (z.snd * (-(imaginary (axialProjection
          (ManifoldQuaternionicAdjointConnection.adjointRepresentation S
            (fixedTangentConjugation S Q p A))))))
    rw [mul_assoc]

theorem chartLie_commutes_J (p : M) (A : E →L[ℝ] E)
    (hJ : ∀ v, symplecticProjection (Q.reduction.Q (achart E p)) A
        ((Q.reduction.Q (achart E p)).J v) =
      (Q.reduction.Q (achart E p)).J
        (symplecticProjection (Q.reduction.Q (achart E p)) A v))
    (z : StandardSpace (E := E)) :
    chartLie S Q p A ((QuaternionicProjectiveStandardHilbertStructure.standardStructure S).J z) =
      (QuaternionicProjectiveStandardHilbertStructure.standardStructure S).J
        (chartLie S Q p A z) := by
  let T := Q.reduction.Q (achart E p)
  let g := modelGauge S T
  have hg (v : E) : g.symm (T.J v) = S.J (g.symm v) := by
    apply g.injective
    rw [g.apply_symm_apply, modelGauge_J, g.apply_symm_apply]
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
  apply Prod.ext
  · change g.symm ((symplecticProjection T A) (g (S.J z.fst))) =
      S.J (g.symm ((symplecticProjection T A) (g z.fst)))
    rw [modelGauge_J, hJ, hg]
  · change (QuaternionicUnitQuaternionTransport.basisJ * z.snd) *
      (-(imaginary (axialProjection
        (ManifoldQuaternionicAdjointConnection.adjointRepresentation S
          (fixedTangentConjugation S Q p A))))) =
      QuaternionicUnitQuaternionTransport.basisJ *
        (z.snd * (-(imaginary (axialProjection
          (ManifoldQuaternionicAdjointConnection.adjointRepresentation S
            (fixedTangentConjugation S Q p A))))))
    rw [mul_assoc]

def standardConnection (p : M) :
    LocalConnection.Form (E := E)
      (A := StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)) :=
  fun y => (chartLie S Q p).comp (D.form p y)

theorem standardConnection_apply (p : M) (y u : E) :
    standardConnection S Q D p y u =
      chartLie S Q p (D.form p y u) := rfl

theorem standardConnection_commutes_I (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (z : StandardSpace (E := E)) :
    standardConnection S Q D p y u
        ((QuaternionicProjectiveStandardHilbertStructure.standardStructure S).I z) =
      (QuaternionicProjectiveStandardHilbertStructure.standardStructure S).I
        (standardConnection S Q D p y u z) := by
  rw [standardConnection_apply]
  apply chartLie_commutes_I S Q p (D.form p y u)
  intro v
  have hc := symplecticConnection_commutes Q D p y u hy
    (Pi.basisFun ℝ (Fin 3) 0)
  have hv := congrArg (fun F : E →L[ℝ] E => F v) hc
  simpa only [symplecticConnection_apply,
    ManifoldQuaternionicRankThreeOrthogonal.synth_basis,
    quaternionicGenerator] using hv


end
end QuaternionicSymmetry.QuaternionicManifoldProjectiveStandardConnection
