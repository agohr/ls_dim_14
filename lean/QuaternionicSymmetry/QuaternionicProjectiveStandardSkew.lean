import QuaternionicSymmetry.QuaternionicManifoldProjectiveStandardConnection

/-! Metric compatibility of the actual local standard connection. -/

namespace QuaternionicSymmetry.QuaternionicProjectiveStandardSkew

open QuaternionicProjectiveStandardLie
  QuaternionicManifoldProjectiveStandardConnection
  ManifoldQuaternionicConnectionSplitting
  QuaternionicIsometryNormalizer
  QuaternionicLieAlgebraProjection
  VectorBundleFrameTransitions
open scoped Quaternion Manifold ContDiff
noncomputable section

theorem imaginary_star (a : Fin 3 → ℝ) :
    star (imaginary a) = -(imaginary a) := by
  ext <;> simp

theorem right_imaginary_skew (a : Fin 3 → ℝ) (w z : ℍ) :
    inner ℝ (w * -(imaginary a)) z +
      inner ℝ w (z * -(imaginary a)) = 0 := by
  rw [Quaternion.inner_def, Quaternion.inner_def]
  rw [star_mul, star_neg, imaginary_star]
  simp [mul_assoc]

theorem scalarLineLie_skew {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    (S : QuaternionicStructure E) (A : E →L[ℝ] E) (w z : ℍ) :
    inner ℝ (scalarLineLie S A w) z +
      inner ℝ w (scalarLineLie S A z) = 0 := by
  change inner ℝ (w * -(imaginary (axialProjection
      (ManifoldQuaternionicAdjointConnection.adjointRepresentation S A)))) z +
    inner ℝ w (z * -(imaginary (axialProjection
      (ManifoldQuaternionicAdjointConnection.adjointRepresentation S A)))) = 0
  exact right_imaginary_skew _ w z

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

theorem chartLie_skew (p : M) (A : E →L[ℝ] E)
    (hB : ∀ v w, inner ℝ
        ((symplecticProjection (Q.reduction.Q (achart E p)) A) v) w +
      inner ℝ v
        ((symplecticProjection (Q.reduction.Q (achart E p)) A) w) = 0)
    (v w : QuaternionicProjectiveStandardL2.StandardSpace (E := E)) :
    inner ℝ (chartLie S Q p A v) w +
      inner ℝ v (chartLie S Q p A w) = 0 := by
  let T := Q.reduction.Q (achart E p)
  let g := QuaternionicManifoldFixedNormalizer.modelGauge S T
  have hE : inner ℝ (g.symm ((symplecticProjection T A) (g v.fst))) w.fst +
      inner ℝ v.fst (g.symm ((symplecticProjection T A) (g w.fst))) = 0 := by
    have h := hB (g v.fst) (g w.fst)
    have h1 : inner ℝ (g.symm ((symplecticProjection T A) (g v.fst))) w.fst =
        inner ℝ ((symplecticProjection T A) (g v.fst)) (g w.fst) := by
      calc
        _ = inner ℝ (g (g.symm ((symplecticProjection T A) (g v.fst))))
            (g w.fst) := (g.inner_map_map _ _).symm
        _ = _ := by rw [g.apply_symm_apply]
    have h2 : inner ℝ v.fst (g.symm ((symplecticProjection T A) (g w.fst))) =
        inner ℝ (g v.fst) ((symplecticProjection T A) (g w.fst)) := by
      calc
        _ = inner ℝ (g v.fst)
            (g (g.symm ((symplecticProjection T A) (g w.fst)))) :=
              (g.inner_map_map _ _).symm
        _ = _ := by rw [g.apply_symm_apply]
    rw [h1, h2]
    exact h
  have hH := scalarLineLie_skew S
    (QuaternionicManifoldProjectiveStandardConnection.fixedTangentConjugation S Q p A)
    v.snd w.snd
  change
    (inner ℝ (g.symm ((symplecticProjection T A) (g v.fst))) w.fst +
      inner ℝ
        (scalarLineLie S
          (QuaternionicManifoldProjectiveStandardConnection.fixedTangentConjugation S Q p A)
          v.snd) w.snd) +
    (inner ℝ v.fst (g.symm ((symplecticProjection T A) (g w.fst))) +
      inner ℝ v.snd
        (scalarLineLie S
          (QuaternionicManifoldProjectiveStandardConnection.fixedTangentConjugation S Q p A)
          w.snd)) = 0
  linarith

variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem standardConnection_skew (p : M) (y u : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (v w : QuaternionicProjectiveStandardL2.StandardSpace (E := E)) :
    inner ℝ (standardConnection S Q D p y u v) w +
      inner ℝ v (standardConnection S Q D p y u w) = 0 := by
  rw [standardConnection_apply]
  apply chartLie_skew S Q p (D.form p y u)
  intro a b
  exact symplecticConnection_skew Q D p y u a b hy

end
end QuaternionicSymmetry.QuaternionicProjectiveStandardSkew
