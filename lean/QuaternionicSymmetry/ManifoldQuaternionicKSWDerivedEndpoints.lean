import QuaternionicSymmetry.ManifoldQuaternionicKSWScalarConstancyDerived
import QuaternionicSymmetry.ManifoldQuaternionicKSWFundamentalClass

/-! Source-relative KSW endpoints with scalar constancy derived by Schur.
The only registered literature inputs are Lemma 3.10 and Eq. (3.8). -/
namespace QuaternionicSymmetry.ManifoldQuaternionicKSWDerivedEndpoints
open ManifoldQuaternionicConnection
open ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicKSWScalarInput
open ManifoldQuaternionicKSWEq38Input
open ManifoldQuaternionicKSWScalarConstancyDerived
open ManifoldQuaternionicKSWFundamentalClass
open ManifoldQuaternionicAdjointChernWeil
open ManifoldQuaternionicFourFormGluing
open ManifoldQuaternionicFundamentalClass
open scoped Manifold ContDiff Topology Quaternion
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem exists_global_hyper_curvature_parameter_of_eq38
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
  let hdecomp := decomposition_of_KSWEq38OnModel S Q heq38 G hn
  obtain ⟨t, htpos, ht⟩ :=
    exists_global_parameter_of_eq38 S Q G hdecomp hn hconn
  refine ⟨t, htpos, ?_⟩
  intro p y hy
  exact correctedCurvature_eq_hyper_fixed S Q G.connection
    (formula_of_KSWLemma310OnModel S Q hsp G hn)
    hdecomp t p y hy (ht p y hy)

theorem exists_positive_fundamental_multiple_of_eq38
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (G : PositiveScalarTangentGeometry Q)
    (hn : 2 ≤ S.quaternionicDimension)
    (hconn : IsPreconnected (Set.univ : Set M)) :
    ∃ t : ℝ, 0 < t ∧ 0 < t ^ 4 / Real.pi ^ 2 ∧
      quarterPontryaginCandidateForm Q G.connection =
        (t ^ 4 / Real.pi ^ 2) • closedFundamental Q G.connection := by
  let hdecomp := decomposition_of_KSWEq38OnModel S Q heq38 G hn
  obtain ⟨t, htpos, ht⟩ :=
    exists_global_parameter_of_eq38 S Q G hdecomp hn hconn
  refine ⟨t, htpos, div_pos (pow_pos htpos 4) (sq_pos_of_pos Real.pi_pos), ?_⟩
  have h := quarterForm_eq_fundamental S Q G.connection
    (formula_of_KSWLemma310OnModel S Q hsp G hn) (t ^ 2)
      (fun p y hy => (ht p y hy).symm)
  have ht4 : (t ^ 2) ^ 2 = t ^ 4 := by ring
  simpa only [ht4] using h

theorem exists_common_hyper_and_fundamental_parameter
    (hsp : KSWLemma310OnModel (E := E) (M := M))
    (heq38 : KSWEq38OnModel (E := E) (M := M))
    (G : PositiveScalarTangentGeometry Q)
    (hn : 2 ≤ S.quaternionicDimension)
    (hconn : IsPreconnected (Set.univ : Set M)) :
    ∃ t : ℝ, 0 < t ∧
      quarterPontryaginCandidateForm Q G.connection =
        (t ^ 4 / Real.pi ^ 2) • closedFundamental Q G.connection ∧
      (∀ (p : M) (y : E)
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
              (W a b z.fst, 0)) := by
  let hdecomp := decomposition_of_KSWEq38OnModel S Q heq38 G hn
  obtain ⟨t, htpos, ht⟩ :=
    exists_global_parameter_of_eq38 S Q G hdecomp hn hconn
  have hform := quarterForm_eq_fundamental S Q G.connection
    (formula_of_KSWLemma310OnModel S Q hsp G hn) (t ^ 2)
      (fun p y hy => (ht p y hy).symm)
  have ht4 : (t ^ 2) ^ 2 = t ^ 4 := by ring
  refine ⟨t, htpos, by simpa only [ht4] using hform, ?_⟩
  intro p y hy
  exact correctedCurvature_eq_hyper_fixed S Q G.connection
    (formula_of_KSWLemma310OnModel S Q hsp G hn)
    hdecomp t p y hy (ht p y hy)

end
end QuaternionicSymmetry.ManifoldQuaternionicKSWDerivedEndpoints
