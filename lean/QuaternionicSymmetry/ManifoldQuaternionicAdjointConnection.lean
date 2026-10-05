import QuaternionicSymmetry.ManifoldQuaternionicConnection

/-! The infinitesimal adjoint representation of an actual compatible tangent
connection on the local quaternionic rank-three fibers. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection

open ManifoldQuaternionicConnection VectorBundleFrameTransitions
open scoped ContDiff

noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [I.Boundaryless] {n : WithTop ℕ∞} [IsManifold I (n + 1) M]

abbrev EndE := E →L[ℝ] E
abbrev R3 := Fin 3 → ℝ
abbrev EndR3 := R3 →L[ℝ] R3

/-- The continuous commutator map in the tangent model. -/
def commutatorMap : EndE (E := E) →L[ℝ]
    (EndE (E := E) →L[ℝ] EndE (E := E)) :=
  (ContinuousLinearMap.compL ℝ E E E) -
    (ContinuousLinearMap.compL ℝ E E E).flip

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem commutatorMap_apply (Γ T : EndE (E := E)) :
    commutatorMap Γ T = Γ.comp T - T.comp Γ := by
  rfl

/-- The rank-three infinitesimal adjoint representation, using local
quaternionic synthesis and coordinates. It is bounded and linear in Γ. -/
def adjointRepresentation (S : QuaternionicStructure E) :
    EndE (E := E) →L[ℝ] EndR3 :=
  ((ContinuousLinearMap.compL ℝ (R3) (EndE (E := E)) R3)
    (QuaternionicFrameReduction.coeff S)).comp
    (((ContinuousLinearMap.compL ℝ R3 (EndE (E := E)) (EndE (E := E))).flip
      (QuaternionicFrameReduction.synth S)).comp commutatorMap)

theorem adjointRepresentation_apply (S : QuaternionicStructure E)
    (Γ : EndE (E := E)) (a : R3) :
    adjointRepresentation S Γ a =
      QuaternionicFrameReduction.coeff S
        (Γ.comp (QuaternionicFrameReduction.synth S a) -
          (QuaternionicFrameReduction.synth S a).comp Γ) := by
  rfl

/-- Infinitesimal preservation of the quaternionic three-plane. -/
def PreservesSpan (S : QuaternionicStructure E) (Γ : EndE (E := E)) : Prop :=
  ∀ T ∈ quaternionicSpan S, commutatorMap Γ T ∈ quaternionicSpan S

omit [Nontrivial E] [FiniteDimensional ℝ E] in
theorem preservesSpan_of_generators (S : QuaternionicStructure E)
    (Γ : EndE (E := E))
    (hgen : ∀ t : Fin 3,
      commutatorMap Γ (quaternionicGenerator S t) ∈ quaternionicSpan S) :
    PreservesSpan S Γ := by
  intro T hT
  have hle : quaternionicSpan S ≤
      (quaternionicSpan S).comap (commutatorMap Γ).toLinearMap := by
    change Submodule.span ℝ (Set.range (quaternionicGenerator S)) ≤ _
    apply Submodule.span_le.mpr
    rintro U ⟨t, rfl⟩
    exact hgen t
  exact hle hT

variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := I) (M := M) (n := n))
variable (D : CompatibleTangentConnection Q)

/-- The connection form induced on the local rank-three quaternionic fiber
by the actual compatible tangent connection. -/
def inducedForm (p : M) : LocalConnection.Form (E := E) (A := EndR3) :=
  fun y => (ContinuousLinearMap.compL ℝ E (EndE (E := E)) EndR3
    (adjointRepresentation (Q.reduction.Q (achart H p)))) (D.form p y)

omit [I.Boundaryless] in
theorem inducedForm_apply (p : M) (y u : E) (a : R3) :
    inducedForm Q D p y u a =
      QuaternionicFrameReduction.coeff (Q.reduction.Q (achart H p))
        ((D.form p y u).comp
            (QuaternionicFrameReduction.synth (Q.reduction.Q (achart H p)) a) -
          (QuaternionicFrameReduction.synth (Q.reduction.Q (achart H p)) a).comp
            (D.form p y u)) := by
  rfl

omit [Nontrivial E] [FiniteDimensional ℝ E] [I.Boundaryless] in
theorem tangentForm_preservesSpan (p : M) (y u : E)
    (hy : y ∈ (extChartAt I p).target) :
    PreservesSpan (Q.reduction.Q (achart H p)) (D.form p y u) := by
  apply preservesSpan_of_generators
  intro t
  rw [commutatorMap_apply]
  exact D.quaternionic p y u t hy

omit [I.Boundaryless] in
/-- In every adapted chart, the induced connection is exactly the
restriction of the tangent commutator to the quaternionic three-plane. -/
theorem synth_inducedForm (p : M) (y u : E)
    (hy : y ∈ (extChartAt I p).target) (a : R3) :
    QuaternionicFrameReduction.synth (Q.reduction.Q (achart H p))
      (inducedForm Q D p y u a) =
      (D.form p y u).comp
          (QuaternionicFrameReduction.synth (Q.reduction.Q (achart H p)) a) -
        (QuaternionicFrameReduction.synth (Q.reduction.Q (achart H p)) a).comp
          (D.form p y u) := by
  rw [inducedForm_apply]
  apply QuaternionicFrameReduction.synth_coeff_of_mem
  exact tangentForm_preservesSpan Q D p y u hy _
    (QuaternionicFrameReduction.synth_mem _ a)

omit [I.Boundaryless] in
theorem inducedForm_smooth (p : M) :
    ContDiffOn ℝ ∞ (inducedForm Q D p) (extChartAt I p).target := by
  exact (ContinuousLinearMap.contDiff _).comp_contDiffOn (D.smooth_form p)

/-- Curvature of the induced local rank-three connection, computed from
actual Fréchet derivatives of its form. -/
def inducedCurvature (p : M) (y : E) :
    LocalConnection.Bilinear (E := E) (A := EndR3) :=
  LocalConnection.curvature (inducedForm Q D p) y

omit [I.Boundaryless] in
theorem inducedCurvature_antisymm (p : M) (y u v : E) :
    inducedCurvature Q D p y u v = -inducedCurvature Q D p y v u :=
  LocalConnection.curvature_antisymm (inducedForm Q D p) y u v

omit [I.Boundaryless] in
theorem inducedCurvature_self (p : M) (y u : E) :
    inducedCurvature Q D p y u u = 0 :=
  LocalConnection.curvature_self (inducedForm Q D p) y u

end
end QuaternionicSymmetry.ManifoldQuaternionicAdjointConnection
