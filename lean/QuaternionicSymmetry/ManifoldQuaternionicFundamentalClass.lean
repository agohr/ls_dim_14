import QuaternionicSymmetry.ManifoldQuaternionicFourFormClosed
import QuaternionicSymmetry.ManifoldFormPowers
import QuaternionicSymmetry.ManifoldDeRhamAllDegreeClasses

/-! The actual de Rham class of the quaternionic fundamental form and its
closed repeated wedges, with closure derived from the compatible connection. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFundamentalClass

open ManifoldDifferentialForms ManifoldDeRhamWedge ManifoldDeRhamAllDegreeClasses
  ManifoldDeRhamAllDegrees ManifoldQuaternionicMetric ManifoldQuaternionicConnection
  ManifoldQuaternionicFourFormGluing ManifoldQuaternionicFourFormClosed ManifoldFormPowers
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

def closedFundamental : closedForms (E := E) (M₀ := M) 4 :=
  ⟨⟨fundamentalFourForm Q, fundamentalFourForm_smooth Q⟩, by
    apply Subtype.ext
    exact fundamentalFourForm_closed Q D⟩

def fundamentalClass : positiveDegreeCohomology (E := E) (M₀ := M) 3 :=
  closedFormClass 3 (closedFundamental Q D)

def closedFundamentalPower (k : ℕ) : closedForms (E := E) (M₀ := M) (4 * k) :=
  ⟨⟨formPower (fundamentalFourForm Q) k,
      formPower_smooth _ (fundamentalFourForm_smooth Q) k⟩, by
    apply Subtype.ext
    exact formPower_closed _ (fundamentalFourForm_smooth Q)
      (fundamentalFourForm_closed Q D) k⟩

def fundamentalPowerClass (k : ℕ) : CohomologyByDegree (E := E) (M := M) (4 * k) :=
  classOfDegree (4 * k) (closedFundamentalPower Q D k)

theorem fundamentalClass_connection_independent (D' : CompatibleTangentConnection Q) :
    fundamentalClass Q D = fundamentalClass Q D' := rfl

theorem fundamentalPowerClass_connection_independent (D' : CompatibleTangentConnection Q)
    (k : ℕ) : fundamentalPowerClass Q D k = fundamentalPowerClass Q D' k := rfl

end
end QuaternionicSymmetry.ManifoldQuaternionicFundamentalClass
