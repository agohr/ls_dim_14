import QuaternionicSymmetry.QuaternionicBilinearOperator

/-! Finite expansion of a quaternionic curvature tensor in skew
quaternion-linear operator coefficients and invariant real two-forms. -/
namespace QuaternionicSymmetry.QuaternionicCurvatureFiniteExpansion
open Module QuaternionicCurvatureCoefficientForms QuaternionicBilinearOperator
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (S : QuaternionicStructure E)
local instance : NormedSpace ℝ E := inferInstance

def operatorSpace : Submodule ℝ (E →L[ℝ] E) :=
  S.skewCentralizer.comap (ContinuousLinearMap.coeLM ℝ)

local instance : NormedSpace ℝ (operatorSpace S) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] operatorSpace S) := inferInstance

abbrev Index := Fin (Module.finrank ℝ (operatorSpace S))

def operatorBasis : Basis (Index S) ℝ (operatorSpace S) :=
  Module.finBasis ℝ (operatorSpace S)

variable (R : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
  (hR : ∀ u v, (R u v).toLinearMap ∈ S.skewCentralizer)

def restrictedCurvature : E →L[ℝ] E →L[ℝ] operatorSpace S :=
  LinearMap.toContinuousLinearMap {
    toFun u := (R u).codRestrict (operatorSpace S) (hR u)
    map_add' := by
      intro u v
      apply ContinuousLinearMap.ext
      intro w
      apply Subtype.ext
      exact congrArg (fun A : E →L[ℝ] E →L[ℝ] E => A w) (R.map_add u v)
    map_smul' := by
      intro r u
      apply ContinuousLinearMap.ext
      intro v
      apply Subtype.ext
      exact congrArg (fun A : E →L[ℝ] E →L[ℝ] E => A v) (R.map_smul r u)
  }

def coefficient (a : Index S) : E →L[ℝ] E →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ E (operatorSpace S) ℝ)
    ((operatorBasis S).coord a).toContinuousLinearMap).comp (restrictedCurvature S R hR)

theorem coefficient_apply (a : Index S) (u v : E) :
    coefficient S R hR a u v =
      (operatorBasis S).repr ⟨R u v, hR u v⟩ a := rfl

theorem expansion (u v : E) :
    ∑ a : Index S, coefficient S R hR a u v • (operatorBasis S a).val = R u v := by
  have h := (operatorBasis S).sum_repr ⟨R u v, hR u v⟩
  simpa only [Submodule.coe_sum, Submodule.coe_smul, coefficient_apply] using
    congrArg (fun A : operatorSpace S => A.val) h

theorem coefficient_antisymm (hanti : ∀ u v, R u v = -R v u)
    (a : Index S) (u v : E) : coefficient S R hR a u v = -coefficient S R hR a v u := by
  have h : restrictedCurvature S R hR u v = -restrictedCurvature S R hR v u :=
    Subtype.ext (hanti u v)
  have he := congrArg (fun A : operatorSpace S => (operatorBasis S).repr A a) h
  simpa only [map_neg, Finsupp.neg_apply] using he

theorem coefficient_invariant (J : E ≃ₗᵢ[ℝ] E)
    (hpair : ∀ u v w z, inner ℝ (R u v w) z = inner ℝ (R w z u) v)
    (hJ : ∀ u v w, R u v (J w) = J (R u v w))
    (a : Index S) (u v : E) :
    coefficient S R hR a (J u) (J v) = coefficient S R hR a u v := by
  have h : restrictedCurvature S R hR (J u) (J v) = restrictedCurvature S R hR u v :=
    Subtype.ext (invariant_of_pair_symmetry R J hpair hJ u v)
  exact congrArg (fun A : operatorSpace S => (operatorBasis S).repr A a) h

theorem coefficient_operator_mem (hanti : ∀ u v, R u v = -R v u)
    (hpair : ∀ u v w z, inner ℝ (R u v w) z = inner ℝ (R w z u) v)
    (a : Index S) :
    (operator (coefficient S R hR a)).toLinearMap ∈ S.skewCentralizer := by
  apply operator_mem_skewCentralizer
  · exact coefficient_antisymm S R hR hanti a
  · apply coefficient_invariant S R hR S.I hpair
    intro u v w
    exact ((S.mem_skewCentralizer_iff _).mp (hR u v)).2.1 w
  · apply coefficient_invariant S R hR S.J hpair
    intro u v w
    exact ((S.mem_skewCentralizer_iff _).mp (hR u v)).2.2 w

end
end QuaternionicSymmetry.QuaternionicCurvatureFiniteExpansion
