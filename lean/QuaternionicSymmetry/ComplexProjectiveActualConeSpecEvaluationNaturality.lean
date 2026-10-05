import QuaternionicSymmetry.ComplexProjectiveActualConeClassicalCarrierChart

/-! The action of an affine Scheme morphism on a complex evaluation point is
the kernel of the composed ring homomorphism. This is used for literal
scheme-point specialization, not as a substitute for regularity. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeSpecEvaluationNaturality

open AlgebraicGeometry
noncomputable section

universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def specEvaluationPoint (ev : S →+* ℂ) : Spec (CommRingCat.of S) :=
  ⟨RingHom.ker ev, RingHom.ker_isPrime ev⟩

theorem specMap_specEvaluationPoint (f : R →+* S) (ev : S →+* ℂ) :
    Spec.map (CommRingCat.ofHom f) (specEvaluationPoint ev) =
      (specEvaluationPoint (ev.comp f) : Spec (CommRingCat.of R)) := by
  apply PrimeSpectrum.ext
  ext a
  rfl

end
end QuaternionicSymmetry.ComplexProjectiveActualConeSpecEvaluationNaturality
