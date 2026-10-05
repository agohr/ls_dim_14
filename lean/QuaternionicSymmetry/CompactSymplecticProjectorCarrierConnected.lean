import QuaternionicSymmetry.CompactSymplecticProjectorColumnHouseholderOrbit

/-! The actual compact-symplectic projector quotient is connected. The proof
uses the fully explicit unit-sphere parametrization, quaternionic phase
normalization, a genuine Sp Householder reflection, and the checked orbit
homeomorphism. No connectedness or model-orbit premise is supplied. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorCarrierConnected

open CompactSymplecticProjectorFirstColumn
open CompactSymplecticProjectorColumnSphereMap
open CompactSymplecticProjectorColumnSphereConnected
open CompactSymplecticProjectorColumnRealGauge
open CompactSymplecticProjectorColumnHouseholderOrbit
open CompactSymplecticProjectorOrbitQuotient
open CompactSymplecticProjectiveQuotient
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev V (n : ℕ) := EuclideanSpace ℂ (I n)

theorem sphereColumnProjector_mem_orbit (n : ℕ)
    (v : Metric.sphere (0 : V n) 1) :
    sphereColumnProjector n v ∈ projectorOrbit n := by
  obtain ⟨w, r, _hr, hfirst, hsecond, hP⟩ :=
    exists_real_first_pair_representative n v
  change columnProjector n ((EuclideanSpace.equiv (I n) ℂ) v.1) ∈ projectorOrbit n
  rw [← hP]
  exact realGauge_columnProjector_mem_orbit n w r hfirst hsecond

theorem sphereColumnProjector_range_eq_orbit (n : ℕ) :
    Set.range (sphereColumnProjector n) = projectorOrbit n := by
  apply Set.Subset.antisymm
  · rintro _ ⟨v, rfl⟩
    exact sphereColumnProjector_mem_orbit n v
  · exact projectorOrbit_subset_sphereColumnProjector_range n

def sphereToOrbit (n : ℕ) :
    Metric.sphere (0 : V n) 1 → projectorOrbit n :=
  fun v => ⟨sphereColumnProjector n v, sphereColumnProjector_mem_orbit n v⟩

theorem continuous_sphereToOrbit (n : ℕ) : Continuous (sphereToOrbit n) :=
  (continuous_sphereColumnProjector n).subtype_mk _

theorem sphereToOrbit_surjective (n : ℕ) :
    Function.Surjective (sphereToOrbit n) := by
  rintro ⟨p, hp⟩
  rw [← sphereColumnProjector_range_eq_orbit n] at hp
  obtain ⟨v, hv⟩ := hp
  exact ⟨v, Subtype.ext hv⟩

theorem projectiveCarrier_connectedSpace (n : ℕ) :
    ConnectedSpace (ProjectiveCarrier n) := by
  letI : ConnectedSpace (Metric.sphere (0 : V n) 1) :=
    Subtype.connectedSpace (unit_column_sphere_connected n)
  let f : Metric.sphere (0 : V n) 1 → ProjectiveCarrier n :=
    (carrierHomeomorphProjectorOrbit n).symm ∘ sphereToOrbit n
  have hfCont : Continuous f :=
    (carrierHomeomorphProjectorOrbit n).symm.continuous.comp
      (continuous_sphereToOrbit n)
  have hfSurj : Function.Surjective f :=
    (carrierHomeomorphProjectorOrbit n).symm.surjective.comp
      (sphereToOrbit_surjective n)
  exact hfSurj.connectedSpace hfCont

end
end QuaternionicSymmetry.CompactSymplecticProjectorCarrierConnected
