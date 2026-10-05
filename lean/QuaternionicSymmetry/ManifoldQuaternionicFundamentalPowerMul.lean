import QuaternionicSymmetry.ManifoldQuaternionicFundamentalNonvanishing

namespace QuaternionicSymmetry.ManifoldQuaternionicFundamentalNonvanishing
open ManifoldDifferentialForms ManifoldDeRhamWedge ManifoldDeRhamRing
  ManifoldDeRhamAllDegrees ManifoldDeRhamAllDegreeClasses
  ManifoldQuaternionicMetric ManifoldQuaternionicConnection
  ManifoldQuaternionicFourFormGluing ManifoldQuaternionicVolume
  ManifoldQuaternionicFundamentalClass ManifoldFormPowers
open scoped Manifold ContDiff Topology
noncomputable section
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 500000
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [Nonempty M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M]
  [BorelSpace M] [CompactSpace M] [T2Space M] [Nonempty M] in
private theorem closedFundamentalPower_succ (k : ℕ) :
    closedFundamentalPower Q D (k + 1) =
      castClosedDegree (Nat.mul_succ 4 k).symm
        (closedWedgeAll (closedFundamentalPower Q D k)
          (closedFundamental Q D)) := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
  [BorelSpace E] [Nonempty M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [T2Space M] in
private theorem castClosedDegree_comp {a b c : ℕ} (h₁ : a = b) (h₂ : b = c)
    (α : closedForms (E := E) (M₀ := M) a) :
    castClosedDegree h₂ (castClosedDegree h₁ α) =
      castClosedDegree (h₁.trans h₂) α := by
  cases h₁
  cases h₂
  rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
  [BorelSpace E] [Nonempty M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [T2Space M] in
private theorem closedWedgeAll_cast_left {p p' q : ℕ} (h : p = p')
    (α : closedForms (E := E) (M₀ := M) p)
    (β : closedForms (E := E) (M₀ := M) q) :
    closedWedgeAll (castClosedDegree h α) β =
      castClosedDegree (congrArg (· + q) h) (closedWedgeAll α β) := by
  cases h
  rfl

def positivePower (k : ℕ) (hk : 0 < k) :
    closedForms (E := E) (M₀ := M) ((4 * k - 1) + 1) :=
  castClosedDegree (by omega : 4 * k = (4 * k - 1) + 1)
    (closedFundamentalPower Q D k)

omit [MeasurableSpace E] [BorelSpace E] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M] in
private theorem positivePower_succ_all (k : ℕ) (hk : 0 < k) :
    positivePower Q D (k + 1) (Nat.succ_pos k) =
      castClosedDegree
        (by omega : ((4 * k - 1) + 1) + 4 =
          (4 * (k + 1) - 1) + 1)
        (closedWedgeAll (positivePower Q D k hk)
          (closedFundamental Q D)) := by
  unfold positivePower
  rw [closedFundamentalPower_succ, castClosedDegree_comp]
  rw [closedWedgeAll_cast_left]
  rw [castClosedDegree_comp]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
  [BorelSpace E] [Nonempty M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [T2Space M] in
private theorem closedWedgeAll_to_closedWedge (k l : ℕ)
    (α : closedForms (E := E) (M₀ := M) (k + 1))
    (β : closedForms (E := E) (M₀ := M) (l + 1)) :
    castClosedDegree
      (by omega : (k + 1) + (l + 1) = (k + l + 1) + 1)
      (closedWedgeAll α β) = closedWedge k l α β := by
  apply Subtype.ext
  apply Subtype.ext
  rw [castClosedDegree_form]
  change castForm _ (formWedge α.val.val β.val.val) =
    castForm _ (formWedge α.val.val β.val.val)
  rfl

def positivePowerClass (k : ℕ) (hk : 0 < k) :
    positiveDegreeCohomology (E := E) (M₀ := M) (4 * k - 1) :=
  closedFormClass (4 * k - 1) (positivePower Q D k hk)

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
  [BorelSpace E] [Nonempty M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [T2Space M] in
theorem castClass_zero {a b : ℕ} (h : a = b) :
    castClass (E := E) (M := M) h 0 = 0 := by
  cases h
  rfl

omit [MeasurableSpace E] [BorelSpace E] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M] in
theorem positivePowerClass_succ (k : ℕ) (hk : 0 < k) :
    positivePowerClass Q D (k + 1) (Nat.succ_pos k) =
      castClass (by omega : (4 * k - 1) + 3 + 1 = 4 * (k + 1) - 1)
        (cohomologyWedge (4 * k - 1) 3
          (positivePowerClass Q D k hk) (fundamentalClass Q D)) := by
  let a := 4 * k - 1
  let b := 4 * (k + 1) - 1
  have hab : a + 3 + 1 = b := by omega
  have hrep : positivePower Q D (k + 1) (Nat.succ_pos k) =
      castClosed hab (closedWedge a 3
        (positivePower Q D k hk) (closedFundamental Q D)) := by
    rw [positivePower_succ_all]
    rw [← closedWedgeAll_to_closedWedge a 3
      (positivePower Q D k hk) (closedFundamental Q D)]
    apply Subtype.ext
    apply Subtype.ext
    rw [castClosedDegree_form, castClosed_form, castClosedDegree_form, castForm_comp]
  change closedFormClass b (positivePower Q D (k + 1) (Nat.succ_pos k)) =
    castClass hab (cohomologyWedge a 3
      (closedFormClass a (positivePower Q D k hk))
      (closedFormClass 3 (closedFundamental Q D)))
  rw [hrep]
  change QuotientAddGroup.mk (castClosed hab
      (closedWedge a 3 (positivePower Q D k hk) (closedFundamental Q D))) =
    castClass hab (cohomologyWedge a 3
      (QuotientAddGroup.mk (positivePower Q D k hk))
      (QuotientAddGroup.mk (closedFundamental Q D)))
  rw [cohomologyWedge_mk, castClass_mk]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
  [BorelSpace E] [Nonempty M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [T2Space M] in
private theorem classOfDegree_positive_cast (p : ℕ) (hp : 0 < p)
    (α : closedForms (E := E) (M₀ := M) p) :
    castDegree (by omega : p = (p - 1) + 1) (classOfDegree p α) =
      closedFormClass (p - 1)
        (castClosedDegree (by omega : p = (p - 1) + 1) α) := by
  cases p with
  | zero => omega
  | succ n =>
      simp only [Nat.succ_sub_one]
      rfl

omit [MeasurableSpace E] [BorelSpace E] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M] in
/-- The degree-indexed fundamental class is precisely the positive-degree
class used in the recurrence, after the canonical degree equality. -/
theorem fundamentalPowerClass_eq_positivePowerClass (k : ℕ) (hk : 0 < k) :
    castDegree (by omega : 4 * k = (4 * k - 1) + 1)
      (fundamentalPowerClass Q D k) = positivePowerClass Q D k hk := by
  unfold fundamentalPowerClass positivePowerClass positivePower
  exact classOfDegree_positive_cast (4 * k) (by omega) (closedFundamentalPower Q D k)

omit [MeasurableSpace E] [BorelSpace E] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [T2Space M] in
/-- The original degree-indexed classes multiply by the fundamental
degree-four class, with all degree transports explicit. -/
theorem fundamentalPowerClass_succ_positive (k : ℕ) (hk : 0 < k) :
    castDegree (by omega : 4 * (k + 1) = (4 * (k + 1) - 1) + 1)
      (fundamentalPowerClass Q D (k + 1)) =
    castClass (by omega : (4 * k - 1) + 3 + 1 = 4 * (k + 1) - 1)
      (cohomologyWedge (4 * k - 1) 3
        (castDegree (by omega : 4 * k = (4 * k - 1) + 1)
          (fundamentalPowerClass Q D k)) (fundamentalClass Q D)) := by
  rw [fundamentalPowerClass_eq_positivePowerClass Q D (k + 1) (Nat.succ_pos k),
    fundamentalPowerClass_eq_positivePowerClass Q D k hk]
  exact positivePowerClass_succ Q D k hk

end
end QuaternionicSymmetry.ManifoldQuaternionicFundamentalNonvanishing
