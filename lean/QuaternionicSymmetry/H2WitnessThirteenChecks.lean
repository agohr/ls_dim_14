import QuaternionicSymmetry.H2WitnessThirteen

/-! Finite data checks for the complete dimension-thirteen H2 witness.
Every coefficient and spectrum in the rational witness is represented below;
`w1_entries`–`w6_entries` identify these tables with the polynomials used
in the kernel-checked density identity. -/

namespace QuaternionicSymmetry.H2WitnessThirteenChecks

open MvPolynomial FiniteTypeCSchurSix H2WitnessThirteen
open scoped BigOperators
noncomputable section

abbrev P := FiniteTypeCSchurSix.P

def sumWeight {m : ℕ} (k : ℕ) (terms : Fin m → List ℕ × ℚ) : P :=
  ∑ i, C (terms i).2 * orbital 13 k (terms i).1

def terms1 : Fin 1 → List ℕ × ℚ := ![
  ([1], 68590932/2695)]
theorem w1_entries : w1 = sumWeight 1 terms1 := by
  simp [w1, sumWeight, terms1]

theorem terms1_positive (i : Fin 1) : 0 < (terms1 i).2 := by
  fin_cases i
  all_goals norm_num [terms1]

theorem terms1_admissible (i : Fin 1) :
    (terms1 i).1.length ≤ 13 ∧ (terms1 i).1 ≠ [] ∧
      ∃ x ∈ (terms1 i).1, 0 < x := by
  fin_cases i
  all_goals norm_num [terms1]

def terms2 : Fin 2 → List ℕ × ℚ := ![
  ([50, 1], 10708383607513441749702953/143951500000000000000000),
  ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 65602910510542820705739997/125756030400000000000000)]
theorem w2_entries : w2 = sumWeight 2 terms2 := by
  simp [w2, sumWeight, terms2, Fin.sum_univ_succ]

theorem terms2_positive (i : Fin 2) : 0 < (terms2 i).2 := by
  fin_cases i
  all_goals norm_num [terms2]

theorem terms2_admissible (i : Fin 2) :
    (terms2 i).1.length ≤ 13 ∧ (terms2 i).1 ≠ [] ∧
      ∃ x ∈ (terms2 i).1, 0 < x := by
  fin_cases i
  all_goals norm_num [terms2]
  all_goals simp

def terms3 : Fin 3 → List ℕ × ℚ := ![
  ([1, 1], 2858719709007/1832600),
  ([1, 1, 1, 1], 4333550741029/8246700),
  ([5, 5, 1, 1, 1, 1, 1, 1, 1, 1], 45675202613/16493400)]
theorem w3_entries : w3 = sumWeight 3 terms3 := by
  simp [w3, sumWeight, terms3, Fin.sum_univ_succ]
  ring

theorem terms3_positive (i : Fin 3) : 0 < (terms3 i).2 := by
  fin_cases i
  all_goals norm_num [terms3]

theorem terms3_admissible (i : Fin 3) :
    (terms3 i).1.length ≤ 13 ∧ (terms3 i).1 ≠ [] ∧
      ∃ x ∈ (terms3 i).1, 0 < x := by
  fin_cases i
  all_goals norm_num [terms3]
  all_goals simp

def terms4 : Fin 5 → List ℕ × ℚ := ![
  ([1, 1, 1], 57797612703712424962645481998175417/20385594215910000000000000000),
  ([5, 2, 2, 2], 1398103055863691053677063102212393/81542376863640000000000000000),
  ([5, 4, 4, 2], 3175237080089429103166917689513/8154237686364000000000000000),
  ([10, 10, 1, 1, 1, 1, 1, 1], 50206219320404685051859164229163/20385594215910000000000000000),
  ([10, 1, 1, 1, 1, 1, 1, 1, 1, 1], 10283164392804210004974670684643/3261695074545600000000000000)]
theorem w4_entries : w4 = sumWeight 4 terms4 := by
  simp [w4, sumWeight, terms4, Fin.sum_univ_succ]
  ring

theorem terms4_positive (i : Fin 5) : 0 < (terms4 i).2 := by
  fin_cases i
  all_goals norm_num [terms4]

theorem terms4_admissible (i : Fin 5) :
    (terms4 i).1.length ≤ 13 ∧ (terms4 i).1 ≠ [] ∧
      ∃ x ∈ (terms4 i).1, 0 < x := by
  fin_cases i
  all_goals norm_num [terms4]
  all_goals simp

def terms5 : Fin 7 → List ℕ × ℚ := ![
  ([1, 1, 1], 529969484698848557981276116/57547966484403635625),
  ([4, 1, 1, 1, 1], 397752879455833518699970273/552460478250274902000),
  ([10, 10, 1, 1, 1], 241608744776390398951066/172643899453210906875),
  ([10, 1, 1, 1, 1, 1, 1, 1, 1], 447701333087150062092017/591921940982437395000),
  ([10, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 82595807681135059652507/191826554948012118750),
  ([20, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 159679884424337004559/8719388861273278125),
  ([20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 8834087592466133875613/61384497583363878000)]
theorem w5_entries : w5 = sumWeight 5 terms5 := by
  simp [w5, sumWeight, terms5, Fin.sum_univ_succ]
  ring

theorem terms5_positive (i : Fin 7) : 0 < (terms5 i).2 := by
  fin_cases i
  all_goals norm_num [terms5]

theorem terms5_admissible (i : Fin 7) :
    (terms5 i).1.length ≤ 13 ∧ (terms5 i).1 ≠ [] ∧
      ∃ x ∈ (terms5 i).1, 0 < x := by
  fin_cases i
  all_goals norm_num [terms5]
  all_goals simp

def terms6 : Fin 11 → List ℕ × ℚ := ![
  ([10, 3], 27371957472941576136978915939311370873942497197111305918685467/737977779560740815938876408995155217630640000000000000000000),
  ([14, 5], 248645550369362999933210936446567436909753915018626160782705511/2213933338682222447816629226985465652891920000000000000000000),
  ([4, 1, 1], 41331773200888048829080288220582102586760342552174507371249731/72456000175054552837635138337706148640099200000000000000),
  ([4, 4, 4, 1, 1], 106306912853123854523001574692173108871615317889249372678997/123980266966204457077731236711186076561947520000000000000),
  ([5, 5, 5, 3, 3], 12628437095926527878653929800597422194499412566410099270471161/111582240269584011369958113040067468905752768000000000000000),
  ([7, 7, 2, 1, 1, 1], 3542745630049154836519186142180856788789684350471761236941/184494444890185203984719102248788804407660000000000000000),
  ([11, 6, 1, 1, 1, 1], 10008127111233974142475608949912417404193457100643361811185299/11069666693411112239083146134927328264459600000000000000000),
  ([12, 2, 2, 1, 1, 1], 2738418964244734630066945034757924255342335560116233481266033/2213933338682222447816629226985465652891920000000000000000),
  ([12, 3, 3, 1, 1, 1], 40829535099584609586615344166076582546648984758425570123451197/15940320038512001624279730434295352700821824000000000000000),
  ([20, 20, 20, 1, 1, 1], 186787855500731456547705433304885920491863917792483941/1073422224815623005002002049447498498371840000000000000),
  ([20, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 23343305979188311063452176259198708735207091218823038824303/3162761912403174925452327467122093789845600000000000000000)]
theorem w6_entries : w6 = sumWeight 6 terms6 := by
  simp [w6, sumWeight, terms6, Fin.sum_univ_succ]
  ring

theorem terms6_positive (i : Fin 11) : 0 < (terms6 i).2 := by
  fin_cases i
  all_goals norm_num [terms6]

theorem terms6_admissible (i : Fin 11) :
    (terms6 i).1.length ≤ 13 ∧ (terms6 i).1 ≠ [] ∧
      ∃ x ∈ (terms6 i).1, 0 < x := by
  fin_cases i
  all_goals norm_num [terms6]
  all_goals simp

/-- Every one of the 29 orbital coefficients is strictly positive. -/
 theorem all_coefficients_positive :
    (∀ i : Fin 1, 0 < (terms1 i).2) ∧
    (∀ i : Fin 2, 0 < (terms2 i).2) ∧
    (∀ i : Fin 3, 0 < (terms3 i).2) ∧
    (∀ i : Fin 5, 0 < (terms4 i).2) ∧
    (∀ i : Fin 7, 0 < (terms5 i).2) ∧
    (∀ i : Fin 11, 0 < (terms6 i).2) := by
  exact ⟨terms1_positive, terms2_positive, terms3_positive,
    terms4_positive, terms5_positive, terms6_positive⟩

/-- The spectra are nonempty lists of natural numbers, have a positive
entry, and fit in thirteen quaternionic slots. Their entries are
nonnegative by their `ℕ` type. -/
 theorem all_spectra_admissible :
    (∀ i : Fin 1, (terms1 i).1.length ≤ 13 ∧ (terms1 i).1 ≠ [] ∧ ∃ x ∈ (terms1 i).1, 0 < x) ∧
    (∀ i : Fin 2, (terms2 i).1.length ≤ 13 ∧ (terms2 i).1 ≠ [] ∧ ∃ x ∈ (terms2 i).1, 0 < x) ∧
    (∀ i : Fin 3, (terms3 i).1.length ≤ 13 ∧ (terms3 i).1 ≠ [] ∧ ∃ x ∈ (terms3 i).1, 0 < x) ∧
    (∀ i : Fin 5, (terms4 i).1.length ≤ 13 ∧ (terms4 i).1 ≠ [] ∧ ∃ x ∈ (terms4 i).1, 0 < x) ∧
    (∀ i : Fin 7, (terms5 i).1.length ≤ 13 ∧ (terms5 i).1 ≠ [] ∧ ∃ x ∈ (terms5 i).1, 0 < x) ∧
    (∀ i : Fin 11, (terms6 i).1.length ≤ 13 ∧ (terms6 i).1 ≠ [] ∧ ∃ x ∈ (terms6 i).1, 0 < x) := by
  exact ⟨terms1_admissible, terms2_admissible, terms3_admissible,
    terms4_admissible, terms5_admissible, terms6_admissible⟩

/-- The checked data table reconstructs the full orbital part of the
kernel-checked density identity, with each `u` power retained. -/
 theorem orbitalSum_entries :
    H2WitnessThirteen.orbitalSum =
      DimensionThirteenFourteenDensity.u ^ 12 * H2WitnessThirteen.embed (sumWeight 1 terms1) +
      DimensionThirteenFourteenDensity.u ^ 11 * H2WitnessThirteen.embed (sumWeight 2 terms2) +
      DimensionThirteenFourteenDensity.u ^ 10 * H2WitnessThirteen.embed (sumWeight 3 terms3) +
      DimensionThirteenFourteenDensity.u ^ 9 * H2WitnessThirteen.embed (sumWeight 4 terms4) +
      DimensionThirteenFourteenDensity.u ^ 8 * H2WitnessThirteen.embed (sumWeight 5 terms5) +
      DimensionThirteenFourteenDensity.u ^ 7 * H2WitnessThirteen.embed (sumWeight 6 terms6) := by
  rw [← w1_entries, ← w2_entries, ← w3_entries, ← w4_entries,
    ← w5_entries, ← w6_entries]
  rfl

private theorem factor_explicit : H2WitnessThirteen.factor =
    C (999999993 / 1000000000 : ℚ) *
      DimensionThirteenFourteenDensity.u ^ 2 * DimensionThirteenFourteenDensity.p1 +
    C (29552 / 1000000000 : ℚ) * DimensionThirteenFourteenDensity.p3 +
    C (83790 / 1000000000 : ℚ) *
      DimensionThirteenFourteenDensity.p1 * DimensionThirteenFourteenDensity.p2 +
    C (74653 / 1000000000 : ℚ) * DimensionThirteenFourteenDensity.p1 ^ 3 := by
  simp [H2WitnessThirteen.factor, H2WitnessThirteen.embed,
    H2WitnessThirteen.f1, H2WitnessThirteen.f3,
    FiniteTypeCSchurSix.p1, FiniteTypeCSchurSix.p2,
    FiniteTypeCSchurSix.p3]
  ring

/-- The single H2 factor has characteristic weight three before any
specialization of the independent `u` and power-sum variables. -/
theorem factor_homogeneous (t : DimensionThirteenFourteenDensity.P) :
    MvPolynomial.aeval ![t * DimensionThirteenFourteenDensity.u,
      t * DimensionThirteenFourteenDensity.p1,
      t ^ 2 * DimensionThirteenFourteenDensity.p2,
      t ^ 3 * DimensionThirteenFourteenDensity.p3,
      t ^ 4 * DimensionThirteenFourteenDensity.p4,
      t ^ 5 * DimensionThirteenFourteenDensity.p5,
      t ^ 6 * DimensionThirteenFourteenDensity.p6] H2WitnessThirteen.factor =
      t ^ 3 * H2WitnessThirteen.factor := by
  rw [factor_explicit]
  simp [DimensionThirteenFourteenDensity.u,
    DimensionThirteenFourteenDensity.p1,
    DimensionThirteenFourteenDensity.p2,
    DimensionThirteenFourteenDensity.p3]
  ring

/-- The complete H2 witness, including every orbital and square term,
has characteristic weight thirteen. -/
theorem witness_homogeneous (t : DimensionThirteenFourteenDensity.P) :
    MvPolynomial.aeval ![t * DimensionThirteenFourteenDensity.u,
      t * DimensionThirteenFourteenDensity.p1,
      t ^ 2 * DimensionThirteenFourteenDensity.p2,
      t ^ 3 * DimensionThirteenFourteenDensity.p3,
      t ^ 4 * DimensionThirteenFourteenDensity.p4,
      t ^ 5 * DimensionThirteenFourteenDensity.p5,
      t ^ 6 * DimensionThirteenFourteenDensity.p6] H2WitnessThirteen.witness =
      t ^ 13 * H2WitnessThirteen.witness := by
  rw [← H2WitnessThirteen.density13_witness]
  exact DimensionThirteenFourteenDensity.density13_homogeneous t

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The complete equality survives evaluation in any commutative rational
algebra, including one with nilpotent coefficients. -/
theorem density13_witness_eval (v : Fin 7 → R) :
    MvPolynomial.aeval v DimensionThirteenFourteenDensity.density13 =
      MvPolynomial.aeval v H2WitnessThirteen.witness :=
  congrArg (MvPolynomial.aeval v) H2WitnessThirteen.density13_witness

end
end QuaternionicSymmetry.H2WitnessThirteenChecks
