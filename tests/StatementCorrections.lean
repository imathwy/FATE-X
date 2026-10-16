import FATEX.«2»
import FATEX.«13»
import FATEX.«15»
import FATEX.«22»
import FATEX.«23»
import FATEX.«45»
import FATEX.«60»
import FATEX.«63»
import FATEX.«96»

namespace CorrectedFatexChecks

/-- The corrected minimal-normal domain retains a genuine nontrivial minimal
normal subgroup in every simple group, rather than selecting bottom. -/
theorem simple_group_has_minimal_nontrivial_normal {G : Type} [Group G] [IsSimpleGroup G] :
    ∃ H : {H : Subgroup G // H.Normal ∧ H ≠ ⊥}, IsMin H := by
  refine ⟨⟨⊤, inferInstance, top_ne_bot⟩, ?_⟩
  intro H _
  have htop : H.val = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal H.val H.property.1).resolve_left H.property.2
  change (⊤ : Subgroup G) ≤ H.val
  rw [htop]

/-- The new hypothesis supplies exactly the nonzero nonunit needed by the proof
for every nontrivial ring; noncommutativity alone no longer satisfies it. -/
theorem nondivision_has_nonzero_nonunit {R : Type} [Ring R] [Nontrivial R]
    (h : ¬ (Nontrivial R ∧ ∀ x : R, x ≠ 0 → IsUnit x)) :
    ∃ x : R, x ≠ 0 ∧ ¬ IsUnit x := by
  classical
  by_contra hn
  push_neg at hn
  exact h ⟨inferInstance, hn⟩

/-- Strict steps and explicit endpoints now admit actual nontrivial composition
series, whereas the previous reflexive maximum-length definition was empty. -/
noncomputable def simpleCompositionSeries (G : Type) [CommGroup G] [IsSimpleGroup G] :
    Problem15.NormalSubgroupCompositionSeries G := by
  have hstep : Problem15.Subgroup.IsMaximalNormal (⊥ : Subgroup G) ⊤ := by
    refine ⟨bot_lt_top, inferInstance, ?_⟩
    intro H _ _ _
    exact IsSimpleGroup.eq_bot_or_eq_top_of_normal H inferInstance
  exact {
    toRelSeries :=
      (RelSeries.singleton (Problem15.Subgroup.IsMaximalNormal.setRel (G := G)) ⊥).snoc ⊤ hstep
    head_eq_bot := by simp
    last_eq_top := by simp
  }

theorem prime_cyclic_series_exists (p : ℕ) [Fact p.Prime] :
    Nonempty (Problem15.NormalSubgroupCompositionSeries (Multiplicative (ZMod p))) := by
  haveI : IsSimpleGroup (Multiplicative (ZMod p)) :=
    isSimpleGroup_of_prime_card (p := p) (by simp [Nat.card_eq_fintype_card])
  exact ⟨simpleCompositionSeries _⟩

/-- The irreducible constant used by the original counterexample is now excluded. -/
theorem constant_two_excluded : ¬ (0 < (Polynomial.C (2 : ℤ)).natDegree) := by simp

/-- Kronecker's theorem supplies a strictly positive root-of-unity exponent;
the repaired conclusion agrees with the standard number-field API. -/
theorem kronecker_positive_exponent (F : Type) [Field F] [NumberField F]
    (x : F) (hx : IsIntegral ℤ x) (hconj : ∀ φ : F →+* ℂ, ‖φ x‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  obtain ⟨n, hn, heq⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one F ℂ hx hconj
  exact ⟨n, hn, heq⟩

/-- The old field/unit-ideal counterexample now has the intended empty set of
associated primes, while the unit ideal is still invertible. -/
theorem field_unit_ideal_admitted :
    Problem60.Ideal.Invertible (⊤ : Ideal ℚ) ∧
    (∀ p ∈ associatedPrimes ℚ (ℚ ⧸ (⊤ : Ideal ℚ)), p.height = 1) := by
  constructor
  · refine ⟨top_ne_bot, ⊤, ?_, top_ne_bot⟩
    simpa using (inferInstance : (⊤ : Ideal ℚ).IsPrincipal)
  · intro p hp
    exact absurd hp not_isAssociatedPrime_of_subsingleton

/-- The corrected associated-prime/height condition does not accidentally admit
the zero ideal over a field. -/
theorem field_zero_ideal_excluded :
    ¬ (∀ p ∈ associatedPrimes ℚ (ℚ ⧸ (⊥ : Ideal ℚ)), p.height = 1) := by
  have hp : (⊥ : Ideal ℚ).IsPrime := inferInstance
  have hass : associatedPrimes ℚ (ℚ ⧸ (⊥ : Ideal ℚ)) = {⊥} := by
    rw [associatedPrimes.eq_singleton_of_isPrimary hp.isPrimary, hp.radical]
  intro h
  have hheight := h ⊥ (by rw [hass]; simp)
  simp at hheight

/-- The constant-map shortcut available when surjectivity was omitted is not a
surjection onto the polynomial algebra. -/
theorem constant_map_is_not_surjective :
    ¬ Function.Surjective (Polynomial.C : ℚ →+* Polynomial ℚ) := by
  intro h
  obtain ⟨c, hc⟩ := h Polynomial.X
  have hcoeff := congrArg (fun f : Polynomial ℚ => f.coeff 1) hc
  simp at hcoeff

/-- A rank-one free polynomial module, with its usual nontrivial variable action,
now has valid grading data and an A-linear degree-preserving identity. -/
theorem nonzero_regular_module_is_admitted {k : Type} [Field k] {r : ℕ} (hr : 0 < r) :
    ∃ pieces : ℕ → Submodule k (MvPolynomial (Fin r) k),
      Nonempty (DirectSum.Decomposition pieces) ∧
      SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin r) k) pieces ∧
      Problem45.IsGradedHom pieces pieces
        (LinearMap.id : MvPolynomial (Fin r) k →ₗ[MvPolynomial (Fin r) k] MvPolynomial (Fin r) k) ∧
      ∃ m : MvPolynomial (Fin r) k,
        (MvPolynomial.X (⟨0, hr⟩ : Fin r) : MvPolynomial (Fin r) k) • m ≠ 0 := by
  letI : SetLike.GradedMonoid (MvPolynomial.homogeneousSubmodule (Fin r) k) :=
    MvPolynomial.HomogeneousSubmodule.gradedMonoid
  refine ⟨MvPolynomial.homogeneousSubmodule (Fin r) k,
    ⟨MvPolynomial.decomposition⟩, inferInstance, ?_, 1, ?_⟩
  · intro d x
    exact x.property
  · simpa only [smul_eq_mul, mul_one] using
      (MvPolynomial.X_ne_zero (⟨0, hr⟩ : Fin r) (R := k))

noncomputable def zeroOrbitPolynomial : RatFunc ℚ :=
  algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.X ^ 2)

/-- A zero orbit point is no longer confused with a pole: polynomial x² has
denominator one and permits the initial point zero. -/
theorem zero_is_allowed_when_not_a_pole :
    (∀ n : ℕ, zeroOrbitPolynomial.denom.eval
      ((zeroOrbitPolynomial.eval (RingHom.id ℚ))^[n] 0) ≠ 0) ∧
    ¬ (∀ n : ℕ, (zeroOrbitPolynomial.eval (RingHom.id ℚ))^[n] 0 ≠ 0) := by
  constructor
  · intro n
    have hd : zeroOrbitPolynomial.denom = 1 := RatFunc.denom_algebraMap _
    rw [hd]
    simp
  · intro h
    exact h 0 (by simp)

#print axioms simple_group_has_minimal_nontrivial_normal
#print axioms nondivision_has_nonzero_nonunit
#print axioms prime_cyclic_series_exists
#print axioms constant_two_excluded
#print axioms kronecker_positive_exponent
#print axioms field_unit_ideal_admitted
#print axioms field_zero_ideal_excluded
#print axioms constant_map_is_not_surjective
#print axioms nonzero_regular_module_is_admitted
#print axioms zero_is_allowed_when_not_a_pole

end CorrectedFatexChecks
