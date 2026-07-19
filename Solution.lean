import Erdos1196

theorem theorem_1196 :
    ∃ C : ℝ, Erdos1196.erdos1196_bound C :=
  Erdos1196.theorem_1196

theorem theorem_164 :
    Summable (fun n : ℕ => Erdos1196.prime_layer.indicator Erdos1196.erdos_weight n) ∧
      ∀ A : Set ℕ, Erdos1196.primitive_set A ->
        Summable (fun n : ℕ => A.indicator Erdos1196.erdos_weight n) ∧
          Erdos1196.erdos_sum A ≤ Erdos1196.erdos_sum Erdos1196.prime_layer :=
  Erdos1196.theorem_164

theorem theorem_1217 :
    ∀ A : Set ℕ, 0 < Erdos1196.upper_doubly_log_density A ->
      ∃ n : ℕ → ℕ,
        Erdos1196.strictly_increasing_divisibility_chain n ∧
        Erdos1196.chain_in_set n A ∧
        Erdos1196.upper_chain_density_at_least n
          (Erdos1196.upper_doubly_log_density A) :=
  Erdos1196.theorem_1217

theorem theorem_odd_banks_martin {k : ℕ} {Q A : Set ℕ}
    (hk : 1 ≤ k) (hQ : Erdos1196.IsSetOfOddPrimes Q)
    (hA : Erdos1196.primitive_set A)
    (hAk : A ⊆ Erdos1196.omega_ge_layer k) :
    Erdos1196.erdos_sum (Erdos1196.restrict_to_primes A Q) ≤
      Erdos1196.erdos_sum (Erdos1196.oddBM_terminal k Q) :=
  Erdos1196.theorem_odd_banks_martin hk hQ hA hAk

theorem theorem_2_strong : Erdos1196.erdos_strong 2 :=
  Erdos1196.theorem_2_strong

theorem theorem_AKS :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x y : ℝ) (A : Set ℕ),
      3 ≤ x -> x ≤ y -> Erdos1196.primitive_set A ->
        Erdos1196.reciprocal_dyadic_interval_sum A x y ≤
          C * Real.log x / Real.sqrt (Real.log (Real.log x)) :=
  Erdos1196.theorem_AKS

theorem aks_LYM_refinement :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x y : ℝ) (A : Set ℕ),
      3 ≤ x -> x ≤ y -> Erdos1196.primitive_set A ->
        Erdos1196.aksLYMSum A x y
            (Erdos1196.aksPartitionFunction x (Erdos1196.aksExponent x)) ≤
          C * Real.log x :=
  Erdos1196.aks_LYM_refinement
