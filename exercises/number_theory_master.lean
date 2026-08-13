import Mathlib.Tactic
import Mathlib.Data.Int.DivMod
import LectureNotes.lecture4.examples4
import LectureNotes.lecture5.examples5

/-
This is a bonus exercise sheet. You can submit it at any point, I do not expect you to finish it by
Monday! You can work on it at your own pace, and you can choose which exercise to do.
The topic of this exercise sheet is Euler's totient function. You can prove two fundamental
relations involving the totient function.
Proving the theorems on paper is already a good exercise, I encourage you to send me your
'normal' proof before you start formalizing it.
The formalization will require you to use essentially all the tools we have developed so far!
-/

noncomputable def ϕ : ℕ → ℕ := fun n => Nat.card {k : Fin n | Nat.Coprime (k : ℕ) n}

--For future reference, we call the set of integers smaller than n and coprime to n, U(n).
abbrev U (n : ℕ) := {k : Fin n | Nat.Coprime (k : ℕ) n}

/-
The first step to define the values of the map f.
-/
def f_fst_val {n m : ℕ} (k : U (m * n)) : Fin n where
  val := k % n
  isLt := by
    by_cases hn : n = 0
    · subst n
      have exponent_positive := k.1.isLt
      simp at exponent_positive
    · exact Nat.mod_lt _ (Nat.pos_of_ne_zero hn)
-- note that the proof is trivial if one of the two numbers is 0!

def f_snd_val {n m : ℕ} (k : U (m * n)) : Fin m where
  val := k % m
  isLt := by
    by_cases hm : m = 0
    · subst m
      have exponent_positive := k.1.isLt
      simp at exponent_positive
    · exact Nat.mod_lt _ (Nat.pos_of_ne_zero hm)
/-
The second step is to show that f(k) lands in U n × U m,
i.e. that the values of f are coprime to n and m respectively.
-/
lemma f_fst_well_defined {n m : ℕ} (k : U (m * n)) : f_fst_val k ∈ U n := by
  change Nat.Coprime ((k.1 : ℕ) % n) n
  have k_coprime_n : Nat.Coprime (k.1 : ℕ) n :=
    (Nat.coprime_mul_iff_right.mp k.2).2
  rw [Nat.coprime_iff_gcd_eq_one]
  rw [← Nat.gcd_rec n (k.1 : ℕ), Nat.gcd_comm]
  exact k_coprime_n.gcd_eq_one

lemma f_snd_well_defined {n m : ℕ} (k : U (m * n)) : f_snd_val k ∈ U m := by
  change Nat.Coprime ((k.1 : ℕ) % m) m
  have k_coprime_m : Nat.Coprime (k.1 : ℕ) m :=
    (Nat.coprime_mul_iff_right.mp k.2).1
  rw [Nat.coprime_iff_gcd_eq_one]
  rw [← Nat.gcd_rec m (k.1 : ℕ), Nat.gcd_comm]
  exact k_coprime_m.gcd_eq_one

/-
Finally we can combine the previous definitions to define the map f.
-/
def f (n m : ℕ) : U (m * n) → U n × U m := by exact
  fun k => (⟨f_fst_val k, f_fst_well_defined k⟩, ⟨f_snd_val k, f_snd_well_defined k⟩)
/-
Proceed by expressing the map f as a composition of the CRT map C and the maps q_res from the lecture.
-/

/-
The proof of both relations involves the following properties of the totient function.
-/
lemma ϕ_prime_power {p k : ℕ} (hp : Nat.Prime p) (exponent_positive : k > 0) : ϕ (p ^ k) = p ^ k - p ^ (k - 1) := by
  obtain ⟨n, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero
      (Nat.pos_iff_ne_zero.mp exponent_positive)
  have phi_as_filter :
      ϕ (p ^ (n + 1)) =
        (Finset.filter
          (fun a => (p ^ (n + 1)).Coprime a)
          (Finset.range (p ^ (n + 1)))).card := by
    unfold ϕ
    let e :
        {x : Fin (p ^ (n + 1)) |
          Nat.Coprime (x : ℕ) (p ^ (n + 1))} ≃
        {a // a ∈
          Finset.filter
            (fun x => (p ^ (n + 1)).Coprime x)
            (Finset.range (p ^ (n + 1)))} :=
      {
        toFun := fun x => ⟨x.1.1, by
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨x.1.2, x.2.symm⟩⟩
        invFun := fun a => by
          have ha := Finset.mem_filter.mp a.2
          exact ⟨⟨a.1, Finset.mem_range.mp ha.1⟩, ha.2.symm⟩
        left_inv := by
          intro x
          apply Subtype.ext
          apply Fin.ext
          rfl
        right_inv := by
          intro x
          apply Subtype.ext
          rfl
      }
    rw [Nat.card_congr e,
        Nat.card_eq_fintype_card,
        Fintype.card_coe]
  rw [phi_as_filter]
  calc
    (Finset.filter
        (fun a => (p ^ (n + 1)).Coprime a)
        (Finset.range (p ^ (n + 1)))).card
      =
      (Finset.range (p ^ (n + 1)) \
        (Finset.range (p ^ n)).image (fun a => a * p)).card := by
        apply congrArg Finset.card
        rw [Finset.sdiff_eq_filter]
        apply Finset.filter_congr
        simp only [
          Finset.mem_range,
          Nat.coprime_pow_left_iff n.succ_pos,
          Finset.mem_image,
          not_exists,
          hp.coprime_iff_not_dvd
        ]
        intro a a_mem
        constructor
        · intro hap b hb
          rcases hb with ⟨_, rfl⟩
          exact hap (dvd_mul_left _ _)
        · rintro h ⟨b, rfl⟩
          rw [Nat.pow_succ'] at a_mem
          exact h b
            ⟨(Nat.mul_lt_mul_right hp.pos).mp (by
              simpa [Nat.mul_comm] using a_mem),mul_comm _ _⟩
    _ = p ^ (n + 1) - p ^ n := by
        have mul_by_p_injective :
            Function.Injective (fun a : ℕ => a * p) := by
          intro a b hab
          exact Nat.eq_of_mul_eq_mul_right hp.pos hab
        have multiples_of_p_subset :
            (Finset.range (p ^ n)).image (fun a => a * p)
              ⊆ Finset.range (p ^ (n + 1)) := by
          intro a ha
          rcases Finset.mem_image.mp ha with ⟨b, hb, rfl⟩
          rw [Finset.mem_range] at hb ⊢
          rw [Nat.pow_succ]
          exact (Nat.mul_lt_mul_right hp.pos).mpr hb
        rw [
          Finset.card_sdiff_of_subset multiples_of_p_subset,
          Finset.card_image_of_injective _ mul_by_p_injective,
          Finset.card_range,
          Finset.card_range
        ]
    _ = p ^ (n + 1) - p ^ ((n + 1) - 1) := by
        simp

lemma ϕ_multiplicative {m n : ℕ} (h : Nat.Coprime m n) : ϕ (m * n) = ϕ m * ϕ n := by
  by_cases hm : m = 0
  · subst m
    have hn : n = 1 := by
      simpa [Nat.Coprime] using h
    subst n
    simp [ϕ]
  by_cases hn : n = 0
  · subst n
    have hm : m = 1 := by
      simpa [Nat.Coprime] using h
    subst m
    simp [ϕ]
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hm_int : (m : ℤ) ≠ 0 := by
    exact_mod_cast hm
  have hn_int : (n : ℤ) ≠ 0 := by
    exact_mod_cast hn
  have h_int : IsCoprime (m : ℤ) (n : ℤ) :=
    h.cast
  have quotient_eq_mod (a d : ℕ) :
      MyQuotient.q (d : ℤ) (a : ℤ) =
        MyQuotient.q (d : ℤ) ((a % d : ℕ) : ℤ) := by
    rw [MyQuotient.q_equality]
    change (d : ℤ) ∣
      (a : ℤ) - ((a % d : ℕ) : ℤ)
    rw [Int.natCast_mod]
    exact ⟨(a : ℤ) / (d : ℤ),
      (Int.mul_ediv_self (a : ℤ) (d : ℤ)).symm⟩
  have residue_equiv {d : ℕ} (hd : d ≠ 0)
      (hdZ : (d : ℤ) ≠ 0) (a : ℕ) :
      MyQuotient.Z_mod_n_fin_n_equiv hdZ
          (MyQuotient.q (d : ℤ) (a : ℤ))
        =
      ⟨a % d, Nat.mod_lt _ (Nat.pos_of_ne_zero hd)⟩ := by
    apply (MyQuotient.Z_mod_n_fin_n_bijection hdZ).1
    have quotient_roundtrip :
        MyQuotient.q_res (d : ℤ)
            (MyQuotient.Z_mod_n_fin_n_equiv hdZ
              (MyQuotient.q (d : ℤ) (a : ℤ)))
          =
        MyQuotient.q (d : ℤ) (a : ℤ) := by
      change
        (MyQuotient.Z_mod_n_fin_n_equiv hdZ).symm
            (MyQuotient.Z_mod_n_fin_n_equiv hdZ
              (MyQuotient.q (d : ℤ) (a : ℤ))) =
          MyQuotient.q (d : ℤ) (a : ℤ)
      exact (MyQuotient.Z_mod_n_fin_n_equiv hdZ).symm_apply_apply
        (MyQuotient.q (d : ℤ) (a : ℤ))
    apply Eq.trans quotient_roundtrip
    change
      MyQuotient.q (d : ℤ) (a : ℤ) =
        MyQuotient.q (d : ℤ) ((a % d : ℕ) : ℤ)
    exact quotient_eq_mod a d
  let fin_to_mod_mn :
      Fin (m * n) ≃
        MyQuotient.ℤ_mod ((m : ℤ) * (n : ℤ)) :=
    (MyQuotient.Z_mod_n_fin_n_equiv
      (Int.mul_ne_zero hm_int hn_int)).symm
  let crt_equiv :
      MyQuotient.ℤ_mod ((m : ℤ) * (n : ℤ)) ≃
        MyQuotient.ℤ_mod (m : ℤ) ×
          MyQuotient.ℤ_mod (n : ℤ) :=
    Equiv.ofBijective
      (MyQuotient.C (m : ℤ) (n : ℤ))
      (MyQuotient.chinese_remainder_theorem
        hm_int hn_int h_int)
  let fin_crt_equiv : Fin (m * n) ≃ Fin n × Fin m :=
    fin_to_mod_mn.trans
      (crt_equiv.trans
        ((Equiv.prodCongr
            (MyQuotient.Z_mod_n_fin_n_equiv hm_int)
            (MyQuotient.Z_mod_n_fin_n_equiv hn_int)).trans
          (Equiv.prodComm (Fin m) (Fin n))))
  let residue_map : Fin (m * n) → Fin n × Fin m :=
    fun x =>
      (⟨x % n, Nat.mod_lt _ hnpos⟩,
       ⟨x % m, Nat.mod_lt _ hmpos⟩)
  have fin_crt_equiv_eq_residue_map (x : Fin (m * n)) :
      fin_crt_equiv x = residue_map x := by
    change
      (MyQuotient.Z_mod_n_fin_n_equiv hn_int
          (MyQuotient.q (n : ℤ) (x : ℤ)),
       MyQuotient.Z_mod_n_fin_n_equiv hm_int
          (MyQuotient.q (m : ℤ) (x : ℤ)))
        =
      (⟨x % n, Nat.mod_lt _ hnpos⟩,
       ⟨x % m, Nat.mod_lt _ hmpos⟩)
    rw [residue_equiv hn hn_int x, residue_equiv hm hm_int x]
  have residue_map_bijective : Function.Bijective residue_map := by
    have equiv_eq_residue_map :
        (fin_crt_equiv : Fin (m * n) → Fin n × Fin m) = residue_map := by
      funext x
      exact fin_crt_equiv_eq_residue_map x
    rw [← equiv_eq_residue_map]
    exact fin_crt_equiv.bijective
  have f_bijective : Function.Bijective (f n m) := by
    constructor
    · intro x y f_values_equal
      have residues_equal : residue_map x = residue_map y := by
        apply Prod.ext
        · apply Fin.ext
          have h' :=
            congrArg
              (fun z : U n × U m => (z.1.1 : ℕ))
              f_values_equal
          simpa [residue_map, f, f_fst_val] using h'
        · apply Fin.ext
          have h' :=
            congrArg
              (fun z : U n × U m => (z.2.1 : ℕ))
              f_values_equal
          simpa [residue_map, f, f_snd_val] using h'
      apply Subtype.ext
      exact residue_map_bijective.1 residues_equal
    · intro y
      obtain ⟨x₀, residue_pair_equal⟩ :=
        residue_map_bijective.2 (y.1.1, y.2.1)
      have x_mod_n :
          (x₀ : ℕ) % n = (y.1.1 : ℕ) := by
        have h' :=
          congrArg
            (fun z : Fin n × Fin m => (z.1 : ℕ))
            residue_pair_equal
        simpa [residue_map] using h'
      have x_mod_m :
          (x₀ : ℕ) % m = (y.2.1 : ℕ) := by
        have h' :=
          congrArg
            (fun z : Fin n × Fin m => (z.2 : ℕ))
            residue_pair_equal
        simpa [residue_map] using h'
      have x_coprime_n : Nat.Coprime (x₀ : ℕ) n := by
        rw [Nat.coprime_iff_gcd_eq_one]
        rw [Nat.gcd_comm, Nat.gcd_rec, x_mod_n]
        exact y.1.2.gcd_eq_one
      have x_coprime_m : Nat.Coprime (x₀ : ℕ) m := by
        rw [Nat.coprime_iff_gcd_eq_one]
        rw [Nat.gcd_comm, Nat.gcd_rec, x_mod_m]
        exact y.2.2.gcd_eq_one
      have x_coprime_mn :
          Nat.Coprime (x₀ : ℕ) (m * n) :=
        Nat.coprime_mul_iff_right.mpr ⟨x_coprime_m, x_coprime_n⟩
      let x : U (m * n) :=
        ⟨x₀, x_coprime_mn⟩
      refine ⟨x, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        apply Fin.ext
        exact x_mod_n
      · apply Subtype.ext
        apply Fin.ext
        exact x_mod_m
  have e : U (m * n) ≃ U n × U m :=
    Equiv.ofBijective (f n m) f_bijective
  change
    Nat.card (U (m * n)) =
      Nat.card (U m) * Nat.card (U n)
  simpa [Nat.card_prod, Nat.mul_comm] using
    Nat.card_congr e

/-
To prove multiplicativity, we construct a map f: U n*m → U n × U m, k ↦ (k mod n, k mod m).
Then use the Chinese remainder theorem and the map q_res from the lecture to show it f is bijective.
If you are familar with rings, you may notice that the proof approach below is somewhat pedestrian,
If you know about rings, you may use ZMod.chineseRemainder to prove multiplicativity.
I suggest to leave this proof for last!
-/

/-
The first relation expresses the totient function as a product over the prime factors of `n`.
I wrote the statement in this elegant form, however, formulated like this it involves rational numbers,
so it will be helpful to expand the product and write it in terms of natural numbers.
-/
theorem product_formula (n : ℕ) : ϕ n = n * ∏ p ∈ (Nat.primeFactors n), (1 - (1 / p) : ℚ) := by
  by_cases hn : n = 0
  · subst n
    simp [ϕ]
  have prime_power_factorization :
      (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    simpa [Finsupp.prod, Nat.support_factorization] using
      (Nat.prod_factorization_pow_eq_self hn)
  have prime_power_coprime_prod :
      ∀ p ∈ n.primeFactors, ∀ s : Finset ℕ,
        s ⊆ n.primeFactors → p ∉ s →
        (p ^ n.factorization p).Coprime
          (∏ q ∈ s, q ^ n.factorization q) := by
    intro p hp s
    induction s using Finset.induction_on with
    | empty =>
        intro _ _
        simp
    | @insert q s hqs ih =>
        intro hs hps
        have hq : q ∈ n.primeFactors :=
          hs (Finset.mem_insert_self q s)
        have hs' : s ⊆ n.primeFactors := by
          intro r hr
          exact hs (Finset.mem_insert_of_mem hr)
        have hpq : p ≠ q := by
          intro hpq
          subst q
          exact hps (Finset.mem_insert_self p s)
        rw [Finset.prod_insert hqs, Nat.coprime_mul_iff_right]
        constructor
        · exact Nat.coprime_pow_primes
            (n.factorization p)
            (n.factorization q)
            (Nat.prime_of_mem_primeFactors hp)
            (Nat.prime_of_mem_primeFactors hq)
            hpq
        · exact ih hs' (by
            intro h
            exact hps (Finset.mem_insert_of_mem h))
  have phi_of_prime_power_product :
      ∀ s : Finset ℕ, s ⊆ n.primeFactors →
        ϕ (∏ p ∈ s, p ^ n.factorization p) =
          ∏ p ∈ s, ϕ (p ^ n.factorization p) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        simp [ϕ]
    | @insert p s hps ih =>
        intro hs
        have hp : p ∈ n.primeFactors :=
          hs (Finset.mem_insert_self p s)
        have hs' : s ⊆ n.primeFactors := by
          intro q hq
          exact hs (Finset.mem_insert_of_mem hq)
        rw [Finset.prod_insert hps, Finset.prod_insert hps]
        rw [ϕ_multiplicative (prime_power_coprime_prod p hp s hs' hps)]
        rw [ih hs']
  have phi_factorization :
      ϕ n =
        ∏ p ∈ n.primeFactors,
          ϕ (p ^ n.factorization p) := by
    calc
      ϕ n =
          ϕ (∏ p ∈ n.primeFactors, p ^ n.factorization p) :=
        congrArg ϕ prime_power_factorization.symm
      _ =
          ∏ p ∈ n.primeFactors, ϕ (p ^ n.factorization p) :=
        phi_of_prime_power_product n.primeFactors (by
          intro p hp
          exact hp)
  have phi_prime_power_term :
      ∀ p ∈ n.primeFactors,
        (ϕ (p ^ n.factorization p) : ℚ) =
          (p : ℚ) ^ n.factorization p *
            (1 - 1 / (p : ℚ)) := by
    intro p hp
    have p_prime : Nat.Prime p :=
      Nat.prime_of_mem_primeFactors hp
    have exponent_positive : 0 < n.factorization p := by
      have p_in_factorization : p ∈ n.factorization.support := by
        simpa [Nat.support_factorization] using hp
      exact Nat.pos_of_ne_zero
        (Finsupp.mem_support_iff.mp p_in_factorization)
    have phi_prime_power_nat :
        ϕ (p ^ n.factorization p) =
          p ^ (n.factorization p - 1) * (p - 1) := by
      calc
        ϕ (p ^ n.factorization p)
            =
            p ^ n.factorization p -
              p ^ (n.factorization p - 1) :=
          ϕ_prime_power p_prime exponent_positive
        _ =
            p ^ (n.factorization p - 1) * p -
              p ^ (n.factorization p - 1) := by
          congr 1
          conv_lhs =>
            rw [show n.factorization p =
              (n.factorization p - 1) + 1 by omega]
          rw [pow_succ]
        _ =
            p ^ (n.factorization p - 1) * (p - 1) := by
          rw [Nat.mul_sub_left_distrib, mul_one]
    rw [phi_prime_power_nat]
    simp only [
      Nat.cast_mul,
      Nat.cast_pow,
      Nat.cast_sub p_prime.one_le
    ]
    have p_nonzero_rat : (p : ℚ) ≠ 0 := by
      exact_mod_cast p_prime.ne_zero
    have split_power :
        (p : ℚ) ^ n.factorization p =
          (p : ℚ) ^ (n.factorization p - 1) * p := by
      calc
        (p : ℚ) ^ n.factorization p
            =
            (p : ℚ) ^ ((n.factorization p - 1) + 1) := by
              congr 1
              omega
        _ = (p : ℚ) ^ (n.factorization p - 1) * p := by
              rw [pow_succ]
    rw [split_power]
    field_simp [p_nonzero_rat]
    ring
  calc
    (ϕ n : ℚ)
        =
        ∏ p ∈ n.primeFactors,
          (ϕ (p ^ n.factorization p) : ℚ) := by
      exact_mod_cast phi_factorization
    _ =
        ∏ p ∈ n.primeFactors,
          ((p : ℚ) ^ n.factorization p *
            (1 - 1 / (p : ℚ))) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact phi_prime_power_term p hp
    _ =
        (∏ p ∈ n.primeFactors,
          (p : ℚ) ^ n.factorization p) *
        ∏ p ∈ n.primeFactors,
          (1 - 1 / (p : ℚ)) := by
      rw [Finset.prod_mul_distrib]
    _ =
        (n : ℚ) *
        ∏ p ∈ n.primeFactors,
          (1 - 1 / (p : ℚ)) := by
      congr 1
      exact_mod_cast prime_power_factorization

/-
The second relation expresses a number `n` as a sum of the totient values of all its divisors.
-/
theorem sum_formula (n : ℕ) : n = ∑ d ∈ (Nat.divisors n), ϕ d := by
  sorry
