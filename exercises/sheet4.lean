import lecture5.examples5

open MyQuotient

-- Two integers define the same class modulo `n` exactly when they have the same remainder modulo `n'.
-- Hint: use `modulo_eq_rest` from the lecture notes.
lemma exercise0 {n m1 m2 : ℤ} (hn : n ≠ 0) : (q n m1) = q n m2 ↔ (m1 % n = m2 % n) := by
  constructor
  · intro hq
    have hdiv : n ∣ m1 - m2 := by
      simpa only [mod_relation] using (q_equality.mp hq)
    obtain ⟨k, hk⟩ := hdiv
    apply modulo_eq_rest n m1 (k + m2 / n) (m2 % n) hn
    · constructor
      · exact Int.emod_nonneg m2 hn
      · exact Int.emod_lt m2 hn
    · calc
        m1 = (m1 - m2) + m2 := by ring
        _ = n * k + m2 := by rw [hk]
        _ = n * k + (n * (m2 / n) + m2 % n) := by
          rw [Int.mul_ediv_add_emod]
        _ = n * (k + m2 / n) + m2 % n := by ring
  · intro hmod
    apply q_equality.mpr
    simp only [mod_relation]
    use m1 / n - m2 / n
    calc
      m1 - m2 =
          (n * (m1 / n) + m1 % n) -
            (n * (m2 / n) + m2 % n) := by
              rw [Int.mul_ediv_add_emod,
                  Int.mul_ediv_add_emod]
      _ = n * (m1 / n - m2 / n) := by
            rw [hmod]
            ring

/- Look at exercise_class.lean in lecture-notes/lecture4 for the setbuilder notation.
Use the properties of equivalence relations to prove the following lemma.
You can access them with `hR.refl`, `hR.symm` and `hR.trans`.
-/
lemma exercise1 {α : Type} {R : α → α → Prop} (hR : Equivalence R) (x y : α) :
    {z : α | R x z} = {z : α | R y z} ↔ R x y := by
  constructor
  · intro hsets
    -- hint: use x ∈ {z : α | R x z}
    have hx : x ∈ {z : α | R x z} := by
      exact hR.refl x
    rw [hsets] at hx
    exact hR.symm hx
  · intro hRxy
    apply Set.Subset.antisymm_iff.mpr -- show both inclusions
    constructor -- hint: A ⊆ B means ∀ x, x ∈ A → x ∈ B
    · intro z hxz
      exact hR.trans (hR.symm hRxy) hxz
    · intro z hyz
      exact hR.trans hRxy hyz

-- use `Quotient.lift` to define a function ℤ/n → ℤ/n sending ⟦x⟧ → ⟦k * x⟧.
def mul_k (n k : ℤ) : ℤ_mod n → ℤ_mod n := by
  refine Quotient.lift (fun x => q n (k * x)) ?_
  intro x y hxy
  simp only [q_equality, mod_relation] at *
  obtain ⟨a, ha⟩ := hxy
  use k * a
  calc
    k * x - k * y = k * (x - y) := by ring
    _ = k * (n * a) := by rw [ha]
    _ = n * (k * a) := by ring

-- A function with a left inverse is injective. Only use definitions to solve this.
lemma f_injective_of_left_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) :
    Function.Injective f := by
  intro x y hxy
  calc
    x = g (f x) := (h x).symm
    _ = g (f y) := by rw [hxy]
    _ = y := h y

-- A function with a right inverse is surjective. Only use definitions to solve this.
lemma f_surjective_of_right_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ y, f (g y) = y) :
    Function.Surjective f := by
  intro y
  use g y
  exact h y

-- Prove that the quotient map q : ℤ → ℤ/n is restricted to Fin n = {0, 1, …, n-1} is a bijection.
-- Hint: You can prove this directly.
theorem exercise2 {n : ℤ} (hn : n ≠ 0) : Function.Bijective (q_res n) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply Fin.ext
    change q n (x.val : ℤ) = q n (y.val : ℤ) at hxy
    have hmod :
        (x.val : ℤ) % n = (y.val : ℤ) % n := by
      exact (exercise0 hn).mp hxy
    have hxmod : (x.val : ℤ) % n = x.val := by
      apply modulo_eq_rest n (x.val : ℤ) 0 (x.val : ℤ) hn
      · constructor
        · exact_mod_cast Nat.zero_le x.val
        · exact_mod_cast x.isLt
      · ring
    have hymod : (y.val : ℤ) % n = y.val := by
      apply modulo_eq_rest n (y.val : ℤ) 0 (y.val : ℤ) hn
      · constructor
        · exact_mod_cast Nat.zero_le y.val
        · exact_mod_cast y.isLt
      · ring
    rw [hxmod, hymod] at hmod
    exact_mod_cast hmod
  · intro z
    obtain ⟨m, hm⟩ := Quotient.exists_rep z
    rw [← hm]
    have hnatAbs_pos : 0 < n.natAbs := by
      exact Int.natAbs_pos.mpr hn
    have hlt : (m % n).toNat < n.natAbs := by
      apply (Int.toNat_lt' hnatAbs_pos).mpr
      exact Int.emod_lt m hn
    use ⟨(m % n).toNat, hlt⟩
    change q n ((m % n).toNat : ℤ) = q n m
    apply (exercise0 hn).mpr
    rw [Int.toNat_of_nonneg (Int.emod_nonneg m hn)]
    exact Int.emod_emod m n

-- If coprime integers `a` and `b` both divide `c`, then their product also divides `c`.
-- Hint: Start with the case of prime powers and then use the prime factorization from last time.
lemma exercise3 {a b c : ℕ} (h1 : a ∣ c) (h2 : b ∣ c) (h3 : Nat.gcd a b = 1) : a * b ∣ c := by
  have hab : Nat.Coprime a b := by
    exact (Nat.coprime_iff_gcd_eq_one).mpr h3
  obtain ⟨k, hk⟩ := h1
  have hb_dvd_ak : b ∣ a * k := by
    rw [← hk]
    exact h2
  have hb_dvd_k : b ∣ k := by
    exact hab.symm.dvd_of_dvd_mul_left hb_dvd_ak
  obtain ⟨l, hl⟩ := hb_dvd_k
  use l
  calc
    c = a * k := hk
    _ = a * (b * l) := by rw [hl]
    _ = a * b * l := by rw [Nat.mul_assoc]
