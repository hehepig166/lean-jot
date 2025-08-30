import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Star


namespace Example

lemma lemma_exist_inverse (x n : ℕ) (hn_pos : 0 < n) (h : x.gcd n = 1) : ∃ y, y ∈ Finset.Icc 1 n ∧ x * y % n = 1 % n := by
  by_cases hn : n = 1
  . use 1
    simp_all [Nat.mod_one x]
  obtain ⟨y, hy⟩ := Nat.exists_mul_emod_eq_gcd (show x.gcd n < n by omega)
  use y % n
  have hy_ne_zero : y % n ≠ 0 := by
    by_contra! h_contra
    have : x * y % n = 0 := by
      refine Nat.mod_eq_zero_of_dvd ?_
      apply Dvd.dvd.mul_left ?_ x
      exact Nat.dvd_of_mod_eq_zero h_contra
    omega
  constructor
  . simp
    constructor
    . omega
    . apply le_of_lt
      exact Nat.mod_lt y hn_pos
  . rw [show 1 % n = 1 by exact Nat.one_mod_eq_one.mpr hn, ← h, ← hy]
    exact Nat.mul_mod_mod x y n

lemma lemma_dvd_of_mul_and_coprime {a b c : ℤ} (hdvd : c ∣ a * b) (h_coprime : gcd c a = 1) : c ∣ b := by
  refine Int.dvd_of_dvd_mul_right_of_gcd_one hdvd ?_
  exact Eq.symm ((fun {m n} ↦ Int.ofNat_inj.mp) (id (Eq.symm h_coprime)))

lemma lemma_exist_unique_inverse_in_range
    (x n : ℕ)
    (hn_pos : 0 < n)
    (h : x.gcd n = 1) :
    ∃! y, (y ∈ Finset.Icc 1 n ∧ x * y % n = 1 % n) := by

  by_cases hn : n = 1
  . use 1
    simp [hn]
    exact Nat.mod_one x

  obtain ⟨y, hy⟩ := lemma_exist_inverse x n hn_pos h
  use y
  simp [hy]
  intro z hz_ge hz_le hz_mod
  by_contra! h_contra

  have h1 : (x : ℤ) * (y : ℤ) ≡ 1 [ZMOD n] := by
    obtain ⟨_, hy⟩ := hy
    zify at hy
    exact hy

  have h2 : (x : ℤ) * (z : ℤ) ≡ 1 [ZMOD n] := by
    zify at hz_mod
    exact hz_mod

  have h3 : (x : ℤ) * (y - z) ≡ 0 [ZMOD n] := by
    rw [mul_sub, show (0 : ℤ) = 1 - 1 by ring]
    exact Int.ModEq.symm (Int.ModEq.sub (id (Int.ModEq.symm h1)) (id (Int.ModEq.symm h2)))

  replace h3 : (n : ℤ) ∣ x * ((y : ℤ) - (z : ℤ)) := by
    exact Int.dvd_of_emod_eq_zero h3

  have h4 : (n : ℤ) ∣ (y : ℤ) - (z : ℤ) := by
    have : gcd (x : ℤ) (n : ℤ) = 1 := by
      zify at h
      rw [← h]
      rfl
    replace this : gcd (n : ℤ) (x : ℤ) = 1 := by
      rw [← this]
      exact gcd_comm (n : ℤ) (x : ℤ)
    exact lemma_dvd_of_mul_and_coprime h3 this

  replace h4 : (y : ℤ) ≡ (z : ℤ) [ZMOD n] := by
    rw [Int.modEq_iff_dvd]
    exact dvd_sub_comm.mp h4

  replace h4 : y % n = z % n := by
    exact Int.ofNat_inj.mp h4

  by_cases hy_eq_n : y = n
  . simp [hy_eq_n] at h4
    have ⟨k, hk⟩ : n ∣ z := by exact Nat.dvd_of_mod_eq_zero (id (Eq.symm h4))
    have : k = 1 := by nlinarith
    simp [hk, this, hy_eq_n] at h_contra

  simp at hy
  obtain ⟨⟨hy_ge, hy_le⟩, _⟩ := hy

  have hz_ne_n : z ≠ n := by
    by_contra! hz_eq_n
    simp [hz_eq_n] at h4
    have ⟨k, hk⟩ : n ∣ y := by exact Nat.dvd_of_mod_eq_zero h4
    have : k = 1 := by nlinarith
    simp [hk, this, hz_eq_n] at h_contra

  have hy_eq : y % n = y := by
    have hy_lt_n : y < n := by omega
    exact Nat.mod_eq_of_lt hy_lt_n

  have hz_eq : z % n = z := by
    have hz_lt_n : z < n := by
      omega
    exact Nat.mod_eq_of_lt hz_lt_n

  apply h_contra
  omega

end Example
