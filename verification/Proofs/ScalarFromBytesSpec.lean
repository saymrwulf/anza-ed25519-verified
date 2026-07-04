/- Proofs/ScalarFromBytesSpec.lean — hash-to-scalar, the apex brick of the
   scalar layer: ⟦from_bytes_wide bytes⟧ = (LE 512-bit value) mod ℓ, the
   mathematical content of Scalar::from_hash after the (opaque) SHA-512.
   The pinned source factors from_bytes_wide → from_bytes_wide_parts →
   split_words_lo/hi (documented pure refactors) so every verification
   walk stays at the proven-cheap ~25-step scale and no walk motive ever
   carries a Montgomery call — the kernel-replay capacity lesson. -/
import Proofs.ScalarUnpackSpec
import Proofs.ScalarAddSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 600

namespace ScalarProofs

open Aeneas.Std.WP

/-- The 512-bit lo/hi split telescope (8 atomic words, isolated omega). -/
theorem wide_split_telescope (v0 v1 v2 v3 v4 v5 v6 v7 : ℕ)
    (h0 : v0 < 2^64) (h1 : v1 < 2^64) (h2 : v2 < 2^64) (h3 : v3 < 2^64)
    (h4 : v4 < 2^64) (h5 : v5 < 2^64) (h6 : v6 < 2^64) (h7 : v7 < 2^64) :
    (v0 % 2^52
      + 2^52  * ((v0 / 2^52 + 2^12 * (v1 % 2^52)) % 2^52)
      + 2^104 * ((v1 / 2^40 + 2^24 * (v2 % 2^40)) % 2^52)
      + 2^156 * ((v2 / 2^28 + 2^36 * (v3 % 2^28)) % 2^52)
      + 2^208 * ((v3 / 2^16 + 2^48 * (v4 % 2^16)) % 2^52))
    + 2^260 *
      ((v4 / 2^4 % 2^52)
      + 2^52  * ((v4 / 2^56 + 2^8  * (v5 % 2^56)) % 2^52)
      + 2^104 * ((v5 / 2^44 + 2^20 * (v6 % 2^44)) % 2^52)
      + 2^156 * ((v6 / 2^32 + 2^32 * (v7 % 2^32)) % 2^52)
      + 2^208 * (v7 / 2^20 % 2^52))
    = v0 + 2^64 * v1 + 2^128 * v2 + 2^192 * v3 + 2^256 * v4
      + 2^320 * v5 + 2^384 * v6 + 2^448 * v7 := by
  omega

/-- The lo-half 52-bit split: exact div/mod value per limb. -/
theorem split_words_lo_spec (words : Std.Array Std.U64 8#usize)
    (v0 v1 v2 v3 v4 v5 v6 v7 : U64)
    (hwsl : (↑words : List U64) = [v0, v1, v2, v3, v4, v5, v6, v7]) :
    backend.serial.u64.scalar.Scalar52.split_words_lo words
      ⦃ s => ∃ i2 i7 i12 i17 i22 : U64,
          (↑s : List U64) = [i2, i7, i12, i17, i22] ∧
          i2.val = v0.val % 2^52 ∧
          i7.val = (v0.val / 2^52 + 2^12 * (v1.val % 2^52)) % 2^52 ∧
          i12.val = (v1.val / 2^40 + 2^24 * (v2.val % 2^40)) % 2^52 ∧
          i17.val = (v2.val / 2^28 + 2^36 * (v3.val % 2^28)) % 2^52 ∧
          i22.val = (v3.val / 2^16 + 2^48 * (v4.val % 2^16)) % 2^52 ⦄ := by
  have hsz64 : (U64.size : ℕ) = 2^64 := by scalar_tac
  unfold backend.serial.u64.scalar.Scalar52.split_words_lo
  have hvb0 : v0.val < 2^64 := by scalar_tac
  have hvb1 : v1.val < 2^64 := by scalar_tac
  have hvb2 : v2.val < 2^64 := by scalar_tac
  have hvb3 : v3.val < 2^64 := by scalar_tac
  have hvb4 : v4.val < 2^64 := by scalar_tac
  have hvb5 : v5.val < 2^64 := by scalar_tac
  have hvb6 : v6.val < 2^64 := by scalar_tac
  have hvb7 : v7.val < 2^64 := by scalar_tac
  step as ⟨sh, hsh⟩
  step as ⟨mask, hmask⟩
  have hmaskv : mask.val = 2^52 - 1 := by
    simp [hmask, hsh, U64.size_def, U64.numBits]
  step as ⟨i1, hi1⟩
  simp [hwsl] at hi1
  have hi1v : i1.val = v0.val := by rw [hi1]
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = (v0.val) % 2^52 := by
    rw [hi2, UScalar.val_and, hmaskv, hi1v, nat_and_mask52]
  step as ⟨i3, hi3⟩
  have hi3v : i3.val = v0.val / 2^52 := by
    rw [hi3, hi1v, Nat.shiftRight_eq_div_pow]
  step as ⟨i4, hi4⟩
  simp [hwsl] at hi4
  have hi4v : i4.val = v1.val := by rw [hi4]
  step as ⟨i5, hi5⟩
  have hi5v : i5.val = 2^12 * (v1.val % 2^52) := by
    rw [hi5]
    simp [hi4v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨i6, hi6⟩
  have hi6add : i3.val ||| i5.val = i3.val + i5.val := by
    have hlt : i3.val < 2^12 := by rw [hi3v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := i3.val) (i := 12) hlt (v1.val % 2^52)
    calc i3.val ||| i5.val
        = i3.val ||| 2^12 * (v1.val % 2^52) := by rw [hi5v]
      _ = 2^12 * (v1.val % 2^52) ||| i3.val := Nat.lor_comm _ _
      _ = 2^12 * (v1.val % 2^52) + i3.val := hor.symm
      _ = i3.val + i5.val := by rw [hi5v]; ring
  have hi6v : i6.val = v0.val / 2^52 + 2^12 * (v1.val % 2^52) := by
    rw [hi6, UScalar.val_or, hi6add, hi3v, hi5v]
  step as ⟨i7, hi7⟩
  have hi7v : i7.val = (v0.val / 2^52 + 2^12 * (v1.val % 2^52)) % 2^52 := by
    rw [hi7, UScalar.val_and, hmaskv, hi6v, nat_and_mask52]
  step as ⟨i8, hi8⟩
  have hi8v : i8.val = v1.val / 2^40 := by
    rw [hi8, hi4v, Nat.shiftRight_eq_div_pow]
  step as ⟨i9, hi9⟩
  simp [hwsl] at hi9
  have hi9v : i9.val = v2.val := by rw [hi9]
  step as ⟨i10, hi10⟩
  have hi10v : i10.val = 2^24 * (v2.val % 2^40) := by
    rw [hi10]
    simp [hi9v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨i11, hi11⟩
  have hi11add : i8.val ||| i10.val = i8.val + i10.val := by
    have hlt : i8.val < 2^24 := by rw [hi8v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := i8.val) (i := 24) hlt (v2.val % 2^40)
    calc i8.val ||| i10.val
        = i8.val ||| 2^24 * (v2.val % 2^40) := by rw [hi10v]
      _ = 2^24 * (v2.val % 2^40) ||| i8.val := Nat.lor_comm _ _
      _ = 2^24 * (v2.val % 2^40) + i8.val := hor.symm
      _ = i8.val + i10.val := by rw [hi10v]; ring
  have hi11v : i11.val = v1.val / 2^40 + 2^24 * (v2.val % 2^40) := by
    rw [hi11, UScalar.val_or, hi11add, hi8v, hi10v]
  step as ⟨i12, hi12⟩
  have hi12v : i12.val = (v1.val / 2^40 + 2^24 * (v2.val % 2^40)) % 2^52 := by
    rw [hi12, UScalar.val_and, hmaskv, hi11v, nat_and_mask52]
  step as ⟨i13, hi13⟩
  have hi13v : i13.val = v2.val / 2^28 := by
    rw [hi13, hi9v, Nat.shiftRight_eq_div_pow]
  step as ⟨i14, hi14⟩
  simp [hwsl] at hi14
  have hi14v : i14.val = v3.val := by rw [hi14]
  step as ⟨i15, hi15⟩
  have hi15v : i15.val = 2^36 * (v3.val % 2^28) := by
    rw [hi15]
    simp [hi14v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨i16, hi16⟩
  have hi16add : i13.val ||| i15.val = i13.val + i15.val := by
    have hlt : i13.val < 2^36 := by rw [hi13v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := i13.val) (i := 36) hlt (v3.val % 2^28)
    calc i13.val ||| i15.val
        = i13.val ||| 2^36 * (v3.val % 2^28) := by rw [hi15v]
      _ = 2^36 * (v3.val % 2^28) ||| i13.val := Nat.lor_comm _ _
      _ = 2^36 * (v3.val % 2^28) + i13.val := hor.symm
      _ = i13.val + i15.val := by rw [hi15v]; ring
  have hi16v : i16.val = v2.val / 2^28 + 2^36 * (v3.val % 2^28) := by
    rw [hi16, UScalar.val_or, hi16add, hi13v, hi15v]
  step as ⟨i17, hi17⟩
  have hi17v : i17.val = (v2.val / 2^28 + 2^36 * (v3.val % 2^28)) % 2^52 := by
    rw [hi17, UScalar.val_and, hmaskv, hi16v, nat_and_mask52]
  step as ⟨i18, hi18⟩
  have hi18v : i18.val = v3.val / 2^16 := by
    rw [hi18, hi14v, Nat.shiftRight_eq_div_pow]
  step as ⟨i19, hi19⟩
  simp [hwsl] at hi19
  have hi19v : i19.val = v4.val := by rw [hi19]
  step as ⟨i20, hi20⟩
  have hi20v : i20.val = 2^48 * (v4.val % 2^16) := by
    rw [hi20]
    simp [hi19v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨i21, hi21⟩
  have hi21add : i18.val ||| i20.val = i18.val + i20.val := by
    have hlt : i18.val < 2^48 := by rw [hi18v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := i18.val) (i := 48) hlt (v4.val % 2^16)
    calc i18.val ||| i20.val
        = i18.val ||| 2^48 * (v4.val % 2^16) := by rw [hi20v]
      _ = 2^48 * (v4.val % 2^16) ||| i18.val := Nat.lor_comm _ _
      _ = 2^48 * (v4.val % 2^16) + i18.val := hor.symm
      _ = i18.val + i20.val := by rw [hi20v]; ring
  have hi21v : i21.val = v3.val / 2^16 + 2^48 * (v4.val % 2^16) := by
    rw [hi21, UScalar.val_or, hi21add, hi18v, hi20v]
  step as ⟨i22, hi22⟩
  have hi22v : i22.val = (v3.val / 2^16 + 2^48 * (v4.val % 2^16)) % 2^52 := by
    rw [hi22, UScalar.val_and, hmaskv, hi21v, nat_and_mask52]
  have hlist : (↑(Array.make 5#usize [ i2, i7, i12, i17, i22 ]) : List U64) = [i2, i7, i12, i17, i22] := by rfl
  try simp only [spec_ok]
  exact ⟨i2, i7, i12, i17, i22, hlist, hi2v, hi7v, hi12v, hi17v, hi22v⟩

/-- The hi-half 52-bit split: exact div/mod value per limb. -/
theorem split_words_hi_spec (words : Std.Array Std.U64 8#usize)
    (v0 v1 v2 v3 v4 v5 v6 v7 : U64)
    (hwsl : (↑words : List U64) = [v0, v1, v2, v3, v4, v5, v6, v7]) :
    backend.serial.u64.scalar.Scalar52.split_words_hi words
      ⦃ s => ∃ i3 i8 i13 i18 i20 : U64,
          (↑s : List U64) = [i3, i8, i13, i18, i20] ∧
          i3.val = v4.val / 2^4 % 2^52 ∧
          i8.val = (v4.val / 2^56 + 2^8 * (v5.val % 2^56)) % 2^52 ∧
          i13.val = (v5.val / 2^44 + 2^20 * (v6.val % 2^44)) % 2^52 ∧
          i18.val = (v6.val / 2^32 + 2^32 * (v7.val % 2^32)) % 2^52 ∧
          i20.val = v7.val / 2^20 % 2^52 ⦄ := by
  have hsz64 : (U64.size : ℕ) = 2^64 := by scalar_tac
  unfold backend.serial.u64.scalar.Scalar52.split_words_hi
  have hvb0 : v0.val < 2^64 := by scalar_tac
  have hvb1 : v1.val < 2^64 := by scalar_tac
  have hvb2 : v2.val < 2^64 := by scalar_tac
  have hvb3 : v3.val < 2^64 := by scalar_tac
  have hvb4 : v4.val < 2^64 := by scalar_tac
  have hvb5 : v5.val < 2^64 := by scalar_tac
  have hvb6 : v6.val < 2^64 := by scalar_tac
  have hvb7 : v7.val < 2^64 := by scalar_tac
  step as ⟨sh, hsh⟩
  step as ⟨mask, hmask⟩
  have hmaskv : mask.val = 2^52 - 1 := by
    simp [hmask, hsh, U64.size_def, U64.numBits]
  step as ⟨i1, hi1⟩
  simp [hwsl] at hi1
  have hi1v : i1.val = v4.val := by rw [hi1]
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = v4.val / 2^4 := by
    rw [hi2, hi1v, Nat.shiftRight_eq_div_pow]
  step as ⟨i3, hi3⟩
  have hi3v : i3.val = (v4.val / 2^4) % 2^52 := by
    rw [hi3, UScalar.val_and, hmaskv, hi2v, nat_and_mask52]
  step as ⟨i4, hi4⟩
  have hi4v : i4.val = v4.val / 2^56 := by
    rw [hi4, hi1v, Nat.shiftRight_eq_div_pow]
  step as ⟨i5, hi5⟩
  simp [hwsl] at hi5
  have hi5v : i5.val = v5.val := by rw [hi5]
  step as ⟨i6, hi6⟩
  have hi6v : i6.val = 2^8 * (v5.val % 2^56) := by
    rw [hi6]
    simp [hi5v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨i7, hi7⟩
  have hi7add : i4.val ||| i6.val = i4.val + i6.val := by
    have hlt : i4.val < 2^8 := by rw [hi4v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := i4.val) (i := 8) hlt (v5.val % 2^56)
    calc i4.val ||| i6.val
        = i4.val ||| 2^8 * (v5.val % 2^56) := by rw [hi6v]
      _ = 2^8 * (v5.val % 2^56) ||| i4.val := Nat.lor_comm _ _
      _ = 2^8 * (v5.val % 2^56) + i4.val := hor.symm
      _ = i4.val + i6.val := by rw [hi6v]; ring
  have hi7v : i7.val = v4.val / 2^56 + 2^8 * (v5.val % 2^56) := by
    rw [hi7, UScalar.val_or, hi7add, hi4v, hi6v]
  step as ⟨i8, hi8⟩
  have hi8v : i8.val = (v4.val / 2^56 + 2^8 * (v5.val % 2^56)) % 2^52 := by
    rw [hi8, UScalar.val_and, hmaskv, hi7v, nat_and_mask52]
  step as ⟨i9, hi9⟩
  have hi9v : i9.val = v5.val / 2^44 := by
    rw [hi9, hi5v, Nat.shiftRight_eq_div_pow]
  step as ⟨i10, hi10⟩
  simp [hwsl] at hi10
  have hi10v : i10.val = v6.val := by rw [hi10]
  step as ⟨i11, hi11⟩
  have hi11v : i11.val = 2^20 * (v6.val % 2^44) := by
    rw [hi11]
    simp [hi10v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨i12, hi12⟩
  have hi12add : i9.val ||| i11.val = i9.val + i11.val := by
    have hlt : i9.val < 2^20 := by rw [hi9v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := i9.val) (i := 20) hlt (v6.val % 2^44)
    calc i9.val ||| i11.val
        = i9.val ||| 2^20 * (v6.val % 2^44) := by rw [hi11v]
      _ = 2^20 * (v6.val % 2^44) ||| i9.val := Nat.lor_comm _ _
      _ = 2^20 * (v6.val % 2^44) + i9.val := hor.symm
      _ = i9.val + i11.val := by rw [hi11v]; ring
  have hi12v : i12.val = v5.val / 2^44 + 2^20 * (v6.val % 2^44) := by
    rw [hi12, UScalar.val_or, hi12add, hi9v, hi11v]
  step as ⟨i13, hi13⟩
  have hi13v : i13.val = (v5.val / 2^44 + 2^20 * (v6.val % 2^44)) % 2^52 := by
    rw [hi13, UScalar.val_and, hmaskv, hi12v, nat_and_mask52]
  step as ⟨i14, hi14⟩
  have hi14v : i14.val = v6.val / 2^32 := by
    rw [hi14, hi10v, Nat.shiftRight_eq_div_pow]
  step as ⟨i15, hi15⟩
  simp [hwsl] at hi15
  have hi15v : i15.val = v7.val := by rw [hi15]
  step as ⟨i16, hi16⟩
  have hi16v : i16.val = 2^32 * (v7.val % 2^32) := by
    rw [hi16]
    simp [hi15v, Nat.shiftLeft_eq, hsz64]
    omega
  step as ⟨i17, hi17⟩
  have hi17add : i14.val ||| i16.val = i14.val + i16.val := by
    have hlt : i14.val < 2^32 := by rw [hi14v]; omega
    have hor := Nat.two_pow_add_eq_or_of_lt (b := i14.val) (i := 32) hlt (v7.val % 2^32)
    calc i14.val ||| i16.val
        = i14.val ||| 2^32 * (v7.val % 2^32) := by rw [hi16v]
      _ = 2^32 * (v7.val % 2^32) ||| i14.val := Nat.lor_comm _ _
      _ = 2^32 * (v7.val % 2^32) + i14.val := hor.symm
      _ = i14.val + i16.val := by rw [hi16v]; ring
  have hi17v : i17.val = v6.val / 2^32 + 2^32 * (v7.val % 2^32) := by
    rw [hi17, UScalar.val_or, hi17add, hi14v, hi16v]
  step as ⟨i18, hi18⟩
  have hi18v : i18.val = (v6.val / 2^32 + 2^32 * (v7.val % 2^32)) % 2^52 := by
    rw [hi18, UScalar.val_and, hmaskv, hi17v, nat_and_mask52]
  step as ⟨i19, hi19⟩
  have hi19v : i19.val = v7.val / 2^20 := by
    rw [hi19, hi15v, Nat.shiftRight_eq_div_pow]
  step as ⟨i20, hi20⟩
  have hi20v : i20.val = (v7.val / 2^20) % 2^52 := by
    rw [hi20, UScalar.val_and, hmaskv, hi19v, nat_and_mask52]
  have hlist : (↑(Array.make 5#usize [ i3, i8, i13, i18, i20 ]) : List U64) = [i3, i8, i13, i18, i20] := by rfl
  try simp only [spec_ok]
  exact ⟨i3, i8, i13, i18, i20, hlist, hi3v, hi8v, hi13v, hi18v, hi20v⟩

/-- The prefix: bytes → words (bytes_unpack_spec) → the lo/hi pair. -/
theorem fbw_parts_spec (bytes : Std.Array Std.U8 64#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (hb : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63]) :
    backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts bytes
      ⦃ p => ∃ v0 v1 v2 v3 v4 v5 v6 v7 i2 i7 i12 i17 i22 h0 h1 h2 h3 h4 : U64,
          (↑p.1 : List U64) = [i2, i7, i12, i17, i22] ∧
          (↑p.2 : List U64) = [h0, h1, h2, h3, h4] ∧
          v0.val = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 ∧
          v1.val = b8.val + b9.val * 2^8 + b10.val * 2^16 + b11.val * 2^24 + b12.val * 2^32 + b13.val * 2^40 + b14.val * 2^48 + b15.val * 2^56 ∧
          v2.val = b16.val + b17.val * 2^8 + b18.val * 2^16 + b19.val * 2^24 + b20.val * 2^32 + b21.val * 2^40 + b22.val * 2^48 + b23.val * 2^56 ∧
          v3.val = b24.val + b25.val * 2^8 + b26.val * 2^16 + b27.val * 2^24 + b28.val * 2^32 + b29.val * 2^40 + b30.val * 2^48 + b31.val * 2^56 ∧
          v4.val = b32.val + b33.val * 2^8 + b34.val * 2^16 + b35.val * 2^24 + b36.val * 2^32 + b37.val * 2^40 + b38.val * 2^48 + b39.val * 2^56 ∧
          v5.val = b40.val + b41.val * 2^8 + b42.val * 2^16 + b43.val * 2^24 + b44.val * 2^32 + b45.val * 2^40 + b46.val * 2^48 + b47.val * 2^56 ∧
          v6.val = b48.val + b49.val * 2^8 + b50.val * 2^16 + b51.val * 2^24 + b52.val * 2^32 + b53.val * 2^40 + b54.val * 2^48 + b55.val * 2^56 ∧
          v7.val = b56.val + b57.val * 2^8 + b58.val * 2^16 + b59.val * 2^24 + b60.val * 2^32 + b61.val * 2^40 + b62.val * 2^48 + b63.val * 2^56 ∧
          i2.val = v0.val % 2^52 ∧
          i7.val = (v0.val / 2^52 + 2^12 * (v1.val % 2^52)) % 2^52 ∧
          i12.val = (v1.val / 2^40 + 2^24 * (v2.val % 2^40)) % 2^52 ∧
          i17.val = (v2.val / 2^28 + 2^36 * (v3.val % 2^28)) % 2^52 ∧
          i22.val = (v3.val / 2^16 + 2^48 * (v4.val % 2^16)) % 2^52 ∧
          h0.val = v4.val / 2^4 % 2^52 ∧
          h1.val = (v4.val / 2^56 + 2^8 * (v5.val % 2^56)) % 2^52 ∧
          h2.val = (v5.val / 2^44 + 2^20 * (v6.val % 2^44)) % 2^52 ∧
          h3.val = (v6.val / 2^32 + 2^32 * (v7.val % 2^32)) % 2^52 ∧
          h4.val = v7.val / 2^20 % 2^52 ⦄ := by
  unfold backend.serial.u64.scalar.Scalar52.from_bytes_wide_parts
  have hrep : (↑(Array.repeat 8#usize 0#u64) : List U64)
      = [0#u64, 0#u64, 0#u64, 0#u64, 0#u64, 0#u64, 0#u64, 0#u64] := by rfl
  step with (bytes_unpack_spec bytes (Array.repeat 8#usize 0#u64)
    b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63
    0#u64 0#u64 0#u64 0#u64 0#u64 0#u64 0#u64 0#u64 hb hrep
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) as
    ⟨v0, v1, v2, v3, v4, v5, v6, v7, ws, hwsl, hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7⟩
  step with (split_words_lo_spec ws v0 v1 v2 v3 v4 v5 v6 v7 hwsl) as
    ⟨i2, i7, i12, i17, i22, slo, hlol, hi2v, hi7v, hi12v, hi17v, hi22v⟩
  step with (split_words_hi_spec ws v0 v1 v2 v3 v4 v5 v6 v7 hwsl) as
    ⟨i3, i8, i13, i18, i20, shi, hhil, hi3v, hi8v, hi13v, hi18v, hi20v⟩
  try simp only [spec_ok]
  exact ⟨v0, v1, v2, v3, v4, v5, v6, v7, i2, i7, i12, i17, i22, i3, i8, i13, i18, i20,
    hlol, hhil, hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7,
    hi2v, hi7v, hi12v, hi17v, hi22v, hi3v, hi8v, hi13v, hi18v, hi20v⟩

/-- **Hash-to-scalar is exact reduction mod ℓ.** -/
theorem from_bytes_wide_spec (bytes : Std.Array Std.U8 64#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 : Std.U8)
    (hb : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b61, b62, b63])
    (T : ℕ) (hT : T = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88 + b12.val * 2^96 + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120 + b16.val * 2^128 + b17.val * 2^136 + b18.val * 2^144 + b19.val * 2^152 + b20.val * 2^160 + b21.val * 2^168 + b22.val * 2^176 + b23.val * 2^184 + b24.val * 2^192 + b25.val * 2^200 + b26.val * 2^208 + b27.val * 2^216 + b28.val * 2^224 + b29.val * 2^232 + b30.val * 2^240 + b31.val * 2^248 + b32.val * 2^256 + b33.val * 2^264 + b34.val * 2^272 + b35.val * 2^280 + b36.val * 2^288 + b37.val * 2^296 + b38.val * 2^304 + b39.val * 2^312 + b40.val * 2^320 + b41.val * 2^328 + b42.val * 2^336 + b43.val * 2^344 + b44.val * 2^352 + b45.val * 2^360 + b46.val * 2^368 + b47.val * 2^376 + b48.val * 2^384 + b49.val * 2^392 + b50.val * 2^400 + b51.val * 2^408 + b52.val * 2^416 + b53.val * 2^424 + b54.val * 2^432 + b55.val * 2^440 + b56.val * 2^448 + b57.val * 2^456 + b58.val * 2^464 + b59.val * 2^472 + b60.val * 2^480 + b61.val * 2^488 + b62.val * 2^496 + b63.val * 2^504) :
    backend.serial.u64.scalar.Scalar52.from_bytes_wide bytes
      ⦃ r => (∃ s0 s1 s2 s3 s4 : U64, (↑r : List U64) = [s0, s1, s2, s3, s4] ∧
              s0.val < 2^52 ∧ s1.val < 2^52 ∧ s2.val < 2^52 ∧ s3.val < 2^52 ∧
              s4.val < 2^52) ∧
            scVal r < Ell ∧
            scDenote r = (T : ZMod Ell) ⦄ := by
  unfold backend.serial.u64.scalar.Scalar52.from_bytes_wide
  apply spec_bind (fbw_parts_spec bytes b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33 b34 b35 b36 b37 b38 b39 b40 b41 b42 b43 b44 b45 b46 b47 b48 b49 b50 b51 b52 b53 b54 b55 b56 b57 b58 b59 b60 b61 b62 b63 hb)
  rintro ⟨lo, hi⟩ ⟨v0, v1, v2, v3, v4, v5, v6, v7, i2, i7, i12, i17, i22, i3, i8, i13, i18, i20,
    hlol, hhil, hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7,
    hi2v, hi7v, hi12v, hi17v, hi22v, hi3v, hi8v, hi13v, hi18v, hi20v⟩
  simp only at hlol hhil
  have hvb0 : v0.val < 2^64 := by scalar_tac
  have hvb1 : v1.val < 2^64 := by scalar_tac
  have hvb2 : v2.val < 2^64 := by scalar_tac
  have hvb3 : v3.val < 2^64 := by scalar_tac
  have hvb4 : v4.val < 2^64 := by scalar_tac
  have hvb5 : v5.val < 2^64 := by scalar_tac
  have hvb6 : v6.val < 2^64 := by scalar_tac
  have hvb7 : v7.val < 2^64 := by scalar_tac
  have hbndi2 : i2.val < 2^52 := by
    rw [hi2v]; exact Nat.mod_lt _ (by norm_num)
  have hbndi7 : i7.val < 2^52 := by
    rw [hi7v]; exact Nat.mod_lt _ (by norm_num)
  have hbndi12 : i12.val < 2^52 := by
    rw [hi12v]; exact Nat.mod_lt _ (by norm_num)
  have hbndi17 : i17.val < 2^52 := by
    rw [hi17v]; exact Nat.mod_lt _ (by norm_num)
  have hbndi22 : i22.val < 2^52 := by
    rw [hi22v]; exact Nat.mod_lt _ (by norm_num)
  have hbndi3 : i3.val < 2^52 := by
    rw [hi3v]; exact Nat.mod_lt _ (by norm_num)
  have hbndi8 : i8.val < 2^52 := by
    rw [hi8v]; exact Nat.mod_lt _ (by norm_num)
  have hbndi13 : i13.val < 2^52 := by
    rw [hi13v]; exact Nat.mod_lt _ (by norm_num)
  have hbndi18 : i18.val < 2^52 := by
    rw [hi18v]; exact Nat.mod_lt _ (by norm_num)
  have hbndi20 : i20.val < 2^52 := by
    rw [hi20v]; exact Nat.mod_lt _ (by norm_num)
  have hlov : scVal lo = scLimbs i2 i7 i12 i17 i22 := scVal_eq _ _ _ _ _ _ hlol
  have hhiv : scVal hi = scLimbs i3 i8 i13 i18 i20 := scVal_eq _ _ _ _ _ _ hhil
  have hlolt : scVal lo < 2^260 := by
    rw [hlov]; unfold scLimbs
    exact nonce_sum_bound hbndi2 hbndi7 hbndi12 hbndi17 hbndi22
  have hhilt : scVal hi < 2^260 := by
    rw [hhiv]; unfold scLimbs
    exact nonce_sum_bound hbndi3 hbndi8 hbndi13 hbndi18 hbndi20
  have hcablo : scVal lo * scVal backend.serial.u64.constants.R < 2^260 * Ell :=
    Nat.mul_lt_mul'' hlolt R_lt
  have hcabhi : scVal hi * scVal backend.serial.u64.constants.RR < 2^260 * Ell :=
    Nat.mul_lt_mul'' hhilt RR_lt
  have hRl0 : (4302102966953709#u64).val = 4302102966953709 := by rfl
  have hRl1 : (1049714374468698#u64).val = 1049714374468698 := by rfl
  have hRl2 : (4503599278581019#u64).val = 4503599278581019 := by rfl
  have hRl3 : (4503599627370495#u64).val = 4503599627370495 := by rfl
  have hRl4 : (17592186044415#u64).val = 17592186044415 := by rfl
  have hRRl0 : (2764609938444603#u64).val = 2764609938444603 := by rfl
  have hRRl1 : (3768881411696287#u64).val = 3768881411696287 := by rfl
  have hRRl2 : (1616719297148420#u64).val = 1616719297148420 := by rfl
  have hRRl3 : (1087343033131391#u64).val = 1087343033131391 := by rfl
  have hRRl4 : (10175238647962#u64).val = 10175238647962 := by rfl
  step with (montgomery_mul_spec lo backend.serial.u64.constants.R
    i2 i7 i12 i17 i22
    (4302102966953709#u64) (1049714374468698#u64) (4503599278581019#u64)
    (4503599627370495#u64) (17592186044415#u64)
    hlol R_limbs
    ⟨hbndi2, hbndi7, hbndi12, hbndi17, hbndi22⟩
    ⟨by rw [hRl0]; norm_num, by rw [hRl1]; norm_num, by rw [hRl2]; norm_num,
     by rw [hRl3]; norm_num, by rw [hRl4]; norm_num⟩
    hcablo) as ⟨lo1, hlo1ex, hlo1c, hlo1d⟩
  obtain ⟨p0, p1, p2, p3, p4, hlo1l, hp0, hp1, hp2, hp3, hp4⟩ := hlo1ex
  step with (montgomery_mul_spec hi backend.serial.u64.constants.RR
    i3 i8 i13 i18 i20
    (2764609938444603#u64) (3768881411696287#u64) (1616719297148420#u64)
    (1087343033131391#u64) (10175238647962#u64)
    hhil RR_limbs
    ⟨hbndi3, hbndi8, hbndi13, hbndi18, hbndi20⟩
    ⟨by rw [hRRl0]; norm_num, by rw [hRRl1]; norm_num, by rw [hRRl2]; norm_num,
     by rw [hRRl3]; norm_num, by rw [hRRl4]; norm_num⟩
    hcabhi) as ⟨hi1, hhi1ex, hhi1c, hhi1d⟩
  obtain ⟨q0, q1, q2, q3, q4, hhi1l, hq0, hq1, hq2, hq3, hq4⟩ := hhi1ex
  apply spec_mono (add_val_spec hi1 lo1 q0 q1 q2 q3 q4 p0 p1 p2 p3 p4 hhi1l hlo1l
    ⟨hq0, hq1, hq2, hq3, hq4⟩ ⟨hp0, hp1, hp2, hp3, hp4⟩ hhi1c hlo1c)
  intro r hr
  refine ⟨hr.1, hr.2.1, ?_⟩
  rw [hr.2.2]
  have hRd : scDenote backend.serial.u64.constants.R = 2^260 := by
    simp only [scDenote, R_scVal]; exact R_denote
  have hRRd : scDenote backend.serial.u64.constants.RR = 2^520 := by
    simp only [scDenote, RR_scVal]; exact RR_denote
  have hlo1v : scDenote lo1 = scDenote lo :=
    R_isUnit.mul_right_cancel (by rw [hlo1d, hRd])
  have hhi1v : scDenote hi1 = scDenote hi * 2^260 :=
    R_isUnit.mul_right_cancel (by rw [hhi1d, hRRd]; ring)
  have hLOv : scVal lo = v0.val % 2^52 + 2^52 * ((v0.val / 2^52 + 2^12 * (v1.val % 2^52)) % 2^52) + 2^104 * ((v1.val / 2^40 + 2^24 * (v2.val % 2^40)) % 2^52) + 2^156 * ((v2.val / 2^28 + 2^36 * (v3.val % 2^28)) % 2^52) + 2^208 * ((v3.val / 2^16 + 2^48 * (v4.val % 2^16)) % 2^52) := by
    rw [hlov]; unfold scLimbs
    rw [hi2v, hi7v, hi12v, hi17v, hi22v]
  have hHIv : scVal hi = v4.val / 2^4 % 2^52 + 2^52 * ((v4.val / 2^56 + 2^8 * (v5.val % 2^56)) % 2^52) + 2^104 * ((v5.val / 2^44 + 2^20 * (v6.val % 2^44)) % 2^52) + 2^156 * ((v6.val / 2^32 + 2^32 * (v7.val % 2^32)) % 2^52) + 2^208 * (v7.val / 2^20 % 2^52) := by
    rw [hhiv]; unfold scLimbs
    rw [hi3v, hi8v, hi13v, hi18v, hi20v]
  have htel := wide_split_telescope v0.val v1.val v2.val v3.val v4.val v5.val
    v6.val v7.val hvb0 hvb1 hvb2 hvb3 hvb4 hvb5 hvb6 hvb7
  have hVB : v0.val + 2^64 * v1.val + 2^128 * v2.val + 2^192 * v3.val + 2^256 * v4.val + 2^320 * v5.val + 2^384 * v6.val + 2^448 * v7.val
      = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88 + b12.val * 2^96 + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120 + b16.val * 2^128 + b17.val * 2^136 + b18.val * 2^144 + b19.val * 2^152 + b20.val * 2^160 + b21.val * 2^168 + b22.val * 2^176 + b23.val * 2^184 + b24.val * 2^192 + b25.val * 2^200 + b26.val * 2^208 + b27.val * 2^216 + b28.val * 2^224 + b29.val * 2^232 + b30.val * 2^240 + b31.val * 2^248 + b32.val * 2^256 + b33.val * 2^264 + b34.val * 2^272 + b35.val * 2^280 + b36.val * 2^288 + b37.val * 2^296 + b38.val * 2^304 + b39.val * 2^312 + b40.val * 2^320 + b41.val * 2^328 + b42.val * 2^336 + b43.val * 2^344 + b44.val * 2^352 + b45.val * 2^360 + b46.val * 2^368 + b47.val * 2^376 + b48.val * 2^384 + b49.val * 2^392 + b50.val * 2^400 + b51.val * 2^408 + b52.val * 2^416 + b53.val * 2^424 + b54.val * 2^432 + b55.val * 2^440 + b56.val * 2^448 + b57.val * 2^456 + b58.val * 2^464 + b59.val * 2^472 + b60.val * 2^480 + b61.val * 2^488 + b62.val * 2^496 + b63.val * 2^504 := by
    rw [hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7]; ring
  have hT2 : T = 2^260 * scVal hi + scVal lo := by
    rw [hT, ← hVB, hHIv, hLOv, ← htel]
    exact Nat.add_comm _ _
  rw [hhi1v, hlo1v, hT2]
  simp only [scDenote]
  push_cast
  ring

end ScalarProofs
