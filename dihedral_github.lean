/-
Copyright (c) 2021 Alexander Griffin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexander Griffin.
-/
import group_theory.specific_groups.dihedral

/-!
# Dihedral Group Centers

In this file we prove which elements can and cannot
be members of the center of a (non-degenerate) dihedral group.

## Main results

- `sr_not_mem_center`: No reflection is central (if the group is non-degenerate).
- `r_not_mem_center`: Rotations with order greater than 2 are not central.
- `r_mem_center_r`: Rotations with order at most 2 commute with all rotations.
- `r_mem_center_sr`: Rotations with order at most 2 commute with all reflections.

## Notation

- `r i`: A rotation element of a dihedral group.
- `sr i`: A reflection element of a dihedral group.

## References

See the file for dihedral groups in mathlib.
-/

open dihedral_group

variables {n : ℕ}
variables {x : dihedral_group n}

namespace dihedral_github

/--
No reflection is central (if the group is non-degenerate).
`i` is any `zmod n`.
-/
lemma sr_not_mem_center [fact (n > 2)] (i : zmod n): ∃ x, sr i * x ≠ x * r i :=
  begin
    use (r 1),
  end

/--
Rotations with order greater than 2 are not central.
`i` is any `zmod n` term satisfying `2 * i ≠ 0`.
-/
theorem r_not_mem_center (i : zmod n): 2 * i ≠ 0 → ∃ x, r i * x ≠ x * r i :=
  begin
    intro h,
    use (sr 1),
    have : r i * sr 1 = sr (1 - i), by refl,
    rw this,
    have : sr 1 * r i = sr (1 + i), by refl,
    rw this,
    ring_nf,
    simp,
    rwa [eq_comm, ← sub_eq_zero, sub_neg_eq_add, ← two_mul],
  end

/--
Rotations with order at most 2 commute with all rotations.
`i` is any `zmod n` term satisfying `2 * i = 0`.
-/
theorem r_mem_center_r (i : zmod n): 2 * i = 0 → ∀ (j : zmod n), r i * r j = r j * r i :=
  begin
    intros h j,
    have : r i * r j = r (i + j), by refl,
    rw this,
    have : r j * r i = r (j + i), by refl,
    rw this,
    ring_nf,
    ring,
  end

/--
Rotations with order at most 2 commute with all reflections.
`i` is any `zmod n` term satisfying `2 * i = 0`.
-/
theorem r_mem_center_sr (i : zmod n): 2 * i = 0 → ∀ (j : zmod n), r i * sr j = sr j * r i :=
  begin
    intros h j,
    have : r i * sr j = sr (j - i), by refl,
    rw this,
    have : sr j * r i = sr (j + i), by refl,
    rw this,
    ring_nf,
    rw sub_eq_add_neg, congr,
    rwa [eq_comm, ← sub_eq_zero, sub_neg_eq_add, ← two_mul],
  end

end dihedral_github