# dihedral-center-suggestion
Some proofs that determine which elements can and cannot be in the center of a (non-degenerate) [dihedral group][wiki:dg].

To see how dihedral groups are implemented in Lean, see [their mathlib file][mathlib:dg].

There are four results that are to be included:

- `sr_not_mem_center`: No reflection is central (if the group is non-degenerate).
- `r_not_mem_center`: Rotations with order greater than 2 are not central.
- `r_mem_center_r`: Rotations with order at most 2 commute with all rotations.
- `r_mem_center_sr`: Rotations with order at most 2 commute with all reflections.

[wiki:dg]: https://en.wikipedia.org/wiki/Dihedral_group
[mathlib:dg]: https://github.com/leanprover-community/mathlib/blob/master/src/group_theory/specific_groups/dihedral.lean
