# Claim

Among seven distinct points on the unit sphere of ℝ³, the regular pentagonal bipyramid (five points on the equator at
angles 2πk/5, one at each pole) minimises the Coulomb energy

    E(x) = Σ_{i<j} ‖x_i − x_j‖⁻¹,

the minimum is E(P) = 1/2 + 5√2 + 5/(2 sin(π/5)) + 5/(2 sin(2π/5)) = 14.4529774142…, and every minimiser is the image of
the bipyramid under a linear isometry of ℝ³ and a relabelling of the points.

## Lean statement

From `formal/lean/ComparatorChallenges/ThomsonN7.lean` (lines 21–40 and 313–324), inside `namespace ThomsonN7`:

```lean
abbrev R3 := EuclideanSpace ℝ (Fin 3)

def SphereConfig (n : ℕ) : Set (Fin n → R3) :=
  {x | (∀ i, ‖x i‖ = 1) ∧ Function.Injective x}

noncomputable def coulombEnergy {n : ℕ} (x : Fin n → R3) : ℝ :=
  ∑ i : Fin n, ∑ j ∈ Finset.Ioi i, ‖x i - x j‖⁻¹

noncomputable def pentBipyramid : Fin 7 → R3 := fun i =>
  if (i : ℕ) < 5 then cyl 1 (2 * π * (i : ℕ) / 5) 0     -- ring, indices 0..4
  else if (i : ℕ) = 5 then cyl 0 0 1                     -- north pole
  else cyl 0 0 (-1)                                      -- south pole

theorem thomson_seven :
    ∀ x ∈ SphereConfig 7, coulombEnergy pentBipyramid ≤ coulombEnergy x

theorem thomson_seven_unique :
    ∀ x ∈ SphereConfig 7, coulombEnergy x = coulombEnergy pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i))
```

with `cyl ρ θ h = !₂[ρ cos θ, ρ sin θ, h]`. Injectivity in `SphereConfig` makes the points distinct; `Finset.Ioi i` counts
each unordered pair once; `g` ranges over all linear isometries, reflections included.

## Proof

Both theorems are proved in `formal/lean/ThomsonN7/Solution.lean` (17,895 lines, `import Mathlib` only, sha256
`6545e982abaeb4cae0a906c74ca51cc502621aa2a05783bb8da35d96493cc9ce`). Its first 310 lines are byte-identical to the
challenge file, and the two theorems close it (lines 17884–17893, docstrings omitted):

```lean
theorem thomson_seven :
    ∀ x ∈ SphereConfig 7, coulombEnergy pentBipyramid ≤ coulombEnergy x :=
  (Glue.seven_of_specs Final.a Final.K Final.hK Final.hcap Final.hslab).1

theorem thomson_seven_unique :
    ∀ x ∈ SphereConfig 7, coulombEnergy x = coulombEnergy pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, x i = g (pentBipyramid (σ i)) :=
  (Glue.seven_of_specs Final.a Final.K Final.hK Final.hcap Final.hslab).2
```

Axioms of both: `propext`, `Classical.choice`, `Quot.sound`.

The argument splits on the smallest pairwise inner product m:

| cell | method | margin |
|---|---|---|
| m ≥ −9/10 (Case 1) | degree-5 three-point semidefinite bound with a polynomial minorant | E ≥ E(P) + 3.2·10⁻⁴ |
| five slabs covering [−0.99, −0.90] | typed three-point bound, one certificate per slab | E ≥ E(P) + 2.6·10⁻⁶ |
| m ≤ −0.99 (cap) | typed three-point bound, then rigidity and exact second-order local minimality | equality only at the bipyramid |

Every certificate is exact integer or rational data checked in the Lean kernel. `paper/PAPER.md` gives the full argument
and `info/THEOREM_MAP.md` the Lean declaration for each step.
