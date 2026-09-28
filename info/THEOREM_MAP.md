# Theorem map: informal claim to Lean declaration

All line numbers refer to `formal/lean/ThomsonN7/Solution.lean` (17,895 lines, sha256 `6545e982…9cc9ce`). The "Meaning" column is a one-line reading of each declaration. Only the two final theorems are the claim; everything else is proof machinery.

## The claim (lines 1-310 are the Challenge preamble; the two theorems are at the end)

| Informal | Lean | Line |
|---|---|---|
| unit-sphere configurations of `n` distinct points | `ThomsonN7.SphereConfig n` (norm 1 and injective) | 25 |
| Coulomb energy `Σ_{i<j} 1/‖x_i − x_j‖` | `ThomsonN7.coulombEnergy` (uses `‖·‖⁻¹`, hence injectivity in `SphereConfig`) | 29 |
| the regular pentagonal bipyramid | `ThomsonN7.pentBipyramid : Fin 7 → ℝ³` (5 equatorial points at `2πk/5`, two poles) | 37 |
| **it minimises the energy** | `ThomsonN7.thomson_seven` | 17884 |
| **and it is the only minimiser up to `O(3)` and relabelling** | `ThomsonN7.thomson_seven_unique` | 17890 |

## The proof spine (assembled by `Glue.seven_of_specs`, line 12804)

| Step | Lean | Line | Meaning |
|---|---|---|---|
| assemble everything | `Glue.seven_of_specs` | 12804 | Case 1 + cap + slabs ⇒ both statements |
| slab parameters | `Final.a`, `Final.K`, `Final.hslab`, `Final.hcap` | 17850, …, 17863, 17873 | the cuts −0.99, −0.98, −0.96, −0.94, −0.93, −0.90 and the data the glue consumes |
| Case 1 (all inner products ≥ −9/10) | `Case1.case1_margin` | 10495 | `E ≥ E(P) + 3/10000`; uses the kernel check `Case1.cf_ok` (10288, split into 13 pieces at 10385-10487) |
| the three-point positivity machinery | namespace `ThreePoint` | 515-1582 | Bachoc–Vallentin type bound on `S²`, addition theorem, symmetrisation |
| certificate soundness | `capSpec_sound`, `slabSpec_sound` | 12729, 12750 | a checked certificate object implies the energy bound |
| Case 2 reduction | `Glue1.exists_minpair_perm` | 12006 | relabel so that the smallest inner product is `⟨y0, y1⟩` |
| gauge (Procrustes) lemma | `Reg.exists_gauge` | 4838 | a Gram-close configuration is close to `P` after an orthogonal map |
| local minimality of `P` | `Reg.pent_local_min` and the `LocalMinAt` chain | 9059 onward | exact second-order argument; its equality clause gives uniqueness |
| interval-arithmetic rigidity | `T4`, `Glue2b` (and `M3.contact_rigidity`, proved but not used in the final terms) | 3886, 12013 | Gram entries near `{−1, 0, c₁, c₂}` ⇒ the configuration is a relabelled `P` |

## Kernel computation: the `decide +kernel` sites

70 tactic uses (71 textual occurrences; one is in a docstring at line 10285): 4 in the shared library, 24 for Case 1, 7 for the cap, 7 for each of the five slabs.
Each evaluates exact integer or rational certificate data in the Lean kernel. 66 of the 70 lie in the dependency cone of the two theorems, whose axioms are only `propext`, `Classical.choice`, `Quot.sound` (see `verification/`).

## Section table

| lines | content |
|---|---|
| 1-310 | the Challenge preamble, unchanged |
| 311-10587 | `Level4` library: Case 1, reductions, local minimality at `P`, Kronecker checker core |
| 10588-12903 | `Typed*`, `T4`, `Glue1..Glue4` (`CapSpec`/`SlabSpec`/`seven_of_specs`), `EPEnc` (40-digit enclosure of `E(P)`) |
| 12905-15885 | `Coerce*`, `CertF`, `CertH/CertQ/CertT` (flat certificate evaluator and its soundness), `SlabHead`, `Bridge*` |
| 15887-17842 | certificate data: `cap_*`, then `s99_98`, `s98_96`, `s96_94`, `s94_93`, `s93_90` |
| 17844-17895 | `Final` and the two theorems |
