# Erdős Problem 289 — ordinary quota proof workbench

**Status:** public editorial/mathematical workbench. No independent PASS is claimed.

This branch develops the shortest currently known authorial proof route to the original Erdős Problem 289. It is deliberately separate from the frozen stronger fibrewise candidate `paper/candidate-r16`.

## Root theorem

For every sufficiently large integer `k`, there is a finite support in the positive-integer path graph with exactly `k` connected components, every component of size two or three, reciprocal weight exactly `1`, and no adjacency between distinct components.

## Current root mechanism

1. Construct one explicit source-closed affine Prefix at a sufficiently late lcm endpoint `E_B`, at one common block count and with a fixed positive margin below reciprocal value `2`.
2. Add a finite bank of equal-value binary neutral coordinates whose two alternatives differ in block count by one. Superquadratic placement makes the entire bank uniformly transparent to all future signed-inverse rows, independently of bank width.
3. For every future prime current `p`, request the endpoint-independent exact quota
   `q_p = floor(p^(2/3))`.
   For every proper prime power `p^e`, `e >= 2`, request exactly `p-1` atoms.
4. At each finite endpoint, use one Haxell quota packing and exact-cardinality trimming. The physical packing may vary with the endpoint; the quota profile does not.
5. Keep the full local residue–grade witness relation until physical composition. Its consumer image is the erosion operator
   `Erode_C(I) = intersection_s union_{c:value(c)=s} (I + grade(c))`.
6. Prime currents use the Dias da Silva–Hamidoune restricted-sum bound at two complementary grades. Proper prime powers use the complete Boolean subset family and repeated Cauchy–Davenport.
7. These give deterministic interval transfers, independent of endpoint packing:
   - prime `p`: `[A,B] -> [A+r_p, B+q_p-r_p]`, where `r_p = O(p^(1/3))`;
   - proper power `p^e`: `[A,B] -> [A+p-1,B]`.
8. Lower comparable-prime supply gives total prime gain `>> Y^(5/3)/log Y` in a fixed-ratio band, while all proper-power loss in the band is `O(Y)`. A finite neutral-bank bootstrap therefore starts an indefinitely legal, overlapping interval chain whose union is a final ray.
9. Prime resource is summable because `sum q_p/p^2 <= sum n^(-4/3)`. Proper-power resource is summable as well. The source is chosen after fixing the Prefix margin so the entire future resource tail fits inside it.
10. The affine centre is transported only by canonical quotient maps. Since it is torsion, it is killed at every sufficiently late endpoint. Pull back the endpoint response at literal residue `0` and a prescribed sufficiently large block count `k`; then `[W]=0` and `0<W<2`, hence `W=1`.

## Why this is different from the fibrewise R16 route

The ordinary proof does not consume MasterSlab, defect-neutral coordinates, DirectLTAR, predecessor donors, Fourier/matching convolution, or opposite-coset Tail exactification. The stronger R16 route remains separately frozen for independent review and possible later publication as a profile-saturation strengthening.

## External theorem frontier

The intended ordinary manuscript may cite:

- Haxell's independent-transversal theorem, through the quota-packing corollary;
- Dias da Silva–Hamidoune restricted sums in `Z/pZ`;
- Cauchy–Davenport (or prove the repeated two-point corollary directly).

Comparable-prime supply remains proved in the paper appendix. No upper prime-density estimate is required.

## Assurance boundary

The uploaded R20 packet reported an internal reconstruction PASS. This branch does **not** inherit that as independent assurance. Before a candidate is frozen, every provider above must be written literally in the active manuscript and then subjected to a fresh no-background review.
