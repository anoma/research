#!/usr/bin/env sage

'''
This script should help with checking whether an optimized circuit is correct.
In particular, whether
    1. the optimized circuit behaves the same way as a non-optimized circuit, and
    2. for a _small_ field, list all valid wire combinations for the circuit.
I'm not yet sure whether (2) is quite as we need it.

TODO: prove that tools in (1) are correct
'''

import argparse

parser = argparse.ArgumentParser()
parser.add_argument("-i", "--inspect", help="give a subset of circuit-satisfying inputs over smaller field for manual inspection", action="store_true")
parser.add_argument("-e", "--equality", help="check functional equality between original and hand-optimized circuits", action="store_true")
args = parser.parse_args()

# If no arguments are specified, both inspection and equality checking are performed
if not args.inspect and not args.equality:
    args.inspect = True
    args.equality = True

p = 101
small_p = 3
field = GF(p)

variable_names = ['u_1', 'v_1', 'u_2', 'v_2', 'u_3', 'v_3', 'A', 'B', 'C', 'T']
R = PolynomialRing(field, sorted(variable_names))
R.inject_variables()

# Helper function listing all variables actually appearing in any polynomial in I
# The `reverse=True` seems to be necessary for sage not to confuse itself. Don't ask me why.
used_vars = lambda polys : sorted(list(set.union(*[set(p.variables()) for p in polys])), reverse=True)

# Helper function returning an ideal with all free variables of I removed
trim_variables = lambda I : I.change_ring(PolynomialRing(field, used_vars(I.basis)))

# Helper function to get all Field Equations given a list of variables
field_eqs = lambda vs : [v^len(field) - v for v in vs]

# The original circuit, probably not adhering to the ZKPS' constraints, but easy™ to read
a_j = 50
d_j = 42
polys_orig = [
    u_3 + (d_j * u_1 * u_2 * v_1 * v_2) * u_3 - (u_1 * v_2 + v_1 * u_2),
    v_3 - (d_j * u_1 * u_2 * v_1 * v_2) * v_3 - (v_1 * v_2 - a_j * u_1 * u_2),
]

# The optimized circuit, adhering to the ZKPS' constraints, and hopefully fast™
polys_opti = [
    (u_1 + v_1) * (v_2 - a_j * u_2) - T,
    u_1 * v_2 - A,
    v_1 * u_2 - B,
    d_j * A * B - C,
    (1 + C) * u_3 - (A + B),
    (1 - C) * v_3 - (T - A + a_j * B),
]

I_orig = trim_variables(Ideal(polys_orig))
gb_orig = I_orig.groebner_basis()

if args.inspect:
    small_R = PolynomialRing(GF(small_p), used_vars(gb_orig))
    gb_orig_with_field_eqs = [small_R(f) for f in gb_orig]
    gb_orig_with_field_eqs += [small_R(v)^small_p - small_R(v) for v in used_vars(gb_orig)]

    V = Ideal(gb_orig_with_field_eqs).variety()

    print()
    for v in V:
        print(v)

    print(f"\n#elements in V:  {len(V)}")

if args.equality:
    I_opti = trim_variables(Ideal(polys_opti))
    # variables introduced when optimizing the circuit that were not needed originally
    introduced_vars = [v for v in used_vars(polys_opti) if not v in used_vars(polys_orig)]
    print(f"Introduced vars: {introduced_vars}")
    gb_opti = I_opti.elimination_ideal(introduced_vars).groebner_basis()
    print(f"Ideals are same: {gb_orig == gb_opti}")
