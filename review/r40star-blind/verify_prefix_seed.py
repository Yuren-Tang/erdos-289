#!/usr/bin/env python3
from fractions import Fraction
import json, pathlib, sys

ROOTS = [
    [],
    [35,56,90,119,152,170,455,494,714],
    [17,35,44,84,104,119,132,170,272,285,455,494,560,714,935],
    [9,17,34,44,77,84,90],
    [7,16,34,44,51,65,77,119,132,153,170,272,285,455,494],
    [2],
]
TARGETS = [Fraction(0),Fraction(1,6),Fraction(1,3),Fraction(1,2),Fraction(2,3),Fraction(5,6)]
GRADES = [0,9,15,7,15,1]
EARLY_BRIDGES = [
    {"lower":6,"upper":12,"p":2,"radii":[1],"bases":[12]},
    {"lower":12,"upper":60,"p":5,"radii":[1,2,3],"bases":[60,30,20]},
]
BOUNDARY_COMPAT_BASES = [12,20,30,60,140,210,420,840,1260,2520]
SEPARATOR = Fraction(1,4)
ROOT_BOUND = Fraction(5,6)
EARLY_BRIDGE_CRUDE_BOUND = Fraction(11,20)
SEED_BOUND = Fraction(3,2)

def P(m): return Fraction(1,m)+Fraction(1,m+1)
def root_mass(xs): return sum((P(m) for m in xs), Fraction(0))
def envelope_mass(a, ternary):
    lo = a if ternary else a+1
    return sum((Fraction(1,n) for n in range(lo,a+3)), Fraction(0))
def subset_sums(xs):
    vals={0}
    for x in xs: vals |= {v+x for v in tuple(vals)}
    return vals

def root_sep(xs):
    return all(a+2 < b for i,a in enumerate(xs) for b in xs[i+1:])
def root_bridge_compat(m,a): return m+2<a or a+3<m
def bridge_compat(a,b): return a+3<b

def build_result():
    checks={}
    masses=[root_mass(xs) for xs in ROOTS]
    checks["1_root_identities"] = all(m==t for m,t in zip(masses,TARGETS))
    checks["2_root_grades"] = all(len(xs)==g for xs,g in zip(ROOTS,GRADES))
    checks["3_root_separation"] = all(root_sep(xs) for xs in ROOTS)
    checks["4_lcmUpto3_and_residue_exhaustion"] = (
        __import__('math').lcm(1,2,3)==6 and TARGETS == [Fraction(j,6) for j in range(6)])

    bridge_formula=[]
    subset_surj=[]
    early_bases=[]
    for B in EARLY_BRIDGES:
        p,D=B["p"],B["lower"]
        ok=(B["upper"]==p*D and len(B["radii"])==len(B["bases"]))
        for r,a in zip(B["radii"],B["bases"]):
            ok &= (a == p*D//r and p*D % r == 0)
            ok &= (envelope_mass(a,True)-envelope_mass(a,False) == Fraction(r,p*D))
        bridge_formula.append(ok)
        subset_surj.append({x%p for x in subset_sums(B["radii"])}==set(range(p)))
        early_bases += B["bases"]
    checks["5_bridge_formula"] = all(bridge_formula)
    checks["6_bridge_subset_sum_surjective"] = all(subset_surj)
    checks["7_root_boundary_bridge_compatibility"] = all(
        root_bridge_compat(m,a) for xs in ROOTS for m in xs for a in BOUNDARY_COMPAT_BASES)
    bs=BOUNDARY_COMPAT_BASES
    checks["8_boundary_bridge_pairwise_compatibility"] = all(
        bridge_compat(a,b) for i,a in enumerate(bs) for b in bs[i+1:])

    root_bound_ok = max(masses) <= ROOT_BOUND
    each_early_bridge_crude = all(envelope_mass(a,True) < Fraction(3,a) for a in early_bases)
    crude_sum = sum((Fraction(3,a) for a in early_bases),Fraction(0))
    checks["9_structural_seed_margin"] = (
        root_bound_ok and each_early_bridge_crude and crude_sum == EARLY_BRIDGE_CRUDE_BOUND and
        ROOT_BOUND + EARLY_BRIDGE_CRUDE_BOUND < SEED_BOUND and
        SEED_BOUND + SEPARATOR < 2)

    return {
        "schema":"E289-R40star-blind-prefix-seed-certificate-v1",
        "status":"PASS" if all(checks.values()) else "FAIL",
        "checks":checks,
        "root_masses":[str(x) for x in masses],
        "root_grades":[len(x) for x in ROOTS],
        "early_seed_bridge_bases":sorted(early_bases),
        "finite_boundary_compatibility_bases":BOUNDARY_COMPAT_BASES,
        "certified_root_bound":str(ROOT_BOUND),
        "certified_early_bridge_crude_bound":str(EARLY_BRIDGE_CRUDE_BOUND),
        "certified_seed_bound":str(SEED_BOUND),
        "prefix_separator_witness":str(SEPARATOR),
        "future_accumulated_bridge_bound":"proved structurally in 03_PREPARED_WIDE_START.md; < 1/5 < 1/4",
        "subset_sum_residues":{
          "p2": sorted({x%2 for x in subset_sums([1])}),
          "p5": sorted({x%5 for x in subset_sums([1,2,3])})
        },
        "explicit_p5_witnesses":{"0":[],"1":[1],"2":[2],"3":[3],"4":[1,3]},
        "non_exported_diagnostics":[
          "exact finite branch maximum intentionally not computed",
          "numeric grade cap intentionally not computed",
          "finite boundary compatibility coordinates die before the prepared-wide-start theorem"
        ]
    }

def main():
    out=build_result()
    text=json.dumps(out,indent=2,sort_keys=True)+"\n"
    if '--write' in sys.argv:
        pathlib.Path(__file__).with_name("PREFIX_SEED_CERTIFICATE.json").write_text(text)
    print(text,end='')
    return 0 if out["status"]=="PASS" else 1

if __name__ == '__main__': sys.exit(main())
