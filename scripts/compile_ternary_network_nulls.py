"""Fixed hypothetical comparator records, never calculated by a candidate engine.

The nine bright reads are the preselected panel for a rational contact vs.
primes through 97. No laboratory reported these measurements. Small separate
pairs preserve the opposite dark outcome and state/readout aliasing controls.
"""

SMALL_PRIMES = (2,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97)
PANEL = (19,24,26,29,30,32,35,40,43)
H, G = (0,1,2), (1,2,3)


def controls():
    def spec(name, rule, contacts, refs, modulus=None, seed=(1,0,0,0)):
        return {"id":name,"family":"ternary_network_nulls","rule":rule,"modulus":modulus,
                "initial":list(seed),"contacts":[list(h) for h in contacts],
                "readouts":[{"after":n,"port":i,"dark":out} for n,i,out in refs]}

    two = (H,G)
    bright = [(2,3,False)]
    dark = [(2,3,True)]
    echo = [(2,0,False),(2,1,True),(2,2,True),(2,3,True)]
    panel = [(2*k,3,False) for k in PANEL]
    scheduled = two*max(PANEL)
    return [
        spec("overlap_bright_mobile","mobile_depth",two,bright),
        spec("overlap_bright_stock","stationary_bucket",two,bright),
        spec("overlap_dark_mobile","mobile_depth",two,dark),
        spec("overlap_dark_stock","stationary_bucket",two,dark),
        spec("overlap_dark_wire","idle_wire",two,dark),
        spec("modfive_dark_mobile","mobile_depth",two*2,[(4,3,True)]),
        spec("modfive_dark_prime","residue_field",two*2,[(4,3,True)],5),
        spec("modfive_bright_prime","residue_field",two*2,[(4,3,False)],5),
        spec("echo_mobile","mobile_depth",(H,H),echo),
        spec("echo_stock","stationary_bucket",(H,H),echo),
        spec("echo_any_wire","idle_wire",(H,H),echo),
        spec("zero_input_mobile","mobile_depth",two,[(2,0,True),(2,3,True)],seed=(0,0,0,0)),
        spec("nine_reads_rational","mobile_depth",scheduled,panel),
        *(spec(f"nine_reads_prime_{p}","residue_field",scheduled,panel,p) for p in SMALL_PRIMES),
        *(spec(f"nine_reads_holdout_{p}","residue_field",scheduled,panel,p) for p in (101,127)),
    ]


if __name__ == "__main__":
    import json

    print(json.dumps(controls(), separators=(",", ":")))
