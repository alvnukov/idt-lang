"""Two candidate mechanisms, predictions at two time resolutions, no data fit.

The input field is one signed mark on a known port. The observation tables
are literal counters; neither mechanism is used to generate a reference.
Both candidate outcomes are kept. A signed counter is not a photon detector.
"""


def controls():
    positive = [(0, 1)] * 3
    cycle = [(3, "prefix", (-1, 2, 2))]
    bucket = [(1, "step", (-1, 0, 0)), (2, "step", (0, 1, 1)), *cycle]
    rotor = [(1, "step", (0, 1, 0)), (2, "step", (0, 0, 1)), *cycle]
    echo = [(1, "step", (1, 0, -1, -1)), (2, "prefix", (0, 0, 0, 0))]

    def record(name, d, rule, phase, inputs, readouts):
        return {
            "id": name, "family": "signed_contact_stream", "ports": d, "rule": rule,
            "initial_phase": phase, "inputs": [{"port": i, "sign": s} for i, s in inputs],
            "readouts": [{"after": k, "scope": scope, "counts": list(counts)} for k, scope, counts in readouts],
        }

    first = "anonymous_bucket"
    second = "ordered_pair_rotor"
    return [
        record("cycle_only_bucket", 3, first, 0, positive, cycle),
        record("cycle_only_rotor", 3, second, 0, positive, cycle),
        record("cycle_only_wire", 3, "idle_wire", 0, positive, cycle),
        record("resolved_bucket_if_bucket", 3, first, 0, positive, bucket),
        record("resolved_rotor_if_bucket", 3, second, 0, positive, bucket),
        record("resolved_bucket_if_rotor", 3, first, 0, positive, rotor),
        record("resolved_rotor_if_rotor", 3, second, 0, positive, rotor),
        record("alternate_phase_ballot", 3, first, 2, positive, [(1, "step", (0, 1, 1)), *cycle]),
        record("negative_echo_resolved_rotor", 4, second, 0, [(0, -1), (0, 1)], echo),
        record("negative_echo_resolved_bucket", 4, first, 0, [(0, -1), (0, 1)], echo),
        record("negative_echo_closed_bucket", 4, first, 0, [(0, -1), (0, 1)], echo[1:]),
        record("two_ports_indistinct_bucket", 2, first, 1, [(0, -1)], [(1, "step", (0, -1))]),
        record("two_ports_indistinct_rotor", 2, second, 1, [(0, -1)], [(1, "step", (0, -1))]),
        record("one_click_is_not_signed_flux", 3, first, 0, positive, [(3, "prefix", (1, 0, 0))]),
    ]


if __name__ == "__main__":
    import json

    print(json.dumps(controls(), separators=(",", ":")))
