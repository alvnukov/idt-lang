"""Competing finite predictions, not observations from nature.

Fixed small ports 3,4. Read counts at named tags after a single calibrated
command, without computing a charge. Write both possible outcomes for the
shifted preparation; do not manufacture a common target from either rule.
The fixtures can exercise the checker but cannot select a physical law.
"""


def controls():
    basic = [((0, 0, 9), 30, 2), ((0, 0, 9), 23, 1), ((23, 30, 30), 0, 2)]
    weak = [((17, 24, 24), 0, 0)]  # both predictions have zero at this tag
    stayed = [((17, 24, 24), 17, 1), ((17, 24, 24), 24, 2)]
    departed = [((17, 24, 24), 6, 2), ((17, 24, 24), 15, 1)]
    wrong_frame = [((0, 0, 9), 30, 2)]

    def spec(name, rule, refs, mark=(3, 4)):
        return {"id": name, "family": "ternary_encounter", "rule": rule, "marked_ports": list(mark),
                "observations": [{"packets":list(s), "vertex":v, "count":n} for s, v, n in sorted(refs)]}

    return [
        spec("anchored_at_calibration", "anchored", basic),
        spec("relative_at_calibration", "relative", basic),
        spec("idle_at_calibration", "idle", basic),
        spec("anchored_if_mark_occupied", "anchored", basic+stayed),
        spec("relative_if_mark_occupied", "relative", basic+stayed),
        spec("anchored_if_mark_vacated", "anchored", basic+departed),
        spec("relative_if_mark_vacated", "relative", basic+departed),
        spec("idle_if_no_calibration_record", "idle", stayed),
        spec("both_may_miss_a_dark_tag", "relative", basic+weak),
        spec("anchored_with_wrong_partition", "anchored", wrong_frame, (0, 3)),
    ]


if __name__ == "__main__":
    import json
    print(json.dumps(controls(), separators=(",", ":")))
