"""An offline, pinned binary-table readout of one real quantum-processor job.

Before reading the counts: choose lexicographically FIRST ordinary CSV path
in the full archive (not __MACOSX); use every x,y, event b=0, and test D=1
and D=2 at simultaneous 95% confidence CONDITIONAL on fixed cell responses
and independent Bernoulli shots within each cell. Do not select a good W,
optimize over jobs or drop the file if incomplete.

Data (CC BY 4.0): Gabor Drotos and Abdelmalek Taoutioui, 2024,
https://doi.org/10.5281/zenodo.10723401 (version of 10.5281/zenodo.10723400).
The repository includes only this unmodified, hash-pinned member and
attribution in data/processor_cut. The article by Drotos,
Pal, Taoutioui & Vertesi, New J. Phys. 26 (2024), Table I and Appendix C,
https://doi.org/10.1088/1367-2630/ad4e5c; https://arxiv.org/abs/2406.08661,
describes four qubit rotations for preparation and three binary measurements,
implemented as 12 circuits. Its semi-device-independent self-test presupposes
a dimension bound; its W and plug-in sampling standard deviation are not our
dimension test or a simultaneous confidence region. For pc001 its W=1.9706
is BELOW the authors' numerical real-qubit upper bound 1.9881 at c=0.25.
The table typically presents best runs; our selection used the archived
filenames. Other hardware runs in the same campaign do not independently
replicate pc001 or establish stability of its shots.

The authors explicitly used equal consecutive shot counts per circuit.
The companion implementation https://doi.org/10.5281/zenodo.10723275 adds
a preparation barrier, compiles each full (x,y) circuit for the selected
qubit, submits the list and reads grouped backend counts; software was
inspected, not executed. A compiler barrier is not an isolation audit.
A submission list is not a verified physical
timeline. No shot timestamps, per-shot assignment probabilities, interleaving
audit, or separately counted missing attempts appear in this CSV. All cells
do sum to the declared 8192. Fixed counts are not propensities. Without
stable shared cell responses or appropriate randomization there is NO
drift-robust empirical dimension conclusion. In particular a receiver
ignoring preparation could use a varying binary response across scheduled
blocks; grouped counts alone cannot exclude that account. No evidence here
about the origin of a detector, reconstruction of QM, or an IDT primitive.

The default CLI replays the bundled count member without network access;
--archive /path/to/zip additionally verifies selection from the whole archive.
The Python API with neither source returns not_replayed. A missing bundled
file is an error in the replay campaign, never synthetic counts.
"""

import argparse
import csv
import hashlib
import io
import itertools
import json
import re
import zipfile
from fractions import Fraction as F
from math import sqrt
from pathlib import Path, PurePosixPath

from theory_experiments.binary_overlap_cut import BinaryOverlapCut, evaluate_binary_overlap_cut
from theory_experiments.primitive_screen import Limits

ARCHIVE_SHA256 = "bbe15662e33dc3d75daae3576eab0d4fd5c4d3d18b1291b04889564a490bab07"
CSV_SHA256 = "6e81009b2df68c0b10cbc41dc46e3fdf8b2ccd4850250b0cc15386d7040b7060"
METADATA_PDF_SHA256 = "1f61fbdc807c1a668a6b4a94da6e0ce5ffdd3cfcd80eac1f979538bff6118ce3"
MEMBER = "pm_umbrella_prepcert_counts_pc001.csv"
N = 8192


def need(ok, why):
    if not ok:
        raise ValueError(why)


def pinned(path, size, digest):
    with Path(path).open("rb") as stream:
        data=stream.read(size+1)
    need(len(data)==size and hashlib.sha256(data).hexdigest()==digest,
         "provided input does not match the published file pin")
    return data


def source_bytes(archive, csv_path):
    if archive is None:
        return pinned(csv_path,273,CSV_SHA256)
    need(csv_path is None,"choose either the complete archive or its pinned member")
    data=pinned(archive,17240,ARCHIVE_SHA256)
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        paths=sorted(v.filename for v in z.infolist() if not v.is_dir()
                     and "__MACOSX" not in PurePosixPath(v.filename).parts
                     and v.filename.lower().endswith(".csv"))
        need(len(paths)==len(set(paths))==52 and paths[0]==MEMBER,
             "pinned archive failed the outcome-blind selection check")
        member=z.read(paths[0])
    need(len(member)==273 and hashlib.sha256(member).hexdigest()==CSV_SHA256,
         "incorrect selected member")
    return member


def counts(data):
    # Parse by explicit outcome, not file order: first outcome varies by cell.
    lines=data.decode("ascii").splitlines()
    parser=csv.DictReader(lines)
    need(parser.fieldnames==["x","y","b","count"],"unrecognised columns")
    table={}
    for row in parser:
        need(set(row)==set(parser.fieldnames) and
             all(re.fullmatch(r"[0-9]+",s) for s in row.values()),"malformed raw row")
        x,y,b,k=(int(row[key]) for key in parser.fieldnames)
        need((x,y,b) not in table,"duplicate cell/outcome")
        table[x,y,b]=k
    keys=set(itertools.product(range(1,5),range(1,4),range(2)))
    need(set(table)==keys and all(table[x,y,0]+table[x,y,1]==N for x,y,_ in keys),
         "missing trial denominator or outcome")
    # Independent byte-level scan, in different order, plus the reported
    # denominator, guards against a mistaken digit or complement convention.
    scan=re.findall(rb"^([1-4]),([1-3]),([01]),([0-9]+)$",data,re.M)
    audit=sorted((int(b),int(y),int(x),int(k)) for x,y,b,k in scan)
    need(len(scan)==24 and audit==sorted((b,y,x,k) for (x,y,b),k in table.items()),
         "independent digit scan differs")
    return tuple(tuple(F(table[x,y,0],N) for y in range(1,4)) for x in range(1,5))


def authors_witness(p):
    # W=sum w_xy (2p_xy-1)/sqrt(9+3*c^2); plug-in variance keeps the
    # anticorrelation of the two binary outcomes in the SAME cell.
    c=F(1,4)
    w=((c,c,c),(1,-1,-1),(-1,1,-1),(-1,-1,1))
    norm2=9+3*c*c
    weighted=sum(a*(2*v-1) for wr,pr in zip(w,p) for a,v in zip(wr,pr))
    variance=sum(4*a*a*v*(1-v)/(N*norm2) for wr,pr in zip(w,p) for a,v in zip(wr,pr))
    def in_rounding_bin(squared, quoted):
        half=F(1,20000)
        return (quoted-half)**2 <= squared < (quoted+half)**2
    need(weighted>0 and in_rounding_bin(weighted**2/norm2,F(19706,10000)) and
         in_rounding_bin(variance,F(81,10000)), "published W or sampling SD not reproduced")
    return {"scaled_W_numerator":str(weighted),"squared_normalizer":str(norm2),
            "W_display":weighted/sqrt(norm2),"plugin_variance":str(variance),
            "plugin_sigma_display":sqrt(variance),"reported_W_sigma":["1.9706","0.0081"],
            "published_real_qubit_numerical_upper":"1.9881"}


def conditional_cut(p):
    # At e=.02, Hoeffding + union over 2*12 tails gives failure probability
    # <=24 exp(-2*N*e^2)<24/512<1/20, using exp(.7)>2 by four positive
    # Taylor terms. Marginal iid within each cell suffices for the union;
    # cross-cell independence is not needed. This is fixed-sample coverage
    # of stable cell parameters, NOT of a randomized common-time target.
    r=F(1,50)
    need(2*N*r*r>=9*F(7,10) and F(24,512)<F(1,20),"radius insufficient")
    box=tuple(tuple((max(F(0),v-r),min(F(1),v+r)) for v in row) for row in p)
    out={}
    for D in (1,2):
        c=BinaryOverlapCut("pc001","bit_zero","unconditional","quantum",D,True,box)
        (check,),detail=evaluate_binary_overlap_cut(c,Limits())
        out[str(D)]={"table_status":check.status,"scaled_upper_gap":detail["scaled_upper_gap"]}
    need(out["1"]["table_status"]=="counterexample" and out["2"]["table_status"]=="inconclusive",
         "pinned conditional analysis changed")
    return {"assumed_sampling":"fixed N independent Bernoulli shots within each stable cell",
            "model":"sufficient cut; no advance suffix leak or other channel; independent shared seed allowed",
            "simultaneous_error_at_most":"1/20","absolute_cell_radius":str(r),"dimension_caps":out}


def probe(archive=None,csv_path=None):
    result={"dataset":"10.5281/zenodo.10723401","concept_doi":"10.5281/zenodo.10723400",
            "attribution":"Gabor Drotos and Abdelmalek Taoutioui, 2024, CC BY 4.0",
            "member":MEMBER,"archive_sha256":ARCHIVE_SHA256,"csv_sha256":CSV_SHA256,
            "metadata_pdf_sha256":METADATA_PDF_SHA256,
            "drift_robust_empirical_cut_status":"unassessed",
            "per_shot_propensities":"not_available; equal block sizes do not supply these"}
    if archive is None and csv_path is None:
        return {**result,"replay_status":"not_replayed_missing_pinned_input"}
    p=counts(source_bytes(archive,csv_path))
    zeros=sum(v*N for row in p for v in row)
    need(zeros==50833,"unexpected count total")
    return {**result,"replay_status":"replayed_pinned_counts","job":"pc001",
            "submission_kind":"12 circuits with grouped outcome counts; no shot-level event order",
            "machine":"ibm_osaka","physical_qubit":7,"c":"1/4",
            "recorded_job_timestamp":"2024-01-19T12:49:36+01:00",
            "cells":12,"shots_per_cell":N,"recorded_shots":12*N,"outcome_zero_total":int(zeros),
            "published_summary_check":authors_witness(p),"conditional_analysis":conditional_cut(p)}


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__.splitlines()[0])
    group=cli.add_mutually_exclusive_group()
    group.add_argument("--archive",type=Path)
    group.add_argument("--csv",type=Path)
    args=cli.parse_args()
    member=args.csv
    if member is None and args.archive is None:
        member=Path(__file__).resolve().parents[1]/"data"/"processor_cut"/MEMBER
    print(json.dumps(probe(args.archive,member),separators=(",",":")))
