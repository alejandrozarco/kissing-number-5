"""Negative-control helper for second-kernel.sh: copy a lean4export file, changing one natural-number literal.
The literal is the longest one (at least 10 digits) that occurs exactly once (the first such in file order); it is
changed to the nearest larger value that occurs nowhere in the export, so the tampered file still parses and a
rejection has to come from type checking.
The file is read line by line, twice, and only a digest of each literal of at least 10 digits is kept, so the memory
needed is small even for exports of several GB (the output is the same as that of reading the whole file at once).
usage: python3 tamper_literal.py EXPORT.ndjson TAMPERED.ndjson"""
import hashlib, re, sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)  # certificate literals can have more than 100000 digits
src, dst = sys.argv[1], sys.argv[2]
NAT = re.compile(r'"natVal":"(\d+)"')


def key(v):
    return hashlib.blake2b(v.encode(), digest_size=16).digest()


# pass 1: occurrence counts of the literals with at least 10 digits (shorter ones cannot equal the new value),
# in order of first occurrence, with their lengths
count, length = {}, {}
with open(src) as f:
    for line in f:
        for v in NAT.findall(line):
            if len(v) >= 10:
                k = key(v)
                if k in count:
                    count[k] += 1
                else:
                    count[k] = 1
                    length[k] = len(v)
once = [k for k in count if count[k] == 1]
if not once:
    sys.exit("no literal with at least 10 digits occurs exactly once")
target = max(once, key=lambda k: length[k])
# pass 2: find the literal, choose the new value, write the copy
lit = None
with open(src) as f:
    for line in f:
        for v in NAT.findall(line):
            if len(v) == length[target] and key(v) == target:
                lit = v
                break
        if lit is not None:
            break
new = int(lit) + 1
while key(str(new)) in count:
    new += 1
new = str(new)
old, rep = '"natVal":"%s"' % lit, '"natVal":"%s"' % new
hits = 0
with open(src) as f, open(dst, "w") as g:
    for line in f:
        c = line.count(old)
        if c:
            hits += c
            line = line.replace(old, rep)
        g.write(line)
assert hits == 1


def short(v):
    return v if len(v) <= 40 else "%s...%s (%d digits)" % (v[:12], v[-12:], len(v))


print("\n== negative control: literal %s changed to %s" % (short(lit), short(new)))
