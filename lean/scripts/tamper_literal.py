"""Negative-control helper for second-kernel.sh: copy a lean4export file, changing one natural-number literal.
The literal is the longest one (at least 10 digits) that occurs exactly once; it is changed to the nearest larger value
that occurs nowhere in the export, so the tampered file still parses and a rejection has to come from type checking.
usage: python3 tamper_literal.py EXPORT.ndjson TAMPERED.ndjson"""
import collections, re, sys

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)  # certificate literals can have more than 100000 digits
src, dst = sys.argv[1], sys.argv[2]
txt = open(src).read()
vals = re.findall(r'"natVal":"(\d+)"', txt)
count = collections.Counter(vals)
once = [v for v in dict.fromkeys(vals) if count[v] == 1 and len(v) >= 10]
if not once:
    sys.exit("no literal with at least 10 digits occurs exactly once")
lit = max(once, key=len)
new = int(lit) + 1
while str(new) in count:
    new += 1
new = str(new)
old = '"natVal":"%s"' % lit
assert txt.count(old) == 1
with open(dst, "w") as f:
    f.write(txt.replace(old, '"natVal":"%s"' % new))


def short(v):
    return v if len(v) <= 40 else "%s...%s (%d digits)" % (v[:12], v[-12:], len(v))


print("\n== negative control: literal %s changed to %s" % (short(lit), short(new)))
