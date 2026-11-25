"""Faithful Python port of Syst3ms/Bismuth (Bismuth.kt) at commit bf7ba654
(2020-07-14 21:25 UTC, "Fix diagonal finding&expansion method").

Kotlin semantics that matter are reproduced:
* Array.resize shares row objects when the width is kept;
* paste / refill mutate in place;
* out-of-range indices raise (Kotlin throws), negative indices are not wrapped;
* integers are unbounded (Bismuth is read as a mathematical notation);
* an iteration of copyOffset that writes nothing while its condition holds
  raises InfiniteLoop (no later iteration writes either);
* other loops are bounded by a step budget (raises Hang).
"""


class Hang(Exception):
    """step budget exhausted (unknown whether it terminates)"""


class InfiniteLoop(Exception):
    """copyOffset: an iteration with the condition true wrote nothing; it loops forever"""


class KErr(Exception):
    """an exception the Kotlin program would throw"""


BUDGET = [0]


def tick():
    BUDGET[0] -= 1
    if BUDGET[0] < 0:
        raise Hang()


def kget(a, i):
    if not isinstance(i, int) or i < 0 or i >= len(a):
        raise KErr(f"index {i} out of {len(a)}")
    return a[i]


def kset(a, i, v):
    if i < 0 or i >= len(a):
        raise KErr(f"index {i} out of {len(a)}")
    a[i] = v


def get_or_null(a, i):
    return a[i] if 0 <= i < len(a) else None


def width(m):
    return len(kget(m, 0))


def first(a):
    if not a:
        raise KErr("first of empty")
    return a[0]


def last(a):
    if not a:
        raise KErr("last of empty")
    return a[-1]


def copy_of_range(a, frm, to):
    if frm > to:
        raise KErr(f"copyOfRange {frm} > {to}")
    if frm < 0 or to > len(a):
        raise KErr(f"copyOfRange {frm} {to} of {len(a)}")
    return list(a[frm:to])


def sub_list(a, frm, to):
    if frm < 0 or to > len(a) or frm > to:
        raise KErr(f"subList {frm} {to} of {len(a)}")
    return list(a[frm:to])


def drop_last(a, n):
    if n < 0:
        raise KErr("dropLast negative")
    return list(a[: max(len(a) - n, 0)])


def resize(m, new_w, new_h):
    result = m
    h = len(m)
    w = len(kget(m, 0))
    if h < new_h:
        result = list(result) + [[0] * w for _ in range(new_h - h)]
    elif new_h < h:
        result = drop_last(result, h - new_h)
    if w < new_w:
        result = [row + [0] * (new_w - w) for row in result]
    elif new_w < w:
        result = [drop_last(row, w - new_w) for row in result]
    return result


def bad_root(m):
    return width(m) - kget(kget(m, len(m) - 2), width(m) - 1) - 1


def paste(m, part, x, y):
    for i in range(len(part)):
        if y + i >= len(m):
            break
        for j in range(width(part)):
            if x + j >= width(m):
                break
            kset(kget(m, y + i), x + j, kget(part[i], j))
    return m


def kslice(m, x, y, x1, y1):
    return [copy_of_range(r, x, x1 + 1) for r in copy_of_range(m, y, y1 + 1)]


def find_parent_index(seq, cur_off, br):
    i = br if br is not None else len(seq) - 2
    current = last(seq)
    while i >= 0:
        tick()
        v = kget(seq, i)
        if 1 <= v < current:
            return i
        elif v == 0:
            break
        i -= max(kget(cur_off, i), 1)
    return None


def refill(value, offset):
    for i in range(len(value) - 2, -1, -1):
        for j in range(width(value)):
            tick()
            off = kget(kget(offset, i), j)
            if off < 0:
                kset(value[i], j, -off)
            else:
                below = get_or_null(value, i + 1)
                b = kget(below, j) if below is not None else 0
                kset(value[i], j, (b + kget(value[i], j - off)))
    return value


def copy_offset(m, br, times=None, size=None):
    result = m
    copy_w = width(result) - br - 1
    new_w = br + copy_w * times + 1 if times is not None else size
    result = resize(result, new_w, len(result))
    i = 1
    while last(first(result)) == 0:
        tick()
        wrote = False
        for j in range(copy_w):
            target = br + copy_w * i + j + 1
            if target >= new_w:
                break
            for k in range(len(result)):
                to_copy = kget(result[k], br + j + 1)
                kset(result[k], target, (to_copy + (copy_w * i if j - to_copy + 1 < 0 else 0)))
                wrote = True
        if not wrote:
            raise InfiniteLoop(f"copyWidth={copy_w} badRoot={br} newWidth={new_w}")
        i += 1
    return result


def list_copy(lst, root, times):
    new = sub_list(lst, 0, root)
    for _ in range(times):
        new += sub_list(lst, root, len(lst))
    return new


def expand(seq, times, first_offset=None):
    value = [seq]
    offset = [[0] * len(seq)]
    row = 0
    while find_parent_index(last(value), last(offset), None if row == 0 else bad_root(offset)) is not None:
        tick()
        value = resize(value, width(value), len(value) + 1)
        offset = resize(offset, width(offset), len(offset) + 1)
        for i in range(width(value)):
            row_list = value[row]
            if first_offset is not None and row == 0:
                diff = (kget(row_list, i) - kget(row_list, i - kget(first_offset, i)))
                kset(value[row + 1], i, diff)
                kset(offset[row], i, first_offset[i])
                continue
            lim = (i - max(kget(kget(offset, row - 1), i), 0)) if row > 0 else None
            pi = find_parent_index(copy_of_range(row_list, 0, i + 1), copy_of_range(offset[row], 0, i + 1), lim)
            if pi is None:
                kset(value[row + 1], i, 0)
                z = row_list[i] == 0 or all(v == 0 for v in copy_of_range(row_list, 0, i))
                kset(offset[row], i, 0 if z else -row_list[i])
            else:
                kset(value[row + 1], i, (row_list[i] - row_list[pi]))
                kset(offset[row], i, i - pi)
        row += 1

    br = bad_root(offset)
    last_row = last(value)
    if last(last_row) > 1:
        cols = [[kget(r, i) for r in value] for i in range(width(value))]
        roots = []
        for i, c in enumerate(cols):
            idx = max([k for k, v in enumerate(c) if v > 0], default=-1)
            roots.append((i, idx))
        diagonal = [kget(kget(value, r[1]), r[0]) for r in roots]
        shape = [s[1] - f[1] for f, s in zip(roots, roots[1:])]
        forced = [0] * len(diagonal)
        for i in range(len(roots)):
            c = roots[i]
            done = False
            while True:  # do { ... } while (cond)
                tick()
                if c == (0, 0):
                    forced[i] = 0 if i == 0 else -diagonal[i]
                    done = True
                    break
                below = get_or_null(value, c[1] + 1)
                bv = kget(below, c[0]) if below is not None else 0
                if bv > 0:
                    d = (kget(kget(offset, c[1]), c[0]), 0)
                else:
                    d = (kget(kget(offset, c[1] - 1), c[0]), 1)
                c = (c[0] - d[0], c[1] - d[1])
                if not (kget(kget(value, c[1] + 1), c[0]) > 0 or kget(kget(value, c[1]), c[0]) >= diagonal[i]):
                    break
            if done:
                continue
            root_index = roots.index(c) if c in roots else -1
            forced[i] = i - root_index
        roots.pop()
        ed = expand(list(diagonal), times + 1, forced)
        new_shape = list_copy(shape, ed[2], times)
        new_roots = list_copy(roots, ed[2], times)
        nb = (len(new_shape), sum(new_shape))
        new_diag = first(ed[0])
        row = 0
        temp_v = resize(value, nb[0] + 1, nb[1] + 1)
        temp_o = resize(offset, nb[0] + 1, nb[1] + 1)
        bad_x, bad_y = kget(roots, ed[2])
        bad_part = copy_offset(kslice(offset, bad_x, bad_y, width(offset) - 1, bad_y), 0, times=times)
        for i in range(len(new_shape)):
            tick()
            s = new_shape[i]
            r = new_roots[i]
            vpart = kslice(value, r[0], min(r[1], r[1] + s), r[0] + 1, max(r[1], r[1] + s))
            kset(kget(vpart, -min(s, 0)), 0, kget(new_diag, i))
            temp_v = paste(temp_v, vpart, i, row + min(s, 0))
            opart = kslice(offset, r[0], r[1], width(offset) - 1, r[1] + max(s, 0))
            if row >= bad_y and s > 0:
                old_w = width(opart)
                opart = paste(resize(opart, width(temp_o) - i, len(opart)),
                              kslice(bad_part, 1, 0, width(bad_part) - 1, 0), old_w, 0)
            elif s > 0:
                opart = copy_offset(opart, bad_x - i, times=times)
            temp_o = paste(temp_o, opart, i, row)
            row += s
        kset(kget(temp_v, row), len(new_shape), kget(new_diag, len(new_shape)))
        return (refill(temp_v, temp_o), temp_o, br)
    else:
        offset = copy_offset(offset, br, times=times)
        for i in range(len(value)):
            kset(value[i], width(value) - 1, 0)
        bpw = width(value) - br - 1
        new_w = br + bpw * times
        value = resize(value, new_w, len(value))
        for i in range(1, times):
            for j in range(bpw):
                for k in range(len(value)):
                    tick()
                    x = br + j
                    if kget(kget(offset, k), x) == 0 and not (k > 0 and x - kget(offset[k - 1], x) < br):
                        kset(value[k], x + bpw * i, kget(value[k], x))
        return (refill(value, offset), offset, br)


def run(seq, bracket, budget=2_000_000):
    """main: returns (sequence, bracket) of the output"""
    BUDGET[0] = budget
    seq = list(seq)
    if last(seq) == 1:
        return seq[:-1], bracket + 1
    res = expand(seq, bracket + 1)
    return list(first(res[0])), bracket
