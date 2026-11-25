"""Faithful Python port of Syst3ms/Bismuth (Bismuth.kt), versions 5e4c65c3
(2019-09-29) and 2213d83a (2019-10-19).

Kotlin semantics that matter are reproduced:
* Array.resize shares row objects when only the height changes;
* paste / refill mutate in place;
* out-of-range indices raise (Kotlin throws), negative indices are not wrapped;
* infinite loops are detected by a step budget (raises Hang).
"""


class Hang(Exception):
    pass


class InfiniteLoop(Exception):
    """copyOffset made an iteration without writing: it loops forever"""


class KErr(Exception):
    """an exception the Kotlin program would throw"""


BUDGET = [0]


def tick():
    BUDGET[0] -= 1
    if BUDGET[0] < 0:
        raise Hang()


def kget(a, i):
    if i < 0 or i >= len(a):
        raise KErr(f"index {i} out of {len(a)}")
    return a[i]


def kset(a, i, v):
    if i < 0 or i >= len(a):
        raise KErr(f"index {i} out of {len(a)}")
    a[i] = v


def width(m):
    return len(kget(m, 0))


def resize(m, new_w, new_h):
    result = m
    h = len(m)
    w = len(kget(m, 0))
    if h < new_h:
        result = list(result) + [[0] * w for _ in range(new_h - h)]
    elif new_h < h:
        result = list(result[: new_h])
    if w < new_w:
        result = [row + [0] * (new_w - w) for row in result]
    elif new_w < w:
        result = [row[: len(row) - (w - new_w)] for row in result]
    return result


def bad_root(m):
    return width(m) - kget(kget(m, len(m) - 2), width(m) - 1) - 1


def paste(m, part, x, y):
    for i in range(len(part)):
        if y + i >= len(m):
            break
        for j in range(len(part[0])):
            if x + j >= len(m[0]):
                break
            kset(m[y + i], x + j, part[i][j])
    return m


def copy_of_range(a, frm, to):
    if frm < 0 or to > len(a) or frm > to:
        raise KErr(f"copyOfRange {frm} {to} of {len(a)}")
    return list(a[frm:to])


def kslice(m, x, y, x1, y1):
    return [copy_of_range(r, x, x1 + 1) for r in copy_of_range(m, y, y1 + 1)]


def find_parent_index(seq, br):
    last = seq[-1]
    for i in range(len(seq) - 2, -1, -1):
        tick()
        if seq[i] == 0 or seq[i] >= last or (br is not None and i > br):
            continue
        return i
    return None


def refill(value, offset, version):
    for i in range(len(value) - 1, -1, -1):
        for j in range(len(value[0])):
            tick()
            off = offset[i][j]
            below = value[i + 1][j] if i + 1 < len(value) else 0
            if version >= 2 and off < 0:
                value[i][j] = -off
            else:
                value[i][j] = below + kget(value[i], j - off)
    return value


def copy_offset(m, br, times=None, size=None, version=1):
    result = m
    copy_w = len(result[0]) - br - 1
    new_w = br + copy_w * times + 1 if times is not None else size
    result = resize(result, new_w, len(result))
    i = 1
    while kget(result[0], len(result[0]) - 1) == 0:
        tick()
        wrote = False
        for j in range(copy_w):
            target = br + copy_w * i + j + 1
            if target >= new_w:
                break
            for k in range(len(result)):
                kset(result[k], target, kget(result[k], br + j + 1))
                wrote = True
        if not wrote:
            # the targets only grow with i, so no later iteration writes either
            raise InfiniteLoop(f"copyWidth={copy_w} badRoot={br} newWidth={new_w}")
        i += 1
    return result


def list_copy(lst, root, times):
    if root < 0 or root > len(lst):
        raise KErr("subList")
    new = list(lst[:root])
    for _ in range(times):
        new += lst[root:]
    return new


def expand(seq, times, version):
    value = [list(seq)]
    offset = [[0] * len(seq)]
    row = 0
    while find_parent_index(value[-1], None if row == 0 else bad_root(offset)) is not None:
        tick()
        value = resize(value, width(value), len(value) + 1)
        offset = resize(offset, width(offset), len(offset) + 1)
        for i in range(width(value)):
            row_list = value[row]
            pi = find_parent_index(row_list[: i + 1], (i - offset[row - 1][i]) if row > 0 else None)
            if pi is None:
                value[row + 1][i] = 0
                if version == 1:
                    offset[row][i] = 0
                else:
                    offset[row][i] = 0 if (row_list[i] == 0 or all(v == 0 for v in row_list[:i])) else -row_list[i]
            else:
                value[row + 1][i] = row_list[i] - row_list[pi]
                offset[row][i] = i - pi
        row += 1

    br = bad_root(offset)
    last_row = value[-1]
    if last_row[-1] > 1:
        shape = []
        diagonal = []
        cx, cy = 0, 0
        while cx < width(value):
            tick()
            diagonal.append(kget(kget(value, cy), cx))
            nxt = 0
            if 0 <= cy + 1 < len(value) and 0 <= cx + 1 < len(value[cy + 1]):
                nxt = value[cy + 1][cx + 1]
            if nxt > 0:
                if version == 1:
                    parents = [i - e for i, e in enumerate(offset[cy])]
                    idx = max([i for i, p in enumerate(parents) if p == cx], default=-1)
                    root = idx - cx
                    shape.append((root, 1))
                    cx, cy = cx + root, cy + 1
                else:
                    seg = copy_of_range(offset[cy], cx + 1, width(offset))
                    children = [(i, i + 1 - e) for i, e in enumerate(seg)]
                    children = [c for c in children if c[1] == 0]
                    if len(children) == len(offset[cy]) - cx - 1:
                        dpart = list_copy([(1, 1), (1, 0)], 1, len(children) - 1)
                        shape += dpart
                        for i in range(len(dpart) - 1):
                            diagonal.append(kget(kget(value, cy + 1), cx + i + 1))
                        sx = sum(p[0] for p in dpart)
                        sy = sum(p[1] for p in dpart)
                        cx, cy = cx + sx, cy + sy
                    else:
                        if not children:
                            raise KErr("last of empty")
                        root = children[-1][0] + 1
                        shape.append((root, 1))
                        cx, cy = cx + root, cy + 1
            else:
                shape.append((1, 0))
                cx, cy = cx + 1, cy
        if not shape:
            raise KErr("removeAt")
        shape.pop()
        roots = []
        for i in range(len(shape)):
            sx = sum(p[0] for p in shape[:i])
            sy = sum(p[1] for p in shape[:i])
            roots.append((sx, sy))
        if version == 1:
            ed = expand(diagonal, times + 2, version)
            new_shape = list_copy(shape, ed[2], times + 1)
            new_roots = list_copy(roots, ed[2], times + 1)
        else:
            ed = expand(diagonal, times + 1, version)
            new_shape = list_copy(shape, ed[2], times)
            new_roots = list_copy(roots, ed[2], times)
        nb = (sum(p[0] for p in new_shape), sum(p[1] for p in new_shape))
        new_diag = ed[0][0]
        cx, cy = 0, 0
        temp_v = resize(value, nb[0] + 1, nb[1] + 1)
        temp_o = resize(offset, nb[0] + 1, nb[1] + 1)
        for i in range(len(new_shape)):
            tick()
            s = new_shape[i]
            r = new_roots[i]
            vpart = kslice(value, r[0], r[1], r[0] + s[0], r[1] + s[1])
            kset(vpart[0], 0, kget(new_diag, i))
            temp_v = paste(temp_v, vpart, cx, cy)
            if version == 1:
                opart = kslice(offset, r[0], r[1], r[0] + s[0], r[1] + s[1])
            else:
                opart = kslice(offset, r[0], r[1], width(offset) - 1, r[1] + s[1])
            if s[1] > 0:
                opart = copy_offset(opart, bad_root(opart), size=width(temp_o), version=version)
            temp_o = paste(temp_o, opart, cx, cy)
            cx, cy = cx + s[0], cy + s[1]
        kset(kget(temp_v, cy), cx, kget(new_diag, len(new_shape)))
        return (refill(temp_v, temp_o, version), temp_o, br)
    else:
        offset = copy_offset(offset, br, times=times, version=version)
        for i in range(len(value)):
            value[i][width(value) - 1] = 0
        bpw = width(value) - br - 1
        new_w = br + bpw * times
        value = resize(value, new_w, len(value))
        for i in range(1, times):
            for j in range(bpw):
                for k in range(len(value)):
                    tick()
                    x = br + j
                    if kget(offset[k], x) == 0 and not (k > 0 and x - kget(offset[k - 1], x) < br):
                        kset(value[k], x + bpw * i, kget(value[k], x))
        return (refill(value, offset, version), offset, br)


def run(seq, bracket, version, budget=2_000_000):
    """The main of the program: returns (sequence, bracket) of the output."""
    BUDGET[0] = budget
    seq = list(seq)
    if seq[-1] == 1:
        return seq[:-1], bracket + 1
    t = bracket if version == 1 else bracket + 1
    res = expand(seq, t, version)
    return res[0][0], bracket
