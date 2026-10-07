"""Literal parity-tree emission; all generated values remain kernel checked."""
def tree(values):
    values=list(values)
    assert values
    if len(values)==1:
        return f'(.leaf {values[0]})'
    length=1<<(len(values)-1).bit_length()
    values += [values[-1]]*(length-len(values))
    def build(v):
        if len(v)==1:return f'(.leaf {v[0]})'
        return f'(.node {build(v[::2])} {build(v[1::2])})'
    return build(values)
