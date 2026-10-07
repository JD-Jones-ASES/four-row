"""Write generated Lean using the public, exposed module interface required at intake."""
import re
from pathlib import Path


def module_source(source):
    if source.startswith("module\n"):
        return source
    source = re.sub(r"^import ", "public import ", source, flags=re.M)
    imports = list(re.finditer(r"^public import [^\n]+\n", source, re.M))
    position = imports[-1].end() if imports else 0
    source = source[:position] + "\n@[expose] public section\n" + source[position:]
    return "module\n\n" + source


def write_lean(path, source):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(module_source(source))
    temporary.replace(path)
