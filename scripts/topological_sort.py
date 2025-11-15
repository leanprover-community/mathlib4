#!/usr/bin/env python3

import os
import re
from collections import defaultdict
from typing import Dict, List, Set

def find_lean_files(root_dir: str) -> List[str]:
    """Find all .lean files in the given directory and its subdirectories."""
    lean_files = []
    for root, _, files in os.walk(root_dir):
        for file in files:
            if file.endswith('.lean'):
                lean_files.append(os.path.join(root, file))
    return lean_files

def extract_imports(file_path: str) -> List[str]:
    """Extract import statements from a Lean file."""
    imports = []
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
            # Match import statements that start with 'import'
            import_matches = re.finditer(r'^import\s+([^\s#]+)', content, re.MULTILINE)
            for match in import_matches:
                imports.append(match.group(1))
    except Exception:
        pass
    return imports

def get_module_path(file_path: str) -> str:
    """Convert a file path to a module path."""
    rel_path = os.path.relpath(file_path, 'Mathlib')
    module_path = rel_path.replace('/', '.').replace('\\', '.')[:-5]
    return 'Mathlib.' + module_path

def build_dependency_graph(files: List[str]) -> Dict[str, Set[str]]:
    """Build a dependency graph from the files and their imports."""
    dependencies = defaultdict(set)

    for file_path in files:
        module_path = get_module_path(file_path)
        imports = extract_imports(file_path)
        for imp in imports:
            if imp.startswith('Mathlib.'):
                dependencies[module_path].add(imp)

    return dependencies

def topological_sort(dependencies: Dict[str, Set[str]]) -> List[str]:
    """Perform topological sort on the dependency graph.
    If A imports B, then B comes before A in the output."""
    result = []
    visited = set()
    temp_mark = set()  # Used in depth-first search to detect cycles

    def visit(node: str):
        if node in temp_mark:
            return  # Skip if we hit a cycle
        if node in visited:
            return

        temp_mark.add(node)
        for imp in dependencies.get(node, set()):
            visit(imp)
        temp_mark.remove(node)
        visited.add(node)
        result.append(node)

    # Visit all nodes
    nodes = set(dependencies.keys()) | {dep for deps in dependencies.values() for dep in deps}
    for node in nodes:
        if node not in visited:
            visit(node)

    return result

def main():
    lean_files = find_lean_files('Mathlib')
    if not lean_files:
        return

    dependencies = build_dependency_graph(lean_files)
    if not dependencies:
        return

    sorted_modules = topological_sort(dependencies)
    for module in sorted_modules:
        print(module)

if __name__ == '__main__':
    main()
